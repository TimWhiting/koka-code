import std/data/json
import std/data/bytes
import std/os/net
import uv/net
import std/async
import rpc/json
import parsers/alex/json-parse

value struct rhandler<p,v>
  call: (maybe<p>) -> pure maybe<v>
  from-json: (json, string) -> pure p
  to-json: (v) -> pure json;

struct request<p>
  id: maybe<int>
  method: string
  params: maybe<p>

value struct response<p>
  id: maybe<int>
  res: either<json-rpc/error, p>

value struct error
  code: int
  message: string
  data: maybe<json>

val parse-error = -32700
val invalid-request = -32600
val method-not-found = -32601
val invalid-params = -32602
val internal-error = -32603

fun server-error(code: int): bool
  code >= -32000 && code <= -32099

fun request/from-json(j: json, path: string, ?from-json: (json, string) -> pure p): pure request<p>
  val j1 = j.as-object(path)
  Request(j1.from-json("id", path), j1.from-json("method", path), j1.from-json("data", path))

fun request/to-json(self: request<p>, ?p/to-json: (p) -> pure json): pure json
  JSObj([
    ("id", self.request/id.to-json),
    ("method", self.method.to-json),
    ("data", self.params.to-json),
    ("jsonrpc", "2.0".to-json)
  ])

fun response/from-json(j: json, path: string, ?from-json: (json, string) -> pure p): pure response<p>
  val j1 = j.as-object(path)
  Response(j1.from-json("id", path), j1.from-json("error", "result", path))

fun response/to-json(self: response<p>, ?to-json: (p) -> pure json): pure json
  JSObj([
    ("id", self.response/id.to-json),
    ("jsonrpc", "2.0".to-json),
    self.res.to-json("error", "result")
  ])

fun error/from-json(j: json, path: string): pure json-rpc/error
  val j1 = j.as-object(path)
  Error(j1.from-json("code", path), j1.from-json("message", path), j1.from-json("data", path))

fun error/to-json(j: json-rpc/error): pure json
  JSObj([
    ("code", j.code.to-json),
    ("message", j.message.to-json),
    ("data", j.data.to-json)
  ])

fun tcp-server(handlers: list<(string, rhandler<p,v>)>): <async,io> ()
  val server = tcp()
  server.bind("0.0.0.0", 8000)
  val connections = server.listen
  while({True}, {handleConnections(handlers, connections)})

effect finish
  final ctl finish(): a

fun handleExn(action: () -> <exn,finish|e> a, onExn: () -> <finish|e> ()): <finish|e> a
  match try({action()})
    exn/Error ->
      onExn()
      finish()
    Ok(x) -> x

fun tryD(default: a, action: () -> <exn|e> a): e a
  match try({action()})
    exn/Error -> default
    Ok(x) -> x

fun handleRequests(handlers: list<(string, rhandler<p,v>)>, connection: uv-stream): <asyncx,div> ()
  val channel = connection.stream 
  while {True}
    val buf = channel.receive
    // Jump out after sending fail response
    with handler final ctl finish() ()
    // Parse JSON
    val req-json = handleExn({json/parse(buf.string)}) fn()
      val to-json = error/to-json
      connection.write(Response(Nothing, Left(Error(parse-error, "Parse Error", Nothing))).response/to-json.show.bytes)
    // Parse request
    val req: request<json> = handleExn({req-json.from-json("root")}) fn()
      val id: maybe<int> = tryD(Nothing) fn()
        req-json.as-object("root").dict/from-json("id", "")
      val to-json = error/to-json
      connection.write(Response(id, Left(Error(invalid-request, "Invalid Request: Json Deserialization Error", Nothing))).response/to-json.show.bytes)
    // Lookup Handler
    match handlers.lookup(fn(m) m == req.method)
      Just(h) -> 
        val from-json = h.from-json
        // Parse strongly typed request json
        val params = handleExn({req.params.maybe(Nothing, fn(x) Just(from-json(x,"root")))}) fn()
          val to-json = error/to-json
          connection.write(Response(req.request/id, Left(Error(invalid-params, "Invalid params", Nothing))).response/to-json.show.bytes)
        // Call the function
        match (h.call)(params)
          Just(resp) ->
            val to-json = h.to-json
            if req.request/id == Nothing then () // Don't send a response to a notification
            else 
              connection.write(Response(req.request/id, Right(resp)).response/to-json.show.bytes)
          Nothing -> ()
      Nothing -> 
        val to-json = error/to-json
        connection.write(Response(Nothing, Left(Error(method-not-found, "Method not found", Nothing))).response/to-json.show.bytes)

fun handleConnections(handlers, connections)
  match connections.receive
    Ok(conn) -> handleRequests(handlers, conn)
    _ -> throw("Error accepting connection")

fun test()
  interleaved({tcp-server(handlers)})
    tcp-client()

val handlers = [
  ("oldest-child", Rhandler(handle-oldest, from-json, to-json))
]

fun handle-oldest(data: maybe<json>)
  Just(Person("John", 30, [], []).to-json)

fun tcp-client()
  val stream = tcp().connect("127.0.0.1", 8000)
  "Sending request...".trace
  stream.write(Request(Just(1), "oldest-child", Just(JSObj([]))).to-json.show.bytes)
  val buf = stream.read
  trace("Got response" ++ buf.string)
  ()

fun main()
  test()
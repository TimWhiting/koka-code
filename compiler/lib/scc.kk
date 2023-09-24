import newstd/data/linearmap
import newstd/data/linearset
import compiler/common/name-collections

alias graph<v> = linearMap<v, list<v>>;
alias edge<v> = (v,v)
alias node<v> = (v,list<v>)

fun nodes(g: graph<v>): list<node<v>>
  g.list

fun graph(es: list<node<v>>, eq: (v, v) -> div bool, showV: (v) -> div string): graph<v>
  linearMap(es, eq, fn(v1, v2) (==)(v1, v2, eq), showV, fn(v) v.show-list(showV))

fun edges(g: graph<v>): list<edge<v>>
  with v <- g.nodes.flatmap
  with w <- v.snd.map
  (v.fst, w)

fun vertices(g: graph<v>): list<v>
  g.nodes.map(fst)

fun successors(g: graph<v>, v: v): list<v>
  g.getDefault(v, [])

fun transpose(g: graph<v>): <> graph<v>
  fun add(e: edge<v>, m:graph<v>): <> graph<v>
    m.update(e.snd,  [], fn(o, r) Cons(e.fst, r))
  g.edges.foldr(g.map(fn (k, v) (k, [])), add)

rec type tree<v>
  Tree
    head: v
    fs: forest<v>

rec type forest<v>
  Forest
    list: list<tree<v>>

fun dff(g: graph<v>): forest<v>
  g.dfs(g.vertices)

fun dfs(g: graph<v>, vs: list<v>): forest<v>
  with unsafe-total
  Forest(vs.map(fn(v) g.tree(v, ref(linearSet([v], g.eq, g.showK))))).prune(g.eq, g.showK)

fun tree(g: graph<v>, v: v, visited: ref<h, linearSet<v>>): <div,read<h>,write<h>> tree<v>
  val f = g.successors(v).flatmap fn(v')
    if (!visited).member(v') then []
    else
      visited.set((!visited).add(v'))
      [g.tree(v'.unsafe-decreasing, visited)]
  Tree(v, Forest(f))

alias vset<v> = linearSet<v>;

fun prune(fs: forest<v>, eq: (v,v) -> div bool, showV: (v) -> div string): forest<v>
  fun chop(ms: vset<v>, fs1: forest<v>): (vset<v>, forest<v>)
    match fs1.list
      [] -> (ms, Forest([]))
      Cons(Tree(v, vs), fs2) ->
        if ms.member(v) then chop(ms.unsafe-decreasing, Forest(fs2))
        else
          val ms0 = ms.add(v)
          val (ms1, vs') = chop(ms0.unsafe-decreasing, vs.unsafe-decreasing)
          val (ms2, fs2') = chop(ms1.unsafe-decreasing, Forest(fs2).unsafe-decreasing)
          (ms2, Forest(Cons(Tree(v, vs'), fs2'.list)))
  linearSet([], eq, showV).chop(fs).snd

fun preorder(g: graph<v>): list<v>
  with unsafe-total
  g.dff.preorderF

fun preorderF(f: forest<v>): div list<v>
  f.list.flatmap(preorderT)

fun preorderT(t: tree<v>): div list<v>
  Cons(t.head, t.fs.preorderF)

fun postorder(g: graph<v>): list<v>
  g.dff.postorderF

pub fun postorderF(f: forest<v>): list<v>
  with unsafe-total
  postorderF'(f.list, [])

fun postorderT'(t: tree<v>, vs: list<v>): div list<v>
  postorderF'(t.fs.list, Cons(t.head, vs))

fun postorderF'(ts: list<tree<v>>, vs: list<v>): div list<v>
  match ts
    [] -> vs
    Cons(t, ts') -> postorderT'(t, postorderF'(ts', vs))

fun scc(nodes: list<node<v>>, eq: (v, v) -> div bool, showV: (v) -> div string): list<list<v>>
  sccG(nodes.graph(eq, showV))

fun sccG(g: graph<v>): list<list<v>>
  with unsafe-total
  g.sccF.map(preorderT)

fun sccF(g: graph<v>): list<tree<v>>
  g.transpose.dfs(g.topsort).list.reverse

fun topsort(g: graph<v>): list<v>
  g.postorder.reverse

fun reachable(g: graph<v>, v: v): list<v>
  with unsafe-total
  g.dfs([v]).preorderF

fun path(g: graph<v>, v: v, w: v): bool
  g.reachable(v).find(fn(e) (g.eq)(e, w)).is-just

// fun main()
//   // "".println
//   scc([(0,[1]),(1,[1,2,3]),(2,[1]),(3,[]),(4,[])], (==)).show-list(fn(l) l.show-list(show)).println
//   scc([('a',"jg".list)
//     ,  ('b',"ia".list)
//     ,  ('c',"he".list)
//     ,  ('d',"".list)
//     ,  ('e',"jhd".list)
//     ,  ('f',"i".list)
//     ,  ('g',"fb".list)
//     ,  ('h',"".list)], (==)).show-list(fn(l) l.show-list(show)).println

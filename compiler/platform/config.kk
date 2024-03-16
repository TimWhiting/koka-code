import std/os/env

pub effect val comp-flags: compilerFlags;

fun @default-comp-flags(f){
  with handler val comp-flags = CompilerFlags(
    programName = "koka",
    version = "0.9.0",
    compiler = "koka",
    buildVariant = "release"
  )
  f()
}

struct compilerFlags
  programName: string
  version: string
  compiler: string
  buildVariant: string;

struct fileConfig
  exeExt: string
  dllExt: string
  objExt: string
  libExt: string
  libPrefix: string;

fun os-config(): <exn,ndet> fileConfig
  match get-os-name()
    "linux" -> FileConfig(".so", ".o", ".a", "lib", "")
    "windows" -> FileConfig(".exe", ".dll", ".obj", ".lib", "")
    "macos" -> FileConfig(".dylib", ".o", ".a", "lib", "")

val source-ext = ".kk"

fun is-path-sep(c: char): bool
  c == '/' || c == '\\'
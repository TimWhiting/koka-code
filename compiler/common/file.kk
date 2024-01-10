import std/os/path
import std/os/file
import compiler/platform/config

fun is-literal-doc(fname: path)
  fname.string.ends-with(source-ext ++ ".md").is-just ||
  fname.string.ends-with(source-ext ++ ".mdk").is-just

// File names
alias fileName = path

fun normalize(fname: fileName)
  fname.string.path // path normalizes it to unix endings
// TODO: Lots


// TODO: Lots
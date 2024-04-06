//-----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------

import std/os/path
import std/os/file
import compiler/platform/config
import std/os/env
import std/core/unsafe
import std/os/process
import newstd/core

fun is-literal-doc(fname: path)
  fname.string.ends-with(source-ext ++ ".md").bool ||
  fname.string.ends-with(source-ext ++ ".mdk").bool

// -------------------------
// File names
// -------------------------
alias fileName = path

// Remove the extension and directory part
fun basename(p: fileName): fileName
  p.nodir.noext

// extname - Get the file extension (already part of std/os/path)

fun ensure-ext(p: fileName, ext: string): fileName
  p.change-ext(ext)

// dirname - Return the directory prefix (including last separator if present) (already part of std/os/path)

// notdir -- Remove the directory prefix (already part of std/os/path as nodir)

// notext -- Remove the extension (already part of std/os/path as noext)

// undelim-paths - Split a string of paths into a list of file names (already part of std/os/path as paths)

// split-path - Split a path into its directory parts (already part of std/os/path as dirparts)

fun on-windows(): bool
  with unsafe-total
  get-os-name() == "windows"

// join-path / join-paths - Join a list of file names into a single path (already part of std/os/path as (/))

// normalize - Normalize path separators (.path on string already does this)

// normalize-with 
fun normalize-with(p: fileName, sep: char): string
  p.dirparts.join(sep.string)

// is-path-sep - Is this a file separator? - regardless of host OS 
fun is-path-sep(c: char): bool
  c == '/' || c == '\\'

// is-path-delimiter - Is this a path delimiter? - regardless of host OS
fun is-path-delimiter(c: char): bool
  c == ':' || c == ';'

// run-system-raw 
fun run-system-raw(cmd: string): io ()
  val res = process/run-system(cmd)
  if res == 0 then ()
  else
    throw("Command failed: " ++ cmd)

fun run-system(cmd: string): io ()
  val res = run-system-ex(cmd)
  if res == 0 then ()
  else
    throw("Command failed: " ++ cmd)

fun run-system-ex(cmd: string): io int
  cmd.path.normalize-with(pathsep().head-char.default('/')).process/run-system

fun run-cmd(cmd: string, args: list<string>): io ()
  val res = process/run-system(cmd ++ " " ++ args.join(" "))
  if res == 0 then ()
  else
    throw("Command failed: (exit code " ++ res.show ++ ")")

// TODO: Need stderr in the output, and setting the child processes environment - not supported by the koka std libraries yet
fun run-cmd-read(env: env, cmd: string, args: list<string>): io string
  val res = process/run-system-read(cmd ++ " " ++ args.join(" "))
  match res
    Ok(s) -> s 
    Error(s) -> throw("Command failed: (exit code " ++ s.show ++ ")")

// TODO: Need setting the child processes environment - not supported by the koka std libraries yet
fun run-cmd-env(env: env, cmd: string, args: list<string>): io ()
  val res = process/run-system(cmd ++ " " ++ args.join(" "))
  if res == 0 then ()
  else
    throw("Command failed: (exit code " ++ res.show ++ ")")

fun build-env(env: env): io maybe<env>
  if env.is-empty then return Nothing
  val old = get-env()
  Just(env ++ old.filter(fn((k,_)) env.lookup(fn(x) x == k).is-nothing))

// TODO: Missing file time and exists functions - in koka std core - though the libuv branch would have it
// Compare to file modification times (uses 0 for non-existing files)
// fun file-time-compare(p1: fileName, p2: fileName): io order
// fun max-file-time
// fun max-file-times
// fun does-file-exist-and-not-empty

// read-text-file (already part of std/os/file)
// write-text-file (already part of std/os/file)

fun copy-text-file(src: path, dest: path): io ()
  file/write-text-file(dest, file/read-text-file(src))

fun copy-text-file-with(src: path, dest: path, transform: (string) -> <io|e> string): <io|e> ()
  file/write-text-file(dest, transform(file/read-text-file(src)))

// binary modes are not supported in koka std lib yet - but are in libuv branch
// copy-binary-file
// copy-binary-if-newer

// Don't have file times / file exists except in libuv branch
// fun copy-text-if-newer
// fun copy-text-if-newer-with
// fun remove-file-if-exists

// get-program-path (already in std/os/path as app-path())

fun common-path-prefix(p1: path, p2: path): io string
  p1.dirparts.zip(p2.dirparts).take-while(fn((a,b)) a == b).map(fst).join(pathsep())

fun default/relative-to-path(pprefix: path, p: path): ndet path
  match maybe/relative-to-path(pprefix, p)
    Just(r) -> r
    Nothing -> p

fun maybe/relative-to-path(pprefix: path, p: path): ndet maybe<path>
  if pprefix.string == "" then Just(p)
  else
    val prefs = pprefix.dirparts
    val ps = p.dirparts
    if prefs.is-prefix-of(ps) then
      Just(ps.drop(prefs.length).join(pathsep()).path)
    else
      Nothing

// is-absolute (already part of std/os/path)

// Find a maximal prefix path given a path and a list of root paths. Returns the root path and relative path.
fun find-maximal-prefix-path(p: path, roots: list<path>): ndet maybe<(path, path)>
  val rels = roots.map(fn(r) 
        match r.maybe/relative-to-path(p)
          Just(rel) -> [(r, rel)]
          Nothing -> []
      ).concat
  match rels
    [] -> Nothing
    xs -> xs.maximum-by(fn((r1, _), (r2, _)) r1.path/show.cmp(r2.path/show))

// Get the maximal relative path
fun get-maximal-prefix-path(p: path, roots: list<path>): ndet (path, path)
  match find-maximal-prefix-path(p, roots)
    Just(rel) -> rel
    Nothing -> ("".path,p)

//----------------------------------
// File searching
//----------------------------------
// TODO: Need file exists function
// fun search-paths
// fun search-paths-suffixes
// fun search-paths-canonical

// Make a file path relative to a set of given paths: return the (maximal) root and stem
// if it is not relative to the paths, return dirname/notdir 
fun make-relative-to-paths(p: path, roots: list<path>): ndet (path, path)
  match find-maximal-prefix-path(p, roots)
    Just(rel) -> rel
    Nothing -> (p.dirname.path, p.nodir)


// TODO: More
fun get-env-paths(n: string): io list<path>
  get-env-value(n).default("").paths

// get-env-var (already part of std/os/env as get-env-value)

// real-path (already part of std/os/path as realpath I think - may not have same behavior)

// TODO: Need file exists function
// fun search-program
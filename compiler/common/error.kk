//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------
// Updated as of 7/23/24: Commit aa9474d

import compiler/common/range
import compiler/common/message
import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/lib/printer
import newstd/core
import std/os/path

//------------------------------
// Error and warning messages
//------------------------------

// Error messages
alias errors = list<error-msg>;

alias warnings = errors;

struct error-msg
  range: range
  message: doc
  severity: error-severity
  kind: error-kind

type error-severity
  SevInfo
  SevWarning
  SevError

type error-kind
  ErrGeneral
  ErrParse
  ErrStatic
  ErrKind
  ErrType
  ErrBuild
  ErrInternal

fun range(errs: errors): range
  errs.map(range).combine

fun err/show(err: error-msg): div string
  err.pretty.show

fun errs/show(errs: errors): div string
  errs.pretty.show

fun err-sev/cmp(e1: error-severity, e2: error-severity): order
  match e1
    SevInfo ->
      match e2
        SevInfo -> Eq
        _ -> Lt
    SevWarning ->
      match e2
        SevInfo -> Gt
        SevWarning -> Eq
        _ -> Lt
    SevError ->
      match e2
        SevError -> Eq
        _ -> Gt
    
fun is-warning(e: error-msg): bool
  e.severity <= SevWarning

fun info-message-kind(ekind: error-kind, rng: range, d: doc): error-msg
  Error-msg(rng, d, SevInfo, ekind)

fun warning-message-kind(ekind: error-kind, rng: range, d: doc): error-msg
  Error-msg(rng, d, SevWarning, ekind)

fun error-message-kind(ekind: error-kind, rng: range, d: doc): error-msg
  Error-msg(rng, d, SevError, ekind)

fun warning-message(rng: range, d: doc): error-msg
  warning-message-kind(ErrGeneral, rng, d)

fun error-message(rng: range, d: doc): error-msg
  error-message-kind(ErrGeneral, rng, d)

//---------------------------------
// pretty
//---------------------------------
fun err/pretty(msg: error-msg): doc
  with color-scheme-default
  msg.pp-error-message("".path, False)

fun errs/pretty(msgs: errors): doc
  with color-scheme-default
  msgs.pp-errors("".path, False)

fun pp-error-severity(sev: error-severity, ekind: error-kind): colorSchemeEffect doc
  val ekindTxt = match ekind
    ErrParse -> "parse"
    ErrKind -> "kind"
    ErrType -> "type"
    ErrBuild -> "build"
    ErrInternal -> "internal"
    _ -> ""
  fun header(clr: colorScheme -> color, txt: string)
    text(ekindTxt ++ txt ++ ":").color(clr(colors))
  match sev
    SevError -> header(colorError, "error")
    SevWarning -> header(colorWarning, "warning")
    SevInfo -> header(colorWarning, "info")

fun pp-error-message(msg: error-msg, cwd: path, showRangeEnd: bool): colorSchemeEffect doc
  (msg.range.pp-range(cwd,showRangeEnd)
  |.| colon |+| msg.severity.pp-error-severity(msg.kind) |+| msg.message
  ).hang(2)

fun pp-errors(errs: errors, cwd: path, showRangeEnd: bool): colorSchemeEffect doc
  vcat(errs.map(fn(e) e.pp-error-message(cwd, showRangeEnd)))

fun to-warning((range, doc): (range, doc), ekind: error-kind): error-msg
  warning-message-kind(ekind, range, doc)

//--------------------
// Errors Monad
//--------------------

effect comp-error<p> // Partial result p
  final ctl comp-errors(errs: errors): a
  fun comp-add-warnings(w: warnings): ()
  fun set-partial(a: p): ()

fun comp-error(err: error-msg): comp-error<p> a
  comp-errors([err])

fun comp-warn(msg: error-msg): comp-error<p> ()
  comp-add-warnings([msg])

// check an 'error'
fun check-error(f: () -> comp-error<p> a): either<errors, (a, warnings)>
  var warns := []
  with handler
    final ctl comp-errors(errs) Left(errs)
    fun comp-add-warnings(w) warns := w ++ warns
    fun set-partial(a) ()
    return(x) Right((x, warns))
  f()

fun check-partial(f: () -> comp-error<p> a): div either<(errors, maybe<p>), (a, warnings, maybe<p>)>
  var warns := []
  var partial := Nothing
  with handler
    final ctl comp-errors(errs) Left((errs, partial))
    fun comp-add-warnings(w) warns :=  w ++ warns
    fun set-partial(a) partial := Just(a)
    return(x) Right((x, warns, partial))
  f()

fun handle-error(f: () -> comp-error<p> a, h: errors -> comp-error<p> a): comp-error<p> a
  with handler
    final ctl comp-errors(errs) h(errs)
    fun comp-add-warnings(w) comp-add-warnings(w)
    fun set-partial(a) set-partial(a)
  f()

fun ignore-warnings(f: () -> comp-error<p> a): comp-error<p> a
  with handler
    final ctl comp-errors(errs) comp-errors(errs)
    fun comp-add-warnings(w) ()
    fun set-partial(a) set-partial(a)
  f()
//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 7/23/24: Commit b8074c2

type resumeKind
  ResumeNever
  ResumeTail
  ResumeScopedOnce
  ResumeScoped
  ResumeOnce
  ResumeNormal
  ResumeOnceRaw
  ResumeNormalRaw

fun show(rk: resumeKind)
  match rk
    ResumeNever -> "never"
    ResumeTail -> "tail"
    ResumeScopedOnce -> "scoped once"
    ResumeScoped -> "scoped"
    ResumeOnce -> "once"
    ResumeNormal -> "normal"
    ResumeOnceRaw -> "once (no finalization)"
    ResumeNormalRaw -> "normal (no finalization)"

fun index(rk: resumeKind)
  match rk
    ResumeNever -> 0
    ResumeTail -> 1
    ResumeScopedOnce -> 2
    ResumeScoped -> 3
    ResumeOnce -> 4
    ResumeNormal -> 5
    ResumeOnceRaw -> 6
    ResumeNormalRaw -> 7
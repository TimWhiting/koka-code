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
# Notes on some issues:
Solved Previously:
- [x] Inline function https://github.com/koka-lang/koka/issues/36 ??
- [x] Documentation? https://github.com/koka-lang/koka/issues/118 ??
- [x] Better error message with type inference after default handler insertion around main: https://github.com/koka-lang/koka/issues/126 (need to do better in language server though to proactively do this)
- [x] Nested masks: https://github.com/koka-lang/koka/issues/153
- [x] Nested masks: https://github.com/koka-lang/koka/issues/154
- [x] crash: https://github.com/koka-lang/koka/issues/188 ??
- [x] main val versus fun: https://github.com/koka-lang/koka/issues/201 ??

Potentially Solved:?
- [ ] Effect opening and tail resumptive analysis https://github.com/koka-lang/koka/issues/72
- [ ] ANSI Left on empty output? https://github.com/koka-lang/koka/issues/99
- [ ] Better windows installation (via the script?) https://github.com/koka-lang/koka/issues/175
- [ ] Readline: https://github.com/koka-lang/koka/issues/216

Solved on dev:
- [x] Compiling absolute paths: https://github.com/koka-lang/koka/issues/33
- [x] Effect var error https://github.com/koka-lang/koka/issues/60
- [x] Type inference taking forever https://github.com/koka-lang/koka/issues/138

Solved by implicit parameters / new overloading:
- [x] https://github.com/koka-lang/koka/issues/15
- [x] https://github.com/koka-lang/koka/issues/16
- [x] https://github.com/koka-lang/koka/issues/20 
  (other than adding file information to trace statements -- could be accomplished by throwing the exception and catching it - as a hack?)
- [x] Record access: https://github.com/koka-lang/koka/issues/177 (overloading with prefix / based on type?)

Solved by language server (I think):
- [x] https://github.com/koka-lang/koka/issues/12 - easier installation / published in vscode marketplace
- [-] Better unit test support https://github.com/koka-lang/koka/issues/21 - much more to this though

Unsolved:
Quick solves? or potentially solved:
- [ ] Shebangs: https://github.com/koka-lang/koka/issues/123
- [ ] Error message on typevars in declarations also in usages: https://github.com/koka-lang/koka/issues/158, https://github.com/koka-lang/koka/issues/211
- [ ] Slice to full string (https://github.com/koka-lang/koka/issues/173)
- [ ] There is better documentation, but this check could help: https://github.com/koka-lang/koka/issues/189
- [ ] Named effect val: https://github.com/koka-lang/koka/issues/203
- [ ] Reload - reload even unsuccessful builds in interpreter: https://github.com/koka-lang/koka/issues/208

Documentation / Questions:
- [ ] Relation to Effect Handlers in Scope / Higher order effects: https://github.com/koka-lang/koka/issues/85
- [ ] Good notes from Daan on some keywords here: https://github.com/koka-lang/koka/issues/102
- [ ] Finally clauses without return cause type issues: https://github.com/koka-lang/koka/issues/195, could be a quick fix
- [ ] Missing c libraries error: https://github.com/koka-lang/koka/issues/205

Compiler:
- [!] High memory usage: https://github.com/koka-lang/koka/issues/34
- [!] genFunDefSig error: https://github.com/koka-lang/koka/issues/186
- [??] https://github.com/koka-lang/koka/issues/204 reflection / parsing

StdLib:
- [ ] Renaming of Just / Nothing to Some / None (https://github.com/koka-lang/koka/issues/39)
- [ ] Renaming of double / ddouble to float64 / float128 (partially done)
- [ ] More integer sizes https://github.com/koka-lang/koka/issues/51 good notes from Daan here: https://github.com/koka-lang/koka/issues/101
- [ ] Aync / Map libraries: good notes from Daan (https://github.com/koka-lang/koka/issues/98)
- [ ] One implementation of a Map here: https://github.com/koka-lang/koka/issues/102

Async Related:
- [!] https://github.com/koka-lang/koka/issues/28 - type error? - check this out
- [ ] https://github.com/koka-lang/koka/issues/111 - preemption async - solved by libuv?

Types:
- [!] Bad total effect with coinductive types: https://github.com/koka-lang/koka/issues/7
- [!] Bad total effect with rec types: https://github.com/koka-lang/koka/issues/149
- [ ] Masking synonyms: https://github.com/koka-lang/koka/issues/155
- [ ] Builtin effect for getting file line number / module name / column number (https://github.com/koka-lang/koka/issues/20, https://github.com/koka-lang/koka/issues/21)
- [ ] Introspection of platform (C / C# / Node / JS) maybe builtin effect or something else (https://github.com/koka-lang/koka/issues/21) 
- [ ] Type to runtime errors: https://github.com/koka-lang/koka/issues/26 (run partial programs)
- [ ] Unsafe effect - https://github.com/koka-lang/koka/issues/43

Syntax:
- [ ] General Partial Application syntax: https://github.com/koka-lang/koka/issues/29 (aka easy lambdas)
- [ ] General prefixed string / prefixed collection syntax (https://github.com/koka-lang/koka/issues/22)
- [ ] String interpolation syntax (https://github.com/koka-lang/koka/issues/122)

Ecosystem:
- [ ] Unit testing library (https://github.com/koka-lang/koka/issues/20 and 21?)
- [ ] Package manager (https://github.com/koka-lang/koka/issues/31)
- [ ] Ninja build naming (https://github.com/koka-lang/koka/issues/182)

Tests:
- [ ] Double failures: https://github.com/koka-lang/koka/issues/212

In the works:
- [ ] Better initialization syntax for vectors (Daan is working on this): https://github.com/koka-lang/koka/issues/22

Javascript Related:
- [ ] Better Javascript support (https://github.com/koka-lang/koka/issues/17,https://github.com/koka-lang/koka/issues/95)
- [ ] Sourcemaps (https://github.com/koka-lang/koka/issues/30)
- [ ] Int multiplication? https://github.com/koka-lang/koka/issues/179

Performance:
- [ ] Inlining of field access / copy functions https://github.com/koka-lang/koka/issues/18
- [ ] Dead code elimination - https://github.com/koka-lang/koka/issues/27

Website:
- [ ] Tooltip hover: https://github.com/koka-lang/koka/issues/214

Other:
- [ ] Annotation system https://github.com/koka-lang/koka/issues/38

Outdated?
- [ ] Jakefile? https://github.com/koka-lang/koka/issues/64

Definitely not planning to solve:

## TODO: Backlog - Takes a bit more thought or time to diagnose / understand the issue:
https://github.com/koka-lang/koka/issues/127
https://github.com/koka-lang/koka/issues/141
https://github.com/koka-lang/koka/issues/144
https://github.com/koka-lang/koka/issues/178
Just a question really: misunderstanding of effects & masking
https://github.com/koka-lang/koka/issues/183
Performance
https://github.com/koka-lang/koka/issues/197

## TODO: Pick up here: 204



## Volunteers
- https://github.com/koka-lang/koka/issues/204
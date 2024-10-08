# TODO
Work on Syntax, Parsing, and Formatter

## Fully up to date
// compiler/lib/* 07/23/24 updated
// compiler/common/* 07/23/24 updated - other than parse, and some missing functions in range and file
// compiler/syntax/lexeme & layout 08/05/24, range-map 08/06/24, partial highlight 08/08/24

## Syntax errors

## Changes
- [ ] check all in core/
- [ ] check all in syntax/
- [ ] check all in lib/ (start with finishing printer)
- [ ] check all in kind/
- [ ] changes in backend/c/from-core
- [ ] integrate error effect into core effect alias

- [ ] syntax/promote
- [ ] syntax/parse (move common/parser to newstd/text/parser)
- [ ] static/bindingGroups
- [ ] core/parse
- [ ] (finish kind/infer)
- [ ] kind/inferMonad
- [ ] type/assumption
- [ ] type/operations
- [ ] type/pretty
- [ ] type/unify

## All dependencies ready
- [ ] backend/c/parc 1037
- [ ] backend/c/parcreuse 731
- [ ] backend/c/parcreusespec 341
- [ ] compiler/package 208
- [ ] core/ctail 691
- [ ] core/simplify 970

## Next priority (lots of dependencies require)

## Needs dependencies
- [ ] core/analysismatch 248 - needs type/unify
- [ ] core/check 336 - needs type/unify
- [ ] core/inline 290 - needs simplify
- [ ] core/specialize 498 - needs simplify
- [ ] type/infermonad 1500 - needs type/unify
- [ ] type/infer 2300 - needs type/infermonad, core/analysismatch
- [ ] compiler/module 180 - needs compiler/package
- [ ] compiler/compile 1865 - needs everything
- [ ] main 144 - needs everything
- [ ] platform(as needed)

## Low priority
- [ ] interpreter/commands 318 - can be done
- [ ] syntax/colorize 607 - can be done
- [ ] syntax/highlight 515 - needs isocline
- [ ] backend/csharp/from-core 1884 - can be done
- [ ] backend/javascript/from-core 1371 - can be done
- [ ] core/gendoc 598 - needs colorize / highlight
- [ ] interpreter/interpret 734 - needs everything

# TODO: Language Server
Lots
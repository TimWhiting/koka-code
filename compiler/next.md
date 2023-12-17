# TODO

## Changes
- [ ] syntax/promote
- [ ] syntax/parse
- [ ] syntax/lexer
- [ ] static/bindingGroups
- [ ] core/parse
- [ ] (finish kind/infer)
- [ ] kind/inferMonad
- [ ] lib/printer
- [ ] type/assumption
- [ ] type/operations
- [ ] type/pretty
- [ ] type/unify
- [ ] common/colorScheme
- [ ] error effect for core passes

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
- [ ] backend/csharp/from-core 1884 - can be done
- [ ] backend/javascript/from-core 1371 - can be done
- [ ] common/file 499 - finish as needed
- [ ] syntax/highlight 515 - needs isocline
- [ ] core/gendoc 598 - needs colorize / highlight
- [ ] interpreter/interpret 734 - needs everything

# TODO: Language Server
Lots
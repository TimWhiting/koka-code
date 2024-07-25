cd ../../koka-community/alex
stack build
# stack run alex -- -k ../../koka-code/compiler/syntax/koka.x -o ../../koka-code/compiler/syntax/koka-lex.kk
stack run alex -- -k ../../koka-code/compiler/syntax/koka-eff.x -o ../../koka-code/compiler/syntax/lex2.kk
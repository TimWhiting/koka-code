cd ../../koka-community/alex
stack build
# stack run alex -- -k ../../koka-code/compiler/syntax/old/koka.x -o ../../koka-code/compiler/syntax/old/koka-lex.kk
stack run alex -- -k ../../koka-code/compiler/syntax/koka.x -o ../../koka-code/compiler/syntax/lex.kk
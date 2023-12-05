# koka_code

A bunch of user-space Koka code.

Translations of various programs

Most things are unfinished

The koka compiler translated to koka is the program with the most code, but is ultimately incomplete.

It exists under the namespace `compiler` unlike the Haskell based compiler. This helps avoid naming conflicts with modules such as `core`

Some functions that don't exist in the koka standard library are in `newstd`.

Some of those are really not meant for production usage. 

For example, there is a very basic implementation of set and map interfaces that use linear searches through a list.

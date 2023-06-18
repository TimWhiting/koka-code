import std/sys/dom
import render


fun main()
  withWindow fn (w)
    render(w)
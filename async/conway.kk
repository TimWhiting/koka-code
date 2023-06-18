/*----------------------------------------------------------------------------
   Copyright 2012-2021, Microsoft Research, Daan Leijen.
  
   Licensed under the Apache License, Version 2.0 ("The Licence"). You may not
   use this file except in compliance with the License. A copy of the License
   can be found in the LICENSE file at the root of this distribution.
----------------------------------------------------------------------------*/

// Demo of HTML5 Canvas.

import std/sys/dom
import std/num/random

import tile

struct cell( row : int, col : int, alive : bool )
alias  world = list<list<cell>>
 
pub fun main()
  withWindow fn(w) { 
    gameOfLife(w) 
  } 

fun gameOfLife( window:   window,
                       gridSize: int                  = 50,
                       lineColor: string              = "#cdcdcd",
                       liveColor: string              = "green",
                       deadColor: string              = "#eee",
                       initialLifeProbability: float64 = 0.1,
                       cellSize: float64               = 8.0) 
{   
  val tile   = window.document.createHtmlTileElement()
  val canvas = window.document.createHtmlCanvasElement()
  tile.caption := "Conway's game of life"
  
  var framecounter := 0
  tile.appendChild2(canvas.node)
  canvas.height := 400
  canvas.width := 400

  fun isAlive(world : world, row : int, col : int) : exn bool {  
    ((world[row % gridSize].unjust)[col % gridSize]).unjust.alive
  }

  fun countNeighbors( w : world, c : cell ) : exn int {
    [ w.isAlive(c.row - 1, c.col - 1),
      w.isAlive(c.row - 1, c.col), 
      w.isAlive(c.row - 1, c.col + 1), 
      w.isAlive(c.row, c.col - 1), 
      w.isAlive(c.row, c.col + 1), 
      w.isAlive(c.row + 1, c.col - 1), 
      w.isAlive(c.row + 1, c.col), 
      w.isAlive(c.row + 1, c.col + 1) ].filter(id).length
  }
 
  fun createWorld() : <random> world { 
    list(0, gridSize - 1).map fn(r) {
      list(0, gridSize - 1).map fn(c) { 
        Cell(r,c, random-float64() < initialLifeProbability)
      }
    } 
  }

  fun mapWorld( w : world, f : cell -> e a ) : e list<list<a>> {
    w.map(fn(xs) { xs.map(f) }) 
  } 

  fun evolve( w : world ) : exn world {
    w.mapWorld fn(c) {
      val count = countNeighbors(w,c)
      if(w.isAlive(c.row, c.col)) {
        c( alive = ( count == 2 || count == 3 ) ) 
      } else {
        c( alive = count == 3 ) 
      }
    } 
  }

  fun draw(ctx : canvasRenderingContext2d, c : cell): <dom> () { 
    ctx.strokeStyle := lineColor
    ctx.strokeRect(c.row.float64 * cellSize, c.col.float64 * cellSize, cellSize, cellSize)
    if(c.alive) {
      ctx.fillStyle := liveColor 
    } else {
      ctx.fillStyle := deadColor
    }
    ctx.fillRect(c.row.float64 * cellSize, c.col.float64 * cellSize, cellSize, cellSize)
  }   

  fun loop(ctx : canvasRenderingContext2d, world : world)
  { 
    framecounter := framecounter + 1
    world.mapWorld fn(c) { draw(ctx, c) } 
    timeout(0) fn() { loop(ctx, world.evolve) }
  }


  fun measurePerformance()
  { 
    println( framecounter.show ++ "fps" )
    framecounter := 0 
  }

  loop(canvas.getContext("2d").toCanvasRenderingContext2d, createWorld())
  interval(1000, measurePerformance)
}

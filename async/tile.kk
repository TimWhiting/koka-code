/*----------------------------------------------------------------------------
   Copyright 2012-2021, Microsoft Research, Daan Leijen.
  
   Licensed under the Apache License, Version 2.0 ("The Licence"). You may not
   use this file except in compliance with the License. A copy of the License
   can be found in the LICENSE file at the root of this distribution.
----------------------------------------------------------------------------*/

import std/sys/dom

abstract struct htmlTileElement( element:     htmlElement,
                                 container:   htmlElement,
                                 captionElem:     htmlElement
                               )

pub fun caption( tile : htmlTileElement, assigned : string ) {
  tile.captionElem.innerHtml := assigned;
}

pub fun appendChild2( tile : htmlTileElement, elem : node ) {
  tile.container.appendChild(elem);
}

pub fun createHtmlTileElement(document: document) : <dom,ndet> htmlTileElement
{ 
  val tile      = document.createHtmlDivElement()
  val captionElem = document.createHtmlSpanElement()
  val container    = document.createHtmlDivElement()

  tile.className := "tile"
  captionElem.innerHtml   := "tile"
  captionElem.className   := "caption"
  container.className := "container"
  tile.appendChild(captionElem.node)
  tile.appendChild(container.node)

  document.body.appendChild(tile.node)

  return HtmlTileElement( tile.htmlElement(), container.htmlElement(), captionElem.htmlElement )
}

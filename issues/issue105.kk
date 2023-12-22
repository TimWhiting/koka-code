type imap<a> {
    con Nil
    con Tip { k: int; v: a }
    con Bin { p: something-do-not-exist; m: int; l: do-not-exist<a>; r: do-not-exist<a> }
}
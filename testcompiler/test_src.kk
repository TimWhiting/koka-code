import compiler/lib/printer
fun main(): <console, exn, fsys, ndet> ()
  with consolePrinter
  "hi\xFF".write-ln() // Will not print unicode on Windows
  with monoPrinter
  "hi\xAA".write-ln() // Also will get rid of unicode on Windows
  with newFilePrinter("tmp/tmp1.txt")
  "new".write()
  " file".write-ln()
  flush()
  with filePrinter("tmp/tmp.txt")
  "hi".write()
  " there".write-ln()
  flush()
  with ansiPrinter
  with override val colorSettings = PrintColorSettings(invert=True)
  "hello".ansiWithColor(Red)
  "world".ansiWithColor(Blue)
  with override val colorSettings = PrintColorSettings(underline=True)
  "hello".ansiWithColor(Red)
  "world".ansiWithColor(Blue)
  with override val colorSettings = PrintColorSettings()
  "hello".ansiWithColor(Red)
  "world".ansiWithColor(Blue)
  ansiWithConsole(PrintColorSettings(fcolor=Green))
    "hello ".write()
    "world!".write-ln()
  ansiWithConsole(PrintColorSettings(fcolor=DarkYellow, invert=True))
    "This is crazy, ".write()
    ansiWithConsole(PrintColorSettings(fcolor=DarkCyan, underline=True))
      "but it's ok".write-ln()





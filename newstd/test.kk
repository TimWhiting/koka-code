fun expect(f: () -> <exn,console> bool, error: string = ""): console ()
  try(
    fn() {
      if !f() then
        if (error == "") then
          println("Error in test")
        else
          println(error)
      else
        println("Test passed")
    },
    fn (e) {
      println("Exception in test: " ++ e.show ++ ":\n" ++ error)
    }
  )
  

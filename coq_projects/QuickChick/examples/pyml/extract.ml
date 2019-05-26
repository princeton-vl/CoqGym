open Py;;

initialize ();;

let plus x y =
  let foo = import "foo" in
  let py_plus = Module.get_function foo (*!*) "plus" (*! "mult" *) in
  Int.to_int (py_plus [| Int.of_int x; Int.of_int y |])

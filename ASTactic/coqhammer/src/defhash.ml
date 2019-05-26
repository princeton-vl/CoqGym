(* Definitions hash *)

open Coqterms

let defhash = Hashtbl.create 1024

let add_lazy name x =
  if Hashtbl.mem defhash name then
    failwith ("duplicate global definition of " ^ name);
  Hashtbl.add defhash name (ref x)

let add x =
  add_lazy (coqdef_name x) (lazy x)

let remove name =
  Hashtbl.remove defhash name

let clear () = Hashtbl.clear defhash

let find name =
  try
    Lazy.force !(Hashtbl.find defhash name)
  with Not_found ->
    failwith ("Defhash.find: " ^ name)

let mem name = Hashtbl.mem defhash name

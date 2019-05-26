open Sexplib.Conv

module Loc = Ser_loc
module Names = Ser_names
module Libnames = Ser_libnames
module Locus = Ser_locus
(* module Globnames = Ser_globnames *)

type h1 = Libnames.qualid list
[@@deriving sexp]

type h2 = Names.GlobRef.t Loc.located Locus.or_var list
[@@deriving sexp]

type h3 = Names.GlobRef.t list
[@@deriving sexp]

let ser_wit_firstorder_using :
  (Libnames.qualid list,
   Names.GlobRef.t Loc.located Locus.or_var list,
   Names.GlobRef.t list) Ser_genarg.gen_ser =
  Ser_genarg.{
    raw_ser = sexp_of_h1;
    raw_des = h1_of_sexp;

    glb_ser = sexp_of_h2;
    glb_des = h2_of_sexp;

    top_ser = sexp_of_h3;
    top_des = h3_of_sexp;
  }

let register () =
  Ser_genarg.register_genser Ground_plugin.G_ground.wit_firstorder_using ser_wit_firstorder_using;
  ()

let _ = register ()

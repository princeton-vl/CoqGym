open Sexplib.Conv

module CAst       = Ser_cAst
module Libnames   = Ser_libnames
module Constrexpr = Ser_constrexpr
module Tactypes   = Ser_tactypes
module Genintern  = Ser_genintern
module EConstr    = Ser_eConstr
module Tacexpr    = Ser_tacexpr

module Ltac_plugin = struct
  module Tacexpr = Ser_tacexpr
end

type 'constr coeff_spec =
  [%import: 'constr Newring_plugin.Newring_ast.coeff_spec]
  [@@deriving sexp]

type cst_tac_spec =
  [%import: Newring_plugin.Newring_ast.cst_tac_spec]
  [@@deriving sexp]

type 'constr ring_mod =
  [%import: 'constr Newring_plugin.Newring_ast.ring_mod]
  [@@deriving sexp]

type 'a field_mod =
  [%import: 'a Newring_plugin.Newring_ast.field_mod]
  [@@deriving sexp]

let ser_wit_field_mod =
  Ser_genarg.
    { raw_ser = sexp_of_field_mod Constrexpr.sexp_of_constr_expr
    ; raw_des = field_mod_of_sexp Constrexpr.constr_expr_of_sexp

    ; glb_ser = sexp_of_unit
    ; glb_des = unit_of_sexp

    ; top_ser = sexp_of_unit
    ; top_des = unit_of_sexp
  }

let ser_wit_field_mods =
  Ser_genarg.
    { raw_ser = sexp_of_list (sexp_of_field_mod Constrexpr.sexp_of_constr_expr)
    ; raw_des = list_of_sexp (field_mod_of_sexp Constrexpr.constr_expr_of_sexp)

    ; glb_ser = sexp_of_unit
    ; glb_des = unit_of_sexp

    ; top_ser = sexp_of_unit
    ; top_des = unit_of_sexp
  }

let ser_wit_ring_mod =
  Ser_genarg.
    { raw_ser = sexp_of_ring_mod Constrexpr.sexp_of_constr_expr
    ; raw_des = ring_mod_of_sexp Constrexpr.constr_expr_of_sexp

    ; glb_ser = sexp_of_unit
    ; glb_des = unit_of_sexp

    ; top_ser = sexp_of_unit
    ; top_des = unit_of_sexp
  }

let ser_wit_ring_mods =
  Ser_genarg.
    { raw_ser = sexp_of_list (sexp_of_ring_mod Constrexpr.sexp_of_constr_expr)
    ; raw_des = list_of_sexp (ring_mod_of_sexp Constrexpr.constr_expr_of_sexp)

    ; glb_ser = sexp_of_unit
    ; glb_des = unit_of_sexp

    ; top_ser = sexp_of_unit
    ; top_des = unit_of_sexp
  }

let register () =
  Ser_genarg.register_genser Newring_plugin.G_newring.wit_field_mod  ser_wit_field_mod;
  Ser_genarg.register_genser Newring_plugin.G_newring.wit_field_mods ser_wit_field_mods;
  Ser_genarg.register_genser Newring_plugin.G_newring.wit_ring_mod  ser_wit_ring_mod;
  Ser_genarg.register_genser Newring_plugin.G_newring.wit_ring_mods ser_wit_ring_mods;
  ()

let _ = register ()

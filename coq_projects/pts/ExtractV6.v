Require Import MlExtract.
Require Import General.
Require Import CoqV6.

Extraction
 Inline Acc3_rec full_cts_type_checker v6_algorithms lift_naif subst_naif.
(*
Extraction NoInline
 pred typ_of_decl
 v6_is_subtype_dec
 cts_prim_algos

(* algos generaux a ne pas expanser *)
 is_a_sort cumul_least_sort cumul_least_prod

(* algos specifiques ecc *)
 calc_dec v6_sort_dec v6_inf_rule v6_inf_axiom (*ecc_algorithms*)

(* acces aux champs des records *)
 pa_infer_axiom pa_infer_rule
 pa_lift pa_subst pa_least_sort pa_least_prod pa_le_type_dec
 scts_whnf scts_convert_hn scts_rt_univ_dec

(* NE PAS EXPANSER: *)
 full_ppal_type (*full_type_checker*)

 tmp_add_typ tmp_check_typ_when_wf tmp_check_wf_type.
*)

Set Extraction AccessOpaque.

Extraction
 "kernel" env_v6 check_type infer_type check_wf_type add_type add_def
         sort_of_gen gen_of_sort.
(* File: Extr_compute_derivations.v  (last edited on 1/11/2000) 
   (c) Klaus Weich  *)

Require Import Search.
Require Extraction.

Unset Extraction Optimize.
Set Extraction AccessOpaque.

(*
Extract Inductive unit => unit [ "()" ].
Extract Inductive bool => bool [ true false ].
Extract Inductive sumbool => bool [ true false ].
*)



 Extract Inlined Constant Int => "int".
 Extract Inlined Constant int_null => "0".
 Extract Inlined Constant int_succ => "succ".
 Extract Inlined Constant equal_dec => "(=)".
 Extract Inlined Constant less_dec => "(<)".

 Extract Inductive sumbool => "bool" [ "true" "false" ].



 Extraction
 NoInline rebalance_left rebalance_right balance_left balance_right
         balance_shrunk_left balance_shrunk_right delete_max lookup_dec
         insert_avl delete_avl lin_avl filter_deco le_app0 inv_nth_app
         rule_shift_work_ni0 rule_shift_work_ds shift_ni_dni
         rule_shift_work_a rule_shift_work_ai_new rule_shift_work_ai_old
         contradiction_atoms fail nax nefq left_p_imp_ai left_p_imp_work
         left_disj left_nimp My_Lt_Ks_rec snd_order_inst derivable_subst
         sound_cons_gamma_weak sound_cons_gamma_weak2
         search_spec_subst_gamma_pos rule_shift_gamma_work rule_vimp_a_gamma
         rule_vimp_imp_gamma rule_gamma_falsum rule_gamma_a_imp_b
         rule_gamma_a rule_vimp_conj_gamma rule_vimp_conj_gamma_new
         rule_vimp_falsum_or_a_gamma rule_vimp_a_or_falsum_gamma
         rule_vimp_atom_or_a_gamma rule_vimp_a_or_b_gamma
         rule_vimp_falsum_imp_b_gamma rule_vimp_atom_imp_b_gamma
         rule_vimp_and_imp_gamma rule_vimp_or_imp_gamma
         rule_vimp_or_imp_gamma_new rule_vimp_falsum_imp_imp_gamma
         rule_vimp_imp_falsum_imp_gamma rule_atom_imp_atom_imp_c_gamma
         rule_atom_imp_b_imp_c_gamma rule_a_imp_b_imp_c_gamma nsearch.


 Extraction "search.ml" search.
 Extraction Language Haskell. 
 Extraction "search.hs" search.





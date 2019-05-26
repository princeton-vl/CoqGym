Require Import Le Max List Bool Cecoa.Lib Cecoa.Syntax Cecoa.CBV_cache NPeano Omega Cecoa.OptionMonad.

Section QI.

Variables variable function constructor : Type.

Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).
Notation term_from_value := (Syntax.term_from_value variable function (constructor:=constructor)).
Notation term_from_pattern := (Syntax.term_from_pattern (variable:=variable) function (constructor:=constructor)).
Variable prog : list rule.
Variable max_arity:nat.
Variable rule_default : rule.

Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.
Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.
Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Notation cache := (CBV_cache.cache variable function constructor).
Notation cache_path := (CBV_cache.cache_path variable_eq_dec function_eq_dec constructor_eq_dec).



Notation cache_path_transitivity := 
           (@CBV_cache.cache_path_transitivity _ _ _ variable_eq_dec function_eq_dec constructor_eq_dec).
Notation cache_path_transitivity_left :=
           (@CBV_cache.cache_path_transitivity_left _ _ _ variable_eq_dec function_eq_dec constructor_eq_dec).
Notation cbv := (CBV_cache.cbv variable function constructor).
Notation wf := (CBV_cache.wf variable_eq_dec  function_eq_dec constructor_eq_dec rule_default
                prog max_arity).

(*Definition 11*)
Definition assignment_constructor := constructor -> list nat -> nat.
Definition assignment_function := function -> list nat -> nat.

(*****************************************************************************************)
(*                  QI of constructors / value                                           *)
(*****************************************************************************************)

(* additivity*)
Variable mcs: nat.

Definition constructor_non_zero cs :=
   forall c:constructor, cs  c > 0. 

Definition additive (qic:assignment_constructor) cs :=
   forall c:constructor, forall l, qic c l=(suml l)+(cs c).

Definition mcs_is_max_constructor_size cs :=
    forall c:constructor, cs c <= mcs.

Lemma monotonicity_qic qic cs: additive qic cs -> forall c:constructor,
  forall lx ly, Forall2 le lx ly -> qic c lx <= qic c ly.
Proof.
intro additivity;intros.
unfold additive in additivity.
rewrite additivity;rewrite additivity.
apply Plus.plus_le_compat_r;trivial.
induction H;auto;simpl.
apply Plus.plus_le_compat;trivial.
Qed.

(* assignment of a value*)
Fixpoint value_assignment (qic:assignment_constructor) (v:value) {struct v}:=
   match v with
  | c_capply c lv => qic c (map (value_assignment qic) lv)
   end.

(*Lemma 67 borne inf *)
Lemma value_size_le_QI qic cs: 
  additive qic cs -> constructor_non_zero cs ->
  forall v:value, value_size v <= value_assignment qic v.
Proof.
intros additivity non_zero.
unfold additive in additivity. unfold constructor_non_zero in non_zero.
induction v using value_ind2.
simpl.
apply le_trans with (m:=suml (map (value_assignment qic) l)+1).
- apply le_trans with (m:=S (suml (map (value_assignment qic) l)));try omega. (* j'ai du mal avec S/+1 *)
  rewrite <- Nat.succ_le_mono.
  apply suml_map_le;trivial.
- rewrite additivity.
  apply Plus.plus_le_compat_l.
  apply (non_zero c).
Qed.

(*Lemma 67 borne sup *)
Lemma QI_le_value_size qic cs: 
  additive qic cs -> mcs_is_max_constructor_size cs ->
  forall v:value, 
  value_assignment qic v <= mcs*(value_size v).
Proof.
intros additivity max_cs.
unfold additive in additivity. unfold mcs_is_max_constructor_size in max_cs.
induction v using value_ind2.
simpl.
rewrite additivity.
apply le_trans with (m:=suml (map (value_assignment qic) l)+mcs).
- apply Plus.plus_le_compat_l.
  apply max_cs.
- replace (S (suml (map (value_size (constructor:=constructor)) l))) 
          with ((suml (map (value_size (constructor:=constructor)) l)+1));try omega.
  (* comment remplacer automatiquement S x par x+1 pour pouvoir appliquer la distributivité ? *)
  rewrite Mult.mult_plus_distr_l;rewrite Mult.mult_1_r;apply Plus.plus_le_compat_r.
  rewrite mult_suml_r;rewrite map_map.
  apply suml_map_le;trivial.
Qed.

(*****************************************************************************************)
(*                  QI of function symbols / terms                                       *)
(*****************************************************************************************)

(* c'est cette forme qui est utilisée partout *)
Definition subterm (qif:assignment_function) := forall f l x, In x l -> x <= qif f l.

(*monotonicity*)
Definition monotonicity_qif (qif:assignment_function) :=
  forall f lx ly, Forall2 le lx ly -> qif f lx <= qif f ly.



(* assignment of a term*)
Fixpoint term_assignment (qic:assignment_constructor) (qif:assignment_function)
(t:term) {struct t}:=
   match t with
  | var v=> 0 (* pas necessaire. Les QI sont toujours appliquées sur des termes clots. *)
  | capply c lt => qic c (map (term_assignment qic qif) lt)
  | fapply f lt=> qif f (map (term_assignment qic qif)  lt) 
 end.

(*Definition 12*)
Definition compatible_QI qic qif := forall f lp t, forall s:variable -> value,
  let ru := rule_intro f lp t in (* f(p1, ..., pn) -> t *)
  (In ru prog) -> 
  term_assignment qic qif (subst s t) <= term_assignment qic qif (subst s (lhs_of_rule ru)). 
  (* pour toute substitution, QI(t) <= QI(f(p1, ..., pn)) *)

Definition valid_QI qic qif cs :=
  (additive qic cs) /\ (mcs_is_max_constructor_size cs) /\ (constructor_non_zero cs) /\
  (subterm qif) /\ (monotonicity_qif qif) /\ (compatible_QI qic qif).

Definition cache_bounded qic qif (c:cache): Prop  := 
  Forall (fun t => value_assignment qic (snd t) <= term_assignment qic qif (fst t)) c.

(* sous typage *)
Lemma value_as_term_assignment qic qif: forall v:value,
  (term_assignment qic qif (term_from_value v)) = (value_assignment qic v).
Proof.
induction v using value_ind2.
simpl.
rewrite map_map.
apply f_equal2;trivial.
apply map_in_ext;trivial.
Qed.


(*****************************************************************************************)
(*                        starting real proofs                                           *)
(*****************************************************************************************)

(* Les 2 lemmes suivants sont utilisés 2 fois par la suite. *)
Lemma qi_fapply_right_le_qi_fapply_left qic qif : forall proof_tree lp f c1,
  monotonicity_qif qif ->
  let l := map (proj_left (constructor:=constructor)) lp in
  let l' := map term_from_value (map (proj_right (constructor:=constructor)) lp) in
  let c := cache_left proof_tree in let v := proj_right proof_tree in
  (forall p, In p lp -> cache_bounded qic qif (cache_left p) -> 
             value_assignment qic (proj_right p) <= term_assignment qic qif (proj_left p) /\ 
             cache_bounded qic qif (cache_right p)) ->
  cache_bounded qic qif c1 -> cache_path c1 c lp = true -> andl (map wf lp) -> 
  (term_assignment qic qif (fapply f l')) <= (term_assignment qic qif (fapply f l)).
Proof.
intros proof_tree lp f c1 monotonicity l l' c v.
intros lp_bound c1_bound c_path wf_lp.
simpl.
unfold monotonicity_qif in monotonicity.
apply monotonicity.
unfold l;unfold l';clear l l'.
rewrite map_map;rewrite map_map;rewrite map_map.
apply Forall2_map.
intros.
rewrite value_as_term_assignment.
apply lp_bound;auto.
apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);auto.
apply lp_bound.
Qed.

Lemma qi_right_le_qi_fapply_left qic qif: forall proof_tree lp f c1,
  monotonicity_qif qif -> wf proof_tree ->
  let l := map (proj_left (constructor:=constructor)) lp in
  let l' := map term_from_value (map (proj_right (constructor:=constructor)) lp) in
  let c := cache_left proof_tree in let c' := cache_right proof_tree in
  let v := proj_right proof_tree in
  proj_left proof_tree = fapply f l' -> 
  (forall p, In p lp -> cache_bounded qic qif (cache_left p) -> wf p ->
             value_assignment qic (proj_right p) <= term_assignment qic qif (proj_left p) /\ 
             cache_bounded qic qif (cache_right p)) ->
  (cache_bounded qic qif c -> value_assignment qic v <= term_assignment qic qif (fapply f l')) ->
  cache_bounded qic qif c1 -> cache_bounded qic qif c' -> cache_path c1 c lp = true ->
    andl (map wf lp) -> 
  value_assignment qic v <= term_assignment qic qif (fapply f l).
Proof.
intros proof_tree lp f c1 monotonicity well_formed l l' c c' v.
intros pl lp_bound val_bound c1_bound c'_bound c_path wf_lp.
apply le_trans with (m:=term_assignment qic qif (fapply f l'));auto.
- apply val_bound;auto.
  apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);auto.
  intros;apply lp_bound;auto.
  apply andl_in_map with (l:=lp);auto.
- apply qi_fapply_right_le_qi_fapply_left with (proof_tree:=proof_tree) (c1:=c1);try tauto.
  intros.
  apply lp_bound;try tauto.
  apply andl_in_map with (l:=lp);auto.
Qed.

(* Lemma 68 *)
(* Lemme clé : pour chaque jugement de cache gauche borné,
               * le cache droit est aussi borné.
               * la QI de gauche est plus grande que la QI de droite
*)
Lemma left_bound_to_right_bound qic qif cs:forall pi:cbv,
    valid_QI qic qif cs -> (wf pi) ->
    cache_bounded qic qif (cache_left pi) ->
    (value_assignment qic (proj_right pi) <= term_assignment qic qif (proj_left pi)
     /\ cache_bounded qic qif (cache_right pi)).
Proof.
intros pi valid.
unfold valid_QI in valid.
destruct valid as (additivity & mcs_is_max & non_zero & sub & mono & compat).
induction pi using cbv_ind2;
          unfold cache_left;unfold proj_right;unfold proj_left;unfold cache_right;
          intros well_formed cache.
- (* cas cbv_constr *)
  assert (cache_bounded qic qif c2).
  + (* preuve du assert : borne sur le cache *)
    simpl in well_formed;destruct t;destruct v;try tauto.
    destruct well_formed as (cpath & Hc & Hl & Hl0 & wf_list & arity).
    apply cache_path_transitivity with (c:=c1) (c':=c2) (l:=lp);auto.
    intros;apply H;auto.
    apply andl_in_map with (l:=lp);auto.
  + (* borne sur les QI *)
    split;auto.
    simpl in well_formed;destruct t;destruct v;try tauto.
    destruct well_formed as (cpath & Hc & Hl & Hl0 & wf_list & arity).
    subst c.
    simpl;apply (monotonicity_qic qic cs);trivial.
    subst l l0.
    rewrite map_map;rewrite map_map.
    apply Forall2_map.
    intros.
    apply H;auto.
    * apply andl_in_map with (l:=lp);auto. 
    * apply cache_path_transitivity_left with (c:=c1) (c':=c2) (l:=lp);auto.
      intros.
      apply H;auto.
      apply andl_in_map with (l:=lp);auto.
- (* cas cbv_split *)
  destruct t;simpl in well_formed;destruct pi;destruct t;try tauto.
  + (* cbv_update *)
    assert (cache_bounded qic qif c2).
    * (* preuve du assert *)
      destruct well_formed as (Hc2 & cpath &  Hl & Hl0 & wf_list & Hf & Hv & well_formed & arity).
      unfold cache_left in IHpi;unfold cache_right in IHpi.
      subst c2.
      apply IHpi;auto.
      apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);auto.
      intros;apply H;auto.
      apply andl_in_map with (l:=lp);auto.
    * (* borne sur les QI *)
      split;auto.
      destruct well_formed as (Hc2 & cpath &  Hl & Hl0 & wf_list & Hf & Hv & well_formed & arity).
      unfold cache_left, cache_right, proj_left, proj_right in IHpi.
      subst c2 l f0 v1.
      set (proof_tree:=cbv_update n v0 pi c (fapply f l0) c0 v).
      subst l0.
      apply qi_right_le_qi_fapply_left with (proof_tree:=proof_tree) (c1:=c1);try tauto.
      intros;apply H;trivial.
  + (* cbv_read *)
    assert (cache_bounded qic qif c2).
    * (* preuve du assert *)
      destruct well_formed as (Hc2 & cpath &  Hl & Hl0 & wf_list & Hf & Hv & well_formed & arity).
      subst c2.
      apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);auto.
      intros;apply H;auto.
      apply andl_in_map with (l:=lp);auto.
    * (* borne sur les QI *)
      split;auto.
      destruct well_formed as (Hc2 & cpath &  Hl & Hl0 & wf_list & Hf & Hv & well_formed & arity).
      unfold cache_left in IHpi;unfold cache_right in IHpi.
      subst c2 l f0 v0.
      set (proof_tree:=cbv_read c (fapply f l0) v).
      subst l0.
      apply qi_right_le_qi_fapply_left with (proof_tree:=proof_tree) (c1:=c1);try tauto.
      intros;apply H;trivial.
- (* cas cbv_update *)
  assert (value_assignment qic v <= term_assignment qic qif t).
  + (* preuve du assert : borne sur les QI*)
    revert well_formed.
    elim t;simpl;try tauto.
    intros.
    destruct well_formed as (_ & lp & r & length & rule & Hl & pl & pr & cl & _ & _ & wf_pi & _).
    rewrite cl in *;clear cl.
    rewrite pl in *;clear pl.
    rewrite pr in *;clear pr.
    generalize (IHpi wf_pi cache).
    generalize (compat f lp r s).
    intros.
    replace (qif f (map (term_assignment qic qif) l)) with 
	    (term_assignment qic qif (subst s (lhs_of_rule (rule_intro f lp r)))).
    * apply le_trans with (m:=term_assignment qic qif (subst s r));try tauto.
      apply H.
      rewrite <- rule;apply nth_In;auto.
    * simpl.
      rewrite Hl.
      rewrite (map_map (term_from_pattern) (subst s) lp).
      rewrite (map_map (psubst s) (term_from_value) lp).
      f_equal;f_equal.
      clear.
      induction lp as [ | p lp IH];simpl;trivial.
      rewrite IH.
      f_equal;apply subst_psubst.
 + (* preuve de la borne sur le cache *)
   split;auto.
   simpl in well_formed.
   destruct t;try tauto.
   destruct well_formed as (_ & _ & _ & _  & _ & _ & _ & _ & cl & _ & new_cache & wf_pi & _).
   subst c2.
   unfold cache_bounded.
   apply Forall_cons.
   * unfold fst, snd;auto.
   * apply IHpi;auto.
     rewrite cl;auto.
- (* cas cbv_read *)
  split;auto.
  simpl in well_formed;destruct t;try tauto.
  destruct well_formed as (c_hit & lv'& Hl).
  unfold cache_bounded in cache.
  apply (Forall_In_l ((fapply f l),v) cache).
  apply (assoc_in (term_beq variable_eq_dec function_eq_dec constructor_eq_dec)
         (fapply f l) c);auto.
  apply (term_beq_eq variable_eq_dec function_eq_dec constructor_eq_dec).
Qed.

(***********************************************************************************)
(*                                                                                 *)
(*             Bornes globales                                                     *)
(*                                                                                 *)
(***********************************************************************************)

(* Lemma 69 *)
Lemma QI_never_increase_global qic qif cs: forall pi proof_tree:cbv, 
  valid_QI qic qif cs -> wf proof_tree -> 
  cache_bounded qic qif (cache_left proof_tree) -> InCBV pi proof_tree -> 
  term_assignment qic qif (proj_left pi) <= term_assignment qic qif (proj_left proof_tree).
Proof.
intros pi proof_tree valid well_formed cache subtree.
unfold valid_QI in valid.
destruct valid as (additivity & max_cs & non_zero & sub & mono & compat).
(* On a parfois besoin de valid en entier (pour appliquer le lemme clé) et parfois de ses composants.
   Détruire valid cause plein de "unfold valid_QI;tauto." à chaque application du lemme clé.
   Est-ce qu'on peut dupliquer l'hypothèse pour pouvoir à la fois conserver l'ensemble
   et les composants et se passer de ces unfold ?                                                   *)
induction proof_tree using cbv_ind2.
- (* cbv_constr *)
  simpl in subtree;destruct subtree as [equal | strict].
  + (* égalité *)
    subst pi;trivial.
  + (* liste de sous arbres *)
    simpl in well_formed.
    destruct t;destruct v;try tauto.
    destruct well_formed as (cpath & Hc & Hl & Hl0 & wf_list & arity).
    rewrite orl_map in strict.
    destruct strict as (x & inlist & intree).    
    apply le_trans with (m:=term_assignment qic qif (proj_left x)).
    * { apply H;trivial.
        - apply andl_in_map with (l:=lp);trivial.
        - apply cache_path_transitivity_left with (c:=c1) (c':=c2) (l:=lp);trivial.
          intros;apply (left_bound_to_right_bound qic qif cs);trivial.
          + unfold valid_QI;tauto.
          + apply andl_in_map with (l:=lp);trivial.
      }
    * simpl;subst l.
      rewrite additivity;rewrite map_map.
      apply Plus.le_plus_trans.
      apply in_le_suml.
      apply in_map with (f:=fun x0 => term_assignment qic qif (proj_left x0));trivial.
- (* cbv_split *)
  simpl in subtree;destruct subtree as [equal | [single | strict]].
  + (* égalité *)
    subst pi;trivial.
  + (* le sous arbre isolé *)
    simpl in well_formed.
    destruct proof_tree;destruct t0;destruct t;try tauto;intuition; 
    (* cet intuition fait aussi du travail dans IHproof_tree *)
             subst f0 c2;try subst v1;try subst v0.
    * (* cbv_update au dessus *)
      { simpl;simpl in cache;simpl in H8.
        simpl in single;destruct single as [equal | strict]. 
        (* les deux cas sont identiques. Peut-on factoriser la preuve ? *)
        - apply le_trans with (m:=qif f (map (term_assignment qic qif) l)).
          + apply H8;auto.
            apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
          + apply mono.
            subst l l0.
            rewrite map_map;rewrite map_map;rewrite map_map.
            apply Forall2_map.
            intros.
            apply le_trans with (m:=value_assignment qic (proj_right x)). (* coercion de type *)
            * apply Nat.eq_le_incl.
              apply value_as_term_assignment.
            * apply (left_bound_to_right_bound qic qif cs);trivial.
              unfold valid_QI;tauto.
              apply andl_in_map with (l:=lp);trivial.
              apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
              intros;apply (left_bound_to_right_bound qic qif cs);trivial.
              unfold valid_QI;tauto.
              apply andl_in_map with (l:=lp);trivial.
        - apply le_trans with (m:=qif f (map (term_assignment qic qif) l)).
          + apply H8;auto.
            apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
          + apply mono.
            subst l l0.
            rewrite map_map;rewrite map_map;rewrite map_map.
            apply Forall2_map.
            intros.
            apply le_trans with (m:=value_assignment qic (proj_right x)).
            * apply Nat.eq_le_incl.
              apply value_as_term_assignment.
            * apply (left_bound_to_right_bound qic qif cs);trivial.
              unfold valid_QI;tauto.
              apply andl_in_map with (l:=lp);trivial.
              apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
              intros;apply (left_bound_to_right_bound qic qif cs);trivial.
              unfold valid_QI;tauto.
              apply andl_in_map with (l:=lp);trivial.
      }
    * (* cbv_read au dessus *)
      simpl in cache;simpl in single;simpl in H8.
      destruct single as [equal | false];try tauto.
      subst pi;simpl in *.
      apply mono.
      subst l l0.
      rewrite map_map;rewrite map_map;rewrite map_map.
      apply Forall2_map.
      intros.
      { apply le_trans with (m:=value_assignment qic (proj_right x)).  (* coercion de type *)
        - apply Nat.eq_le_incl.
          apply value_as_term_assignment.
        - apply (left_bound_to_right_bound qic qif cs);trivial.
          + unfold valid_QI;tauto.
          + apply andl_in_map with (l:=lp);trivial.
          + apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
      }
  + (* liste de sous arbres *)
    simpl in well_formed.
    destruct proof_tree;destruct t0;destruct t;try tauto;intuition;
    (* cet intuition fait aussi du travail dans IHproof_tree *)
             simpl;simpl in H9;simpl in cache;subst c2 f0;try subst v1;try subst v0.
    (* les deux cas sont identiques, peut-on factoriser ? *)
    * (* cbv_update au dessus *)
      { rewrite orl_map in strict.
        destruct strict as (x & inlist & intree).
        apply le_trans with (m:=term_assignment qic qif (proj_left x)).
        - apply H;trivial.
          + apply andl_in_map with (l:=lp);trivial.
          + apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
        - subst l0;rewrite map_map.
          apply sub.
          apply in_map with (f:=fun x0 => term_assignment qic qif (proj_left x0));trivial.
      }
    * (* cbv_read au dessus *)
      { rewrite orl_map in strict.
        destruct strict as (x & inlist & intree).
        apply le_trans with (m:=term_assignment qic qif (proj_left x)).
        - apply H;trivial.
          + apply andl_in_map with (l:=lp);trivial.
          + apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
        - subst l0;rewrite map_map.
          apply sub.
          apply in_map with (f:=fun x0 => term_assignment qic qif (proj_left x0));trivial.
      }
- (* cbv_update *)
  simpl;simpl in cache.
  simpl in subtree;destruct subtree as [equal | strict].
  + (* égalité *)
    subst pi;trivial.
  + (* sous arbre *)
    simpl in well_formed.
    destruct t;try tauto.
    destruct well_formed as (_ & lp & t & n_le_lp & rule & Hl & pl & pr & cl & _ & _ & wf_ind & _).
    apply le_trans with (m:=term_assignment qic qif (proj_left proof_tree)).
    * subst c1;apply IHproof_tree;trivial.
    * rewrite pl.
      simpl;unfold compatible_QI in compat.
      { replace l with (map (subst s) (map term_from_pattern lp)).
        - apply compat.
          rewrite <- rule;apply nth_In;trivial.
        - subst l.
          rewrite map_map;rewrite map_map.
          apply map_ext.
          intros;apply subst_psubst.
      }
- (* cbv_read *)
  simpl in subtree;destruct subtree as [equal | impossible];try tauto.
  subst pi;trivial.
Qed.

Lemma cache_left_bounded_global qic qif cs: forall pi proof_tree:cbv,
  valid_QI qic qif cs -> wf proof_tree -> 
  cache_bounded qic qif (cache_left proof_tree) -> InCBV pi proof_tree ->
  cache_bounded qic qif (cache_left pi).
Proof.
intros pi proof_tree valid well_formed cache subtree.
induction proof_tree using cbv_ind2.
- (* cbv_constr *)
  simpl in subtree;destruct subtree as [ equal | strict].
  + (* égalité *)
    subst pi;trivial.
  + (* liste de sous arbres *)
    simpl in well_formed.
    destruct t;destruct v;try tauto.
    destruct well_formed as (cpath & Hc & Hl & Hl0 & wf_list & arity).
    rewrite orl_map in strict.
    destruct strict as (x & inlist & intree).
    apply H with (p:=x);auto.
    * apply andl_in_map with (l:=lp);trivial.
    * apply cache_path_transitivity_left with (c:=c1) (c':=c2) (l:=lp);auto.
      intros;apply (left_bound_to_right_bound qic qif cs);trivial.
      apply andl_in_map with (l:=lp);trivial.
- (* cbv_split *)
  simpl in subtree;destruct subtree as [equal | [single | strict]].
  + (* égalité *)
    subst pi;trivial.
  + (* le sous arbre isolé *)
    simpl in well_formed.
    destruct proof_tree;destruct t0;destruct t;try tauto;intuition;simpl in cache.
    (* cet intuition fait aussi du travail dans IHproof_tree *)
    * (* cbv_update au dessus *)
      apply H8;auto.
      simpl.
      apply cache_path_transitivity with (c:=c1) (l:=lp);auto.
      intros;apply (left_bound_to_right_bound qic qif cs);trivial.
      apply andl_in_map with (l:=lp);trivial.
    * (* cbv_read au dessus *)
      simpl in single;destruct single as [equal | impossible];try tauto.
      subst pi;simpl.
      apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);auto.
      intros;apply (left_bound_to_right_bound qic qif cs);trivial.
      apply andl_in_map with (l:=lp);trivial.
  + (* liste de sous arbres *)
    simpl in well_formed.
    destruct proof_tree;destruct t0;destruct t;try tauto;intuition.
    (* cet intuition fait aussi du travail dans IHproof_tree *)
    (* les deux cas sont identiques, peut-on factoriser ? *)
    * (* cbv_update au dessus *)
      { rewrite orl_map in strict.
        destruct strict as (x & inlist & intree).
        apply H with (p:=x);auto.
        - apply andl_in_map with (l:=lp);trivial.
        - apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);auto.
          intros;apply (left_bound_to_right_bound qic qif cs);trivial.
          apply andl_in_map with (l:=lp);trivial.
      }
    * (* cbv_read au dessus *)
      { rewrite orl_map in strict.
        destruct strict as (x & inlist & intree).
        apply H with (p:=x);auto.
        - apply andl_in_map with (l:=lp);trivial.
        - apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);auto.
          intros;apply (left_bound_to_right_bound qic qif cs);trivial.
          apply andl_in_map with (l:=lp);trivial.
      }
- (* cbv_update *)
  simpl in well_formed.
  destruct t;try tauto.
  simpl in cache.
  destruct well_formed as (_ & _ & _ & _ & _ & _ & _ & _ & cl & _ & _ & wf_ind & _).
  simpl in subtree.
  destruct subtree as [equal | strict].
  + subst pi;simpl;tauto.
  + apply IHproof_tree;auto.
    rewrite cl;trivial.   
- (* cbv_read *)
  simpl in subtree.
  destruct subtree as [equal | impossible];try tauto.
  subst pi;simpl;trivial.
Qed.

Definition judgsize (p:cbv) := term_size (proj_left p) + value_size (proj_right p).

(* remarque préliminaire du Théorème 70 *)
Lemma qi_active_bounded_by_size qic qif cs: forall f lval lt,
  valid_QI qic qif cs ->
  let t :=  (fapply f lt) in
  let l := (map (fun x=> mcs * (term_size t)) lt) in
  (* lt devrait aussi être défini par un let … in, mais ça plante à l'application du lemme et
     je ne comprends pas pourquoi. *)
  lt = map term_from_value lval ->
  term_assignment qic qif t <= (qif f l).
Proof.
intros f lval lt valid.
unfold valid_QI in valid.
destruct valid as (additivity & max_cs & non_zero & sub & mono & compat).
intros.
apply le_trans with (m:=qif f (map (fun v => mcs*(term_size v)) lt)).
apply le_trans with (m:=qif f (map (term_assignment qic qif) lt)).
- simpl;auto.
- apply mono.
  subst lt.
  rewrite map_map;rewrite map_map.
  apply Forall2_map.
  intros.
  rewrite compatible_sizes.
  rewrite value_as_term_assignment.
  apply (QI_le_value_size qic cs);trivial.
- unfold l.
  apply mono.
  
  apply Forall2_map.
  intros.
  apply Mult.mult_le_compat_l.
  simpl.
  apply le_trans with (m:=suml (map (term_size (constructor:=constructor)) lt)).
  apply le_trans with (m:=maxl (map (term_size (constructor:=constructor)) lt)).
  + apply maxl_is_max.
    apply in_map;trivial.
  + apply maxl_le_suml.
  + omega. 
Qed.

(* Théorème 70 *)
Lemma active_size_bound qic qif cs: forall i sub p c f lv d v, forall pi,
  valid_QI qic qif cs ->
  let t :=  (fapply f lv) in
  let proof_tree := cbv_update i sub p c t d v in 
  let l:= (map (fun x=> mcs * (term_size t)) lv) in
  wf proof_tree -> In pi (activations proof_tree) -> cache_bounded qic qif c -> 
  judgsize pi <= (max_arity + 1) * (qif f l) + 1.
Proof.
intros i sub p c f lv d v pi valid t proof_tree l well_formed active cache.
unfold valid_QI in valid;destruct valid as (additivity & max_cs & non_zero & subt & mono & compat).
(* pour ajouter les hypothèses explicitement *)
assert (InCBV pi proof_tree) as subtree.
apply activations_inCBV;trivial.
assert (wf pi) as sub_wf.
apply wf_InCBV_wf with (proof_tree:=proof_tree);trivial.
(* maintenant, on peut détruire active pour forcer la forme de pi *)
apply activation_is_function in active.
destruct active as (i' & sub' & p' & c1 & t0 & c2 & v0 & pi_is_upd).
destruct pi;try discriminate pi_is_upd.
simpl.
simpl in sub_wf;destruct t1;try tauto.
destruct sub_wf as (_ & lp & _ & _ & _ & Hl0 & _ & _ & _ & _ & _ & _ & arity).
set (s:=fapply f0 l0);set (u:=v2).

(* On empile les inégalités *)
apply le_trans with (m:=(max_arity+1) * (term_assignment qic qif (fapply f lv)) + 1).
apply le_trans with (m:=(max_arity+1)*(term_assignment qic qif s) + 1).
apply le_trans with (m:=(length l0)*(term_assignment qic qif s) + (term_assignment qic qif s) + 1).
apply le_trans with (m:=suml (map (fun t => term_assignment qic qif s) l0) + (term_assignment qic qif s) + 1).
apply le_trans with (m:=suml (map (term_assignment qic qif) l0) + (term_assignment qic qif s) + 1).
apply le_trans with (m:=suml (map (@term_size _ _ _) l0) + (term_assignment qic qif s) + 1).
apply le_trans with (m:=(term_size s) + (term_assignment qic qif s)).
apply le_trans with (m:=(term_size s) + (value_assignment qic u)).
apply le_trans with (m:=(term_size s) + (value_size u)).

(* Et on les dépile *)
- auto.
- apply Plus.plus_le_compat_l.
  apply (value_size_le_QI qic cs);auto.
- apply Plus.plus_le_compat_l.
  apply (left_bound_to_right_bound qic qif cs) with (pi:=cbv_update n v1 pi c0 s c3 u);trivial. (* lemme clé *)
  + unfold valid_QI;tauto.
  + apply wf_InCBV_wf with (proof_tree:=proof_tree);trivial.
  + apply (cache_left_bounded_global qic qif cs) with (proof_tree:=proof_tree);auto.
    unfold valid_QI;tauto.
- simpl;omega.
- apply Plus.plus_le_compat_r;apply Plus.plus_le_compat_r.
  subst l0.
  apply suml_map_le;intros.
  rewrite in_map_iff in H;destruct H;destruct H as (eq & inl).
  subst x.
  rewrite compatible_sizes.
  rewrite value_as_term_assignment.
  apply (value_size_le_QI qic cs);trivial.
- apply Plus.plus_le_compat_r;apply Plus.plus_le_compat_r.
  apply suml_map_le;intros.
  unfold s;simpl.
  apply subt.
  apply in_map;trivial.
- apply Plus.plus_le_compat_r;apply Plus.plus_le_compat_r.
  rewrite Mult.mult_comm.
  apply Nat.eq_le_incl.
  apply suml_map_const.
- apply Plus.plus_le_compat_r.
  rewrite Mult.mult_plus_distr_r.
  rewrite Mult.mult_1_l.
  apply Plus.plus_le_compat_r;apply Mult.mult_le_compat_r;trivial.
- apply Plus.plus_le_compat_r;apply Mult.mult_le_compat_l.
  apply (QI_never_increase_global qic qif cs) with 
        (pi:=cbv_update n v1 pi c0 s c3 u) (proof_tree:=proof_tree);auto.
  unfold valid_QI;tauto.
- apply Plus.plus_le_compat_r;apply Mult.mult_le_compat_l.
  unfold proof_tree in *;clear proof_tree.
  unfold t in *;clear t.
  simpl in well_formed.
  destruct well_formed as (_ & lp0 & t' & _ & _ & Hlv & _ & _ & _ & _ & _ & wfp & _).
  apply (qi_active_bounded_by_size qic qif cs) with (lval:=map (psubst sub) lp0) (lt:=lv);auto.
  unfold valid_QI;tauto.
Qed.

Lemma active_size_bound_max qic qif cs: forall i s p c f lv d v,
  valid_QI qic qif cs ->
  let t :=  (fapply f lv) in
  let pi := cbv_update i s p c t d v in 
  let la := (activations pi)  in
  let l:= (map (fun x=> mcs * (term_size t)) lv) in
  wf pi -> cache_bounded qic qif c -> forall la', incl la' la -> 
  maxl (map judgsize la') <= (max_arity + 1) * qif f l + 1.
Proof.
intros i s p c f lv d v valid t pi la l Hwf Hcb la' Hsslist.
induction la';simpl.
- apply le_0_n.
- apply max_lub.
  + apply (active_size_bound qic qif cs i s p c f lv d v a);auto.
    apply (Hsslist a);apply in_eq.
  + apply IHla'.
    apply tl_incl with (a:=a);trivial.
Qed.

Lemma max_active_size_sublist: forall c c' lp lp',
  andl (map wf lp) -> cache_path c c' lp = true -> incl lp' lp ->
  (forall p : cbv, In p lp -> wf p ->
   max_active_size p <= maxl (map judgsize (activations p))) ->
   maxl (map (@max_active_size _ _ _) lp') <= 
   maxl (map judgsize (flat_map (activations (constructor:=constructor)) lp')).
Proof.
induction lp'.
- (* induction : nil *)
  simpl;intros;auto. 
- (* induction : cons *)
  intros.
  simpl.
  rewrite map_app.
  rewrite maxl_app.
  apply Nat.max_le_compat.
  + (* cas gauche du max_le_compat *)
    apply (H2 a).
    unfold incl in H1;apply H1;simpl;auto.
    apply andl_in_map with (l:=lp);auto.
    unfold incl in H1;apply (H1 a);simpl;auto.
  + (* cas droite du max_le_compat *)
    apply IHlp';intros;auto.
    apply tl_incl with (a:=a);trivial.
Qed.

Lemma max_active_size_is_max: forall pi,
   let S := max_active_size pi in
   wf pi -> S <= maxl (map judgsize (activations pi)).
Proof.
induction pi using cbv_ind2;intros;auto.
- (* cas cbv_constr *)
  unfold S;simpl.  
  simpl in H0;destruct t;destruct v;try tauto.
  destruct H0 as (cpath & Hc & HGl & Hl0 & wf_list & arity).
  apply max_active_size_sublist with (c:=c1) (c':=c2) (lp:=lp);auto.
  apply incl_refl.
- (* cas cbv_split *)
  unfold S;simpl.
  rewrite map_app.
  rewrite maxl_app.  
  apply Nat.max_le_compat.
  + (* le sous arbre isolé *)
    apply IHpi.
    simpl in H0.
    destruct pi;destruct t0;destruct t;tauto.
  + (* la liste de sous-arbres *)
    simpl in H0;destruct pi;destruct t0;destruct t;try tauto;
          destruct H0 as (Hc & cpath & Hl0 & Hl & wf_list & Hf & Hv & wfp & arity);
          apply max_active_size_sublist with (c:=c1) (c':=c) (lp:=lp);auto;apply incl_refl.
- (* cas cbv_update *)
  simpl activations.
  rewrite map_cons.
  simpl maxl.
  simpl in S.
  apply Nat.max_le_compat;auto.
  apply IHpi.
  simpl in H.
  destruct t;try tauto.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _);trivial.
Qed.

Theorem max_active_size_bound qic qif cs: forall i s p c f lv d v,
  valid_QI qic qif cs ->
  let t :=  (fapply f lv) in
  let pi := cbv_update i s p c t d v in 
  let l:= (map (fun x=> mcs * (term_size t)) lv) in
  let S := max_active_size pi in
  wf pi -> cache_bounded qic qif c -> S <= (max_arity + 1) * (qif f l) + 1.
Proof.
intros i s p c f lv d v valid;intros.
generalize (max_active_size_is_max pi H).
unfold S, pi,t.
intros.
apply le_trans with (m:=maxl (map judgsize (activations pi)));auto.
apply (active_size_bound_max qic qif cs i s p c f lv d v);auto.
apply incl_refl.
Qed.

(* partial version of compatible QI *)

Definition p_assignment_function := function -> option(list nat -> nat).

(* partial assignment of a term*)
Fixpoint p_term_assignment (qic:assignment_constructor) (qif:p_assignment_function)
(t:term) {struct t} : option nat:=
   match t with
  | var v=> Some 0 (* pas necessaire. Les QI sont toujours appliquées sur des termes clots. *)
  | capply c lt => option_map (qic c) (option_list_map(map (p_term_assignment qic qif) lt))
  | fapply f lt=> option_bind (fun g => option_map g (option_list_map(map (p_term_assignment qic qif)  lt)))
                              (qif f)
end.

Definition complete_p_QI (qif : p_assignment_function) f := 
  complete_option maxl (qif f).

Lemma p_term_assignment_term_assignment qic qif t v:
  p_term_assignment qic qif t = Some v ->
  term_assignment qic (complete_p_QI qif) t = v.
Proof.
revert v; induction t using term_ind2.
- intros n H; now inversion H.
- unfold option_map; intros v H0; simpl p_term_assignment in H0.
  simpl term_assignment.
  case_eq (option_list_map (map (p_term_assignment qic qif) l));
    [| intro H1; rewrite H1 in H0; inversion H0].
  intros lv Hlv.
  rewrite option_list_map_map with (f := complete_option 0) in H0.
  + simpl option_map in H0; inversion H0.
    rewrite map_map; f_equal; apply map_ext_in; intros a Ha.
    apply option_list_map_Some with (x := p_term_assignment qic qif a) in Hlv.
    * destruct Hlv as (va & Hva); rewrite Hva; auto.
    * now apply in_map.
  + intros x Hx.
    eapply option_list_map_Some in Hlv; eauto.
    now destruct Hlv as [vx Hvx]; rewrite Hvx.
- unfold option_map, complete_p_QI; intros v H0; simpl p_term_assignment in H0.
  case_eq (qif f); [ | intro Hf; rewrite Hf in H0; inversion H0].
  intros g Hg; rewrite Hg in *; simpl in H0.
  simpl term_assignment.
  case_eq (option_list_map (map (p_term_assignment qic qif) l));
    [| intro H1; rewrite H1 in H0; inversion H0].
  intros lv Hlv.
  rewrite Hg; simpl.
  rewrite Hlv in H0.
  inversion H0.
  subst v.
  f_equal.
  assert(Heq : Some (map
  (term_assignment qic
     (fun f0 : function => complete_option maxl (qif f0)))
  l) = Some lv); [ | now inversion Heq].
  rewrite <- Hlv.
  erewrite option_list_map_map.
  + rewrite map_map.
    instantiate (1 := complete_option 0).
    f_equal.
    apply map_ext_in.
    intros a Ha.
    apply option_list_map_Some with (x := p_term_assignment qic qif a) in Hlv.
    * destruct Hlv as (va & Hva); rewrite Hva; auto.
    * now apply in_map.
  + intros x Hx.
    eapply option_list_map_Some in Hlv; eauto.
    now destruct Hlv as [vx Hvx]; rewrite Hvx.
Qed.

Definition p_compatible_QI qic qif:= forall f lp t, forall s:variable -> value,
  let ru := rule_intro f lp t in
  (In ru prog) -> 
    p_term_assignment qic qif (subst s t) ≤p 
    p_term_assignment qic qif (subst s (lhs_of_rule ru)).

Lemma p_compatible_compatible qic:
  {pqif | p_compatible_QI qic pqif} -> {qif | compatible_QI qic qif}.
Proof.
unfold compatible_QI, p_compatible_QI.
intros [qif H]; exists (complete_p_QI qif).
intros f lp t s Hr.
assert (H' := H f lp t s Hr).
destruct H' as (v1 & v2 & Hv1 & Hv2 & Heq).
apply p_term_assignment_term_assignment in Hv1.
apply p_term_assignment_term_assignment in Hv2.
now subst.
Qed.

Lemma p_term_assignment_ext qic f f': 
 (forall x, f x = f' x) ->
 forall t, p_term_assignment qic f t= p_term_assignment qic f' t.
Proof.
intro Heq.
induction t using term_ind2.
- trivial.
- simpl p_term_assignment; f_equal; f_equal; now apply map_ext_in.
- simpl p_term_assignment.
  rewrite <- Heq.
  destruct (f f0) as [v |]; trivial.
  simpl; f_equal; f_equal; now apply map_ext_in.
Qed.

Lemma p_compatible_QI_ext qic f f': 
 (forall x, f x = f' x) ->
 p_compatible_QI qic f ->
 p_compatible_QI qic f'.
Proof.
intros Heq Hf; unfold p_compatible_QI in *.
intros;
do 2(rewrite <- p_term_assignment_ext with (f := f) (f' := f'); trivial).
auto.
Qed.

Lemma p_compatible_QI_split qic f h:
  {g | p_compatible_QI qic (f;;h;;g)} -> {g | p_compatible_QI qic (f;;g)}.
Proof.
- intro H.
destruct H as (g & Hhg).
exists (h;;g); eapply p_compatible_QI_ext; [ | exact Hhg].
intro; now rewrite option_choice_assoc.
Qed.

Lemma p_term_assignment_first_choice qic f t v:
  p_term_assignment qic f t = Some v ->
  forall g, p_term_assignment qic (f;;g) t = Some v.
Proof.
revert v.
induction t using term_ind2.
- intros; assumption.
- intros v Hv g; simpl in *.
  rewrite <- Hv; do 2 f_equal.
  apply map_ext_in; intros a Ha.
  apply option_map_Some in Hv; destruct Hv as (v' & Hv').
  apply option_list_map_Some with (x := p_term_assignment qic f a) in Hv';
  [ | now apply in_map].
  destruct Hv' as (v'' & Hv''); rewrite Hv''.
  apply H; assumption.
- intros v Hv g; simpl in *.
  rewrite <- Hv.
  simpl option_choice.
  case_eq (f f0); [| intro Hnone; rewrite Hnone in Hv; inversion Hv].
  intros v' Hv'.
  assert (Hfg : (f;; g) f0 = Some v') by
    (unfold option_choice; now rewrite Hv').
  rewrite Hfg.
  simpl.
  do 2 f_equal.
  apply map_ext_in.
  intros a Ha.
  apply option_bind_Some in Hv.
  destruct Hv as (v'' & _ & Hv).
  apply option_map_Some in Hv.
  destruct Hv as (v'''' & Hv).
  apply option_list_map_Some with (x := p_term_assignment qic f a) in Hv.
  + destruct Hv as (lv & Hlv).
    erewrite H; eauto.
  + now apply in_map.
Qed.

Lemma value_as_p_term_assignment qic qif: forall v:value,
  (p_term_assignment qic qif (term_from_value v)) = Some (value_assignment qic v).
Proof.
induction v using value_ind2.
simpl.
unfold option_map, option_list_map.
rewrite map_map.
rewrite option_list_map_map with 
  (f := fun x => match x with Some v => v | None => 0 end).
- do 2 f_equal; rewrite map_map; apply map_ext_in.
  intros; rewrite H; trivial.
- intros x Hx.
  apply in_map_iff in Hx.
  destruct Hx as (n & Hn1 & Hn2).
  rewrite H in Hn1; trivial.
  rewrite <- Hn1; trivial.
Qed.

Definition p_subterm (qif : p_assignment_function) : Prop :=
forall (f : function) (l : list nat) (x : nat), x ∈ l ->
  match qif f with 
  | None => True 
  | Some f0 => (x <= f0 l)
  end.

Definition p_monotonicity (qif : p_assignment_function) : Prop :=
  forall (f : function) (lx ly : list nat),
    Forall2 le lx ly -> 
    match qif f with 
    | None => True 
    | Some f0 => f0 lx <= f0 ly
    end.

Definition p_smc qic (qif : p_assignment_function) : Prop :=
 p_subterm qif /\ p_monotonicity qif /\ p_compatible_QI qic qif.

Lemma p_smc_split f h qic:
  {g | p_smc qic (f;;h;;g)} -> {g | p_smc qic (f;;g)}.
Proof.
intro H.
unfold p_smc in *.
destruct H as (g & Hhgs & Hhgm & Hhgc).
exists (h;;g).
unfold p_subterm, p_monotonicity, p_compatible_QI in *.
repeat split; intros f0 l x Hin.
- assert (H := Hhgs f0 l x Hin); now rewrite <- option_choice_assoc in H.
- assert (H := Hhgm f0 l x Hin); now rewrite <- option_choice_assoc in H.
- eapply p_compatible_QI_ext; [ | exact Hhgc]; intro; now rewrite option_choice_assoc.
Qed.

Lemma p_smc_smc qic :
  {pqif | p_smc qic ((fun _ => None);; pqif)} -> 
  {qif | subterm qif /\ monotonicity_qif qif /\ compatible_QI qic qif}.
Proof.
unfold p_smc, compatible_QI, p_compatible_QI, p_subterm, subterm, 
       monotonicity_qif, p_monotonicity.
intros (qif & Hs & Hm & Hc); exists (complete_p_QI qif).
repeat split.
- intros f l x Hin.
  assert (H' := Hs f l x Hin).
  unfold complete_p_QI, complete_option.
  unfold option_choice in H'.
  destruct (qif f); trivial.
  now apply maxl_is_max.
- intros f l x Hin.
  assert (H' := Hm f l x Hin).
  unfold complete_p_QI, complete_option.
  unfold option_choice in H'.
  destruct (qif f); trivial.
  now apply forall2_le_maxl.
- intros f lp t s Hr.
  assert (H' := Hc f lp t s Hr).
  destruct H' as (v1 & v2 & Hv1 & Hv2 & Heq).
  apply p_term_assignment_term_assignment in Hv1.
  apply p_term_assignment_term_assignment in Hv2.
  now subst.
Qed.

End QI.

Section Partial_QI.

Variables variable function constructor : Type.

Notation p_compatible_QI := (p_compatible_QI variable function constructor).
Notation term_from_value := (Syntax.term_from_value variable function (constructor:=constructor)).
Notation p_smc := (p_smc variable function constructor).

(* f is the current partial qi, and g is what remains to be defined *)
Lemma p_compatible_QI_app f prog1 prog2 qic:
  p_compatible_QI prog1 qic f ->
  {g | p_compatible_QI prog2 qic (f;;g)} ->
  {g | p_compatible_QI (prog1 ++ prog2) qic (f;;g)}.
Proof.
intros Hf [g Hg]; exists g.
unfold p_compatible_QI; intros f0 lp t s Hrule.
apply in_app_iff in Hrule; destruct Hrule as [Hr1 | Hr2]; auto.
eapply (Hf f0 lp t s) in Hr1.
destruct Hr1 as (v1 & v2 & Hv1 & Hv2 & Heq);
exists v1; exists v2; intuition;
now apply p_term_assignment_first_choice.
Qed.

Lemma p_smc_QI_app f prog1 prog2 qic:
  p_compatible_QI prog1 qic f ->
  {g | p_smc prog2 qic (f;;g)} ->
  {g | p_smc (prog1 ++ prog2) qic (f;;g)}.
Proof.
unfold p_smc.
intros Hfc (g & Hs & Hm & Hc); exists g; repeat split.
- unfold p_subterm in *; intros h l x Hin.
  assert (H' := Hs h l x Hin).
  unfold option_choice in *; destruct (f h); trivial.
- unfold p_monotonicity in *; intros h l x Hin.
  assert (H' := Hm h l x Hin).
  unfold option_choice in *; destruct (f h); trivial.
- intros f0 lp t s r Hrule.
  apply in_app_iff in Hrule; destruct Hrule as [Hr1 | Hr2].
  + eapply (Hfc f0 lp t s) in Hr1.
    destruct Hr1 as (v1 & v2 & Hv1 & Hv2 & Heq);
    exists v1; exists v2; intuition;
    now apply p_term_assignment_first_choice.
  + now apply Hc.
Qed.

End Partial_QI.
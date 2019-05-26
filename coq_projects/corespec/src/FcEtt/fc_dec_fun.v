Require Import FcEtt.sigs.

Require Import FcEtt.fc_dec_fuel.
Require Import FcEtt.fc_dec_aux.

Require Import FcEtt.imports.
Require Export FcEtt.ett_inf_cs.
Require Import FcEtt.ett_ind.
Require Export FcEtt.fc_invert.

Require Import FcEtt.dep_prog.

Require Import FcEtt.toplevel.

Require Import FcEtt.fc_get.
Require Import FcEtt.fc_context_fv.


Module fc_dec_fun (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig) (unique: fc_unique_sig).

Module invert := fc_invert wf weak subst.
Module fuel := fc_dec_fuel wf weak subst unique.
Module aux := fc_dec_aux wf weak subst unique.
Module get := fc_get wf weak subst unique.

Import fuel aux unique wf subst invert get.

Unset Implicit Arguments.

Ltac obtacpre :=
  intros; simpl in *.

Ltac obtacsolve :=
  intros; simpl in *; try solve [ok].


Lemma An_IsoConv': ∀ (G : context) (D : available_props)
                     (a1 a2 A a1' a2' B : tm) phi1 phi2 (g : co),
  phi1 =  (Eq a1 a2 A)  →
  phi2 = (Eq a1' a2' B) →
  AnnDefEq G D g A B  →
  AnnPropWff G phi1 →
  AnnPropWff G phi2 →
  erase_tm a1 = erase_tm a1' →
  erase_tm a2 = erase_tm a2' →
  AnnIso G D (g_IsoConv phi1 phi2 g) phi1 phi2.
Proof.
  intros.
  subst phi1 phi2.
  eauto.
Qed.



(* More pratical version of these lemma (both forms are useful, though) *)
Lemma get_tpg_correct' : ∀ {G : context} {a A : tm},
    AnnTyping G a A → A = get_tpg G a.
Proof.
  move => G a A tpg.
  by rewrite (@get_tpg_correct _ _ _(get_tpg G a) tpg _).
Defined.


Lemma get_deq_correct' : ∀ {G : context} {D : available_props} {g : co} {A B},
    AnnDefEq G D g A B → get_deq G g = (A, B).
Proof.
  move => G ? g A B deq.
  have eq: get_deq G g = (fst (get_deq G g), snd (get_deq G g)) by destruct (get_deq G g).
  by move: (@get_deq_correct _ _ _ _ _ (fst (get_deq G g)) (snd (get_deq G g)) deq eq) => [-> ->].
Defined.

Lemma get_iso_correct' : ∀ {G : context} {D : available_props} {g : co} {phi1 phi2 : constraint}, AnnIso G D g phi1 phi2 → get_iso G g = (phi1, phi2).
Proof.
  move => G ? g phi1 phi2 iso.
  have eq: get_iso G g = (fst (get_iso G g), snd (get_iso G g)) by destruct (get_iso G g).
  by move: (@get_iso_correct _ _ _ _ _ (fst (get_iso G g)) (snd (get_iso G g)) iso eq) => [-> ->].
Defined.



(**** Tactics ****)
(* TODO: reorganize the tactics, and move the ones which don't belong here *)


(* FIXME: that may be defined in fc_dec_fun *)
Ltac clear_annoying :=
  repeat match goal with
    | [H: <<_>> = _ |- _ ] => clear H
    | [H: <<_, _>> = _ |- _ ] => clear H
    | [H: !! = _ |- _ ] => clear H
    | [H: yeah = _ |- _ ] => clear H
    | [H: nope = _ |- _ ] => clear H
    | [ H :     !! = _     |- _ ] => clear H
    | [ H :     _ + { _ } |- _ ] => clear H
    | [ H : { _ } + { _ } |- _ ] => clear H
    | [ H : { _ | _} + { _ } |- _ ] => clear H
    | [ H : { _, _ | _} + { _ } |- _ ] => clear H
  end.



Ltac intro_uniq_full H :=
    match type of H with
      | AnnTyping ?G ?a ?A =>
        let x := fresh "u" in
        move : (@AnnTyping_unique G a A H) => x;
        (* Apply uniqueness to other hyps about the same term (and ctx) and discard them *)
        repeat match goal with
          | [H' : AnnTyping G a ?A' |- _ ] =>  move: (x _ H') => ?; wrap_hyp H'
        end
      | AnnDefEq ?G ?L ?g ?A1 ?A2 =>
        let x := fresh "u" in
        move : (@AnnDefEq_unique G L g A1 A2 H) => x;
        (* Apply uniqueness to other hyps about the same term (and ctx) and discard them *)
        repeat match goal with
          | [H' : AnnDefEq G L g ?A1' ?A2' |- _ ] =>  move: (x _ _ H') => ?; wrap_hyp H'
        end
      | AnnIso ?G ?L ?g ?phi1 ?phi2 =>
        let x := fresh "u" in
        move : (@AnnIso_unique G L g phi1 phi2 H) => x;
        (* Apply uniqueness to other hyps about the same term (and ctx) and discard them *)
        repeat match goal with
          | [H' : AnnIso G L g ?phi1' ?phi2' |- _ ] =>  move: (x _ _ H') => ?; wrap_hyp H'
        end
    end.


(* Apply uniqueness of type to existing typing hyps *)
Ltac auto_uniq_full :=
  revert_all_with intro_uniq_full; intros; pcess_hyps.

Ltac terminator := auto_uniq_full; subst_forall; subst; cbn; pcess_hyps;
  (* FIXME: eauto db version: basic_nosolve_n 3 *)
  (* FIXME: eauto doesn't (always, at least) use the typing constructors, while in theory it should... *)
  try solve [try econstructor; intuition (subst; eauto 3) | intuition (subst; eauto 3 with smart_cons_exists)].

Ltac hacky :=
  do 3 (
    intros;
    (*
    repeat match goal with
      | [ p : tm * tm |- _ ] => destruct p; cbn in *
    end; *)
  try(
  try (multimatch goal with
    | [ |- ¬ _ ] => let H := fresh in intro H; inversion H; terminator
    | _ => idtac
  end);
  try (multimatch goal with
    | [ H : ¬ _ |-  _ ] => solve [edestruct H; terminator]
    | [ H : forall _, ¬ _ |-  _ ] => solve [edestruct H; terminator]
    | [ H : forall _ _, ¬ _ |-  _ ] => solve [edestruct H; terminator]
  end); terminator)).


(* Cleanup tactics
   TODO: do we want them here or elsewhere? *)
Ltac clearbodies :=
  repeat match goal with
    | [ H := _ : _ |- _] => clearbody H
  end.
(* TODO: should be in tactics.v *)
Ltac clearbodies' :=
  repeat match goal with
    | [ x := ?bdy : _ |- _] =>
      move: (eq_refl x);
      rewrite -{2}[x]/bdy;
      clearbody x;
      let eqname := fresh "eq" x in
      move => eqname
  end.




(* Ugly to have to grab them by their types, but we can't refer to their names (even after the definitions) *)
Ltac clean_fun :=
  match goal with
    | [
        AnnTyping_dec : Tactics.fix_proto (∀ (G : context) (t : tm), fuel_tpg t → AnnCtx G → {T : tm | AnnTyping G t T} + {(∀ T : tm, ¬ AnnTyping G t T)}),
        AnnPropWff_dec : Tactics.fix_proto (∀ (G : context) (phi : constraint), fuel_pwf phi → AnnCtx G → {AnnPropWff G phi} + {¬ AnnPropWff G phi}),
        AnnDefEq_dec : Tactics.fix_proto (∀ (G : context) (S : available_props) (g : co), fuel_deq g → AnnCtx G → {A, B | AnnDefEq G S g A B} + {(∀ A B : tm, ¬ AnnDefEq G S g A B)}),
        AnnIso_dec : Tactics.fix_proto (∀ (G : context) (S : available_props) (g : co), fuel_iso g → AnnCtx G → {phi1, phi2 | AnnIso G S g phi1 phi2} + {(∀ phi1 phi2 : constraint, ¬ AnnIso G S g phi1 phi2)})
      |- _ ] => clear AnnTyping_dec AnnPropWff_dec AnnDefEq_dec AnnIso_dec
  end.


Ltac clear_sums :=
  repeat match goal with
    | [ H :     !! = _     |- _ ] => clear H
    | [ H :     _ + { _ } |- _ ] => clear H
    | [ H : { _ } + { _ } |- _ ] => clear H
  end.


Ltac cleanup_param cbodies sbst:=
  clear_annoying;
  intros; simpl in *;
  cbodies;
  try solve [ok];
  try clean_fun;
  clear_sums;
  sbst. (* FIXME: for some reason, that subst breaks clear_fun if placed before it *)

Ltac cleanup := cleanup_param clearbodies subst.
Ltac cleanup' := cleanup_param clearbodies' idtac.




Obligation Tactic := try solve [hacky].

(* We need an unfueled version for AnnIso_dec - in that case, we have the subterms and a typing for them (by regularity), but no *fuel* *)
Program Definition AnnPropWff_dec' (G: context) (a b A : tm) (A' B': tm) (H : AnnCtx G)
                                  (pA: AnnTyping G a A') (pB: AnnTyping G b B') : {AnnPropWff G (Eq a b A)} + {¬ AnnPropWff G (Eq a b A)} :=
  tm_eq_dec A A' >-->
  tm_eq_dec (erase A) (erase B') >-->
  yeah.

Obligation Tactic := obtacpre; first [match goal with [|- tm] => idtac end | eassumption].

(** A system FC development wouldn't be right without a good, Haskell-style code. So please, enjoy. **)

(* Naming scheme: fX is the name of the fuel for X *)
Program Fixpoint AnnTyping_dec (G : context) (t : tm) (fuel : fuel_tpg t) (H : AnnCtx G) {struct fuel} : {T : tm | AnnTyping G t T } + {(forall T, ¬ AnnTyping G t T)}  :=
  match fuel with
    | FT_Star =>  << a_Star >>

    | FT_Var_f x =>
      A <- binds_dec_tm x G;
      << A >>

    | FT_Pi rho A B fB fA =>
      let (x, p) := atom_fresh (dom G \u fv_tm_tm_tm B) in
      KA <- AnnTyping_dec G A fA _;
      tm_eq_dec KA a_Star >--->
      KB <- AnnTyping_dec ([(x, Tm A)] ++ G) (open_tm_wrt_tm B (a_Var_f x)) (fB x _) _;
      tm_eq_dec KB a_Star >--->
      << a_Star >>

    | FT_Abs rho a A fa fA =>
      (* (∀ x : atom, ¬ x `in` L → Typing ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) *)
      let (x, p) := atom_fresh (dom G \u fv_tm_tm_tm a) in
      KA <- AnnTyping_dec G A fA _;
      tm_eq_dec KA a_Star >--->
      B <- AnnTyping_dec ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x)) (fa x _) _;
      RhoCheck_erase_dec rho x (open_tm_wrt_tm a (a_Var_f x)) _ >--->
      << a_Pi rho A (close_tm_wrt_tm x B )>>


    | FT_App rho b a fb fa =>
      A <- AnnTyping_dec G a fa _;
      Tf <- AnnTyping_dec G b fb _;
      match Tf with
        | a_Pi rho' A' B =>
          tm_eq_dec A' A >--->
          rho_eq_dec rho rho' >---> << open_tm_wrt_tm B a >>
        | _ => !!
      end

    | FT_Conv a g fa fg =>
      A <- AnnTyping_dec G a fa _;
      A' & B <- AnnDefEq_dec G (dom G) g fg _;
      let K := get_tpg G B in
  (*  K <- AnnTyping_dec G B _ _;  *)
      tm_eq_dec K a_Star >--->
      tm_eq_dec A A' >--->
      << B >>

    | FT_CApp b g fb fg =>
      TB <- AnnTyping_dec G b fb _ ;
      A1' & A2' <- AnnDefEq_dec G (dom G) g fg _;
      match TB with
        | (a_CPi (Eq A1 A2 K) B) =>
          tm_eq_dec A1 A1' >--->
          tm_eq_dec A2 A2' >--->
          << open_tm_wrt_co B g >>
        | _ => !!
      end

    | FT_Const T =>
      K <- binds_dec_cs T an_toplevel;
      (@DataTy_Star_dec K) _ >--->
      << K >>

    | FT_CPi phi B fB fphi =>
      AnnPropWff_dec G phi fphi _ >--->
      let (c, p) := atom_fresh (dom G \u fv_co_co_tm B) in
      KB <- AnnTyping_dec ([(c, Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c)) (fB c _) _;
      tm_eq_dec KB a_Star >--->
      << a_Star >>

    | FT_CAbs a phi fa fphi =>
      AnnPropWff_dec G phi fphi _ >--->
      let (c, p) := atom_fresh (dom G \u fv_co_co_constraint phi \u fv_co_co_tm a) in
      Bc <- AnnTyping_dec ((c ~ Co  phi ) ++  G) (open_tm_wrt_co a (g_Var_f c)) (fa c _) _;
      << a_CPi phi (close_tm_wrt_co c Bc) >>

    (* Erased language side: not typable in the annotated *)
    | FT_UAbs _ _ => !!
    | FT_UCAbs _  => !!
    | FT_Bullet   => !!


    | FT_Var_b _ => !!
  (*  | a_FamApp _ _ => !! *)
    | FT_DataCon _ => !!
    | FT_Case _ _ => !!

    | FT_Fam F =>
      a & A <- binds_dec_ax F an_toplevel;
        << A >>
  end


with AnnPropWff_dec (G: context) (phi : constraint) (fuel : fuel_pwf phi)
                    (H : AnnCtx G) {struct fuel} : {AnnPropWff G phi} + {¬ AnnPropWff G phi} :=
  match fuel with
    | FP_fuel_pwf a b K fa fb =>
      Ka <-- AnnTyping_dec G a fa _;
      Kb <-- AnnTyping_dec G b fb _;
      tm_eq_dec K Ka >-->
      tm_eq_dec (erase K) (erase Kb) >--> yeah
  end


with AnnDefEq_dec (G: context) (S : available_props) (g : co) (fuel : fuel_deq g)
                  (H: AnnCtx G) {struct fuel} : {A, B | AnnDefEq G S g A B} + {(forall A B, ¬ AnnDefEq G S g A B)} :=
  match fuel with
    | FD_Assn c =>
        in_dec c S >--->
        AB & K <- binds_dec_co c G;
        << fst AB, snd AB >>

    | FD_Refl a fa =>
        A <- AnnTyping_dec G a fa _;
        <<a, a>>

    | FD_Refl2 a b g fa fb fg =>
        A <- AnnTyping_dec G a fa _;
        B <- AnnTyping_dec G b fb _;
        tm_eq_dec (erase_tm a) (erase_tm b) >--->
        A' & B' <- AnnDefEq_dec G (dom G) g fg _;
        tm_eq_dec A A' >--->
        tm_eq_dec B B' >--->
        << a, b >>

    | FD_Sym g fg =>
        b & a <- AnnDefEq_dec G S g fg _;
        << a, b >>

    | FD_Trans g1 g2 fg1 fg2 =>
        a & c <- AnnDefEq_dec G S g1 fg1 _;
        d & b <- AnnDefEq_dec G S g2 fg2 _;
        tm_eq_dec c d >--->
        << a, b >>


    | FD_Beta a1 a2 fa1 fa2 =>
        A1 <- AnnTyping_dec G a1 fa1 _;
        A2 <- AnnTyping_dec G a2 fa2 _;
        tm_eq_dec (erase_tm A1) (erase_tm A2) >--->
        @beta_dec (erase_tm a1) (erase_tm a2) _ >--->
        << a1, a2 >>


    | FD_PiCong rho g1 g2 fg1 fg2 =>
      A1 & A2 <- AnnDefEq_dec G S g1 fg1 _;
      tm_eq_dec (get_tpg G A1) a_Star >--->
      tm_eq_dec (get_tpg G A2) a_Star >--->
      let (x, _) := atom_fresh (dom G \u fv_tm_tm_co g1 \u fv_tm_tm_co g2) in
      B1x & B2x <- AnnDefEq_dec ([(x, Tm A1)] ++ G) S (open_co_wrt_tm g2 (a_Var_f x)) (fg2 x _) _;
      let B1  := close_tm_wrt_tm x B1x in
      let B2  := close_tm_wrt_tm x B2x in
      let B3x := tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x B2x in
      let B3  := close_tm_wrt_tm x B3x in
      (* let B3 := close_tm_wrt_tm x (tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x B2x) in *)
      tm_eq_dec (get_tpg ([(x, Tm A1)] ++ G) B1x) a_Star >--->
      tm_eq_dec (get_tpg ([(x, Tm A1)] ++ G) B2x) a_Star >--->
      tm_eq_dec (get_tpg ([(x, Tm A2)] ++ G) B3x) a_Star >--->
      << a_Pi rho A1 B1, a_Pi rho A2 B3 >>


    | FD_AbsCong rho g1 g2 fg1 fg2 =>
      A1 & A2 <- AnnDefEq_dec G S g1 fg1 _;
      tm_eq_dec (get_tpg G A1) a_Star >--->
      tm_eq_dec (get_tpg G A2) a_Star >--->
      let (x, p) := atom_fresh (dom G \u fv_tm_tm_co g1 \u fv_tm_tm_co g2) in
      B1x & B2x <- AnnDefEq_dec ([(x, Tm A1)] ++ G) S (open_co_wrt_tm g2 (a_Var_f x)) (fg2 x _) _;
      let B1 := close_tm_wrt_tm x B1x in
      let B2 := close_tm_wrt_tm x B2x in
      let B3x := tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x B2x in
      let B3  := close_tm_wrt_tm x B3x in
      (* let B3 := close_tm_wrt_tm x (open_tm_wrt_tm B2 (a_Conv (a_Var_f x) (g_Sym g1))) in *)
      (* let B3 := close_tm_wrt_tm x (tm_subst_tm_tm (a_Conv (a_Var_f x) (g_Sym g1)) x B2x) in *)
      RhoCheck_erase_dec rho x B1x _ >--->
      RhoCheck_erase_dec rho x B3x _ >--->
      (* B <- AnnTyping_dec G (a_Abs rho A1 B2) _ _; *)
      << a_Abs rho A1 B1, a_Abs rho A2 B3 >>


    | FD_AppCong g1 g2 rho fg1 fg2 =>
      a1 & a2 <- AnnDefEq_dec G S g1 fg1 _;
      b1 & b2 <- AnnDefEq_dec G S g2 fg2 _;
      let Ta1 := get_tpg G a1 in
      let Ta2 := get_tpg G a2 in
      let Tb1 := get_tpg G b1 in
      let Tb2 := get_tpg G b2 in
      match Ta1, Ta2 with
        | a_Pi rho1 A1 _, a_Pi rho2 A2 _ =>
          tm_eq_dec A1 Tb1 >--->
          tm_eq_dec A2 Tb2 >--->
          rho_eq_dec rho rho1 >--->
          rho_eq_dec rho rho2 >--->
          << a_App a1 rho b1, a_App a2 rho b2 >>
        | _, _ => !!
      end


    | FD_CPiCong g1 g3 fg1 fg3 =>
        phi1 & phi2 <- AnnIso_dec G S g1 fg1 _;
        let (c, _) := atom_fresh (S \u dom G \u fv_co_co_co g1 \u fv_co_co_co g3) in
        B1c & B2c <- AnnDefEq_dec ([(c, Co phi1)] ++ G) S (open_co_wrt_co g3 (g_Var_f c)) (fg3 c _) _;
        let B1  := close_tm_wrt_co c B1c in
        let B2  := close_tm_wrt_co c B2c in
        let B3c := open_tm_wrt_co B2 (g_Cast (g_Var_f c) (g_Sym g1)) in
        let B3  := close_tm_wrt_co c (B3c) in
        tm_eq_dec (get_tpg ([(c,Co phi1)] ++ G) B1c) a_Star >--->
        tm_eq_dec (get_tpg ([(c,Co phi2)] ++ G) B3c) a_Star >--->
        tm_eq_dec (get_tpg ([(c,Co phi1)] ++ G) B2c) a_Star >--->
        << a_CPi phi1 B1, a_CPi phi2 B3 >>


    | FD_CAbsCong g1 g3 g4 fg1 fg3 fg4 =>
        phi1 & phi2 <- AnnIso_dec G S g1 fg1 _;
        let (c, _) := atom_fresh (S \u dom G \u fv_co_co_co g1 \u fv_co_co_co g3) in
        a1c & a2c <- AnnDefEq_dec ([(c, Co phi1)] ++ G) S (open_co_wrt_co g3 (g_Var_f c)) (fg3 c _) _;
        let a1  := close_tm_wrt_co c a1c in
        let a2  := close_tm_wrt_co c a2c in
        let a3c := open_tm_wrt_co a2 (g_Cast (g_Var_f c) (g_Sym g1)) in
        let a3  := close_tm_wrt_co c a3c in
        let B1c := get_tpg ([(c, Co phi1)] ++ G) a1c in
        let B3c := get_tpg ([(c, Co phi2)] ++ G) a3c in
        CPi1 & CPi2 <- AnnDefEq_dec G (dom G) g4 fg4 _;
        tm_eq_dec CPi1 (a_CPi phi1 (close_tm_wrt_co c B1c)) >--->
        tm_eq_dec CPi2 (a_CPi phi2 (close_tm_wrt_co c B3c)) >--->
        << a_CAbs phi1 a1, a_CAbs phi2 a3 >>


    | FD_CAppCong g1 g2 g3 fg1 fg2 fg3 =>
      a1 & a2 <- AnnDefEq_dec G S g1 fg1 _;
      b1 & b2 <- AnnDefEq_dec G (dom G) g2 fg2 _;
      c1 & c2 <- AnnDefEq_dec G (dom G) g3 fg3 _;
      let Ta1 := get_tpg G a1 in
      let Ta2 := get_tpg G a2 in
      match Ta1, Ta2 with
        | a_CPi (Eq Ta11 Ta12 _) _, a_CPi (Eq Ta21 Ta22 _) _ =>
          (* TODO: in theory, one would want to do a cons_eq_dec - but DeqEq_dec doesn't return the type *)
          tm_eq_dec Ta11 b1 >--->
          tm_eq_dec Ta12 b2 >--->
          tm_eq_dec Ta21 c1 >--->
          tm_eq_dec Ta22 c2 >--->
          << a_CApp a1 g2, a_CApp a2 g3 >>
        | _, _ => !!
      end

    | FD_CPiSnd g1 g2 g3 fg1 fg2 fg3 =>
      a1 & a2 <- AnnDefEq_dec G S g1 fg1 _;
      a & a' <- AnnDefEq_dec G (dom G) g2 fg2 _;
      b & b' <- AnnDefEq_dec G (dom G) g3 fg3 _;
      match a1, a2 with
        | a_CPi (Eq a_ a_' _) B1, a_CPi (Eq b_ b_' _) B2 =>
          tm_eq_dec a  a_  >--->
          tm_eq_dec a' a_' >--->
          tm_eq_dec b  b_  >--->
          tm_eq_dec b' b_' >--->
          << open_tm_wrt_co B1 g2, open_tm_wrt_co B2 g3 >>
        | _, _ => !!
      end


    | FD_Cast g1 g2 fg1 fg2 =>
      a & a' <- AnnDefEq_dec G S g1 fg1 _;
      phi1 & phi2 <- AnnIso_dec G S g2 fg2 _;
      match phi1, phi2 with
        | Eq a_ a'_ _, Eq b b' _ =>
          tm_eq_dec a  a_  >--->
          tm_eq_dec a' a'_ >--->
          << b, b' >>
      end

    | FD_PiFst g fg =>
      T1 & T2 <- AnnDefEq_dec G S g fg _;
      match T1, T2 with
        | a_Pi rho1 A1 B1, a_Pi rho2 A2 B2 => rho_eq_dec rho1 rho2 >---> << A1, A2 >>
        | _, _ => !!
      end



    | FD_PiSnd g1 g2 fg1 fg2 =>
        T1 & T2 <- AnnDefEq_dec G S g1 fg1 _;
        a1 & a2 <- AnnDefEq_dec G S g2 fg2 _;
     (* A1 <- AnnTyping_dec G a1 _ _;
        A2 <- AnnTyping_dec G a2 _ _; *)
        let A1 := get_tpg G a1 in
        let A2 := get_tpg G a2 in
        match T1 with
          | a_Pi rho A1' B1 =>
            tm_eq_dec A1 A1' >--->
            match T2 with
              | a_Pi rho' A2' B2 =>
                tm_eq_dec A2 A2' >--->
                rho_eq_dec rho rho' >--->
                << open_tm_wrt_tm B1 a1, open_tm_wrt_tm B2 a2 >>
              | _ => !!
            end
          | _ => !!
        end


    | FD_IsoSnd g fg =>
      phi1 & phi2 <- AnnIso_dec G S g fg _;
      match phi1, phi2 with
        | (Eq _ _ A), (Eq _ _ B) => << A, B>>
      end


    | FD_Eta b fb =>
      let (x, p) := atom_fresh (dom G \u fv_tm_tm_tm b) in
      T <- AnnTyping_dec G b fb _;
      match T with
      | a_Pi Rel A B =>
        << a_Abs Rel A (close_tm_wrt_tm x (a_App b Rel (a_Var_f x))), b >>
      | a_Pi Irrel A B =>
        << a_Abs Irrel A (close_tm_wrt_tm x (a_App b Irrel (a_Var_f x))), b >>
      | a_CPi phi B =>
        << a_CAbs phi (close_tm_wrt_co x (a_CApp b (g_Var_f x))), b >>
      | _ => !!
      end

    | FD_Left g1  g2 fg1 fg2  => !!
    | FD_Right _ _ _ _ => !!
(* Left/Right.   This doesn't work yet.
    | FD_Left g1  g2 fg1 fg2  =>
      s1 & s2 <- AnnDefEq_dec G S g1 fg1 _;
      t1 & t2 <- AnnDefEq_dec G (dom G) g2 fg2 _ ;
      match s1 with
      | (a_App a1 Rel a2) =>
        match s2 with
        | (a_App a1' Rel a2') =>
          match t1 with
          | (a_Pi Rel A1 B1) =>
            match t2 with
            | (a_Pi Rel A2 B2) =>
              path_dec a1 >--->
              path_dec a1' >--->
              let A := get_tpg G a1  in
              let A' := get_tpg G a1' in
              tm_eq_dec A (a_Pi Rel A1 B1) >--->
              tm_eq_dec A' (a_Pi Rel A2 B2) >--->
              << a1 , a1' >>
            | _ => !!
            end
          | _ => !!
          end
        | _ => !!
        end
      | _ => !!
      end
        (*
      | (a_App a1 Irrel a2, a_App a1' Irrel a2', a_Pi Irrel A1 B1, a_Pi Irrel A2 B2) =>
          let A := get_tpg G a1  in
          let A' := get_tpg G a1' in
          tm_eq_dec A (a_Pi Irrel A1 B1) >--->
          tm_eq_dec A' (a_Pi Irrel A2 B2) >--->
          << a1 , a1' >>

      | (a_CApp a1 a2, a_CApp a1' a2', a_CPi A1 B1, a_CPi A2 B2) =>
          let A := get_tpg G a1  in
          let A' := get_tpg G a1' in
          tm_eq_dec A (a_CPi A1 B1) >--->
          tm_eq_dec A' (a_CPi A2 B2) >--->
          << a1 , a1' >>

      | _ => !!
      end *)

    | FD_Right g1  g2 fg1 fg2  =>
      s1 & s2 <- AnnDefEq_dec G S g1 fg1 _;
      t1 & t2 <- AnnDefEq_dec G (dom G) g2 fg2 _ ;
      match (s1, s2, t1, t2) with
      | (a_App a1 r1 a2, a_App a1' r2 a2', a_Pi r3 A1 B1, a_Pi r4 A2 B2) =>
          let A := get_tpg G a1  in
          let A' := get_tpg G a1' in
          tm_eq_dec A (a_Pi r3 A1 B1) >--->
          tm_eq_dec A' (a_Pi r4 A2 B2) >--->
          rho_eq_dec r1 r2 >--->
          rho_eq_dec r1 r3 >--->
          rho_eq_dec r1 r4 >--->
          << a2 , a2' >>
      | _ => !!
      end
*)
    (* Trivial cases *)
    | FD_Triv          => !!
    | FD_Var_b _       => !!
    | FD_CPiFst _      => !!
    | FD_Cong _ _ _    => !!
    | FD_IsoConv _ _ _ => !!

  end


with AnnIso_dec (G: context) (S : available_props) (g : co) (fuel : fuel_iso g)
                (H: AnnCtx G) {struct fuel} : {phi1, phi2 | AnnIso G S g phi1 phi2} + {(forall phi1 phi2, ¬ AnnIso G S g phi1 phi2)} :=
  match fuel with
    | FI_Cong g1 A g2 fg1 fg2 =>
      A1 & A2 <- AnnDefEq_dec G S g1 fg1 _;
      B1 & B2 <- AnnDefEq_dec G S g2 fg2 _;
      AnnPropWff_dec' G A1 B1 A (get_tpg G A1) (get_tpg G B1) _ _ _ >--->
      AnnPropWff_dec' G A2 B2 A (get_tpg G A2) (get_tpg G B2) _ _ _ >--->
      << Eq A1 B1 A, Eq A2 B2 A >>

    | FI_CPiFst g fg =>
      pi1 & pi2 <- AnnDefEq_dec G S g fg _;
      match pi1, pi2 with
        | a_CPi phi1 _, a_CPi phi2 _ =>
          << phi1, phi2 >>
        | _, _ => !!
      end

    | FI_IsoSym g fg =>
      phi2 & phi1 <- AnnIso_dec G S g fg _;
      << phi1, phi2 >>


    | FI_IsoConv g phi1 phi2 fg fpwf1 fpwf2  =>
      A' & B' <- AnnDefEq_dec G S g fg _;
      AnnPropWff_dec G phi1 fpwf1 _ >--->
      AnnPropWff_dec G phi2 fpwf2 _ >--->
      match phi1, phi2 with
        | Eq a1 a2 A, Eq a1' a2' B =>
          tm_eq_dec (erase_tm  a1) (erase_tm  a1') >--->
          tm_eq_dec (erase_tm  a2) (erase_tm  a2') >--->
          tm_eq_dec A A' >--->
          tm_eq_dec B B' >--->
          << phi1, phi2 >>
      end



    (* Non-iso coercions *)
    | FI_Var_f c => !!
    | FI_Var_b _ => !!
    | FI_Refl a => !!
    | FI_Refl2 a b g => !!
    | FI_Trans g1 g2 =>  !!
    | FI_Beta a1 a2 => !!
    | FI_PiCong rho g1 g2 => !!
    | FI_AbsCong _ _ _ => !!
    | FI_AppCong g1 rho g2 => !!
    | FI_CAbsCong _ _ _ => !!
    | FI_CAppCong g1 g2 g3 => !!
    | FI_PiFst g => !!
    | FI_Cast g1 g2 => !!
    | FI_PiSnd g1 g2 => !!
    | FI_Triv => !!
    | FI_CPiCong _ _ => !!
    | FI_CPiSnd _ _ _ => !!
    | FI_IsoSnd _ => !!
    | FI_Eta _ => !!
    | FI_Left _ _ => !!
    | FI_Right _ _ => !!
  end

.




(*
Solve Obligations of AnnDefEq_dec with obtacpre; first [match goal with [|- tm] => idtac end | eassumption].
*)





Obligation Tactic :=
  obtacsolve.








(******** AnnDefEq_dec ********)

Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
Defined.
Next Obligation.
  hacky.
Defined.

(* An_EraseEq *)
Next Obligation.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
Defined.

(* An_Sym *)
Next Obligation.
  hacky.
Defined.

Obligation Tactic := obtacpre.


Next Obligation.
  eauto using An_Sym2.
Defined.

(* An_Trans *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  subst.
  eauto using An_Trans2.
Defined.


(* An_Beta *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  move: lc_erase => [h0 _].
  eapply h0.
  move: (AnnTyping_lc wildcard'0) => [h1 _].
  auto.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup.
Defined.


(* FIXME: in the following hard cases (Abs/CAbs/Pi/CPi -Cong), the code likely contains a lot of junk
    It could also be made more concise, by using more ssr magic *)

(* TODO: this belongs in tactics *)
  Ltac reg H :=
  match type of H with
    | AnnTyping _ ?a ?A =>
      first
        [ let tpgA := fresh "tpg" A in move: (AnnTyping_regularity H) => tpgA
        | let tpgA := fresh "tpg"   in move: (AnnTyping_regularity H) => tpgA]
    | AnnDefEq _ _ ?g ?A ?B =>
      let KA := fresh "K" A in
      let KB := fresh "K" B in
      let g' := fresh "g" in
      let tpgA := fresh "tpg" A in
      let tpgB := fresh "tpg" B in
      (* let deqg' := fresh "deq" g' in *)
      move: (AnnDefEq_regularity H) => [KA [KB [g' [tpgA [tpgB (* deqg' *) _]]]]]
    (* FIXME: this is the same case than above, with less informative fresh names.
       This is needed because fresh can fail (like, seriously?)
       TODO: failproof version of fresh *)
    | AnnDefEq _ _ ?g ?A ?B =>
      let KA := fresh "K" in
      let KB := fresh "K" in
      let g' := fresh "g" in
      let tpgA := fresh "tpg" in
      let tpgB := fresh "tpg" in
      (* let deqg' := fresh "deq" g' in *)
      move: (AnnDefEq_regularity H) => [KA [KB [g' [tpgA [tpgB (* deqg' *) _]]]]]

    | AnnIso _ _ ?g ?phi1 ?phi2 =>
      let pwfp1 := fresh "pwf" phi1 in
      let pwfp2 := fresh "pwf" phi2 in
      move: (AnnIso_regularity H) => [pwfp1 pwfp2]
  end.


Ltac cleanup_getcor :=
  repeat match goal with
    | [ _: get_tpg _ _ = get_tpg _ _ |- _ ] => fail
    | [ eq: _ = get_tpg _ _ |- _ ] => symmetry in eq
  end.


(* FIXME: same, should be elsewhere (fc_invert.v?) *)
Ltac getcor a :=
  cleanup_getcor;
  match goal with
    | [ eq: get_tpg ?G a = _,
        tpg : AnnTyping ?G a ?A |- _ ] =>
          let t := fresh tpg in
          move: (get_tpg_correct tpg eq) => t; subst A
  end.


(* TODO: location *)
(* For now, this assumes that we only need regularity on defeq hyps *)
Ltac autoreg :=
  repeat match goal with
    | [ H: AnnDefEq _ _ _ _ _ |- _ ] =>
      reg H; wrap_hyp H
    | [ H: AnnIso _ _ _ _ _ |- _ ] =>
      reg H; wrap_hyp H
  end;
  pcess_hyps.

Ltac clearget :=
  cleanup_getcor;
  repeat match goal with
    | [ H: get_tpg _ _ = get_tpg _ _ |- _ ] => fail
    | [ eqTa : get_tpg ?G ?a = ?Ta,
        tpga : AnnTyping ?G ?a ?Ta' |- _ ] =>
      let eq := fresh in
      (* FIXME: in the following subst, we don't control which equation gets rewritten -> inconsistent results *)
      move:(get_tpg_correct' tpga); move=> eq; rewrite <- eq in *; clear eq; subst Ta'
  end.




(* An_PiCong *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup.
  inversion 1.
  auto_uniq_full.
  apply wildcard'.
  have: A0 = A1 by done. move => <-.
  inversion H9.
  by move: (get_tpg_correct' H21) => <-.
Defined.
Next Obligation.
  cleanup.
  inversion 1.
  auto_uniq_full.
  apply wildcard'.
  have: A3 = A2 by done. move => <-.
  inversion H12.
  by move: (get_tpg_correct' H21) => <-.
Defined.
Next Obligation. (* Fuel: aux obligation *)
  fsetdec.
Defined.
Next Obligation. (* Ctx wf *)
  econstructor; try eassumption.
  - cleanup.
    reg wildcard'0.
    by getcor A1.
  - fsetdec.
Defined.
Next Obligation.
  cleanup.
  move /An_PiCong_inversion.
  move => [a1 [b1 [a2 [b2 [b3 [eqA [eqB [tpg1 [tpg2 [tpg3 [defeq h]]]]]]]]]]].
  apply: wildcard'.
  have xnotin: x `notin` dom G by fsetdec.
  move: (h _ xnotin) => [h' _].
  auto_uniq_full; subst.
  by apply: h'.
Defined.
Next Obligation.
  cleanup'.
  move /An_PiCong_inversion.
  move => [a1 [b1 [a2 [b2 [b3 [eqA [eqB [tpg1 [tpg2 [tpg3 [defeq h]]]]]]]]]]].
  eapply wildcard'.
  have xG: x `notin` dom G by fsetdec.
  move: (h _ xG) => /= [h' _].
  have: A1 = a1 by cleanup; auto_uniq_full. move => ?; subst A1.
  auto_uniq_full.
  move: (An_Pi_inversion tpg1) => [_ [_]] /(_ _ xG).
  by move: (u3 _ _ wildcard'3) => [<- _] => /(get_tpg_correct') ->.
Defined.
Next Obligation.
  cleanup'.
  move /An_PiCong_inversion.
  move => [a1 [b1 [a2 [b2 [b3 [eqA [eqB [tpg1 [tpg2 [tpg3 [defeq h]]]]]]]]]]].
  eapply wildcard'.
  have xG: x `notin` dom G by fsetdec.
  move: (h _ xG) => /= [h' _].
  have: A1 = a1 by cleanup; auto_uniq_full. move => ?; subst A1.
  clearbodies'.
  auto_uniq_full.
  move: (An_Pi_inversion tpg3) => [_ [_]] /(_ _ xG).
  by move: (u3 _ _ wildcard'3) => [_ <-] => /(get_tpg_correct') ->.
Defined.
Next Obligation.
  cleanup'.
  move /An_PiCong_inversion.
  move => [a1 [b1 [a2 [b2 [b3 [eqA [eqB [tpg1 [tpg2 [tpg3 [defeq h]]]]]]]]]]].
  eapply wildcard'.
  have xG: x `notin` dom G by fsetdec.
  move: (h _ xG) => /= [h' eqb3].
  have: A1 = a1 by cleanup; auto_uniq_full. move => ?; subst A1.
  have: A2 = a2 by cleanup; auto_uniq_full. move => ?; subst A2.
  clearbodies'.
  auto_uniq_full.
  move: (An_Pi_inversion tpg2) => [_ [_]] /(_ _ xG).
  have realeq : B3x = open_tm_wrt_tm B2 (a_Conv (a_Var_f x) (g_Sym g1)) by rewrite eqB3x eqB2 tm_subst_tm_tm_spec.
  move: realeq eqb3 eqB2 H2 => -> -> -> <-. rewrite close_tm_wrt_tm_open_tm_wrt_tm.
  - by move => /(get_tpg_correct') ->.
  - (* Fv in context for tpg hyp *) (* TODO: tactic *)
    move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _  tpg3) /= [htmco [hcoco [htmtm hcotm ] ] ].
    by fsetdec.
Defined.
Next Obligation.
  cleanup'.
  rewrite eqB1 eqB3.
  eapply An_PiCong_exists3 with (x := x); try eassumption.
  fsetdec.
Defined.



(* An_AbsCong *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup.
  move /An_AbsCong_inversion => [a1' [a2' [b1' [b2' [b3' [B' h]]]]]].
  move: h => [eqA [eqB [tpga1' [tpga2' [defg1 [tpga1b2' h]]]]]].
  apply: wildcard'.
  have: A1 = a1' by auto_uniq_full.
  move=> ->.
  by rewrite (get_tpg_correct' tpga1').
Defined.
Next Obligation.
  cleanup.
  move /An_AbsCong_inversion => [a1' [a2' [b1' [b2' [b3' [B' h]]]]]].
  move: h => [eqA [eqB [tpga1' [tpga2' [defg1 [tpga1b2' h]]]]]].
  apply: wildcard'.
  have: A2 = a2' by auto_uniq_full.
  move=> ->.
  by rewrite (get_tpg_correct' tpga2').
Defined.
Next Obligation. (* Fuel: aux obligation *)
  fsetdec.
Defined.
Next Obligation. (* Ctx wf *)
  econstructor; try eassumption.
  - cleanup.
    reg wildcard'0.
    by getcor A1.
  - fsetdec.
Defined.
Next Obligation.
  cleanup.
  move /An_AbsCong_inversion => [a1' [a2' [b1' [b2' [b3' [B' h]]]]]].
  move: h => [eqA [eqB [tpga1' [tpga2' [defg1 [tpga1b2' h]]]]]].
  apply: wildcard'.
  auto_uniq_full.
  have: A1 = a1' /\ A2 = a2' by split; congruence.
  move=> [? ?]. subst A1 A2.
  have xG: x `notin` dom G by fsetdec.
  move: (h x xG) => [tpgg2 [_ [h' _] ] ].
  eassumption.
Defined.
Next Obligation.
  by move: (wf.AnnDefEq_lc1 wildcard').
Defined.
Next Obligation.
  cleanup.
  move /An_AbsCong_inversion => [a1' [a2' [b1' [b2' [b3' [B' h]]]]]].
  move: h => [eqA [eqB [tpga1' [tpga2' [defg1 [tpga1b2' h]]]]]].
  have p': x `notin` dom G by fsetdec.
  move: (h x p') => [tpgg2 [_ [h' _] ] ].
  apply wildcard'.
  suff eq: B1x = open_tm_wrt_tm b1' (a_Var_f x) by rewrite eq.
  auto_uniq_full.
  move: (u2 _ _ wildcard'0) => [eqA1 _].
  rewrite eqA1 in tpgg2.
  by move: (u _ _ tpgg2) => [->].
Defined.
Next Obligation.
  cleanup'.
  move: (wf.AnnDefEq_lc2 wildcard'3).
  rewrite eqB3x => ?.
  apply: tm_subst_tm_tm_lc_tm => /=.
  + done.
  + apply lc_a_Conv.
    - done.
    - move: (wf.AnnDefEq_lc3 wildcard'0) => ?.
      econstructor; eassumption.
Defined.
Next Obligation.
  clear dependent filtered_var.
  cleanup'.
  move=> tpgg1g2. move: (tpgg1g2).
  move /An_AbsCong_inversion => [a1' [a2' [b1' [b2' [b3' [B' h]]]]]].
  move: h => [eqA [eqB [tpga1' [tpga2' [defg1 [tpga1b2' h]]]]]].
  apply wildcard'.
  have p': x `notin` dom G by fsetdec.
  move: (h x p') => [tpgg2 [eqb3' [_ h'] ] ].
  suff eq: B3x = open_tm_wrt_tm b3' (a_Var_f x) by rewrite eq.
  auto_uniq_full.
  have: A1 = a1' /\ A2 = a2' by split; congruence.
  move=> [? ?]. subst A1 A2.
  rewrite eqB3x.
  move: (u5 _ _ wildcard'3) => [_ eqb2'].
  rewrite -eqb2' eqb3' tm_subst_tm_tm_spec close_tm_wrt_tm_open_tm_wrt_tm.
  - done.
  - (* Fv in context for tpg hyp *)
    move: ann_context_fv_mutual => [h''' [_ [_ [_ _] ] ] ]; move: h''' => /(_ _ _ _ tpga1b2') /= [htmco'' [hcoco'' [htmtm'' hcotm'' ] ] ].
    by fsetdec.
Defined.
Next Obligation.
  clear dependent filtered_var.
  cleanup'.
  rewrite eqB1 eqB3.
  eapply An_AbsCong_exists3; try eassumption.
  - fsetdec.
  - reflexivity.
Defined.




(* An_AppCong *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup'.
  inversion 1.
  apply wildcard'.
  reg wildcard'2.
  reg wildcard'1.
  getcor a1.
  getcor b1.
  subst Ta1 Tb1.
  auto_uniq_full.
  intro_uniq_full wildcard'2. (* FIXME: auto_uniq_full not working here *)
  intro_uniq_full wildcard'1. (* FIXME: auto_uniq_full not working here *)
  have: a0 = a1 by congruence => [-> _].
  move=> ?.
  subst a0. subst a3.
  inversion H8.
  intro_uniq_full H19. (* TODO: this proof is messy *)
  have: A1 = A3 by congruence. move => ->.
  by move: (get_tpg_correct' H21).
Defined.
Next Obligation.
  cleanup'.
  inversion 1.
  apply wildcard'.
  reg wildcard'2.
  reg wildcard'1.
  getcor a2.
  getcor b2.
  subst Ta2 Tb2.
  auto_uniq_full.
  intro_uniq_full wildcard'2. (* FIXME: auto_uniq_full not working here *)
  intro_uniq_full wildcard'1. (* FIXME: auto_uniq_full not working here *)
  have: a0 = a1 by congruence => [-> _].
  move=> ?.
  subst b0. subst b2.
  inversion H11.
  intro_uniq_full H20. (* TODO: this proof is messy *)
  have: A2 = A3 by congruence. move => ->.
  by move: (get_tpg_correct' H21).
Defined.
Next Obligation.
  cleanup'.
  cleanup_getcor.
  autoreg.
  clearget.
  inversion 1. inversion H8.
  apply: wildcard'.
  auto_uniq_full. subst a0.
  move: (u9 _ tpga1).
  congruence.
Defined.
Next Obligation.
  cleanup'.
  cleanup_getcor.
  autoreg.
  clearget.
  inversion 1. inversion H11.
  apply: wildcard'.
  auto_uniq_full. subst b0.
  move: (u9 _ tpga2).
  congruence.
Defined.
Next Obligation.
  (* FIXME: cleanup' not working *)
  clear dependent filtered_var.
  clear dependent filtered_var1.
  clear dependent filtered_var0.
  clear dependent filtered_var2.
  clear dependent filtered_var4.
  clear dependent filtered_var3. subst. clear dependent fuel.
  clean_fun. clearbodies'.

  autoreg.
  clearget.
  auto_uniq_full.
  eapply An_AppCong2; try eassumption.
  all: econstructor;
  eauto using An_AppCong2.
  subst Ta1. eassumption.
  subst Ta2. eassumption.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  hacky.
Defined.


(* The numerous cases for the pattern match have been inlined -> solving them automatically *)
Ltac discr_pat_match :=
  solve [obtacpre; solve [ let eq1 := fresh in let eq2 := fresh in move=> [eq1 eq2]; try discriminate eq1; discriminate eq2
                         | subst; inversion 1 ] ].

Solve Obligations of AnnDefEq_dec with discr_pat_match.



(* An_CPiCong *)
Next Obligation.
  hacky.
Defined.
Next Obligation. (* Fuel: Aux *)
  fsetdec.
Defined.
Next Obligation.
  econstructor.
  - eassumption.
  - cleanup'. by autoreg.
  - fsetdec.
Defined.
Next Obligation.
  cleanup.
  move /An_CPiCong_inversion.
  move => [ph1 [ph2 [b1 [b2 [b3 [eqA [eqB [isoph1 [tpgp1 [tpgp2 [tpg3 h]]]]]]]]]]].
  apply: wildcard'.
  have cG: c `notin` dom G by ok.
  move: (h _ cG) => /= [h' _].
  auto_uniq_full; subst.
  by apply: h'.
Defined.
Next Obligation.
  cleanup'.
  pcess_hyps.
  move /An_CPiCong_inversion.
  move => [ph1 [ph2 [b1 [b2 [b3 [eqA [eqB [isoph1 [tpgp1 [tpgp2 [tpg3 h]]]]]]]]]]].
  apply: wildcard'.
  auto_uniq_full.
  have cG: c `notin` dom G by ok.
  have: phi1 = ph1 by congruence. move=> eqphi. rewrite eqphi.
  move: (An_CPi_inversion tpgp1). do 2 move=> [_]. move => /(_ c cG) h'.
  move: (get_tpg_correct' h') => ->.
  suff: B1c = (open_tm_wrt_co b1 (g_Var_f c)) by move=> ->.
  move: (h _ cG) => /= [h'' _].
  auto_uniq_full.
  (* Fv in context for tpg hyp *)
  move: ann_context_fv_mutual => [h''' [_ [_ [_ _] ] ] ]; move: h''' => /(_ _ _ _ tpgp1) /= [? [? [? ?]]].
  rewrite eqphi in wildcard'1.
  by move:  (u10 _ _ wildcard'1) => [<- _].
Defined.
Next Obligation.
  cleanup'.
  move /An_CPiCong_inversion.
  move => [ph1 [ph2 [b1 [b2 [b3 [eqA [eqB [isoph1 [tpgp1 [tpgp2 [tpg3 h]]]]]]]]]]].
  apply: wildcard'.
  auto_uniq_full.
  have cG: c `notin` dom G by ok.
  have: phi1 = ph1 by congruence. move=> eqph1.
  have: phi2 = ph2 by congruence. move=> eqph2. rewrite eqph2.
  move: (An_CPi_inversion tpgp2). do 2 move=> [_]. move => /(_ c cG) h'.
  move: (get_tpg_correct' h') => ->.
  suff: B3c = (open_tm_wrt_co b3 (g_Var_f c)) by move=> ->.
  move: (h _ cG) => /= [h'' eqb3].
  auto_uniq_full.
  (* Fv in context for tpg hyp *)
  move: ann_context_fv_mutual => [h''' [_ [_ [_ _] ] ] ]; move: h''' => /(_ _ _ _ tpg3) /= [? [? [? ?]]].
  rewrite eqph1 in wildcard'2.
  rewrite eqB3c eqB2 eqb3.
  subst phi1.
  move:  (u10 _ _ wildcard'1) => [_ <-].
  rewrite close_tm_wrt_co_open_tm_wrt_co; by [|fsetdec].
Defined.
Next Obligation.
  cleanup'.
  move /An_CPiCong_inversion.
  move => [ph1 [ph2 [b1 [b2 [b3 [eqA [eqB [isoph1 [tpgp1 [tpgp2 [tpg3 h]]]]]]]]]]].
  apply: wildcard'.
  auto_uniq_full.
  have cG: c `notin` dom G by ok.
  have: phi1 = ph1 by congruence. move=> eqph1.
  have: phi2 = ph2 by congruence. move=> eqph2. rewrite eqph1.
  move: (An_CPi_inversion tpg3). do 2 move=> [_]. move => /(_ c cG) h'.
  move: (get_tpg_correct' h') => ->.
  suff: B2c = (open_tm_wrt_co b2 (g_Var_f c)) by move=> ->.
  move: (h _ cG) => /= [h'' eqb3].
  auto_uniq_full.
  (* Fv in context for tpg hyp *)
  move: ann_context_fv_mutual => [h''' [_ [_ [_ _] ] ] ]; move: h''' => /(_ _ _ _ tpg3) /= [? [? [? ?]]].
  rewrite eqph1 in wildcard'2.
  subst ph1.
  by move:  (u10 _ _ wildcard'1) => [_ <-].
Defined.
Next Obligation.
  cleanup'.
  (* Fv in context for eqdec hyp *)
  move: ann_context_fv_mutual => [_ [_ [_ [h''' _] ] ] ]; move: h''' => /(_ _ _ _  _ _ wildcard'1) /= [? [? [? ?]]].
  autoreg.
  rewrite eqB1 eqB3.
  eapply An_CPiCong_exists_3 with (c := c) (B2 := B2c);
    try eassumption.
  - fsetdec.
  - move: co_subst_co_tm_spec. congruence.
Defined.



(* An_CAbsCong *)
Next Obligation.
  hacky.
Defined.
Next Obligation. (* Fuel: aux *)
  fsetdec.
Defined.
Next Obligation. (* Ctx wf *)
  cleanup'.
  autoreg.
  econstructor; try eassumption.
  fsetdec.
Defined.
Next Obligation.
  cleanup.
  move /An_CAbsCong_inversion.
  move => [ph1 [ph2 [a1' [a2' [a3' [B1' [B2' [B3' [eqA [eqB [isoph12 [tpg1 [tpg2 [tpg3 [defeq4 h]]]]]]]]]]]]]]].
  have cG: c `notin` dom G by ok.
  move: (h _ cG) => /= [defeq3 eq23].
  apply: wildcard'.
  auto_uniq_full; subst.
  by apply: defeq3.
Defined.
Next Obligation.
  eassumption.
Defined.
Next Obligation.
  cleanup_param clearbodies' idtac.
  move /An_CAbsCong_inversion.
  move => [ph1 [ph2 [a1' [a2' [a3' [B1' [B2' [B3' [eqA [eqB [isoph12 [tpg1 [tpg2 [tpg3 [defeq4 h]]]]]]]]]]]]]]].
  (* Fv in context for eqdec hyp *)
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ tpg1) /= [? [? [? ?] ] ].
  have cG: c `notin` dom G by ok.
  move: (h _ cG) => /= [defeq3 eq23].
  apply: wildcard'.
  auto_uniq_full. (* TODO: it needs to be smarter on the opened contexts/when things are just congruent *)
  have eqphi1: phi1 = ph1 by move: (u0 _ _ wildcard'0) => [-> _].
  suff: a1 = a1' by move: (eqphi1) => [-> ->]; eassumption.
  rewrite eqphi1 in wildcard'1.
  move: (eqa1) (u5 _ _ wildcard'1) close_tm_wrt_co_open_tm_wrt_co => -> [<- _] ->; ok.
Defined.
Next Obligation.
  cleanup'.
  move /An_CAbsCong_inversion.
  move => [ph1 [ph2 [a1' [a2' [a3' [B1' [B2' [B3' [eqA [eqB [isoph12 [tpg1 [tpg2 [tpg3 [defeq4 h]]]]]]]]]]]]]]].
  (* Fv in context for eqdec hyp *)
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ tpg1) /= [? [? [? ?] ] ].
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ tpg2) /= [? [? [? ?] ] ].
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ tpg3) /= [? [? [? ?] ] ].
  have cG: c `notin` dom G by ok.
  move: (h _ cG) => /= [defeq3 eq23].
  apply: wildcard'.
  auto_uniq_full. (* TODO: it needs to be smarter on the opened contexts/when things are just congruent *)
  have [eqphi1 eqphi2] : phi1 = ph1 /\ phi2 = ph2 by move: (u0 _ _ wildcard'0) => [-> ->]. subst ph1 ph2.

  subst CPi1.
  have: a1 = a1' by move: eqa1 (u _ _ defeq3) => -> [-> _]; autorewrite with lngen.
  intros; subst a1'.
  rewrite eqB1c.
  move: (An_CAbs_inversion tpg1) => [B0 [tmp h'']]. injection tmp.
  intros; subst B0.
  move: (h'' c cG) => [_ tpga1].
  move: (get_tpg_correct' tpga1).
  rewrite eqa1. autorewrite with lngen.
  move=> <-.
  by autorewrite with lngen.
Defined.
Next Obligation.
  cleanup'.
  move /An_CAbsCong_inversion.
  move => [ph1 [ph2 [a1' [a2' [a3' [B1' [B2' [B3' [eqA [eqB [isoph12 [tpg1 [tpg2 [tpg3 [defeq4 h]]]]]]]]]]]]]]].
  (* Fv in context for eqdec hyp *)
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ tpg1) /= [? [? [? ?] ] ].
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ tpg2) /= [? [? [? ?] ] ].
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ tpg3) /= [? [? [? ?] ] ].
  have cG: c `notin` dom G by ok.
  move: (h _ cG) => /= [defeq3 eq23].
  apply: wildcard'.
  auto_uniq_full. (* TODO: it needs to be smarter on the opened contexts/when things are just congruent *)
  have [eqphi1 eqphi2] : phi1 = ph1 /\ phi2 = ph2 by move: (u0 _ _ wildcard'0) => [-> ->]. subst ph1 ph2.

  subst CPi2.
  have: a2 = a2' by move: eqa2 (u _ _ defeq3) => -> [_ ->]; autorewrite with lngen.
  intros; subst a2'.
  have: a3 = a3' by rewrite eqa3 eqa3c -eq23; autorewrite with lngen.
  intros; subst a3'.
  rewrite eqB3c.
  move: (An_CAbs_inversion tpg2) => [B0 [tmp h'']]. injection tmp.
  intros; subst B0.
  move: (h'' c cG) => [_ tpga2].
  move: (get_tpg_correct' tpga2).
  rewrite eqa3. autorewrite with lngen.
  move=> <-.
  by autorewrite with lngen.
Defined.
Next Obligation.
  cleanup'.
  (* Fv in context for eqdec hyp *)
  move: ann_context_fv_mutual => [_ [_ [_ [h''' _]]]]; move: h''' => /(_ _ _ _  _ _ wildcard'2) /= [? [? [? ?]]].
  rewrite eqa1 eqa3.
  autoreg.
  (* FIXME: clearget not working here (losing an eq) *)
  (* clearget. *)
  eapply An_CAbsCong_exists3 with (c := c) (a2 := a2c) (B1 := B1c) (B3 := B3c); try eassumption; try congruence.
  - fsetdec.
  - rewrite co_subst_co_tm_spec.
    congruence.
  - by rewrite eqB1c.
  - by rewrite eqB3c.
Defined.
Next Obligation.
  hacky.
Defined.



(* An_CAppCong *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  subst Ta1 Ta2.

  (* Inversion and glueing *)
  inversion 1.
  have: a0 = a1 /\ b0 = a2 by auto_uniq_full; split; congruence.
  move=> [? ?]; subst a0 b0; clear H4.
  have: a3 = b1 /\ b3 = b2 by auto_uniq_full; split; congruence.
  move=> [? ?]; subst a3 b3; clear H5.

  (* Contra *)
  apply wildcard'.
  inversion H9.
  have: Ta11 = a0 by auto_uniq_full; congruence.
  move=> ?; subst a0.
  by auto_uniq_full.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  subst Ta1 Ta2.

  (* Inversion and glueing *)
  inversion 1.
  have: a0 = a1 /\ b0 = a2 by auto_uniq_full; split; congruence.
  move=> [? ?]; subst a0 b0; clear H4.
  have: a3 = b1 /\ b3 = b2 by auto_uniq_full; split; congruence.
  move=> [? ?]; subst a3 b3; clear H5.

  (* Contra *)
  apply wildcard'.
  inversion H9.
  have: Ta12 = b2 by auto_uniq_full; congruence.
  move=> ?; subst b2.
  by auto_uniq_full.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  subst Ta1 Ta2.

  (* Inversion and glueing *)
  inversion 1.
  have: a0 = a1 /\ b0 = a2 by auto_uniq_full; split; congruence.
  move=> [? ?]; subst a0 b0; clear H4.
  have: a3 = b1 /\ b3 = b2 by auto_uniq_full; split; congruence.
  move=> [? ?]; subst a3 b3; clear H5.

  (* Contra *)
  apply wildcard'.
  inversion H12.
  have: Ta21 = c1 by auto_uniq_full; congruence.
  move=> ?; subst c1.
  by auto_uniq_full.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  subst Ta1 Ta2.

  (* Inversion and glueing *)
  inversion 1.
  have: a0 = a1 /\ b0 = a2 by auto_uniq_full; split; congruence.
  move=> [? ?]; subst a0 b0; clear H4.
  have: a3 = b1 /\ b3 = b2 by auto_uniq_full; split; congruence.
  move=> [? ?]; subst a3 b3; clear H5.

  (* Contra *)
  apply wildcard'.
  inversion H12.
  have: Ta22 = c2 by auto_uniq_full; congruence.
  move=> ?; subst c2.
  by auto_uniq_full.
Defined.
Next Obligation.
  (* FIXME: cleanup' not working *)
  clear dependent filtered_var.
  clear dependent filtered_var2.
  clear dependent filtered_var1.
  clear dependent filtered_var0.
  clear dependent filtered_var4.
  clear dependent filtered_var3. subst. clear dependent fuel.
  clean_fun. clearbodies'.

  autoreg.
  clearget.
  subst.

  apply: An_CAppCong2;
    try econstructor; eassumption.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  hacky.
Defined.


Solve Obligations of AnnDefEq_dec with discr_pat_match.


(* An_CPiSnd *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.

Solve Obligations of AnnDefEq_dec with discr_pat_match.



(* FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME

   Make the pattern-match inversion tactic check whether or not it is applied to a goal it can solve (too slow to run on everything)

   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
   FIXME FIXME FIXME FIXME FIXME
*)

(* An_CastCo *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.


(* An_PiFst *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.

Solve Obligations of AnnDefEq_dec with discr_pat_match.


(* An_PiSnd *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  hacky.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  apply: An_PiSnd;
    subst; eauto.
Defined.
Next Obligation.
  hacky.
Defined.

Solve Obligations of AnnDefEq_dec with discr_pat_match.

Next Obligation.
  hacky.
Defined.


Solve Obligations of AnnDefEq_dec with discr_pat_match.

(* An_IsoSnd *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.


(* FIXME: old cases. Currently, DefEq_dec is done at that point *)
(*
(* g_triv (impossible) *)
Next Obligation.
  (* FIXME: discriminate doesn't work *)
  inversion 1; ok.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup'. autoreg.

  econstructor.
      move: (AnnDefEq_regularity wildcard'6). => [KA [KB [g' [tpgA [tpgB (* deqg' *) _]]]]]
  reg wildcard'6.
  ok.
Defined.
Next Obligation.
  ok.
Defined.
Next Obligation.
  ok.
Defined.
Next Obligation.
  ok.
Defined.
*)

(* An_Eta *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  eapply An_Eta with (L := dom G)(B := B).
  subst. auto.
  intros.
  rewrite -tm_subst_tm_tm_spec.
  simpl. destruct eq_dec; try done.
  rewrite tm_subst_tm_tm_fresh_eq. auto.
  auto.
Defined. 
Next Obligation.
  eapply An_Eta with (L := dom G)(B := B).
  subst. auto.
  intros.
  rewrite -tm_subst_tm_tm_spec.
  simpl. edestruct eq_dec; try done.
  rewrite tm_subst_tm_tm_fresh_eq. auto.
  auto.
Defined.
Next Obligation. 
  eapply An_EtaC with (L := dom G).
  subst. eapply wildcard'.
  intros.
  rewrite -co_subst_co_tm_spec.
  simpl. edestruct eq_dec; try done.
  rewrite co_subst_co_tm_fresh_eq. auto.
  move: (AnnTyping_context_fv wildcard') => h0.
  fsetdec.
Defined. 
Next Obligation.
  cleanup. inversion 1; subst;
  inversion H0; clear H0;
  inversion H4; clear H4.
  destruct rho.
  move: (H5 A0 B0) => h0.
  destruct h0.
  eapply AnnTyping_unique. eauto. eauto.
  move: (H2 A0 B0) => h0.
  destruct h0.
  eapply AnnTyping_unique. eauto. eauto.
  move: (H0 phi) => h0.
  edestruct h0.
  eapply AnnTyping_unique. eauto. eauto.
Defined. 

Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.
Next Obligation.
  unfold wildcard'.
  repeat split; intros; discriminate.
Defined.


 (* cleanup'.
  subst.
  move=> h0.
  inversion h0. subst.
  apply (H0 A0 B0).
  auto_uniq_full.
  apply u0.
  auto. admit. admit. *)

(*

Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.    *)

(*
(* An_Left *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  intro h0; inversion h0. subst.
  eapply wildcard'.
  erewrite <- get_tpg_correct'. eauto.
  auto_uniq_full.
  eauto.
  subst. eapply wildcard'.
  erewrite <- get_tpg_correct'. eauto.
  auto_uniq_full.
  try done.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  intro h0; inversion h0. subst.
  eapply wildcard'.
  erewrite <- get_tpg_correct'. eauto.
  auto_uniq_full.
  try done.
  subst.   eapply wildcard'.
  erewrite <- get_tpg_correct'. eauto.
  auto_uniq_full.
  try done.
Defined.
Next Obligation.
  eapply An_Left2; try eassumption.
 *)

(******** AnnIso_dec ********)

(* An_Cong *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  erewrite <- get_tpg_correct'; eassumption.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  erewrite <- get_tpg_correct'; eassumption.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  eassumption.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  erewrite <- get_tpg_correct'; eassumption.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  erewrite <- get_tpg_correct'; eassumption.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  eauto.
Defined.


(* An_CPiFst *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.

Solve Obligations of AnnIso_dec with discr_pat_match.


(* An_IsoSym *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  eauto.
Defined.


(* An_IsoConv *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  rewrite Heq_phi1 Heq_phi2.
  subst A' B'.
  eapply An_IsoConv'.
   rewrite -Heq_phi1. reflexivity.
   rewrite -Heq_phi2. reflexivity.
  all: try eassumption.
Defined.



(******** AnnPropWff_dec ********)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.


(******** AnnTyping_dec ********)
(* An_Star *)
Next Obligation.
  hacky.
Defined.

(* An_Var *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.


(* An_Pi *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation. (* Fuel: aux *)
  fsetdec.
Defined.
Next Obligation. (* Ctx Wf *)
  cleanup'.
  autoreg.
  subst.
  econstructor; eauto.
Defined.
Next Obligation.
  move /An_Pi_inversion => [_ [_] ].
  have xG: x `notin` dom G by fsetdec.
  move /(_ x xG).
  ok.
Defined.
Next Obligation.
  move /An_Pi_inversion => [? ?].
  cleanup.
  apply: wildcard'.
  auto_uniq_full.
  ok.
Defined.
Next Obligation.
  apply An_Pi_exists2 with (x := x); ok.
Defined.


(* An_Abs *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation. (* Fuel: aux *)
  fsetdec.
Defined.
Next Obligation. (* Ctx Wf *)
  cleanup'.
  autoreg.
  subst.
  econstructor; eauto.
Defined.
Next Obligation.
  cleanup.
  move /An_Abs_inversion => [? [_ [_] ] ].
  have xG: x `notin` dom G by fsetdec.
  move /(_ x xG).
  ok.
Defined.
Next Obligation.
  by move: (wf.AnnTyping_lc1 wildcard').
Defined.
Next Obligation.
  cleanup.
  move /An_Abs_inversion => [? [_ [_] ] ].
  have xG: x `notin` dom G by fsetdec.
  move /(_ x xG) => [h _].
  by apply wildcard'.
Defined.
Next Obligation.
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ wildcard'2) /= [? [? [? ?] ] ].
  eapply An_Abs_exists with (x := x); try done.
  - autorewrite with lngen. fsetdec.
  - by subst.
  - by autorewrite with lngen.
Defined.


(* An_App *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  subst.
  apply: An_App; eassumption.
Defined.
Next Obligation.
  hacky.
Defined.

Solve All Obligations with discr_pat_match.


(* An_Cast *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  hacky.
Defined.
Next Obligation.
  hacky.
  Unshelve.
  all: apply a_Star.
Defined.
Next Obligation.
  cleanup'.
  autoreg.
  clearget.
  subst.
  apply: An_Conv; eassumption.
Defined.


(* An_CApp *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  hacky.
Defined.
Next Obligation.
  subst.
  apply: An_CApp; eassumption.
Defined.
Next Obligation.
  hacky.
Defined.

Solve All Obligations with discr_pat_match.


(* An_Const *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  move: (an_toplevel_to_const wildcard') => AT.
  move: (AnnTyping_lc AT) => [lc1 lc2].
  eapply lc_set_tm_of_lc_tm. eauto.
Defined.
Next Obligation.
  inversion 1.
  (* TODO: uniq should be discharged via typeclasses/CS *)
  move: (binds_unique _ _ _ _ _ H3 wildcard'0 uniq_an_toplevel).
  intro h0. inversion h0. subst.
  move: (binds_to_type _ _ AnnSig_an_toplevel H3) => h1. done.
Defined.
Next Obligation.
  subst.
  apply: An_Const; eauto.
  eapply an_toplevel_to_const; eauto.
Defined.


(* An_CPi *)
Next Obligation.
  hacky.
Defined.
Next Obligation. (* Fuel: aux *)
  fsetdec.
Defined.
Next Obligation.
  cleanup'.
  econstructor; try eassumption.
  fsetdec.
Defined.
Next Obligation.
  move /An_CPi_inversion => [_ [_] ].
  have cG: c `notin` dom G by fsetdec.
  move /(_ c cG).
  ok.
Defined.
Next Obligation.
  move /An_CPi_inversion => [_ [_] ].
  have cG: c `notin` dom G by fsetdec.
  move /(_ c cG) => /= h.
  apply wildcard'.
  auto_uniq_full.
  by move: (u0 _ wildcard'1) => ->.
Defined.
Next Obligation.
  apply An_CPi_exists with (c := c);
  ok.
Defined.


(* An_CAbs *)
Next Obligation.
  hacky.
Defined.
Next Obligation. (* Fuel: aux *)
  fsetdec.
Defined.
Next Obligation.
  cleanup'.
  econstructor; try eassumption.
  fsetdec.
Defined.
Next Obligation.
  move /An_CAbs_inversion => [? [? ] ].
  have cG: c `notin` dom G by fsetdec.
  move /(_ _ cG).
  ok.
Defined.
Next Obligation.
  move: ann_context_fv_mutual => [h'' [_ [_ [_ _] ] ] ]; move: h'' => /(_ _ _ _ wildcard') /= [? [? [? ?] ] ].
  apply An_CAbs_exists with (c := c); try eassumption.
  - autorewrite with lngen. fsetdec.
  - autorewrite with lngen. eassumption.
Defined.


(* An_Fam *)
Next Obligation.
  hacky.
Defined.
Next Obligation.
  clear_annoying.
  subst.
  move: (an_toplevel_closed wildcard') => tpg.
  autoreg. (* TODO: autoreg should do this one too (only use case though...) *)
  move: (AnnTyping_regularity tpg) => kdg.
  econstructor; eassumption.
Defined.

End fc_dec_fun.

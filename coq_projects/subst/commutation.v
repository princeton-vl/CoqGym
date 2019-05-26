(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                              commutation.v                               *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Coq  - Calculus of Inductive Constructions V5.8           *)
(*****************************************************************************)
(*                                                                           *)
(*      Meta-theory of the explicit substitution calculus lambda-env         *)
(*      Amokrane Saibi                                                       *)
(*                                                                           *)
(*      September 1993                                                       *)
(*                                                                           *)
(*****************************************************************************)


                 (*  SL commute avec B|| de la maniere suivante:
      
                                           B||
                                       x ---------> z
                                       |            |
                                    SL |            |SL*
                                       |            | 
                                       V            V
                                       y ----------> u
                                         SL*B||SL*              *)
Require Import sur_les_relations.
Require Import TS.
Require Import egaliteTS.
Require Import sigma_lift.
Require Import betapar.
Require Import SLstar_bpar_SLstar.
Require Import determinePC_SL.

Definition e_diag1 (b : wsort) (x y : TS b) :=
  forall z : TS b,
  e_beta_par _ x z ->
  exists u : TS b, e_slstar_bp_slstar _ y u /\ e_relSLstar _ z u.

Notation diag1 := (e_diag1 _) (only parsing).
(* <Warning> : Syntax is discontinued *)


(* les regles du systeme sigma-lift (SL) verifient le diagramme *)

Goal forall x y : terms, reg_app x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros a b0 s z H0.
pattern z in |- *; apply case_benv with (app a b0) s.
2: assumption.
intros x' s' H1 H2; pattern x' in |- *; apply case_bapp with a b0.
3: assumption.
(* 1-regle B||: app *)
intros a' b0' H3 H4; exists (app (env a' s') (env b0' s')); auto 6.
 (* (a[s])(b0[s]) SL*B||SL* (a'[s'])(b0'[s']) *)
 (* (a'b0')[s'] SL* (a'[s'])(b0'[s']) *)
(* 2-regle B||: beta *)
intros a1 a1' b0' H3 H4 H5; rewrite H3.
exists (env a1' (cons (env b0' s') s')); split.
 (* ((L a1)[s])(b0[s]) SL*B||SL* a1'[b0'[s'].s'] *)
red in |- *; apply comp_2rel with (app (lambda (env a1 (lift s))) (env b0 s)).
   (* ((L a1)[s])(b0[s]) SL* (L (a1[||S]))(b0[s]) *) 
auto 6.
   (* (L (a1[||S]))(b0[s]) B|| (a1'[||s'])[b0'[s'].id] *)
apply comp_2rel with (env (env a1' (lift s')) (cons (env b0' s') id)).
auto.
   (* (a1'[||s'])[b0'[s'].id] SL* a1'[b0'[s'].s'] *)
red in |- *;
 apply star_trans1 with (env a1' (comp (lift s') (cons (env b0' s') id))).
auto.
apply star_trans1 with (env a1' (cons (env b0' s') (comp s' id))); auto 6.
 (* (a1'[b0'id])[s'] SL* a1'[b0'[s'].s'] *)
red in |- *; apply star_trans1 with (env a1' (comp (cons b0' id) s')).
auto.
apply star_trans1 with (env a1' (cons (env b0' s') (comp id s'))); auto 6.
Save commut_app.
Hint Resolve commut_app.

Goal forall x y : terms, reg_lambda x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros a s z H0.
pattern z in |- *; apply case_benv with (lambda a) s.
2: assumption.
intros x' s' H1 H2; pattern x' in |- *; apply case_blambda with a.
2: assumption.
intros a' H3; exists (lambda (env a' (lift s'))); auto 6.
(* L(a[||s]) SL*B||*SL L(a'[||s']) *)
(* (L a0')[s'] SL* L(a0'[||s']) *)
Save commut_lambda.
Hint Resolve commut_lambda.

Goal forall x y : terms, reg_clos x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros a s t z H0.
pattern z in |- *; apply case_benv with (env a s) t.
2: assumption.
intros x' t' H1 H2; pattern x' in |- *; apply case_benv with a s.
2: assumption.
intros a' s' H3 H4; exists (env a' (comp s' t')); auto 6.
(*  a[sot] SL*B||SL* a'[s'ot'] *)
(* (a'[s'])[t'] SL* a'[s'ot'] *)
Save commut_clos.
Hint Resolve commut_clos.

Goal forall x y : terms, reg_varshift1 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros n z H0.
pattern z in |- *; apply case_benv with (var n) shift.
2: assumption.
intros x' s' H1 H2; pattern x' in |- *; apply case_bvar with n.
2: assumption.
pattern s' in |- *; apply case_bshift.
2: assumption.
exists (var (S n)); auto 6.
(* n+1 SL*B||SL* n+1 *)
(* n[|] SL* n+1 *)
Save commut_varshift1.
Hint Resolve commut_varshift1.

Goal forall x y : terms, reg_varshift2 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros n s z H0.
pattern z in |- *; apply case_benv with (var n) (comp shift s).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bvar with n.
2: assumption.
pattern y' in |- *; apply case_bcomp with shift s.
2: assumption.
intros t' s' H3 H4; pattern t' in |- *; apply case_bshift.
2: assumption.
exists (env (var (S n)) s'); auto 6.
(* n+1[s] SL*B||SL* n+1[s'] *)
(* n[|os'] SL* n+1[s'] *)
Save commut_varshift2.
Hint Resolve commut_varshift2.

Goal forall x y : terms, reg_fvarcons x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros a s z H0.
pattern z in |- *; apply case_benv with (var 0) (cons a s).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bvar with 0.
2: assumption.
pattern y' in |- *; apply case_bcons with a s.
2: assumption.
intros a' s' H3 H4; exists a'; auto 6.
(* a SL*B||SL* a' *)
(* 0[a'.s'] SL* a' *)
Save commut_fvarcons.
Hint Resolve commut_fvarcons.

Goal forall x y : terms, reg_fvarlift1 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s z H0.
pattern z in |- *; apply case_benv with (var 0) (lift s).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bvar with 0.
2: assumption.
pattern y' in |- *; apply case_blift with s.
2: assumption.
intros s' H3; exists (var 0); auto 6.
(* 0 SL*B||SL* 0 *)
(* 0[||s'] SL* 0 *)
Save commut_fvarlift1.
Hint Resolve commut_fvarlift1.

Goal forall x y : terms, reg_fvarlift2 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s t z H0.
pattern z in |- *; apply case_benv with (var 0) (comp (lift s) t).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bvar with 0.
2: assumption.
pattern y' in |- *; apply case_bcomp with (lift s) t.
2: assumption.
intros z' t' H3 H4; pattern z' in |- *; apply case_blift with s.
2: assumption.
intros s' H5; exists (env (var 0) t'); auto 6.
(* 0[t] SL*B||SL* 0[t'] *)
(* 0[||s'ot'] SL* 0[t'] *)
Save commut_fvarlift2.
Hint Resolve commut_fvarlift2.

Goal forall x y : terms, reg_rvarcons x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros n a s z H0.
pattern z in |- *; apply case_benv with (var (S n)) (cons a s).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bvar with (S n).
2: assumption.
pattern y' in |- *; apply case_bcons with a s.
2: assumption.
intros a' s' H3 H4; exists (env (var n) s'); auto 6.
(* n[s] SL*B||SL* n[s'] *)
(* n+1[a'.s'] SL* n[s'] *)
Save commut_rvarcons.
Hint Resolve commut_rvarcons.

Goal forall x y : terms, reg_rvarlift1 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros n s z H0.
pattern z in |- *; apply case_benv with (var (S n)) (lift s).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bvar with (S n).
2: assumption.
pattern y' in |- *; apply case_blift with s.
2: assumption.
intros s' H3; exists (env (var n) (comp s' shift)); auto 6.
(* n[so|] SL*B||SL* n[s'o|] *)
(* n+1[||s'] SL* n[s'o|] *)
Save commut_rvarlift1.
Hint Resolve commut_rvarlift1.

Goal forall x y : terms, reg_rvarlift2 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros n s t z H0.
pattern z in |- *; apply case_benv with (var (S n)) (comp (lift s) t).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bvar with (S n).
2: assumption.
pattern y' in |- *; apply case_bcomp with (lift s) t.
2: assumption.
intros z' t' H3 H4; pattern z' in |- *; apply case_blift with s.
2: assumption.
intros s' H5; exists (env (var n) (comp s' (comp shift t'))); auto 6.
(* n[so(|ot)] SL*B||SL* n[s'o(|ot')] *)
(* n+1[||s'ot'] SL* n[s'o(|ot')] *)
Save commut_rvarlift2.
Hint Resolve commut_rvarlift2.

Goal forall x y : sub_explicits, reg_assenv x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s t u z H0.
pattern z in |- *; apply case_bcomp with (comp s t) u.
2: assumption.
intros x' u' H1 H2; pattern x' in |- *; apply case_bcomp with s t.
2: assumption.
intros s' t' H3 H4; exists (comp s' (comp t' u')); auto 6.
(* so(tou) SL*B||SL* s'o(t'ou') *)
(*  (s'ot')ou' SL* s'o(t'ou') *)
Save commut_assenv.
Hint Resolve commut_assenv.

Goal forall x y : sub_explicits, reg_mapenv x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros a s t z H0.
pattern z in |- *; apply case_bcomp with (cons a s) t.
2: assumption.
intros x' t' H1 H2; pattern x' in |- *; apply case_bcons with a s.
2: assumption.
intros a' s' H3 H4; exists (cons (env a' t') (comp s' t')); auto 6.
(* a[t].(sot) SL*B||SL a'[t'].(s'ot') *)
(* (a'.s')ot' SL* a'[t'].(s'ot') *)
Save commut_mapenv.
Hint Resolve commut_mapenv.

Goal forall x y : sub_explicits, reg_shiftcons x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros a s z H0.
pattern z in |- *; apply case_bcomp with shift (cons a s).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bshift.
2: assumption.
pattern y' in |- *; apply case_bcons with a s.
2: assumption.
intros a' s' H3 H4; exists s'; auto 6.
(* s SL*B||SL* s' *)
(* shift o(a'.s') SL* s' *)
Save commut_shiftcons.
Hint Resolve commut_shiftcons.

Goal forall x y : sub_explicits, reg_shiftlift1 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s z H0.
pattern z in |- *; apply case_bcomp with shift (lift s).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bshift.
2: assumption.
pattern y' in |- *; apply case_blift with s.
2: assumption.
intros s' H3; exists (comp s' shift); auto 6.
(* so| SL*B||SL* s'o| *)
(* |o(|| s') SL* s'o| *)
Save commut_shiftlift1.
Hint Resolve commut_shiftlift1.

Goal forall x y : sub_explicits, reg_shiftlift2 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s t z H0.
pattern z in |- *; apply case_bcomp with shift (comp (lift s) t).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_bshift.
2: assumption.
pattern y' in |- *; apply case_bcomp with (lift s) t.
2: assumption.
intros z' t' H3 H4; pattern z' in |- *; apply case_blift with s.
2: assumption.
intros s' H5; exists (comp s' (comp shift t')); auto 6.
(* so(|ot) SL*B||SL* s'o(|ot') *)
(* (|| s')ot' SL* s'o(|ot') *)
Save commut_shiftlift2.
Hint Resolve commut_shiftlift2.

Goal forall x y : sub_explicits, reg_lift1 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s t z H0.
pattern z in |- *; apply case_bcomp with (lift s) (lift t).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_blift with s.
2: assumption.
intros s' H3; pattern y' in |- *; apply case_blift with t.
2: assumption.
intros t' H4; exists (lift (comp s' t')); auto 6.
(* ||(sot) SL*B||SL* ||(s'ot') *)
(* ||s' o ||t' SL* ||(s'ot') *)
Save commut_lift1.
Hint Resolve commut_lift1.

Goal forall x y : sub_explicits, reg_lift2 x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s t u z H0.
pattern z in |- *; apply case_bcomp with (lift s) (comp (lift t) u).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_blift with s.
2: assumption.
intros s' H3; pattern y' in |- *; apply case_bcomp with (lift t) u.
2: assumption.
intros z' u' H4 H5; pattern z' in |- *; apply case_blift with t.
2: assumption.
intros t' H6; exists (comp (lift (comp s' t')) u'); auto 6.
(* ||(sot)ou SL*B||SL* ||(s'ot')ou' *) 
(* ||s'o(||t'ou') SL* ||(s'ot')ou' *) 
Save commut_lift2.
Hint Resolve commut_lift2.

Goal forall x y : sub_explicits, reg_liftenv x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros a s t z H0.
pattern z in |- *; apply case_bcomp with (lift s) (cons a t).
2: assumption.
intros x' y' H1 H2; pattern x' in |- *; apply case_blift with s.
2: assumption.
intros s' H3; pattern y' in |- *; apply case_bcons with a t.
2: assumption.
intros a' t' H4 H5; exists (cons a' (comp s' t')); auto 6.
(* a.(sot) SL*B||SL* a'.(s'ot') *)
(* ||s'o(a'.t') SL* a'.(s'ot') *)
Save commut_liftenv.
Hint Resolve commut_liftenv.

Goal forall x y : sub_explicits, reg_idl x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s z H0.
pattern z in |- *; apply case_bcomp with id s.
2: assumption.
intros x' s' H1 H2; pattern x' in |- *; apply case_bid.
2: assumption.
exists s'; auto 6.
(* s SL*B||SL* s' *)
(* idos' SL* s' *)
Save commut_idl.
Hint Resolve commut_idl.

Goal forall x y : sub_explicits, reg_idr x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros s z H0.
pattern z in |- *; apply case_bcomp with s id.
2: assumption.
intros s' x' H1 H2; pattern x' in |- *; apply case_bid.
2: assumption.
exists s'; auto 6.
(* s SL*B||SL* s' *)
(* s'oid SL* s' *)
Save commut_idr.
Hint Resolve commut_idr.

Goal forall x y : sub_explicits, reg_liftid x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros z H0.
pattern z in |- *; apply case_blift with id.
2: assumption.
intros x' H1; pattern x' in |- *; apply case_bid.
2: assumption.
exists id; auto 6.
(* id SL*B||SL* id *)
(* ||id SL* id *)
Save commut_liftid.
Hint Resolve commut_liftid.

Goal forall x y : terms, reg_id x y -> e_diag1 _ x y.
simple induction 1; red in |- *; intros a z H0.
pattern z in |- *; apply case_benv with a id.
2: assumption.
intros a' x' H1 H2; pattern x' in |- *; apply case_bid.
2: assumption.
exists a'; auto 6.
(* a SLB||SL* a' *)
(* a'[id] SL* a' *)
Save commut_id.
Hint Resolve commut_id.
 
Goal forall (b : wsort) (x y : TS b), e_systemSL _ x y -> e_diag1 _ x y.
simple induction 1; intros; auto.
Save commut_systemSL.

(* lemmes techniques *)

Goal
forall (P : terms -> Prop) (a : terms),
(forall a' : terms, e_relSLstar _ a a' -> P (lambda a')) ->
forall M N : terms, e_relSLstar _ N M -> N = lambda a -> P M.
intros P a H M N H0; generalize a H; elim H0.
intros x a0 H1 H2; rewrite H2; apply (H1 a0); red in |- *; apply star_refl.
intros x y z H1 H2 H3 a0 H4 H5; generalize H1; rewrite H5; intro H6.
cut (y = y).
2: trivial.
pattern y at 2 in |- *; apply case_SLlambda with a0.
2: assumption.
intros a0' H7 H8; apply (H3 a0').
intros a' H9; apply H4; red in |- *; apply star_trans1 with a0'; assumption.
assumption.
Save case_SLstar_lambda'.

Goal
forall (P : terms -> Prop) (a : terms),
(forall a' : terms, e_relSLstar _ a a' -> P (lambda a')) ->
forall M : terms, e_relSLstar _ (lambda a) M -> P M.
intros; pattern M in |- *; apply case_SLstar_lambda' with a (lambda a);
 auto 6.
Save case_SLstar_lambda.

Goal
forall (P : terms -> Prop) (a : terms),
(forall a' : terms, e_slstar_bp_slstar _ a a' -> P (lambda a')) ->
forall M : terms, e_slstar_bp_slstar _ (lambda a) M -> P M.
intros P a H M H0.
elim
 (comp_case terms (e_relSLstar wt)
    (explicit_comp_rel _ (e_beta_par wt) (e_relSLstar wt)) 
    (lambda a) M H0).
intros x H1; elim H1; intros H2.
pattern x in |- *; apply case_SLstar_lambda with a.
2: assumption.
intros a' H3 H4.
elim (comp_case terms (e_beta_par wt) (e_relSLstar wt) (lambda a') M H4).
intros y H5; elim H5; intros H6.
pattern y in |- *; apply case_blambda with a'.
2: assumption.
intros a'' H7 H8.
pattern M in |- *; apply case_SLstar_lambda with a''.
2: assumption.
intros a_ H9; apply H.
red in |- *; apply comp_2rel with a'.
assumption.
apply comp_2rel with a''; assumption.
Save case_slbpsl_lambda.

Goal forall a a' : terms, e_diag1 _ (lambda a) (lambda a') -> e_diag1 _ a a'.
red in |- *; intros a a' H z H0.
elim (H (lambda z)).
2: apply lambda_bpar; assumption.
intros u1 H1; elim H1; intros H2 H3.
cut (u1 = u1).
2: trivial.
pattern u1 at 1 in |- *; apply case_SLstar_lambda with z.
2: assumption.
intros z' H4; pattern u1 in |- *; apply case_slbpsl_lambda with a'.
2: assumption.
intros a'' H5 H6; exists a''; split.
assumption.
elim (proj_lambda z' a'' H6); assumption.
Save diag1_lambda.

Theorem commut :
 forall (b : wsort) (x y : TS b), e_relSL _ x y -> e_diag1 _ x y.
simple induction 1; intros.
(* regles de reecriture *)
apply commut_systemSL; assumption.
(* contexte app droit *)
red in |- *; intros z H2; generalize H0 H1.
pattern z in |- *; apply case_bapp with a b0.
3: assumption.
 (* regle B||: app *)
intros a'' b0'' H3 H4 H5 H6.
elim (H6 a'' H3); intros a_ H7; elim H7; intros H8 H9.
exists (app a_ b0''); auto.
 (* regle B||: beta *)
intros a1 a1'' b0'' H3 H4 H5; rewrite H3.
intro H6; pattern a' in |- *; apply case_SLlambda with a1.
2: assumption.
intros a1' H7 H8.
elim (diag1_lambda a1 a1' H8 a1'' H4); intros a_ H9; elim H9; intros H10 H11.
exists (env a_ (cons b0'' id)); auto.
(* contexte app gauche *)
red in |- *; intros z H2; pattern z in |- *; apply case_bapp with a b0.
3: assumption.
 (* regle B||: app *)
intros a'' b0'' H3 H4.
elim (H1 b0'' H4); intros b0_ H5; elim H5; intros H6 H7.
exists (app a'' b0_); auto.
 (* regle B||: beta *)
intros a1 a1'' b0'' H3 H4 H5; rewrite H3.
elim (H1 b0'' H5); intros b0_ H6; elim H6; intros H7 H8.
exists (env a1'' (cons b0_ id)); auto.
(* contexte lambda *)
red in |- *; intros z H2.
pattern z in |- *; apply case_blambda with a.
2: assumption.
intros a'' H3.
elim (H1 a'' H3); intros a_ H4; elim H4; intros H5 H6.
exists (lambda a_); auto.
(* contexte env droit *)
red in |- *; intros z H2.
pattern z in |- *; apply case_benv with a s.
2: assumption.
intros a'' s'' H3 H4.
elim (H1 a'' H3); intros a_ H5; elim H5; intros H6 H7.
exists (env a_ s''); auto.
(* contexte env gauche *)
red in |- *; intros z H2.
pattern z in |- *; apply case_benv with a s.
2: assumption.
intros a'' s'' H3 H4.
elim (H1 s'' H4); intros s_ H5; elim H5; intros H6 H7.
exists (env a'' s_); auto.
(* contexte cons droit *)
red in |- *; intros z H2.
pattern z in |- *; apply case_bcons with a s.
2: assumption.
intros a'' s'' H3 H4.
elim (H1 a'' H3); intros a_ H5; elim H5; intros H6 H7.
exists (cons a_ s''); auto.
(* contexte cons gauche *)
red in |- *; intros z H2.
pattern z in |- *; apply case_bcons with a s.
2: assumption.
intros a'' s'' H3 H4.
elim (H1 s'' H4); intros s_ H5; elim H5; intros H6 H7.
exists (cons a'' s_); auto.
(* contexte comp droit *)
red in |- *; intros z H2.
pattern z in |- *; apply case_bcomp with s t.
2: assumption.
intros s'' t'' H3 H4.
elim (H1 s'' H3); intros s_ H5; elim H5; intros H6 H7.
exists (comp s_ t''); auto.
(* contexte comp gauche *)
red in |- *; intros z H2.
pattern z in |- *; apply case_bcomp with s t.
2: assumption.
intros s'' t'' H3 H4.
elim (H1 t'' H4); intros t_ H5; elim H5; intros H6 H7.
exists (comp s'' t_); auto.
(* contexte lift *)
red in |- *; intros z H2.
pattern z in |- *; apply case_blift with s.
2: assumption.
intros s'' H3.
elim (H1 s'' H3); intros s_ H4; elim H4; intros H5 H6.
exists (lift s_); auto.
Qed.


(***************************************************)
(*    SL verifie le diagramme ci-dessus            *)
(***************************************************)

Theorem commutation :
 forall (b : wsort) (x y z : TS b),
 e_relSL _ x y ->
 e_beta_par _ x z ->
 exists u : TS b, e_relSLstar _ z u /\ e_slstar_bp_slstar _ y u.
intros b x y z H H0; apply Ex_PQ; generalize z H0.
change (e_diag1 _ x y) in |- *.
apply commut; assumption.
Qed.


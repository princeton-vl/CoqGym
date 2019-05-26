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
(*                             determinePC_SL.v                             *)
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

 
    (* confluence locale de sigma-lift: determination des paires critiques *)


  (* L'idee est:
     partant d'un terme-substitution X, trouver tous ses "reduits" possibles
     par la relation sigma-lift (SL), c.a.d. tous les Y tq: X--SL-->Y.
     on prendra notamment pour X tous les membres gauches des regles de
     sigma-lift, ceci nous indique les paires critiques (PC) a resoudre     *)

Require Import TS.
Require Import sur_les_relations.
Require Import egaliteTS.
Require Import sigma_lift.
Require Import inversionSL.

(*** (var n) SL ? ***)

Goal forall (n : nat) (M : terms), ~ e_relSL _ (var n) M.
red in |- *; intros n M H; cut (e_invSL _ (var n) M).
2: auto.
simple induction 1.
Save case_SLvar.

(*** (app a b) SL ? ***)

Goal
forall (P : terms -> Prop) (a b : terms),
(forall a' : terms, e_relSL _ a a' -> P (app a' b)) ->
(forall b' : terms, e_relSL _ b b' -> P (app a b')) ->
forall M : terms, e_relSL _ (app a b) M -> P M.
intros P a b H H0 M H1; cut (e_invSL _ (app a b) M).
2: auto.
pattern M in |- *; apply terms_ind.
(* var *)
simple induction 1.
(* app *)
simple induction 3; simple induction 1; intros.
elim H7; apply H; assumption.
elim H6; apply H0; assumption.
(* lam *)
simple induction 2.
(* env *)
simple induction 2.
(* X *)
simple induction 1.
Save case_SLapp.

(*** (lambda a) SL ? ***)

Goal
forall (P : terms -> Prop) (a : terms),
(forall a' : terms, e_relSL _ a a' -> P (lambda a')) ->
forall M : terms, e_relSL _ (lambda a) M -> P M.
intros P a H M H0; cut (e_invSL _ (lambda a) M).
2: auto.
pattern M in |- *; apply terms_ind.
(* var *)
simple induction 1.
(* app *)
simple induction 3.
(* lambda *)
unfold e_invSL at 2 in |- *; intros; apply H; assumption.
(* env *)
simple induction 2.
(* X *)
simple induction 1.
Save case_SLlambda.

(*** (env a s) SL ? ***)

Goal
forall (P : terms -> sub_explicits -> terms -> Prop) 
  (a : terms) (s : sub_explicits),
(forall a1 b1 : terms, P (app a1 b1) s (app (env a1 s) (env b1 s))) ->
(forall a1 : terms, P (lambda a1) s (lambda (env a1 (lift s)))) ->
(forall (a1 : terms) (s1 : sub_explicits),
 P (env a1 s1) s (env a1 (comp s1 s))) ->
(forall n : nat, P (var n) shift (var (S n))) ->
(forall (n : nat) (s1 : sub_explicits),
 P (var n) (comp shift s1) (env (var (S n)) s1)) ->
(forall (a1 : terms) (s1 : sub_explicits), P (var 0) (cons a1 s1) a1) ->
(forall s1 : sub_explicits, P (var 0) (lift s1) (var 0)) ->
(forall s1 s2 : sub_explicits, P (var 0) (comp (lift s1) s2) (env (var 0) s2)) ->
(forall (n : nat) (a1 : terms) (s1 : sub_explicits),
 P (var (S n)) (cons a1 s1) (env (var n) s1)) ->
(forall (n : nat) (s1 : sub_explicits),
 P (var (S n)) (lift s1) (env (var n) (comp s1 shift))) ->
(forall (n : nat) (s1 s2 : sub_explicits),
 P (var (S n)) (comp (lift s1) s2) (env (var n) (comp s1 (comp shift s2)))) ->
P a id a ->
(forall a' : terms, e_relSL _ a a' -> P a s (env a' s)) ->
(forall s' : sub_explicits, e_relSL _ s s' -> P a s (env a s')) ->
forall M : terms, e_relSL _ (env a s) M -> P a s M.
intros P a s; intros; cut (e_invSL _ (env a s) M).
2: auto.
pattern M in |- *; apply terms_ind.
(* var *)
simple induction 1.
 (* varshift1 *)
do 2 simple induction 1; simple induction 2; intros.
rewrite H20; rewrite H19; rewrite H17; apply H2.
 (* fvarlift1 *)
simple induction 1.
do 2 simple induction 1; simple induction 2; intros.
rewrite H21; rewrite H20; rewrite H18; apply H5.
 (* fvarcons *)
simple induction 1.
do 2 simple induction 1; intros.
rewrite H20; rewrite H19; apply H4.
 (* id *)
simple induction 1; intros.
elim H18; rewrite H19; apply H10.
(* app *)
 (* app *)
simple induction 3.
do 3 simple induction 1; simple induction 2; intros.
rewrite H23; rewrite H22; rewrite H20; apply H.
 (* fvarcons *)
simple induction 1.
do 2 simple induction 1; intros.
rewrite H21; rewrite H20; apply H4.
 (* id *)
simple induction 1; intros.
rewrite H20; elim H19; apply H10.
(* lam *)
 (* lambda *)
simple induction 2.
do 2 simple induction 1; intros.
rewrite H19; rewrite H18; apply H0.
 (* fvarcons *)
simple induction 1.
do 2 simple induction 1; intros.
rewrite H20; rewrite H19; apply H4.
 (* id *)
simple induction 1; intros.
rewrite H19; elim H18; apply H10.
(* env *)
 (* clos *)
simple induction 2.
do 2 simple induction 1; intros.
rewrite H19; rewrite H18; apply H1.
 (* varshift2 *)
simple induction 1.
do 2 simple induction 1; simple induction 2; intros.
rewrite H22; rewrite H21; rewrite H19; apply H3.
 (* fvarcons *) 
simple induction 1.
do 2 simple induction 1; intros.
rewrite H21; rewrite H20; apply H4.
 (* favrlift2 *)
simple induction 1.
do 2 simple induction 1; simple induction 2; intros.
rewrite H24; rewrite H23; rewrite H21; apply H6.
 (* rvarcons *)
simple induction 1.
do 3 simple induction 1; simple induction 2; intros.
rewrite H26; rewrite H25; rewrite H23; apply H7.
 (* rvarlift1 *)
simple induction 1.
do 3 simple induction 1; do 2 simple induction 2; intros.
rewrite H29; rewrite H28; rewrite H26; rewrite H24; apply H8.
 (* rvarlift2 *)
simple induction 1.
do 4 simple induction 1; do 2 simple induction 2; intros.
rewrite H31; rewrite H30; rewrite H28; rewrite H26; apply H9.
 (* id *)
simple induction 1.
simple induction 1; intros.
rewrite H25; elim H24; apply H10.
 (* contexte droit *)
simple induction 1.
simple induction 1; intros.
elim H26; apply H11; assumption.
 (* contexte gauche *)
simple induction 1.
simple induction 1; intros.
elim H25; apply H12; assumption.
(* X *)
simple induction 1.
 (* fvarcons *)
do 2 simple induction 1; intros.
rewrite H18; rewrite H17; apply H4.
 (* id *)
simple induction 1; intros.
elim H16; rewrite H17; assumption.
Save case_SLenv.

(*** id SL ? ***)

Goal forall M : sub_explicits, ~ e_relSL _ id M.
red in |- *; intros M H; cut (e_invSL _ id M).
2: auto.
simple induction 1.
Save case_SLid.

(*** shift SL ? ***)

Goal forall M : sub_explicits, ~ e_relSL _ shift M.
red in |- *; intros M H; cut (e_invSL _ shift M).
2: auto.
simple induction 1.
Save case_SLshift.

(*** (cons a s) SL ? ***)

Goal
forall (P : sub_explicits -> Prop) (a : terms) (s : sub_explicits),
(forall a' : terms, e_relSL _ a a' -> P (cons a' s)) ->
(forall s' : sub_explicits, e_relSL _ s s' -> P (cons a s')) ->
forall M : sub_explicits, e_relSL _ (cons a s) M -> P M.
intros P a s H H0 M H1; cut (e_invSL _ (cons a s) M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id *)
simple induction 1.
(* | *)
simple induction 1.
(* . *)
simple induction 2; simple induction 1; intros.
elim H6; apply H; assumption.
elim H5; apply H0; assumption.
(* o *)
simple induction 3.
(* || *)
simple induction 2.
(* x *)
simple induction 1.
Save case_SLcons.

(*** (comp s t) SL ? ***)

Goal
forall (P : sub_explicits -> sub_explicits -> sub_explicits -> Prop)
  (s t : sub_explicits),
(forall s1 s2 : sub_explicits, P (comp s1 s2) t (comp s1 (comp s2 t))) ->
(forall (a : terms) (s1 : sub_explicits),
 P (cons a s1) t (cons (env a t) (comp s1 t))) ->
(forall (a : terms) (t1 : sub_explicits), P shift (cons a t1) t1) ->
(forall t1 : sub_explicits, P shift (lift t1) (comp t1 shift)) ->
(forall t1 t2 : sub_explicits,
 P shift (comp (lift t1) t2) (comp t1 (comp shift t2))) ->
(forall s1 t1 : sub_explicits, P (lift s1) (lift t1) (lift (comp s1 t1))) ->
(forall s1 t1 t2 : sub_explicits,
 P (lift s1) (comp (lift t1) t2) (comp (lift (comp s1 t1)) t2)) ->
(forall (a : terms) (s1 t1 : sub_explicits),
 P (lift s1) (cons a t1) (cons a (comp s1 t1))) ->
P id t t ->
P s id s ->
(forall s' : sub_explicits, e_relSL _ s s' -> P s t (comp s' t)) ->
(forall t' : sub_explicits, e_relSL _ t t' -> P s t (comp s t')) ->
forall M : sub_explicits, e_relSL _ (comp s t) M -> P s t M.
intros P s t; intros; cut (e_invSL _ (comp s t) M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id *)
 (* shiftcons *)
simple induction 1.
do 2 simple induction 1; intros.
rewrite H15; rewrite H16; apply H1.
 (* idr, idl *)
simple induction 1; intros.
rewrite H14; pattern id at 2 in |- *; elim H15; apply H7.
(* | *)
simple induction 1.
do 2 simple induction 1; intros.
rewrite H15; rewrite H16; apply H1.
 (* idl *)
simple induction 1.
simple induction 1; intros.
rewrite H15; elim H16; apply H7.
 (* idr *)
simple induction 1; intros.
rewrite H16; elim H15; apply H8.
(* cons *)
 (* mapenv *)
simple induction 2.
do 3 simple induction 1; simple induction 2; intros.
rewrite H17; rewrite H20; rewrite H19; apply H0.
 (* shiftcons *)
simple induction 1.
do 2 simple induction 1; intros.
rewrite H17; rewrite H18; apply H1.
 (* liftenv *)
simple induction 1.
do 3 simple induction 1; simple induction 2; intros.
rewrite H22; rewrite H21; rewrite H19; apply H6.
 (* idl *)
simple induction 1.
simple induction 1; intros.
rewrite H18; elim H19; apply H7.
 (* idr *)
simple induction 1; intros.
rewrite H19; elim H18; apply H8.
(* comp *)
simple induction 3.
 (* assenv *)
do 2 simple induction 1; intros.
rewrite H18; rewrite H17; apply H.
 (* shiftcons *)
simple induction 1.
do 2 simple induction 1; intros.
rewrite H18; rewrite H19; apply H1.
 (* shiftlift1 *)
simple induction 1.
simple induction 1; simple induction 2; intros.
rewrite H21; rewrite H20; rewrite H18; apply H2.
 (* shiftlift2 *)
simple induction 1.
do 2 simple induction 1; simple induction 2; intros.
rewrite H23; rewrite H22; rewrite H20; apply H3.
 (* lift2 *)
simple induction 1.
do 3 simple induction 1; simple induction 2; intros.
rewrite H25; rewrite H24; rewrite H22; apply H5.
 (* idl *)
simple induction 1.
simple induction 1; intros.
rewrite H21; elim H22; apply H7.
 (* idr *)
simple induction 1.
simple induction 1; intros.
rewrite H23; elim H22; apply H8.
 (* contexte gauche *)
simple induction 1.
simple induction 1; intros.
elim H24; apply H9; assumption.
 (* contexte droit *)
simple induction 1; intros.
elim H23; apply H10; assumption.
(* lift *)
simple induction 2.
 (* shiftcons *)
do 2 simple induction 1; intros.
rewrite H17; rewrite H16; apply H1.
 (* lift1 *)
simple induction 1.
do 3 simple induction 1; simple induction 2; intros.
rewrite H21; rewrite H20; rewrite H18; apply H4.
 (* idl *)
simple induction 1.
simple induction 1; intros.
rewrite H17; elim H18; apply H7.
 (* idr *)
simple induction 1; intros.
rewrite H18; elim H17; apply H8.
(* x *)
simple induction 1.
do 2 simple induction 1; intros.
rewrite H15; rewrite H16; apply H1.
 (* idl *)
simple induction 1.
simple induction 1; intros.
rewrite H15; elim H16; apply H7.
 (* idr *)
simple induction 1; intros.
rewrite H16; elim H15; apply H8.
Save case_SLcomp.

(*** (lift s) SL ? ***)

Goal
forall (P : sub_explicits -> sub_explicits -> Prop) (s : sub_explicits),
P id id ->
(forall s' : sub_explicits, e_relSL _ s s' -> P s (lift s')) ->
forall M : sub_explicits, e_relSL _ (lift s) M -> P s M.
intros P s H H0 M H1; cut (e_invSL _ (lift s) M).
2: auto.
pattern M in |- *; apply sub_explicits_ind.
(* id *)
simpl in |- *; intro H2; rewrite H2; assumption.
(* | *)
simple induction 1.
(* . *)
simple induction 2.
(* o *)
simple induction 3.
(* || *)
unfold e_invSL at 2 in |- *; intros; apply H0; assumption.
(* x *)
simple induction 1.
Save case_SLlift.

(*** (env (lambda a) s) SL ? ***)

Goal
forall (P : sub_explicits -> terms -> Prop) (a : terms) (s : sub_explicits),
P s (lambda (env a (lift s))) ->
P id (lambda a) ->
(forall x' : terms, e_relSL _ (lambda a) x' -> P s (env x' s)) ->
(forall s' : sub_explicits, e_relSL _ s s' -> P s (env (lambda a) s')) ->
forall M : terms, e_relSL _ (env (lambda a) s) M -> P s M.
intros.
cut (lambda a = lambda a).
2: auto.
pattern (lambda a) at 1, s, M in |- *; apply case_SLenv; intros.
15: assumption.
(* app *)elim (diff_app_lambda a1 b1 a H4).
(* lambda *)
rewrite (proj_lambda a1 a H4); assumption.
(* clos *)elim (diff_lambda_env a a1 s1 (sym_equal H4)).
(* varshift1 *)elim (diff_var_lambda n a H4).
(* varshift2 *)elim (diff_var_lambda n a H4).
(* fvarcons *)elim (diff_var_lambda 0 a H4).
(* fvarlift1 *)elim (diff_var_lambda 0 a H4).
(* fvarlift2 *)elim (diff_var_lambda 0 a H4).
(* rvarcons *)elim (diff_var_lambda (S n) a H4).
(* rvarlift1 *)elim (diff_var_lambda (S n) a H4).
(* rvarlift2 *)elim (diff_var_lambda (S n) a H4).
(* id *)
assumption.
(* contexte gauche*)
apply H1; assumption.
(* contexte droit *)
apply H2; assumption.
Save case_SL_reg_lambda.

(*** (env (app a b) s) SL ? ***)

Goal
forall (P : sub_explicits -> terms -> Prop) (a b : terms) (s : sub_explicits),
P s (app (env a s) (env b s)) ->
P id (app a b) ->
(forall x' : terms, e_relSL _ (app a b) x' -> P s (env x' s)) ->
(forall s' : sub_explicits, e_relSL _ s s' -> P s (env (app a b) s')) ->
forall M : terms, e_relSL _ (env (app a b) s) M -> P s M.
intros.
cut (app a b = app a b).
2: auto.
pattern (app a b) at 1, s, M in |- *; apply case_SLenv; intros.
15: assumption.
(* app *)
rewrite (proj_app1 a1 b1 a b H4); rewrite (proj_app2 a1 b1 a b H4);
 assumption.
(* lambda *)elim (diff_app_lambda a b a1 (sym_equal H4)).
(* clos *)elim (diff_app_env a b a1 s1 (sym_equal H4)).
(* varshift1 *)elim (diff_var_app n a b H4).
(* varshift2 *)elim (diff_var_app n a b H4).
(* fvarcons *)elim (diff_var_app 0 a b H4).
(* fvarlift1 *)elim (diff_var_app 0 a b H4).
(* fvarlift2 *)elim (diff_var_app 0 a b H4).
(* rvarcons *)elim (diff_var_app (S n) a b H4).
(* rvarlift1 *)elim (diff_var_app (S n) a b H4).
(* rvarlift2 *)elim (diff_var_app (S n) a b H4).
(* id *)
assumption.
(* contexte gauche*)
apply H1; assumption.
(* contexte droit *)
apply H2; assumption.
Save case_SL_reg_app.

(*** (env (env a s) t) SL ? ***)

Goal
forall (P : sub_explicits -> terms -> Prop) (a : terms) (s t : sub_explicits),
P t (env a (comp s t)) ->
P id (env a s) ->
(forall x' : terms, e_relSL _ (env a s) x' -> P t (env x' t)) ->
(forall t' : sub_explicits, e_relSL _ t t' -> P t (env (env a s) t')) ->
forall M : terms, e_relSL _ (env (env a s) t) M -> P t M.
intros.
cut (env a s = env a s).
2: auto.
pattern (env a s) at 1, t, M in |- *; apply case_SLenv; intros.
15: assumption.
(* app *)elim (diff_app_env a1 b1 a s H4).
(* lambda *)elim (diff_lambda_env a1 a s H4).
(* clos *)
rewrite (proj_env1 a1 a s1 s H4); rewrite (proj_env2 a1 a s1 s H4).
assumption.
(* varshift1 *)elim (diff_var_env n a s H4).
(* varshift2 *)elim (diff_var_env n a s H4).
(* fvarcons *)elim (diff_var_env 0 a s H4).
(* fvarlift1 *)elim (diff_var_env 0 a s H4).
(* fvarlift2 *)elim (diff_var_env 0 a s H4).
(* rvarcons *)elim (diff_var_env (S n) a s H4).
(* rvarlift1 *)elim (diff_var_env (S n) a s H4).
(* rvarlift2 *)elim (diff_var_env (S n) a s H4).
(* id *)
assumption.
(* contexte gauche*)
apply H1; assumption.
(* contexte droit *)
apply H2; assumption.
Save case_SL_clos.

(*** (env (var n) shift) SL ? ***)

Goal
forall (P : terms -> Prop) (n : nat),
P (var (S n)) -> forall M : terms, e_relSL _ (env (var n) shift) M -> P M.
intros.
cut (var n = var n).
2: auto.
cut (shift = shift).
2: auto.
pattern (var n) at 1, shift at 1, M in |- *; apply case_SLenv; intros.
15: assumption.
(* app *)elim (diff_var_app n a1 b1 (sym_equal H2)).
(* lambda *)elim (diff_var_lambda n a1 (sym_equal H2)).
(* clos *)elim (diff_var_env n a1 s1 (sym_equal H2)).
(* varshift1 *)
rewrite (proj_var n0 n H2); assumption.
(* varshift2 *)elim (diff_shift_comp shift s1 (sym_equal H1)).
(* fvarcons *)elim (diff_shift_cons a1 s1 (sym_equal H1)).
(* fvarlift1 *)elim (diff_shift_lift s1 (sym_equal H1)).
(* fvarlift2 *)elim (diff_shift_comp (lift s1) s2 (sym_equal H1)).
(* rvarcons *)elim (diff_shift_cons a1 s1 (sym_equal H1)).
(* rvarlift1 *)elim (diff_shift_lift s1 (sym_equal H1)).
(* rvarlift2 *)elim (diff_shift_comp (lift s1) s2 (sym_equal H1)).
(* id *)elim (diff_id_shift H1).
(* contexte gauche*)elim (case_SLvar n a' H1).
(* contexte droit *)elim (case_SLshift s' H1).
Save case_SL_varshift1.

(*** (comp shift s) SL ? ***)

Goal
forall (P : sub_explicits -> sub_explicits -> Prop) (s : sub_explicits),
(forall (a : terms) (s1 : sub_explicits), P (cons a s1) s1) ->
(forall s1 : sub_explicits, P (lift s1) (comp s1 shift)) ->
(forall s1 t : sub_explicits, P (comp (lift s1) t) (comp s1 (comp shift t))) ->
P id shift ->
(forall s' : sub_explicits, e_relSL _ s s' -> P s (comp shift s')) ->
forall M : sub_explicits, e_relSL _ (comp shift s) M -> P s M.
intros.
cut (shift = shift).
2: auto.
pattern shift at 1, s, M in |- *; apply case_SLcomp; intros.
13: assumption.
(* assenv *)elim (diff_shift_comp s1 s2 (sym_equal H5)).
(* mapenv *)elim (diff_shift_cons a s1 (sym_equal H5)).
(* shiftcons *)
apply H.
(* shiftlift1 *)
apply H0.
(* shiftlift2 *)
apply H1.
(* lift1 *)elim (diff_shift_lift s1 (sym_equal H5)).
(* lift2 *)elim (diff_shift_lift s1 (sym_equal H5)).
(* liftenv *)elim (diff_shift_lift s1 (sym_equal H5)).
(* idl *)elim (diff_id_shift H5).
(* idr *)
assumption.
(* contexte gauche *)elim (case_SLshift s' H5).
(* contexte droit *)
apply H3; assumption.
Save case_SLcomp1.

(*** (env (var n) (comp shift s)) SL ? ***)

Goal
forall (P : terms -> Prop) (n : nat) (s : sub_explicits),
P (env (var (S n)) s) ->
(forall x' : sub_explicits, e_relSL _ (comp shift s) x' -> P (env (var n) x')) ->
forall M : terms, e_relSL _ (env (var n) (comp shift s)) M -> P M.
intros.
cut (var n = var n).
2: auto.
cut (comp shift s = comp shift s).
2: auto.
pattern (var n) at 1, (comp shift s) at 1, M in |- *; apply case_SLenv;
 intros.
15: assumption.
(* app *)elim (diff_var_app n a1 b1 (sym_equal H3)).
(* lambda *)elim (diff_var_lambda n a1 (sym_equal H3)).
(* clos *)elim (diff_var_env n a1 s1 (sym_equal H3)).
(* varshift1 *)elim (diff_shift_comp shift s H2).
(* varshift2 *)
rewrite (proj_var n0 n H3); rewrite (proj_comp2 shift shift s1 s H2);
 assumption.
(* fvarcons *)elim (diff_cons_comp a1 s1 shift s H2).
(* fvarlift1 *)elim (diff_comp_lift shift s s1 (sym_equal H2)).
(* fvarlift2 *)elim
                (diff_shift_lift s1
                   (sym_equal (proj_comp1 (lift s1) shift s2 s H2))).
(* rvarcons *)elim (diff_cons_comp a1 s1 shift s H2).
(* rvarlift1 *)elim (diff_comp_lift shift s s1 (sym_equal H2)).
(* rvarlift2 *)elim
                (diff_shift_lift s1
                   (sym_equal (proj_comp1 (lift s1) shift s2 s H2))).
(* id *)elim (diff_id_comp shift s H2).
(* contexte gauche*)elim (case_SLvar n a' H2).
(* contexte droit *)apply H0; assumption.
Save case_SL_varshift2.

(*** (env (var O) (cons a s)) SL ? ***)

Goal
forall (P : terms -> Prop) (a : terms) (s : sub_explicits),
P a ->
(forall x' : sub_explicits, e_relSL _ (cons a s) x' -> P (env (var 0) x')) ->
forall M : terms, e_relSL _ (env (var 0) (cons a s)) M -> P M.
intros.
cut (var 0 = var 0).
2: auto.
cut (cons a s = cons a s).
2: auto.
pattern (var 0) at 1, (cons a s) at 1, M in |- *; apply case_SLenv; intros.
15: assumption.
(* app *)elim (diff_var_app 0 a1 b1 (sym_equal H3)).
(* lambda *)elim (diff_var_lambda 0 a1 (sym_equal H3)).
(* clos *)elim (diff_var_env 0 a1 s1 (sym_equal H3)).
(* varshift1 *)elim (diff_shift_cons a s H2).
(* varshift2 *)elim (diff_cons_comp a s shift s1 (sym_equal H2)).
(* fvarcons *)rewrite (proj_cons1 a1 a s1 s H2); assumption.
(* fvarlift1 *)elim (diff_cons_lift a s s1 (sym_equal H2)).
(* fvarlift2 *)elim (diff_cons_comp a s (lift s1) s2 (sym_equal H2)).
(* rvarcons *)elim (O_S n (sym_equal (proj_var (S n) 0 H3))).
(* rvarlift1 *)elim (diff_cons_lift a s s1 (sym_equal H2)).
(* rvarlift2 *)elim (O_S n (sym_equal (proj_var (S n) 0 H3))).
(* id *)elim (diff_id_cons a s H2).
(* contexte gauche*)elim (case_SLvar 0 a' H2).
(* contexte droit *)apply H0; assumption.
Save case_SL_fvarcons.

(*** (env (var O) (lift s)) SL ? ***)

Goal
forall (P : terms -> Prop) (s : sub_explicits),
P (var 0) ->
(forall x' : sub_explicits, e_relSL _ (lift s) x' -> P (env (var 0) x')) ->
forall M : terms, e_relSL _ (env (var 0) (lift s)) M -> P M.
intros.
cut (var 0 = var 0).
2: auto.
cut (lift s = lift s).
2: auto.
pattern (var 0) at 1, (lift s) at 1, M in |- *; apply case_SLenv; intros.
15: assumption.
(* app *)elim (diff_var_app 0 a1 b1 (sym_equal H3)).
(* lambda *)elim (diff_var_lambda 0 a1 (sym_equal H3)).
(* clos *)elim (diff_var_env 0 a1 s1 (sym_equal H3)).
(* varshift1 *)elim (diff_shift_lift s H2).
(* varshift2 *)elim (diff_comp_lift shift s1 s H2).
(* fvarcons *)elim (diff_cons_lift a1 s1 s H2).
(* fvarlift1 *)assumption.
(* fvarlift2 *)elim (diff_comp_lift (lift s1) s2 s H2).
(* rvarcons *)elim (diff_cons_lift a1 s1 s H2).
(* rvarlift1 *)elim (O_S n (sym_equal (proj_var (S n) 0 H3))).
(* rvarlift2 *)elim (diff_comp_lift (lift s1) s2 s H2).
(* id *)elim (diff_id_lift s H2).
(* contexte gauche*)elim (case_SLvar 0 a' H2).
(* contexte droit *)apply H0; assumption.
Save case_SL_fvarlift1.

(*** (comp (lift s) t) SL ? ***)

Goal
forall (P : sub_explicits -> sub_explicits -> Prop) (s t : sub_explicits),
(forall t1 : sub_explicits, P (lift t1) (lift (comp s t1))) ->
(forall t1 t2 : sub_explicits,
 P (comp (lift t1) t2) (comp (lift (comp s t1)) t2)) ->
(forall (a : terms) (t1 : sub_explicits), P (cons a t1) (cons a (comp s t1))) ->
P id (lift s) ->
(forall x' : sub_explicits, e_relSL _ (lift s) x' -> P t (comp x' t)) ->
(forall t' : sub_explicits, e_relSL _ t t' -> P t (comp (lift s) t')) ->
forall M : sub_explicits, e_relSL _ (comp (lift s) t) M -> P t M.
intros.
cut (lift s = lift s).
2: auto.
pattern (lift s) at 1, t, M in |- *; apply case_SLcomp; intros.
13: assumption.
(* assenv *)elim (diff_comp_lift s1 s2 s H6).
(* mapenv *)elim (diff_cons_lift a s1 s H6).
(* shiftcons *)elim (diff_shift_lift s H6).
(* shiftlift1 *)elim (diff_shift_lift s H6).
(* shiftlift2 *)elim (diff_shift_lift s H6).
(* lift1 *)
rewrite (proj_lift s1 s H6); apply H.
(* lift2 *)
rewrite (proj_lift s1 s H6); apply H0.
(* liftenv *)
rewrite (proj_lift s1 s H6); apply H1.
(* idl *)elim (diff_id_lift s H6).
(* idr *)
assumption.
(* contexte gauche *)
apply H3; assumption.
(* contexte droit *)
apply H4; assumption.
Save case_SLcomp2.

(*** (env (var O) (comp (lift s) t)) SL ? ***)

Goal
forall (P : terms -> Prop) (s t : sub_explicits),
P (env (var 0) t) ->
(forall x' : sub_explicits,
 e_relSL _ (comp (lift s) t) x' -> P (env (var 0) x')) ->
forall M : terms, e_relSL _ (env (var 0) (comp (lift s) t)) M -> P M.
intros.
cut (var 0 = var 0).
2: auto.
cut (comp (lift s) t = comp (lift s) t).
2: auto.
pattern (var 0) at 1, (comp (lift s) t) at 1, M in |- *; apply case_SLenv;
 intros.
15: assumption.
(* app *)elim (diff_var_app 0 a1 b1 (sym_equal H3)).
(* lambda *)elim (diff_var_lambda 0 a1 (sym_equal H3)).
(* clos *)elim (diff_var_env 0 a1 s1 (sym_equal H3)).
(* varshift1 *)elim (diff_shift_comp (lift s) t H2).
(* varshift2 *)elim (diff_shift_lift s (proj_comp1 shift (lift s) s1 t H2)).
(* fvarcons *)elim (diff_cons_comp a1 s1 (lift s) t H2).
(* fvarlift1 *)elim (diff_comp_lift (lift s) t s1 (sym_equal H2)).
(* fvarlift2 *)
rewrite (proj_comp2 (lift s1) (lift s) s2 t H2); assumption.
(* rvarcons *)elim (diff_cons_comp a1 s1 (lift s) t H2).
(* rvarlift1 *)elim (diff_comp_lift (lift s) t s1 (sym_equal H2)).
(* rvarlift2 *)elim (O_S n (sym_equal (proj_var (S n) 0 H3))).
(* id *)elim (diff_id_comp (lift s) t H2).
(* contexte gauche*)elim (case_SLvar 0 a' H2).
(* contexte droit *)apply H0; assumption.
Save case_SL_fvarlift2.

(*** (env (var (S n)) (cons a s)) SL ? ***)

Goal
forall (P : terms -> Prop) (n : nat) (a : terms) (s : sub_explicits),
P (env (var n) s) ->
(forall x' : sub_explicits, e_relSL _ (cons a s) x' -> P (env (var (S n)) x')) ->
forall M : terms, e_relSL _ (env (var (S n)) (cons a s)) M -> P M.
intros P n a s H H0 M H1.
cut (var (S n) = var (S n)).
2: auto.
cut (cons a s = cons a s).
2: auto.
pattern (var (S n)) at 1, (cons a s) at 1, M in |- *; apply case_SLenv;
 intros.
15: assumption.
(* app *)elim (diff_var_app (S n) a1 b1 (sym_equal H3)).
(* lambda *)elim (diff_var_lambda (S n) a1 (sym_equal H3)).
(* clos *)elim (diff_var_env (S n) a1 s1 (sym_equal H3)).
(* varshift1 *)elim (diff_shift_cons a s H2).
(* varshift2 *)elim (diff_cons_comp a s shift s1 (sym_equal H2)).
(* fvarcons *)elim (O_S n (proj_var 0 (S n) H3)).
(* fvarlift1 *)elim (diff_cons_lift a s s1 (sym_equal H2)).
(* fvarlift2 *)elim (diff_cons_comp a s (lift s1) s2 (sym_equal H2)).
(* rvarcons *)
rewrite (eq_add_S n0 n (proj_var (S n0) (S n) H3)).
rewrite (proj_cons2 a1 a s1 s H2); assumption.
(* rvarlift1 *)elim (diff_cons_lift a s s1 (sym_equal H2)).
(* rvarlift2 *)elim (diff_cons_comp a s (lift s1) s2 (sym_equal H2)).
(* id *)elim (diff_id_cons a s H2).
(* contexte gauche*)elim (case_SLvar (S n) a' H2).
(* contexte droit *)apply H0; assumption.
Save case_SL_rvarcons.

(*** (env (var (S n)) (lift s)) SL ? ***)

Goal
forall (P : terms -> Prop) (n : nat) (s : sub_explicits),
P (env (var n) (comp s shift)) ->
(forall x' : sub_explicits, e_relSL _ (lift s) x' -> P (env (var (S n)) x')) ->
forall M : terms, e_relSL _ (env (var (S n)) (lift s)) M -> P M.
intros P n s H H0 M H1.
cut (var (S n) = var (S n)).
2: auto.
cut (lift s = lift s).
2: auto.
pattern (var (S n)) at 1, (lift s) at 1, M in |- *; apply case_SLenv; intros.
15: assumption.
(* app *)elim (diff_var_app (S n) a1 b1 (sym_equal H3)).
(* lambda *)elim (diff_var_lambda (S n) a1 (sym_equal H3)).
(* clos *)elim (diff_var_env (S n) a1 s1 (sym_equal H3)).
(* varshift1 *)elim (diff_shift_lift s H2).
(* varshift2 *)elim (diff_comp_lift shift s1 s H2).
(* fvarcons *)elim (O_S n (proj_var 0 (S n) H3)).
(* fvarlift1 *)elim (O_S n (proj_var 0 (S n) H3)).
(* fvarlift2 *)elim (O_S n (proj_var 0 (S n) H3)).
(* rvarcons *)elim (diff_cons_lift a1 s1 s H2).
(* rvarlift1 *)
rewrite (eq_add_S n0 n (proj_var (S n0) (S n) H3)).
rewrite (proj_lift s1 s H2); assumption.
(* rvarlift2 *)elim (diff_comp_lift (lift s1) s2 s H2).                   
(* id *)elim (diff_id_lift s H2).
(* contexte gauche*)elim (case_SLvar (S n) a' H2).
(* contexte droit *)apply H0; assumption.
Save case_SL_rvarlift1.

(*** (env (var (S n)) (comp (lift s) t)) SL ? ***)

Goal
forall (P : terms -> Prop) (n : nat) (s t : sub_explicits),
P (env (var n) (comp s (comp shift t))) ->
(forall x' : sub_explicits,
 e_relSL _ (comp (lift s) t) x' -> P (env (var (S n)) x')) ->
forall M : terms, e_relSL _ (env (var (S n)) (comp (lift s) t)) M -> P M.
intros P n s t H H0 M H1.
cut (var (S n) = var (S n)).
2: auto.
cut (comp (lift s) t = comp (lift s) t).
2: auto.
pattern (var (S n)) at 1, (comp (lift s) t) at 1, M in |- *; apply case_SLenv;
 intros.
15: assumption.
(* app *)elim (diff_var_app (S n) a1 b1 (sym_equal H3)).
(* lambda *)elim (diff_var_lambda (S n) a1 (sym_equal H3)).
(* clos *)elim (diff_var_env (S n) a1 s1 (sym_equal H3)).
(* varshift1 *)elim (diff_shift_comp (lift s) t H2).
(* varshift2 *)elim (diff_shift_lift s (proj_comp1 shift (lift s) s1 t H2)).
(* fvarcons *)elim (diff_cons_comp a1 s1 (lift s) t H2).
(* fvarlift1 *)elim (diff_comp_lift (lift s) t s1 (sym_equal H2)).
(* fvarlift2 *)elim (O_S n (proj_var 0 (S n) H3)).
(* rvarcons *)elim (diff_cons_comp a1 s1 (lift s) t H2).
(* rvarlift1 *)elim (diff_comp_lift (lift s) t s1 (sym_equal H2)).
(* rvarlift2 *)
rewrite (eq_add_S n0 n (proj_var (S n0) (S n) H3)).
rewrite (proj_lift s1 s (proj_comp1 (lift s1) (lift s) s2 t H2)).
rewrite (proj_comp2 (lift s1) (lift s) s2 t H2); assumption.
(* id *)elim (diff_id_comp (lift s) t H2).
(* contexte gauche*)elim (case_SLvar (S n) a' H2).
(* contexte droit *)apply H0; assumption.
Save case_SL_rvarlift2.

(*** (comp (comp s t) u) SL ? ***)

Goal
forall (P : sub_explicits -> sub_explicits -> Prop) (s t u : sub_explicits),
P u (comp s (comp t u)) ->
P id (comp s t) ->
(forall x' : sub_explicits, e_relSL _ (comp s t) x' -> P u (comp x' u)) ->
(forall u' : sub_explicits, e_relSL _ u u' -> P u (comp (comp s t) u')) ->
forall M : sub_explicits, e_relSL _ (comp (comp s t) u) M -> P u M. 
intros P s t u H H0 H1 H2 M H3.
cut (comp s t = comp s t).
2: auto.
pattern (comp s t) at 1, u, M in |- *; apply case_SLcomp; intros.
13: assumption.
(* assenv *)
rewrite (proj_comp1 s1 s s2 t H4).
rewrite (proj_comp2 s1 s s2 t H4); assumption.
(* mapenv *)elim (diff_cons_comp a s1 s t H4).
(* shiftcons *)elim (diff_shift_comp s t H4).
(* shiftlift1 *)elim (diff_shift_comp s t H4).
(* shiftlift2 *)elim (diff_shift_comp s t H4).
(* lift1 *)elim (diff_comp_lift s t s1 (sym_equal H4)).
(* lift2 *)elim (diff_comp_lift s t s1 (sym_equal H4)).
(* liftenv *)elim (diff_comp_lift s t s1 (sym_equal H4)).
(* idl *)elim (diff_id_comp s t H4).
(* idr *)
assumption.
(* contexte gauche *)
apply H1; assumption.
(* contexte droit *)
apply H2; assumption.
Save case_SL_assenv.

(*** (comp (cons a s) t) SL ? ***)

Goal
forall (P : sub_explicits -> sub_explicits -> Prop) 
  (a : terms) (s t : sub_explicits),
P t (cons (env a t) (comp s t)) ->
P id (cons a s) ->
(forall x' : sub_explicits, e_relSL _ (cons a s) x' -> P t (comp x' t)) ->
(forall t' : sub_explicits, e_relSL _ t t' -> P t (comp (cons a s) t')) ->
forall M : sub_explicits, e_relSL _ (comp (cons a s) t) M -> P t M. 
intros P a s t H H0 H1 H2 M H3.
cut (cons a s = cons a s).
2: auto.
pattern (cons a s) at 1, t, M in |- *; apply case_SLcomp; intros.
13: assumption.
(* assenv *)elim (diff_cons_comp a s s1 s2 (sym_equal H4)).
(* mapenv *)
rewrite (proj_cons1 a0 a s1 s H4).
rewrite (proj_cons2 a0 a s1 s H4); assumption.
(* shiftcons *)elim (diff_shift_cons a s H4).
(* shiftlift1 *)elim (diff_shift_cons a s H4).
(* shiftlift2 *)elim (diff_shift_cons a s H4).
(* lift1 *)elim (diff_cons_lift a s s1 (sym_equal H4)).
(* lift2 *)elim (diff_cons_lift a s s1 (sym_equal H4)).
(* liftenv *)elim (diff_cons_lift a s s1 (sym_equal H4)).
(* idl *)elim (diff_id_cons a s H4).
(* idr *)
assumption.
(* contexte gauche *)
apply H1; assumption.
(* contexte droit *)
apply H2; assumption.
Save case_SL_mapenv.

(*** (comp shift (cons a s)) SL ? ***)

Goal
forall (P : sub_explicits -> Prop) (a : terms) (s : sub_explicits),
P s ->
(forall x' : sub_explicits, e_relSL _ (cons a s) x' -> P (comp shift x')) ->
forall M : sub_explicits, e_relSL _ (comp shift (cons a s)) M -> P M. 
intros P a s H H0 M H1.
cut (cons a s = cons a s).
2: auto.
pattern (cons a s) at 1, M in |- *; apply case_SLcomp1; intros.
6: assumption.
(* shiftcons *)
rewrite (proj_cons2 a0 a s1 s H2); assumption.
(* shiftlift1 *)elim (diff_cons_lift a s s1 (sym_equal H2)).
(* shiftlift2 *)elim (diff_cons_comp a s (lift s1) t (sym_equal H2)).
(* idl *)elim (diff_id_cons a s H2).
(* contexte gauche *)
apply H0; assumption.
Save case_SL_shiftcons.
 
(*** (comp shift (lift s)) SL ? ***)

Goal
forall (P : sub_explicits -> Prop) (s : sub_explicits),
P (comp s shift) ->
(forall x' : sub_explicits, e_relSL _ (lift s) x' -> P (comp shift x')) ->
forall M : sub_explicits, e_relSL _ (comp shift (lift s)) M -> P M. 
intros P s H H0 M H1.
cut (lift s = lift s).
2: auto.
pattern (lift s) at 1, M in |- *; apply case_SLcomp1; intros.
6: assumption.
(* shiftcons *)elim (diff_cons_lift a s1 s H2).
(* shiftlift1 *)
rewrite (proj_lift s1 s H2); assumption.
(* shiftlift2 *)elim (diff_comp_lift (lift s1) t s H2).
(* idl *)elim (diff_id_lift s H2).
(* contexte gauche *)
apply H0; assumption.
Save case_SL_shiflift1.

(*** (comp shift (comp (lift s) t)) SL ? ***)

Goal
forall (P : sub_explicits -> Prop) (s t : sub_explicits),
P (comp s (comp shift t)) ->
(forall x' : sub_explicits,
 e_relSL _ (comp (lift s) t) x' -> P (comp shift x')) ->
forall M : sub_explicits, e_relSL _ (comp shift (comp (lift s) t)) M -> P M. 
intros P s t H H0 M H1.
cut (comp (lift s) t = comp (lift s) t).
2: auto.
pattern (comp (lift s) t) at 1, M in |- *; apply case_SLcomp1; intros.
6: assumption.
(* shiftcons *)elim (diff_cons_comp a s1 (lift s) t H2).
(* shiftlift1 *)elim (diff_comp_lift (lift s) t s1 (sym_equal H2)).
(* shiftlift2 *)
rewrite (proj_lift s1 s (proj_comp1 (lift s1) (lift s) t0 t H2)).
rewrite (proj_comp2 (lift s1) (lift s) t0 t H2); assumption.
(* idl *)elim (diff_id_comp (lift s) t H2).
(* contexte gauche *)
apply H0; assumption.
Save case_SL_shiflift2.

(*** (comp (lift s) (lift t)) SL ? ***)

Goal
forall (P : sub_explicits -> Prop) (s t : sub_explicits),
P (lift (comp s t)) ->
(forall x' : sub_explicits, e_relSL _ (lift s) x' -> P (comp x' (lift t))) ->
(forall x' : sub_explicits, e_relSL _ (lift t) x' -> P (comp (lift s) x')) ->
forall M : sub_explicits, e_relSL _ (comp (lift s) (lift t)) M -> P M.
intros P s t H H0 H1 M H2.
cut (lift t = lift t).
2: auto.
pattern (lift t) at 1, M in |- *; apply case_SLcomp2 with s; intros.
7: assumption.
(* lift1 *)
rewrite (proj_lift t1 t H3); assumption.
(* lift2 *)elim (diff_comp_lift (lift t1) t2 t H3).
(* liftenv *)elim (diff_cons_lift a t1 t H3).
(* idr *)elim (diff_id_lift t H3).
(* contexte gauche *)
apply H0; assumption.
(* contexte droit *)
apply H1; assumption.
Save case_SL_lift1.


(*** (comp (lift s) (comp (lift t) u)) SL ? ***)

Goal
forall (P : sub_explicits -> Prop) (s t u : sub_explicits),
P (comp (lift (comp s t)) u) ->
(forall x' : sub_explicits,
 e_relSL _ (lift s) x' -> P (comp x' (comp (lift t) u))) ->
(forall x' : sub_explicits,
 e_relSL _ (comp (lift t) u) x' -> P (comp (lift s) x')) ->
forall M : sub_explicits,
e_relSL _ (comp (lift s) (comp (lift t) u)) M -> P M.
intros P s t u H H0 H1 M H2.
cut (comp (lift t) u = comp (lift t) u).
2: auto.
pattern (comp (lift t) u) at 1, M in |- *; apply case_SLcomp2 with s; intros.
7: assumption.
(* lift1 *)elim (diff_comp_lift (lift t) u t1 (sym_equal H3)).
(* lift2 *)
rewrite (proj_lift t1 t (proj_comp1 (lift t1) (lift t) t2 u H3)).
rewrite (proj_comp2 (lift t1) (lift t) t2 u H3); assumption.
(* liftenv *)elim (diff_cons_comp a t1 (lift t) u H3).
(* idr *)elim (diff_id_comp (lift t) u H3).
(* contexte gauche *)
apply H0; assumption.
(* contexte droit *)
apply H1; assumption.
Save case_SL_lift2.

(*** (comp (lift s) (cons a t)) SL ? ***)

Goal
forall (P : sub_explicits -> Prop) (a : terms) (s t : sub_explicits),
P (cons a (comp s t)) ->
(forall x' : sub_explicits, e_relSL _ (lift s) x' -> P (comp x' (cons a t))) ->
(forall x' : sub_explicits, e_relSL _ (cons a t) x' -> P (comp (lift s) x')) ->
forall M : sub_explicits, e_relSL _ (comp (lift s) (cons a t)) M -> P M.
intros P a s t H H0 H1 M H2.
cut (cons a t = cons a t).
2: auto.
pattern (cons a t) at 1, M in |- *; apply case_SLcomp2 with s; intros.
7: assumption.
(* lift1 *)elim (diff_cons_lift a t t1 (sym_equal H3)).
(* lift2 *)elim (diff_cons_comp a t (lift t1) t2 (sym_equal H3)).
(* liftenv *)
rewrite (proj_cons1 a0 a t1 t H3).
rewrite (proj_cons2 a0 a t1 t H3); assumption.
(* idr *)elim (diff_id_cons a t H3).
(* contexte gauche *)
apply H0; assumption.
(* contexte droit *)
apply H1; assumption.
Save case_SL_liftenv.

(*** (comp id s) SL ? ***)

Goal
forall (P : sub_explicits -> sub_explicits -> Prop) (s : sub_explicits),
P s s ->
P id id ->
(forall s' : sub_explicits, e_relSL _ s s' -> P s (comp id s')) ->
forall M : sub_explicits, e_relSL _ (comp id s) M -> P s M.
intros P s H H0 H1 M H2.
cut (id = id).
2: auto.
cut (s = s).
2: auto.
pattern id at 1, s at 1, M in |- *; apply case_SLcomp; intros.
13: assumption.
(* assenv *)elim (diff_id_comp s1 s2 (sym_equal H4)).
(* mapenv *)elim (diff_id_cons a s1 (sym_equal H4)).
(* shiftcons *)elim (diff_id_shift (sym_equal H4)).
(* shiftlift1 *)elim (diff_id_shift (sym_equal H4)).
(* shiftlift2 *)elim (diff_id_shift (sym_equal H4)).
(* lift1 *)elim (diff_id_lift s1 (sym_equal H4)).
(* lift2 *)elim (diff_id_lift s1 (sym_equal H4)).
(* liftenv *)elim (diff_id_lift s1 (sym_equal H4)).
(* idl *)
assumption.
(* idr *)
elim H3; assumption.
(* contexte gauche *)
elim (case_SLid s' H3).
(* contexte droit *)
apply H1; assumption.
Save case_SL_idl.

(*** (comp s id) SL ? ***)

Goal
forall (P : sub_explicits -> sub_explicits -> Prop) (s : sub_explicits),
P s s ->
(forall s1 s2 : sub_explicits, P (comp s1 s2) (comp s1 (comp s2 id))) ->
(forall (a : terms) (s1 : sub_explicits),
 P (cons a s1) (cons (env a id) (comp s1 id))) ->
P id id ->
(forall s' : sub_explicits, e_relSL _ s s' -> P s (comp s' id)) ->
forall M : sub_explicits, e_relSL _ (comp s id) M -> P s M.
intros P s H H0 H1 H2 H3 M H4.
cut (id = id).
2: auto.
cut (s = s).
2: auto.
pattern s at 1, id at 1, M in |- *; apply case_SLcomp; intros.
13: assumption.
(* assenv *)
elim H5; apply H0.
(* mapenv *)
elim H5; apply H1.
(* shiftcons *)elim (diff_id_cons a t1 (sym_equal H6)).
(* shiftlift1 *)elim (diff_id_lift t1 (sym_equal H6)).
(* shiftlift2 *)elim (diff_id_comp (lift t1) t2 (sym_equal H6)).
(* lift1 *)elim (diff_id_lift t1 (sym_equal H6)).
(* lift2 *)elim (diff_id_comp (lift t1) t2 (sym_equal H6)).
(* liftenv *)elim (diff_id_cons a t1 (sym_equal H6)).
(* idl *)
elim H5; assumption.
(* idr *)
assumption.
(* contexte gauche *)
apply H3; assumption.
(* contexte droit *)
elim (case_SLid t' H5).
Save case_SL_idr.

(*** (lift id ) SL ? ***)

Goal
forall P : sub_explicits -> Prop,
P id -> forall M : sub_explicits, e_relSL _ (lift id) M -> P M.
intros P H M H0.
cut (id = id).
2: auto.
pattern id at 1, M in |- *; apply case_SLlift; intros.
3: assumption.
(* liftid *)
assumption.
(* contexte *)elim (case_SLid s' H1).
Save case_SL_liftid.

(*** (env a id) SL ? ***)

Goal
forall (P : terms -> terms -> Prop) (a : terms),
P a a ->
(forall a1 b1 : terms, P (app a1 b1) (app (env a1 id) (env b1 id))) ->
(forall a1 : terms, P (lambda a1) (lambda (env a1 (lift id)))) ->
(forall (a1 : terms) (s : sub_explicits), P (env a1 s) (env a1 (comp s id))) ->
(forall a' : terms, e_relSL _ a a' -> P a (env a' id)) ->
forall M : terms, e_relSL _ (env a id) M -> P a M.
intros P a H H0 H1 H2 H3 M H4.
cut (id = id).
2: auto.
pattern a, id at 2, M in |- *; apply case_SLenv; intros.
15: assumption.
(* app *)
apply H0.
(* lambda *)
apply H1.
(* clos *)
apply H2.
(* varshift1 *)elim (diff_id_shift H5).
(* varshift2 *)elim (diff_id_comp shift s1 H5).
(* fvarcons *)elim (diff_id_cons a1 s1 H5).
(* fvarlift1 *)elim (diff_id_lift s1 H5).
(* fvarlift2 *)elim (diff_id_comp (lift s1) s2 H5).
(* rvarcons *)elim (diff_id_cons a1 s1 H5).
(* rvarlift1 *)elim (diff_id_lift s1 H5).
(* rvarlift2 *)elim (diff_id_comp (lift s1) s2 H5).
(* id *)
assumption.
(* contexte gauche*)
apply H3; assumption.
(* contexte droit *)
elim (case_SLid s' H5).
Save case_SL_reg_id.



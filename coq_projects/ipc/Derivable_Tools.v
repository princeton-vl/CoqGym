(* File: Derivable.v  (last edited on 1/1/2000) (c) Klaus Weich  *)


Require Export Derivable_Def.


Lemma derivable_eq :
 forall (context context' : flist) (a a' : form),
 context = context' -> a = a' -> Derivable context a -> Derivable context' a'.
intros context context' a a' eq_context eq_a.
 rewrite eq_context.
 rewrite eq_a.
intros; assumption.
Qed.



Lemma derivable_subst :
 forall (i : Int) (g : form) (context : flist) (a : form),
 Derivable context a -> Derivable (subst_list i g context) (subst_form i g a).
intros i g context a der.
elim der; clear der.
intros t der.
elim der; clear der a t context.

intros context n a nth.
apply Derivable_Intro with (Var n).
apply ByAssumption.
apply subst_nth; assumption.

intros context t a der ih.
elim ih; clear ih.
intros t1 der1.
apply Derivable_Intro with (Efq t1 (subst_form i g a)).
apply ByAbsurdity; assumption.

intros context a t b der ih.
elim ih; clear ih.
intros t1 der1.
apply Derivable_Intro with (Abs (subst_form i g a) t1).
simpl in |- *.
apply ImpIntro; assumption.

intros context r s a b der_r ih_r der_s ih_s.
elim ih_r; clear ih_r.
intros r1 der_r1.
elim ih_s; clear ih_s.
intros s1 der_s1.
apply Derivable_Intro with (App (subst_form i g a) r1 s1).
apply ImpElim; assumption.

intros context r s a b der_r ih_r der_s ih_s.
elim ih_r; clear ih_r.
intros r1 der_r1.
elim ih_s; clear ih_s.
intros s1 der_s1.
apply Derivable_Intro with (Pair r1 s1).
simpl in |- *; apply AndFIntro; assumption.

intros context r a b der_r ih.
elim ih; clear ih; intros r1 der_r1.
apply Derivable_Intro with (PrL (subst_form i g b) r1).
apply AndFElimL; assumption.

intros context r a b der_r ih.
elim ih; clear ih; intros r1 der_r1.
apply Derivable_Intro with (PrR (subst_form i g a) r1).
apply AndFElimR; assumption.

intros context r a b der_r ih.
elim ih; clear ih; intros r1 der_r1.
apply Derivable_Intro with (OrFL r1 (subst_form i g b)).
simpl in |- *; apply OrFIntroL; assumption.

intros context r a b der_r ih.
elim ih; clear ih; intros r1 der_r1.
apply Derivable_Intro with (OrFR r1 (subst_form i g a)).
simpl in |- *; apply OrFIntroR; assumption.

intros context r s t a b c der_r ih_r der_s ih_s der_t ih_t.
elim ih_r; clear ih_r; intros r1 der_r1.
elim ih_s; clear ih_s; intros s1 der_s1.
elim ih_t; clear ih_t; intros t1 der_t1.
apply
 Derivable_Intro with (Cas (subst_form i g a) (subst_form i g b) r1 s1 t1).
apply OrFElim; assumption.

intros context r a b der_r ih_r.
elim ih_r; clear ih_r; intros r1 der_r1.
apply Derivable_Intro with (Shift r1).
simpl in |- *; apply ShiftIntro; assumption.
Qed.


Lemma snd_order_inst :
 forall (context : flist) (i : Int),
 Derivable context (Atom i) ->
 below_list context i -> forall b : form, Derivable context b.
intros context i der below b.
cut (subst_form i b (Atom i) = b).
intro eq_b.
 rewrite <- eq_b.
 rewrite <- (subst_list_below i b context).
apply derivable_subst; assumption.
assumption.
simpl in |- *.
apply equal_dec_refl.
Qed.


Lemma derivable_weak :
 forall (context : flist) (a b : form),
 Derivable context a -> Derivable (b :: context) a.
intros context a b der_a.
elim der_a; clear der_a.
intros t der_t.
apply Derivable_Intro with (Shift t).
apply ShiftIntro; assumption.
Qed.


Lemma derivable_weak_list :
 forall (context1 context2 : flist) (a : form),
 Derivable context1 a -> Derivable (context2 ++ context1) a.
intros context1 context2 a der1.
elim context2; clear context2.
assumption.
intros b context2 ih.
simpl in |- *; apply derivable_weak; assumption.
Qed.


Lemma derivable_cut_aux :
 forall (context : flist) (t : proof_term) (b : form),
 derives context t b ->
 forall (a : form) (l1 l2 : flist),
 context = l1 ++ a :: l2 -> Derivable fnil a -> Derivable (l1 ++ l2) b.
intros context t b der_t.
elim der_t; clear der_t context t b.

intros context n a nth b l1 l2 eq_context.
 rewrite eq_context in nth.
elim (inv_nth_app form n l1 (b :: l2) a nth); clear nth.
intros nth0 der_b.
apply Derivable_Intro with (Var n).
apply ByAssumption.
apply nth_app0; assumption.
clear n; intros n; case n; clear n.
intros nth_eq.
 rewrite (inv_nthO form b l2 a nth_eq).
intros der_a.
 rewrite (app_nil_end (l1 ++ l2)).
apply derivable_weak_list.
assumption.
intros n nth1 der_b.
apply Derivable_Intro with (Var (length l1 + n)).
apply ByAssumption.
apply nth_app1.
inversion_clear nth1; assumption.

intros context t a der_t ih b l1 l2 eq_context der_b.
elim (ih b l1 l2); try assumption.
intros t0 der_t0.
apply Derivable_Intro with (Efq t0 a).
apply ByAbsurdity; assumption.

intros context a t b der_t ih c l1 l2 eq_context der_c.
elim (ih c (a :: l1) l2); clear ih.
intros t0 der_t0.
apply Derivable_Intro with (Abs a t0).
apply ImpIntro; assumption.
 rewrite eq_context.
trivial.
assumption.

intros context r s a b der_r ih_r der_s ih_s c l1 l2 eq_context der_c.
elim (ih_r c l1 l2); clear ih_r; try assumption.
intros r0 der_r0.
elim (ih_s c l1 l2); clear ih_s; try assumption.
intros s0 der_s0.
apply Derivable_Intro with (App a r0 s0).
apply ImpElim; assumption.

intros context r s a b der_r ih_r der_s ih_s c l1 l2 eq_context der_c.
elim (ih_r c l1 l2); clear ih_r; try assumption.
intros r0 der_r0.
elim (ih_s c l1 l2); clear ih_s; try assumption.
intros s0 der_s0.
apply Derivable_Intro with (Pair r0 s0).
apply AndFIntro; assumption.

intros context r a b der_r ih_r c l1 l2 eq_context der_c.
elim (ih_r c l1 l2); clear ih_r; try assumption.
intros r0 der_r0.
apply Derivable_Intro with (PrL b r0).
apply AndFElimL; assumption.

intros context r a b der_r ih_r c l1 l2 eq_context der_c.
elim (ih_r c l1 l2); clear ih_r; try assumption.
intros r0 der_r0.
apply Derivable_Intro with (PrR a r0).
apply AndFElimR; assumption.

intros context r a b der_r ih_r c l1 l2 eq_context der_c.
elim (ih_r c l1 l2); clear ih_r; try assumption.
intros r0 der_r0.
apply Derivable_Intro with (OrFL r0 b).
apply OrFIntroL; assumption.

intros context r a b der_r ih_r c l1 l2 eq_context der_c.
elim (ih_r c l1 l2); clear ih_r; try assumption.
intros r0 der_r0.
apply Derivable_Intro with (OrFR r0 a).
apply OrFIntroR; assumption.

intros context r s t a b c der_r ih_r der_s ih_s der_t ih_t d l1 l2
 eq_context der_d; clear der_r der_s der_t.
elim (ih_r d l1 l2); try assumption; clear ih_r.
intros r0 der_r0.
elim (ih_s d (a :: l1) l2); clear ih_s.
intros s0 der_s0.
elim (ih_t d (b :: l1) l2); clear ih_t.
intros t0 der_t0.
apply Derivable_Intro with (Cas a b r0 s0 t0).
apply OrFElim; assumption.
 rewrite eq_context; trivial.
assumption.
 rewrite eq_context; trivial.
assumption.

intros context r a b der_r ih_r c l1.
case l1; clear l1.
simpl in |- *; intros l2 eq_context der_c.
apply Derivable_Intro with r.
 injection eq_context; intros H1 H2.
 rewrite <- H1; assumption.
simpl in |- *; intros d l1 l2 eq_context der_c.
elim (ih_r c l1 l2); clear ih_r; try assumption.
intros r0 der_r0.
apply derivable_weak.
apply Derivable_Intro with r0; assumption.

 injection eq_context.
intros; assumption.
Qed.




Lemma derivable_cut :
 forall (context : flist) (a b : form),
 Derivable fnil a -> Derivable (a :: context) b -> Derivable context b.
intros context a b der_a der_b.
elim der_b; clear der_b.
intros t der_b.
apply (derivable_cut_aux (a :: context) t b der_b a fnil context).
trivial.
assumption.
Qed.


Lemma derivable_cut_merge :
 forall (context : flist) (a b : form),
 Derivable context a -> Derivable (a :: context) b -> Derivable context b.
intros context; elim context; clear context.

intros; apply derivable_cut with a; assumption.

intros c context ih a b der_a der_b.
elim (ih (Imp c a) (Imp c b)); clear ih.
intros t der_t.
apply Derivable_Intro with (App c (Shift t) (Var 0)).
apply ImpElim.
apply ShiftIntro; assumption.
apply ByAssumption.
apply My_NthO.
elim der_a; clear der_a; intros t der_t.
apply Derivable_Intro with (Abs c t).
apply ImpIntro; assumption.
elim der_b; clear der_b; intros t der_t.
apply
 Derivable_Intro
  with
    (Abs c
       (App a (App c (Shift (Shift (Abs c (Abs a t)))) (Var 0))
          (App c (Var 1) (Var 0)))).
apply ImpIntro.
apply ImpElim.
apply ImpElim.
apply ShiftIntro.
apply ShiftIntro.
apply ImpIntro.
apply ImpIntro.
assumption.
apply ByAssumption.
apply My_NthO.
apply ImpElim.
apply ByAssumption.
apply My_NthS.
apply My_NthO.
apply ByAssumption.
apply My_NthO.
Qed.


(************************************************************************)


Lemma derivable_a_imp_a : forall a : form, Derivable fnil (Imp a a).
intros a.
apply Derivable_Intro with (Abs a (Var 0)).
apply ImpIntro.
apply ByAssumption.
apply My_NthO.
Qed.

     

Lemma derivable_a_and_b__derivable_a :
 forall (a b : form) (context : flist),
 Derivable context (AndF a b) -> Derivable context a.
intros a b context der.
elim der; clear der.
intros t der_t.
apply Derivable_Intro with (PrL b t).
apply AndFElimL; assumption.
Qed.


Lemma derivable_a_and_b__derivable_b :
 forall (a b : form) (context : flist),
 Derivable context (AndF a b) -> Derivable context b.
intros a b context der.
elim der; clear der.
intros t der_t.
apply Derivable_Intro with (PrR a t).
apply AndFElimR; assumption.
Qed.




Lemma derivable_falsum_or_a__derivable_a :
 forall (a : form) (context : flist),
 Derivable context (OrF Falsum a) -> Derivable context a.
intros a context der.
elim der; clear der.
intros t der_t.
apply Derivable_Intro with (Cas Falsum a t (Efq (Var 0) a) (Var 0)).
apply OrFElim.
assumption.
apply ByAbsurdity.
apply ByAssumption.
apply My_NthO.
apply ByAssumption.
apply My_NthO.
Qed.



Lemma derivable_a_or_falsum__derivable_a :
 forall (a : form) (context : flist),
 Derivable context (OrF a Falsum) -> Derivable context a.
intros a context der.
elim der; clear der.
intros t der_t.
apply Derivable_Intro with (Cas a Falsum t (Var 0) (Efq (Var 0) a)).
apply OrFElim.
assumption.
apply ByAssumption.
apply My_NthO.
apply ByAbsurdity.
apply ByAssumption.
apply My_NthO.
Qed.



Lemma derivable_a_imp_falsum_or_b__derivable_a_imp_b :
 forall (context : flist) (a b : form),
 Derivable context (Imp a (OrF Falsum b)) -> Derivable context (Imp a b).
intros context a b der.
elim der; clear der.
intros t der_t.
apply
 Derivable_Intro
  with
    (Abs a (Cas Falsum b (App a (Shift t) (Var 0)) (Efq (Var 0) b) (Var 0))).
apply ImpIntro.
apply OrFElim.
apply ImpElim.
apply ShiftIntro; assumption.
apply ByAssumption; apply My_NthO.
apply ByAbsurdity.
apply ByAssumption; apply My_NthO.
apply ByAssumption; apply My_NthO.
Qed.




Lemma derivable_a_imp_b_or_falsum__derivable_a_imp_b :
 forall (context : flist) (a b : form),
 Derivable context (Imp a (OrF b Falsum)) -> Derivable context (Imp a b).
intros context a b der.
elim der; clear der.
intros t der_t.
apply
 Derivable_Intro
  with
    (Abs a (Cas b Falsum (App a (Shift t) (Var 0)) (Var 0) (Efq (Var 0) b))).
apply ImpIntro.
apply OrFElim.
apply ImpElim.
apply ShiftIntro; assumption.
apply ByAssumption; apply My_NthO.
apply ByAssumption; apply My_NthO.
apply ByAbsurdity.
apply ByAssumption; apply My_NthO.
Qed.




Lemma derivable_a0_and_a1_imp_b__derivable_a0_imp_a1_imp_b :
 forall (a0 a1 b : form) (context : flist),
 Derivable context (Imp (AndF a0 a1) b) ->
 Derivable context (Imp a0 (Imp a1 b)).
intros a0 a1 b context der.
elim der; clear der.
intros t der.
apply
 Derivable_Intro
  with
    (Abs a0
       (Abs a1 (App (AndF a0 a1) (Shift (Shift t)) (Pair (Var 1) (Var 0))))).
apply ImpIntro.
apply ImpIntro.
apply ImpElim.
apply ShiftIntro.
apply ShiftIntro.
assumption.
apply AndFIntro.
apply ByAssumption.
apply My_NthS; apply My_NthO.
apply ByAssumption.
apply My_NthO.
Qed.



Lemma derivable_a0_or_a1_imp_b__derivable_a0_imp_b :
 forall (context : flist) (a0 a1 b : form),
 Derivable context (Imp (OrF a0 a1) b) -> Derivable context (Imp a0 b).
intros context a0 a1 b der.
elim der; clear der.
intros t der_t.
apply
 Derivable_Intro with (Abs a0 (App (OrF a0 a1) (Shift t) (OrFL (Var 0) a1))).
apply ImpIntro.
apply ImpElim.
apply ShiftIntro; assumption.
apply OrFIntroL.
apply ByAssumption; apply My_NthO.
Qed.


Lemma derivable_a0_or_a1_imp_b__derivable_a1_imp_b :
 forall (context : flist) (a0 a1 b : form),
 Derivable context (Imp (OrF a0 a1) b) -> Derivable context (Imp a1 b).
intros context a0 a1 b der.
elim der; clear der.
intros t der_t.
apply
 Derivable_Intro with (Abs a1 (App (OrF a0 a1) (Shift t) (OrFR (Var 0) a0))).
apply ImpIntro.
apply ImpElim.
apply ShiftIntro; assumption.
apply OrFIntroR.
apply ByAssumption; apply My_NthO.
Qed.




Lemma derivable_falsum_imp_b_imp_c__derivable_c :
 forall (context : flist) (b c : form),
 Derivable context (Imp (Imp Falsum b) c) -> Derivable context c.
intros context b c der.
elim der; clear der.
intros t der_t.
apply
 Derivable_Intro with (App (Imp Falsum b) t (Abs Falsum (Efq (Var 0) b))).
apply ImpElim.
assumption.
apply ImpIntro.
apply ByAbsurdity.
apply ByAssumption; apply My_NthO.
Qed.


Lemma derivable_b__derivable_a_imp_b :
 forall (a b : form) (context : flist),
 Derivable context b -> Derivable context (Imp a b).
intros a b context der.
elim der; clear der.
intros t der_t.
apply Derivable_Intro with (Abs a (Shift t)).
apply ImpIntro.
apply ShiftIntro; assumption.
Qed.


Lemma derivable_a_a_imp_b__derivable_b :
 forall (a b : form) (context : flist),
 Derivable context a -> Derivable context (Imp a b) -> Derivable context b.
intros a b context der_a der_ab.
elim der_a; clear der_a.
intros t der_t.
elim der_ab; clear der_ab.
intros s der_s.
apply Derivable_Intro with (App a s t).
apply ImpElim; assumption.
Qed.


Lemma derivable_a_context_b__derivable_a_imp_b :
 forall (a b : form) (context : flist),
 Derivable (a :: context) b -> Derivable context (Imp a b).
intros a b context der.
elim der; clear der.
intros t der_t.
apply Derivable_Intro with (Abs a t).
apply ImpIntro; assumption.
Qed.


Lemma derivable_vimp :
 forall (context : flist) (l : list Int) (a b : form),
 (forall context : flist, Derivable context a -> Derivable context b) ->
 Derivable context (vimp l a) -> Derivable context (vimp l b).
intros context l.
elim l; clear l.
intros a b der_ab der_a.
apply der_ab; assumption.
simpl in |- *; intros i l ih a b der_ab der_a.
apply ih with (a := Imp (Atom i) a); try assumption.
intros context' der_ia.
elim der_ia; clear der_ia; intros t der_ia.
elim (der_ab (Atom i :: context')).
intros s der_b.
apply Derivable_Intro with (Abs (Atom i) s).
apply ImpIntro; assumption.
apply Derivable_Intro with (App (Atom i) (Shift t) (Var 0)).
apply ImpElim.
apply ShiftIntro; assumption.
apply ByAssumption.
apply My_NthO.
Qed.


Lemma derivable_vimp2 :
 forall (context : flist) (l : list Int) (a b c : form),
 (forall context : flist,
  Derivable context a -> Derivable context b -> Derivable context c) ->
 Derivable context (vimp l a) ->
 Derivable context (vimp l b) -> Derivable context (vimp l c).
intros context l.
elim l; clear l.
intros a b c der_abc der_a der_b.
apply der_abc; assumption.
simpl in |- *; intros i l ih a b c der_abc der_a der_b.
apply ih with (a := Imp (Atom i) a) (b := Imp (Atom i) b); try assumption.
clear ih.
intros context' der_ia der_ib.
elim der_ia; clear der_ia; intros t der_ia.
elim der_ib; clear der_ib; intros s der_ib.
elim (der_abc (Atom i :: context')).
intros r der_r.
apply Derivable_Intro with (Abs (Atom i) r).
apply ImpIntro; assumption.
apply Derivable_Intro with (App (Atom i) (Shift t) (Var 0)).
apply ImpElim.
apply ShiftIntro; assumption.
apply ByAssumption.
apply My_NthO.
apply Derivable_Intro with (App (Atom i) (Shift s) (Var 0)).
apply ImpElim.
apply ShiftIntro; assumption.
apply ByAssumption.
apply My_NthO.
Qed.


Lemma derivable_vimp0 :
 forall (context : flist) (l : list Int) (a : form),
 (forall context : flist, Derivable context a) ->
 Derivable context (vimp l a).
intros context l.
elim l; clear l.
intros a der_a.
apply der_a; assumption.
simpl in |- *; intros i l ih a der_a.
apply ih.
intros context'.
elim der_a with (Atom i :: context'); clear der_a; intros t der_a.
apply Derivable_Intro with (Abs (Atom i) t).
apply ImpIntro; assumption.
Qed.

(* File: Derivations.v  (last edited on 1/11/2000) (c) Klaus Weich  *)


Require Export Forms.


(*******   Derivations    *****************************************)

Inductive proof_term : Set :=
  | Var : nat -> proof_term
  | Efq : proof_term -> form -> proof_term
  | Abs : form -> proof_term -> proof_term
  | App : form -> proof_term -> proof_term -> proof_term
  | Pair : proof_term -> proof_term -> proof_term
  | PrL : form -> proof_term -> proof_term
  | PrR : form -> proof_term -> proof_term
  | OrFL : proof_term -> form -> proof_term
  | OrFR : proof_term -> form -> proof_term
  | Cas :
      form -> form -> proof_term -> proof_term -> proof_term -> proof_term
  | Shift : proof_term -> proof_term.



Inductive derives : flist -> proof_term -> form -> Prop :=
  | ByAssumption :
      forall (context : flist) (n : nat) (a : form),
      my_nth form n context a -> derives context (Var n) a
  | ByAbsurdity :
      forall (context : flist) (t : proof_term) (a : form),
      derives context t Falsum -> derives context (Efq t a) a
  | ImpIntro :
      forall (context : flist) (a : form) (r : proof_term) (b : form),
      derives (a :: context) r b -> derives context (Abs a r) (Imp a b)
  | ImpElim :
      forall (context : flist) (r s : proof_term) (a b : form),
      derives context r (Imp a b) ->
      derives context s a -> derives context (App a r s) b
  | AndFIntro :
      forall (context : flist) (r s : proof_term) (a b : form),
      derives context r a ->
      derives context s b -> derives context (Pair r s) (AndF a b)
  | AndFElimL :
      forall (context : flist) (r : proof_term) (a b : form),
      derives context r (AndF a b) -> derives context (PrL b r) a
  | AndFElimR :
      forall (context : flist) (r : proof_term) (a b : form),
      derives context r (AndF a b) -> derives context (PrR a r) b
  | OrFIntroL :
      forall (context : flist) (r : proof_term) (a b : form),
      derives context r a -> derives context (OrFL r b) (OrF a b)
  | OrFIntroR :
      forall (context : flist) (r : proof_term) (a b : form),
      derives context r b -> derives context (OrFR r a) (OrF a b)
  | OrFElim :
      forall (context : flist) (r s t : proof_term) (a b c : form),
      derives context r (OrF a b) ->
      derives (a :: context) s c ->
      derives (b :: context) t c -> derives context (Cas a b r s t) c
  | ShiftIntro :
      forall (context : flist) (r : proof_term) (a b : form),
      derives context r b -> derives (a :: context) (Shift r) b.


Lemma derives_rec :
 forall P : flist -> proof_term -> form -> Set,
 (forall (context : flist) (n : nat) (a : form),
  my_nth form n context a -> P context (Var n) a) ->
 (forall (context : flist) (t : proof_term) (a : form),
  derives context t Falsum -> P context t Falsum -> P context (Efq t a) a) ->
 (forall (context : flist) (a : form) (r : proof_term) (b : form),
  derives (a :: context) r b ->
  P (a :: context) r b -> P context (Abs a r) (Imp a b)) ->
 (forall (context : flist) (r s : proof_term) (a b : form),
  derives context r (Imp a b) ->
  P context r (Imp a b) ->
  derives context s a -> P context s a -> P context (App a r s) b) ->
 (forall (context : flist) (r s : proof_term) (a b : form),
  derives context r a ->
  P context r a ->
  derives context s b -> P context s b -> P context (Pair r s) (AndF a b)) ->
 (forall (context : flist) (r : proof_term) (a b : form),
  derives context r (AndF a b) ->
  P context r (AndF a b) -> P context (PrL b r) a) ->
 (forall (context : flist) (r : proof_term) (a b : form),
  derives context r (AndF a b) ->
  P context r (AndF a b) -> P context (PrR a r) b) ->
 (forall (context : flist) (r : proof_term) (a b : form),
  derives context r a -> P context r a -> P context (OrFL r b) (OrF a b)) ->
 (forall (context : flist) (r : proof_term) (a b : form),
  derives context r b -> P context r b -> P context (OrFR r a) (OrF a b)) ->
 (forall (context : flist) (r s t : proof_term) (a b c : form),
  derives context r (OrF a b) ->
  P context r (OrF a b) ->
  derives (a :: context) s c ->
  P (a :: context) s c ->
  derives (b :: context) t c ->
  P (b :: context) t c -> P context (Cas a b r s t) c) ->
 (forall (context : flist) (r : proof_term) (a b : form),
  derives context r b -> P context r b -> P (a :: context) (Shift r) b) ->
 forall (context : flist) (t : proof_term) (a : form),
 derives context t a -> P context t a.
intros P var efq abs app pari prl prr orl orr cas shift context t.
generalize context; clear context.
elim t; clear t.

intros n context a der.
apply var.
inversion_clear der; assumption.

intros t ih a context b der.
cut (a = b).
intros eq_a;  rewrite eq_a.
apply efq.
inversion_clear der; assumption.
apply ih.
inversion_clear der; assumption.
inversion_clear der; trivial.

intros a t ih context b. 
case b; clear b.
intros der_t; elimtype False; inversion_clear der_t.
intros i der_t; elimtype False; inversion_clear der_t.
intros b0 b1 der_t; elimtype False; inversion_clear der_t.
intros b0 b1 der_t; elimtype False; inversion_clear der_t.
intros b0 b1 der_t.
cut (a = b0).
intros eq_a;  rewrite eq_a.
apply abs.
inversion_clear der_t; assumption.
apply ih.
inversion_clear der_t; assumption.
inversion_clear der_t; trivial.

intros a s ih_s t ih_t context b der.
apply app.
inversion_clear der; assumption.
apply ih_s.
inversion_clear der; assumption.
inversion_clear der; assumption.
apply ih_t.
inversion_clear der; assumption.

intros s ih_s t ih_t context a.
case a; clear a.
intros der; elimtype False; inversion_clear der.
intros i der; elimtype False; inversion_clear der.
intros a0 a1 der.
apply pari.
inversion_clear der; assumption.
apply ih_s.
inversion_clear der; assumption.
inversion_clear der; assumption.
apply ih_t.
inversion_clear der; assumption.
intros a0 a1 der; elimtype False; inversion_clear der.
intros a0 a1 der; elimtype False; inversion_clear der.

intros a s ih context b der.
apply prl.
inversion_clear der; assumption.
apply ih.
inversion_clear der; assumption.

intros a s ih context b der.
apply prr.
inversion_clear der; assumption.
apply ih.
inversion_clear der; assumption.

intros s ih a context b.
case b; clear b.
intros der; elimtype False; inversion_clear der.
intros i der; elimtype False; inversion_clear der.
intros b0 b1 der; elimtype False; inversion_clear der.
intros b0 b1 der.
cut (a = b1).
intros eq_a;  rewrite eq_a.
apply orl.
inversion_clear der; assumption.
apply ih.
inversion_clear der; assumption.
inversion_clear der; trivial.
intros b0 b1 der; elimtype False; inversion_clear der.

intros s ih a context b.
case b; clear b.
intros der; elimtype False; inversion_clear der.
intros i der; elimtype False; inversion_clear der.
intros b0 b1 der; elimtype False; inversion_clear der.
intros b0 b1 der.
cut (a = b0).
intros eq_a;  rewrite eq_a.
apply orr.
inversion_clear der; assumption.
apply ih.
inversion_clear der; assumption.
inversion_clear der; trivial.
intros b0 b1 der; elimtype False; inversion_clear der.

intros a b r ih_r s ih_s t ih_t context c der.
apply cas.
inversion_clear der; assumption.
apply ih_r.
inversion_clear der; assumption.
inversion_clear der; assumption.
apply ih_s.
inversion_clear der; assumption.
inversion_clear der; assumption.
apply ih_t.
inversion_clear der; assumption.

intros t ih context a.
case context; clear context.
intros der; elimtype False; inversion_clear der.
intros b context der.
apply shift.
inversion_clear der; assumption.
apply ih.
inversion_clear der; assumption.
Qed.



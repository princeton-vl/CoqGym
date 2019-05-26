From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From fcsl
Require Import axioms pred prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**********)
(* Posets *)
(**********)

Module Poset.

Section RawMixin.

Record mixin_of (T : Type) := Mixin {
  mx_leq : T -> T -> Prop;
  _ : forall x, mx_leq x x;
  _ : forall x y, mx_leq x y -> mx_leq y x -> x = y;
  _ : forall x y z, mx_leq x y -> mx_leq y z -> mx_leq x z}.

End RawMixin.

Section ClassDef.

Record class_of T := Class {mixin : mixin_of T}.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

(* produce a poset type out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack (m0 : mixin_of T) :=
  fun m & phant_id m0 m => Pack (@Class T m) T.

Definition leq := mx_leq (mixin class).

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation poset := Poset.type.
Notation PosetMixin := Poset.Mixin.
Notation Poset T m := (@pack T _ m id).

Notation "[ 'poset' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'poset'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'poset' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'poset'  'of'  T ]") : form_scope.

Notation "x <== y" := (Poset.leq x y) (at level 70).

(* re-state lattice properties using the exported notation *)
Section Laws.
Variable T : poset.

Lemma poset_refl (x : T) : x <== x.
Proof. by case: T x=>S [[leq B R]]. Qed.

Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
Proof. by case: T x y=>S [[l R A Tr]] *; apply: (A). Qed.

Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.
Proof. by case: T y x z=>S [[l R A Tr]] ? x y z; apply: (Tr). Qed.

End Laws.

Hint Resolve poset_refl.

Add Parametric Relation (T : poset) : T (@Poset.leq T)
  reflexivity proved by (@poset_refl _)
  transitivity proved by (fun x y => @poset_trans _ y x) as poset_rel.

End Exports.

End Poset.

Export Poset.Exports.

(**************************)
(* some basic definitions *)
(**************************)

Definition monotone (T1 T2 : poset) (f : T1 -> T2) :=
  forall x y, x <== y -> f x <== f y.

Section IdealDef.
Variable T : poset.

Structure ideal (P : T) := Ideal {id_val : T; id_pf : id_val <== P}.

(* Changing the type of the ideal *)

Lemma relaxP (P1 P2 : T) : P1 <== P2 -> forall p, p <== P1 -> p <== P2.
Proof. by move=>H1 p H2; apply: poset_trans H1. Qed.

Definition relax (P1 P2 : T) (x : ideal P1) (pf : P1 <== P2) :=
  Ideal (relaxP pf (id_pf x)).

End IdealDef.

(***********************)
(* poset constructions *)
(***********************)

Section SubPoset.
Variables (T : poset) (s : Pred T).

Local Notation tp := {x : T | x \In s}.

Definition sub_leq (p1 p2 : tp) := sval p1 <== sval p2.

Lemma sub_refl x : sub_leq x x.
Proof. by rewrite /sub_leq. Qed.

Lemma sub_asym x y : sub_leq x y -> sub_leq y x -> x = y.
Proof.
move: x y=>[x Hx][y Hy]; rewrite /sub_leq /= => H1 H2.
move: (poset_asym H1 H2) Hy=> <- Hy; congr exist.
by apply: pf_irr.
Qed.

Lemma sub_trans x y z : sub_leq x y -> sub_leq y z -> sub_leq x z.
Proof.
move: x y z=>[x Hx][y Hy][z Hz]; rewrite /sub_leq /=.
by apply: poset_trans.
Qed.

(* no need to put canonical here, because the system won't be *)
(* able to get the proof C from the {x : T | x \In s} syntax *)
Definition subPosetMixin := PosetMixin sub_refl sub_asym sub_trans.
Definition subPoset := Eval hnf in Poset tp subPosetMixin.

End SubPoset.

(* pairing of posets *)

Section PairPoset.
Variable (A B : poset).
Local Notation tp := (A * B)%type.

Definition pair_leq (p1 p2 : tp) := p1.1 <== p2.1 /\ p1.2 <== p2.2.

Lemma pair_refl x : pair_leq x x.
Proof. by []. Qed.

Lemma pair_asym x y : pair_leq x y -> pair_leq y x -> x = y.
Proof.
move: x y=>[x1 x2][y1 y2][/= H1 H2][/= H3 H4].
by congr (_, _); apply: poset_asym.
Qed.

Lemma pair_trans x y z : pair_leq x y -> pair_leq y z -> pair_leq x z.
Proof.
move: x y z=>[x1 x2][y1 y2][z1 z2][/= H1 H2][/= H3 H4]; split=>/=.
- by apply: poset_trans H3.
by apply: poset_trans H4.
Qed.

Definition pairPosetMixin :=
  PosetMixin pair_refl pair_asym pair_trans.
Canonical pairPoset := Eval hnf in Poset tp pairPosetMixin.

End PairPoset.

(* functions into a poset form a poset *)

Section FunPoset.
Variable (A : Type) (B : poset).
Local Notation tp := (A -> B).

Definition fun_leq (p1 p2 : tp) := forall x, p1 x <== p2 x.

Lemma fun_refl x : fun_leq x x.
Proof. by []. Qed.

Lemma fun_asym x y : fun_leq x y -> fun_leq y x -> x = y.
Proof.
move=>H1 H2; apply: fext=>z;
by apply: poset_asym; [apply: H1 | apply: H2].
Qed.

Lemma fun_trans x y z : fun_leq x y -> fun_leq y z -> fun_leq x z.
Proof. by move=>H1 H2 t; apply: poset_trans (H2 t). Qed.

Definition funPosetMixin := PosetMixin fun_refl fun_asym fun_trans.
Canonical funPoset := Eval hnf in Poset tp funPosetMixin.

End FunPoset.

(* dependent functions into a poset form a poset *)

Section DFunPoset.
Variables (A : Type) (B : A -> poset).
Local Notation tp := (forall x, B x).

Definition dfun_leq (p1 p2 : tp) := forall x, p1 x <== p2 x.

Lemma dfun_refl x : dfun_leq x x.
Proof. by []. Qed.

Lemma dfun_asym x y : dfun_leq x y -> dfun_leq y x -> x = y.
Proof.
move=>H1 H2; apply: fext=>z;
by apply: poset_asym; [apply: H1 | apply: H2].
Qed.

Lemma dfun_trans x y z : dfun_leq x y -> dfun_leq y z -> dfun_leq x z.
Proof. by move=>H1 H2 t; apply: poset_trans (H2 t). Qed.

(* no point in declaring this canonical, since it's keyed on forall *)
(* and forall is not a symbol *)
Definition dfunPosetMixin :=
  PosetMixin dfun_refl dfun_asym dfun_trans.
Definition dfunPoset := Eval hnf in Poset tp dfunPosetMixin.

End DFunPoset.

(* ideal of a poset is a poset *)

Section IdealPoset.
Variable (T : poset) (P : T).

Definition ideal_leq (p1 p2 : ideal P) := id_val p1 <== id_val p2.

Lemma ideal_refl x : ideal_leq x x.
Proof. by case: x=>x H; rewrite /ideal_leq. Qed.

Lemma ideal_asym x y : ideal_leq x y -> ideal_leq y x -> x = y.
Proof.
move: x y=>[x1 H1][x2 H2]; rewrite /ideal_leq /= => H3 H4; move: H1 H2.
rewrite (poset_asym H3 H4)=>H1 H2.
congr Ideal; apply: pf_irr.
Qed.

Lemma ideal_trans x y z : ideal_leq x y -> ideal_leq y z -> ideal_leq x z.
Proof. by apply: poset_trans. Qed.

Definition idealPosetMixin :=
  PosetMixin ideal_refl ideal_asym ideal_trans.
Canonical idealPoset := Eval hnf in Poset (ideal P) idealPosetMixin.

End IdealPoset.

(* Prop is a poset *)

Section PropPoset.

Definition prop_leq (p1 p2 : Prop) := p1 -> p2.

Lemma prop_refl x : prop_leq x x.
Proof. by []. Qed.

Lemma prop_asym x y : prop_leq x y -> prop_leq y x -> x = y.
Proof. by move=>H1 H2; apply: pext. Qed.

Lemma prop_trans x y z : prop_leq x y -> prop_leq y z -> prop_leq x z.
Proof. by move=>H1 H2; move/H1. Qed.

Definition propPosetMixin :=
  PosetMixin prop_refl prop_asym prop_trans.
Canonical propPoset := Eval hnf in Poset Prop propPosetMixin.

End PropPoset.

(* Pred is a poset *)

(* Can be inherited from posets of -> and Prop, but we declare a *)
(* dedicated structure to keep the infix notation of Pred. Otherwise, *)
(* poset inference turns Pred A into A -> Prop. *)

(*
Section PredPoset.
Variable A : Type.

Definition predPosetMixin : Poset.mixin_of (Pred A) :=
  funPosetMixin A propPoset.
Canonical predPoset := Eval hnf in Poset (Pred A) predPosetMixin.

End PredPoset.
*)

(*********************)
(* Complete lattices *)
(*********************)

Module Lattice.

Section RawMixin.

Variable T : poset.

Record mixin_of := Mixin {
  mx_sup : Pred T -> T;
  _ : forall (s : Pred T) x, x \In s -> x <== mx_sup s;
  _ : forall (s : Pred T) x,
        (forall y, y \In s -> y <== x) -> mx_sup s <== x}.

End RawMixin.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : Poset.class_of T;
  mixin : mixin_of (Poset.Pack base T)}.

Local Coercion base : class_of >-> Poset.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

(* produce a lattice type out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack b0 (m0 : mixin_of (Poset.Pack b0 T)) :=
  fun m & phant_id m0 m => Pack (@Class T b0 m) T.

Definition sup (s : Pred cT) : cT := mx_sup (mixin class) s.

Definition poset := Poset.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Poset.class_of.
Coercion sort : type >-> Sortclass.
Coercion poset : type >-> Poset.type.
Canonical Structure poset.

Notation lattice := Lattice.type.
Notation LatticeMixin := Lattice.Mixin.
Notation Lattice T m := (@pack T _ _ m id).

Notation "[ 'lattice' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'lattice'  'of'  T  'for' cT ]") : form_scope.
Notation "[ 'lattice' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'lattice'  'of'  T ]") : form_scope.

Arguments Lattice.sup [cT].
Prenex Implicits Lattice.sup.
Notation sup := Lattice.sup.

(* re-state lattice properties using the exported notation *)
Section Laws.
Variable T : lattice.

Lemma supP (s : Pred T) x : x \In s -> x <== sup s.
Proof. by case: T s x=>S [[p]][/= s H1 *]; apply: H1. Qed.

Lemma supM (s : Pred T) x : (forall y, y \In s -> y <== x) -> sup s <== x.
Proof. by case: T s x=>S [[p]][/= s H1 H2 *]; apply: (H2). Qed.

End Laws.

End Exports.

End Lattice.

Export Lattice.Exports.

(* we have greatest lower bounds too *)
Section Infimum.
Variable T : lattice.

Definition inf (s : Pred T) :=
  sup [Pred x : T | forall y, y \In s -> x <== y].

Lemma infP s : forall x, x \In s -> inf s <== x.
Proof. by move=>x H; apply: supM=>y; apply. Qed.

Lemma infM s : forall x, (forall y, y \In s -> x <== y) -> x <== inf s.
Proof. by apply: supP. Qed.

End Infimum.

(* we can compute least and greatest fixed points *)

Section Lat.
Variable T : lattice.

Definition lbot : T := sup Pred0.

Definition tarski_lfp (f : T -> T) := inf [Pred x : T | f x <== x].
Definition tarski_gfp (f : T -> T) := sup [Pred x : T | x <== f x].

Definition sup_closed (T : lattice) :=
  [Pred s : Pred T | forall d, d <=p s -> sup d \In s].

Definition sup_closure (T : lattice) (s : Pred T) :=
  [Pred p : T | forall t : Pred T, s <=p t -> t \In sup_closed T -> p \In t].

End Lat.

Arguments lbot [T].
Arguments sup_closed [T].
Arguments sup_closure [T].
Prenex Implicits sup_closed sup_closure.


Section BasicProperties.
Variable T : lattice.

Lemma sup_mono (s1 s2 : Pred T) : s1 <=p s2 -> sup s1 <== sup s2.
Proof. by move=>H; apply: supM=>y; move/H; apply: supP. Qed.

Lemma supE (s1 s2 : Pred T) : s1 =p s2 -> sup s1 = sup s2.
Proof. by move=>H; apply: poset_asym; apply: supM=>y; move/H; apply: supP. Qed.

(* Knaster-Tarski *)
Lemma tarski_lfp_fixed (f : T -> T) :
        monotone f -> f (tarski_lfp f) = tarski_lfp f.
Proof.
move=>M; suff L: f (tarski_lfp f) <== tarski_lfp f.
- by apply: poset_asym=>//; apply: infP; apply: M L.
by apply: infM=>x L; apply: poset_trans (L); apply: M; apply: infP.
Qed.

Lemma tarski_lfp_least f : forall x : T, f x = x -> tarski_lfp f <== x.
Proof. by move=>x H; apply: infP; rewrite InE /= H. Qed.

Lemma tarski_gfp_fixed (f : T -> T) :
        monotone f -> f (tarski_gfp f) = tarski_gfp f.
Proof.
move=>M; suff L: tarski_gfp f <== f (tarski_gfp f).
- by apply: poset_asym=>//; apply: supP; apply: M L.
by apply: supM=>x L; apply: poset_trans (L) _; apply: M; apply: supP.
Qed.

Lemma tarski_gfp_greatest f : forall x : T, f x = x -> x <== tarski_gfp f.
Proof. by move=>x H; apply: supP; rewrite InE /= H. Qed.

(* closure contains s *)
Lemma sup_clos_sub (s : Pred T) : s <=p sup_closure s.
Proof. by move=>p H1 t H2 H3; apply: H2 H1. Qed.

(* closure is smallest *)
Lemma sup_clos_min (s : Pred T) :
        forall t, s <=p t -> sup_closed t -> sup_closure s <=p t.
Proof. by move=>t H1 H2 p; move/(_ _ H1 H2). Qed.

(* closure is closed *)
Lemma sup_closP (s : Pred T) : sup_closed (sup_closure s).
Proof.
move=>d H1 t H3 H4; move: (sup_clos_min H3 H4)=>{H3} H3.
by apply: H4=>x; move/H1; move/H3.
Qed.

Lemma sup_clos_idemp (s : Pred T) : sup_closed s -> sup_closure s =p s.
Proof. by move=>p; split; [apply: sup_clos_min | apply: sup_clos_sub]. Qed.

Lemma sup_clos_mono (s1 s2 : Pred T) :
        s1 <=p s2 -> sup_closure s1 <=p sup_closure s2.
Proof.
move=>H1; apply: sup_clos_min (@sup_closP s2).
by move=>t /H1; apply: sup_clos_sub.
Qed.

End BasicProperties.

(* lattice constructions *)

Section SubLattice.
Variables (T : lattice) (s : Pred T) (C : sup_closed s).
Local Notation tp := (subPoset s).

Definition sub_sup' (u : Pred tp) : T :=
  sup [Pred x : T | exists y, y \In u /\ x = sval y].

Lemma sub_supX (u : Pred tp) : sub_sup' u \In s.
Proof. by apply: C=>x [][y H][_] ->. Qed.

Definition sub_sup (u : Pred tp) : tp :=
  exist _ (sub_sup' u) (sub_supX u).

Lemma sub_supP (u : Pred tp) (x : tp) : x \In u -> x <== sub_sup u.
Proof. by move=>H; apply: supP; exists x. Qed.

Lemma sub_supM (u : Pred tp) (x : tp) :
        (forall y, y \In u -> y <== x) -> sub_sup u <== x.
Proof. by move=>H; apply: supM=>y [z][H1] ->; apply: H H1. Qed.

Definition subLatticeMixin := LatticeMixin sub_supP sub_supM.
Definition subLattice := Eval hnf in Lattice {x : T | x \In s} subLatticeMixin.

End SubLattice.

(* pairing *)

Section PairLattice.
Variables (A B : lattice).
Local Notation tp := (A * B)%type.

Definition pair_sup (s : Pred tp) : tp :=
            (sup [Pred p | exists f, p = f.1 /\ f \In s],
             sup [Pred p | exists f, p = f.2 /\ f \In s]).

Lemma pair_supP (s : Pred tp) (p : tp) : p \In s -> p <== pair_sup s.
Proof. by move=>H; split; apply: supP; exists p. Qed.

Lemma pair_supM (s : Pred tp) (p : tp) :
        (forall q, q \In s -> q <== p) -> pair_sup s <== p.
Proof. by move=>H; split; apply: supM=>y [f][->]; case/H. Qed.

Definition pairLatticeMixin := LatticeMixin pair_supP pair_supM.
Canonical pairLattice := Eval hnf in Lattice tp pairLatticeMixin.

End PairLattice.

(* functions into a latice form a lattice *)

Section FunLattice.
Variables (A : Type) (B : lattice).
Local Notation tp := (A -> B).

Definition fun_sup (s : Pred tp) : tp :=
  fun x => sup [Pred p | exists f, f \In s /\ p = f x].

Lemma fun_supP (s : Pred tp) (p : tp) : p \In s -> p <== fun_sup s.
Proof. by move=>H x; apply: supP; exists p. Qed.

Lemma fun_supM (s : Pred tp) (p : tp) :
        (forall q, q \In s -> q <== p) -> fun_sup s <== p.
Proof. by move=>H t; apply: supM=>x [f][H1] ->; apply: H. Qed.

Definition funLatticeMixin := LatticeMixin fun_supP fun_supM.
Canonical funLattice := Eval hnf in Lattice tp funLatticeMixin.

End FunLattice.

(* dependent functions into a lattice form a lattice *)

Section DFunLattice.
Variables (A : Type) (B : A -> lattice).
Local Notation tp := (dfunPoset B).

Definition dfun_sup (s : Pred tp) : tp :=
  fun x => sup [Pred p | exists f, f \In s /\ p = f x].

Lemma dfun_supP (s : Pred tp) (p : tp) :
        p \In s -> p <== dfun_sup s.
Proof. by move=>H x; apply: supP; exists p. Qed.

Lemma dfun_supM (s : Pred tp) (p : tp) :
       (forall q, q \In s -> q <== p) -> dfun_sup s <== p.
Proof. by move=>H t; apply: supM=>x [f][H1] ->; apply: H. Qed.

Definition dfunLatticeMixin := LatticeMixin dfun_supP dfun_supM.
Definition dfunLattice := Eval hnf in Lattice (forall x, B x) dfunLatticeMixin.

End DFunLattice.

(* applied sup equals the sup of applications *)

Lemma sup_appE A (B : lattice) (s : Pred (A -> B)) (x : A) :
        sup s x = sup [Pred y : B | exists f, f \In s /\ y = f x].
Proof. by []. Qed.

Lemma sup_dappE A (B : A -> lattice) (s : Pred (dfunLattice B)) (x : A) :
        sup s x = sup [Pred y : B x | exists f, f \In s /\ y = f x].
Proof. by []. Qed.

(* ideal of a lattice forms a lattice *)

Section IdealLattice.
Variables (T : lattice) (P : T).

Definition ideal_sup' (s : Pred (ideal P)) :=
  sup [Pred x | exists p, p \In s /\ id_val p = x].

Lemma ideal_supP' (s : Pred (ideal P)) : ideal_sup' s <== P.
Proof. by apply: supM=>y [[x]] H /= [_] <-. Qed.

Definition ideal_sup (s : Pred (ideal P)) := Ideal (ideal_supP' s).

Lemma ideal_supP (s : Pred (ideal P)) p :
        p \In s -> p <== ideal_sup s.
Proof. by move=>H; apply: supP; exists p. Qed.

Lemma ideal_supM (s : Pred (ideal P)) p :
        (forall q, q \In s -> q <== p) -> ideal_sup s <== p.
Proof. by move=>H; apply: supM=>y [q][H1] <-; apply: H. Qed.

Definition idealLatticeMixin := LatticeMixin ideal_supP ideal_supM.
Canonical idealLattice := Eval hnf in Lattice (ideal P) idealLatticeMixin.

End IdealLattice.

(* Prop is a lattice *)

Section PropLattice.

Definition prop_sup (s : Pred Prop) : Prop := exists p, p \In s /\ p.

Lemma prop_supP (s : Pred Prop) p : p \In s -> p <== prop_sup s.
Proof. by exists p. Qed.

Lemma prop_supM (s : Pred Prop) p :
        (forall q, q \In s -> q <== p) -> prop_sup s <== p.
Proof. by move=>H [r][]; move/H. Qed.

Definition propLatticeMixin := LatticeMixin prop_supP prop_supM.
Canonical propLattice := Eval hnf in Lattice Prop propLatticeMixin.

End PropLattice.

(*
(* Pred is a lattice *)

Section PredLattice.
Variable A : Type.

Definition predLatticeMixin := funLatticeMixin A propLattice.
Canonical predLattice := Eval hnf in Lattice (Pred A) predLatticeMixin.

End PredLattice.
*)

(* monotonicity *)

Lemma id_mono (T : poset) : monotone (@id T).
Proof. by []. Qed.

Arguments id_mono [T].
Prenex Implicits id_mono.

Lemma const_mono (T1 T2 : poset) (y : T2) : monotone (fun x : T1 => y).
Proof. by []. Qed.

Arguments const_mono [T1 T2 y].
Prenex Implicits const_mono.

Lemma comp_mono (T1 T2 T3 : poset) (f1 : T2 -> T1) (f2 : T3 -> T2) :
        monotone f1 -> monotone f2 -> monotone (f1 \o f2).
Proof. by move=>M1 M2 x y H; apply: M1; apply: M2. Qed.

Arguments comp_mono [T1 T2 T3 f1 f2].
Prenex Implicits comp_mono.

Lemma proj1_mono (T1 T2 : poset) : monotone (@fst T1 T2).
Proof. by case=>x1 x2 [y1 y2][]. Qed.

Lemma proj2_mono (T1 T2 : poset) : monotone (@snd T1 T2).
Proof. by case=>x1 x2 [y1 y2][]. Qed.

Arguments proj1_mono [T1 T2].
Arguments proj2_mono [T1 T2].
Prenex Implicits proj1_mono proj2_mono.

Lemma diag_mono (T : poset) : monotone (fun x : T => (x, x)).
Proof. by []. Qed.

Arguments diag_mono [T].
Prenex Implicits diag_mono.

Lemma app_mono A (T : poset) (x : A) : monotone (fun f : A -> T => f x).
Proof. by move=>f1 f2; apply. Qed.

Arguments app_mono [A T].
Prenex Implicits app_mono.

Lemma dapp_mono A (T : A -> poset) (x : A) :
  monotone (fun f : dfunPoset T => f x).
Proof. by move=>f1 f2; apply. Qed.

Arguments dapp_mono [A T].
Prenex Implicits dapp_mono.

Lemma prod_mono (S1 S2 T1 T2 : poset) (f1 : S1 -> T1) (f2 : S2 -> T2) :
        monotone f1 -> monotone f2 -> monotone (f1 \* f2).
Proof.
by move=>M1 M2 [x1] x2 [y1 y2][/= H1 H2]; split; [apply: M1 | apply: M2].
Qed.

Arguments prod_mono [S1 S2 T1 T2 f1 f2].
Prenex Implicits prod_mono.


(**********)
(* Chains *)
(**********)

Section Chains.
Variable T : poset.

Definition chain_axiom (s : Pred T) :=
  (exists d, d \In s) /\
  (forall x y, x \In s -> y \In s -> x <== y \/ y <== x).

Structure chain := Chain {
  pred_of :> Pred T;
  _ : chain_axiom pred_of}.

Canonical chainPredType := @mkPredType T chain pred_of.

End Chains.

Lemma chainE (T : poset) (s1 s2 : chain T) :
        s1 = s2 <-> pred_of s1 =p pred_of s2.
Proof.
split=>[->//|]; move: s1 s2=>[s1 H1][s2 H2] /= E; move: H1 H2.
suff: s1 = s2 by move=>-> H1 H2; congr Chain; apply: pf_irr.
by apply: fext=>x; apply: pext; split; move/E.
Qed.

(* mapping monotone function over a chain *)

Section ImageChain.
Variables (T1 T2 : poset) (s : chain T1) (f : T1 -> T2) (M : monotone f).

Lemma image_chainP :
        chain_axiom [Pred x2 : T2 | exists x1, x2 = f x1 /\ x1 \In s].
Proof.
case: s=>p [[d H1] H2]; split=>[|x y]; first by exists (f d); exists d.
case=>x1 [->] H3 [y1][->] H4; rewrite -!toPredE /= in H3 H4.
by case: (H2 x1 y1 H3 H4)=>L; [left | right]; apply: M L.
Qed.

Definition image_chain := Chain image_chainP.

End ImageChain.

Notation "[ f '^^' s 'by' M ]" := (@image_chain _ _ s f M)
  (at level 0, format "[ f  '^^'  s  'by'  M ]") : form_scope.


(* some chain constructions *)

Section ChainId.
Variables (T : poset) (s : chain T).

Lemma id_chainE (M : monotone id) : [id ^^ s by M] = s.
Proof. by apply/chainE=>x; split; [case=>y [<-]|exists x]. Qed.

End ChainId.


Section ChainConst.
Variables (T1 T2 : poset) (y : T2).

Lemma const_chainP : chain_axiom (Pred1 y).
Proof. by split; [exists y | move=>x1 x2 ->->; left]. Qed.

Definition const_chain := Chain const_chainP.

Lemma const_chainE s : [_ ^^ s by @const_mono T1 T2 y] = const_chain.
Proof.
apply/chainE=>z1; split; first by case=>z2 [->].
by case: s=>s [[d] H1] H2 <-; exists d.
Qed.

End ChainConst.


Section ChainCompose.
Variables (T1 T2 T3 : poset) (f1 : T2 -> T1) (f2 : T3 -> T2).
Variables (s : chain T3) (M1 : monotone f1) (M2 : monotone f2).

Lemma comp_chainE :
        [f1 ^^ [f2 ^^ s by M2] by M1] = [f1 \o f2 ^^ s by comp_mono M1 M2].
Proof.
apply/chainE=>x1; split; first by case=>x2 [->][x3][->]; exists x3.
by case=>x3 [->]; exists (f2 x3); split=>//; exists x3.
Qed.

End ChainCompose.

(* projections out of a chain *)

Section ProjChain.
Variables (T1 T2 : poset) (s : chain [poset of T1 * T2]).

Definition proj1_chain := [@fst _ _ ^^ s by proj1_mono].
Definition proj2_chain := [@snd _ _ ^^ s by proj2_mono].

End ProjChain.


(* diagonal chain *)

Section DiagChain.
Variable (T : poset) (s : chain T).

Definition diag_chain := [_ ^^ s by @diag_mono T].

Lemma proj1_diagE : proj1_chain diag_chain = s.
Proof. by rewrite /proj1_chain /diag_chain comp_chainE id_chainE. Qed.

Lemma proj2_diagE : proj2_chain diag_chain = s.
Proof. by rewrite /proj2_chain /diag_chain comp_chainE id_chainE. Qed.

End DiagChain.


(* applying functions from a chain of functions *)

Section AppChain.
Variables (A : Type) (T : poset) (s : chain [poset of A -> T]).

Definition app_chain x := [_ ^^ s by app_mono x].

End AppChain.


(* ditto for dependent functions *)

Section DAppChain.
Variables (A : Type) (T : A -> poset) (s : chain (dfunPoset T)).

Definition dapp_chain x := [_ ^^ s by dapp_mono x].

End DAppChain.

(* pairing chain applications *)

Section ProdChain.
Variables (S1 S2 T1 T2 : poset) (f1 : S1 -> T1) (f2 : S2 -> T2).
Variables (M1 : monotone f1) (M2 : monotone f2).
Variable (s : chain [poset of S1 * S2]).

Definition prod_chain := [f1 \* f2 ^^ s by prod_mono M1 M2].

Lemma proj1_prodE : proj1_chain prod_chain = [f1 ^^ proj1_chain s by M1].
Proof.
rewrite /proj1_chain /prod_chain !comp_chainE !/comp /=.
by apply/chainE.
Qed.

Lemma proj2_prodE : proj2_chain prod_chain = [f2 ^^ proj2_chain s by M2].
Proof.
rewrite /proj2_chain /prod_chain !comp_chainE !/comp /=.
by apply/chainE.
Qed.

End ProdChain.



(*********)
(* CPO's *)
(*********)

Module CPO.

Section RawMixin.

Record mixin_of (T : poset) := Mixin {
  mx_bot : T;
  mx_lim : chain T -> T;
  _ : forall x, mx_bot <== x;
  _ : forall (s : chain T) x, x \In s -> x <== mx_lim s;
  _ : forall (s : chain T) x,
        (forall y, y \In s -> y <== x) -> mx_lim s <== x}.

End RawMixin.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : Poset.class_of T;
  mixin : mixin_of (Poset.Pack base T)}.

Local Coercion base : class_of >-> Poset.class_of.

Structure type : Type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (Poset.Pack b0 T)) :=
  fun m & phant_id m0 m => Pack (@Class T b0 m) T.

Definition poset := Poset.Pack class cT.
Definition lim (s : chain poset) : cT := mx_lim (mixin class) s.
Definition bot : cT := mx_bot (mixin class).

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Poset.class_of.
Coercion sort : type >-> Sortclass.
Coercion poset : type >-> Poset.type.
Canonical Structure poset.

Notation cpo := type.
Notation CPOMixin := Mixin.
Notation CPO T m := (@pack T _ _ m id).

Notation "[ 'cpo' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'cpo'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'cpo' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'cpo'  'of'  T ]") : form_scope.

Arguments CPO.bot [cT].
Arguments CPO.lim [cT].
Prenex Implicits CPO.lim.
Prenex Implicits CPO.bot.
Notation lim := CPO.lim.
Notation bot := CPO.bot.

Section Laws.
Variable D : cpo.

Lemma botP (x : D) : bot <== x.
Proof. by case: D x=>S [[p]][/= b l H1 *]; apply: H1. Qed.

Lemma limP (s : chain D) x : x \In s -> x <== lim s.
Proof. by case: D s x=>S [[p]][/= b l H1 H2 *]; apply: (H2). Qed.

Lemma limM (s : chain D) x : (forall y, y \In s -> y <== x) -> lim s <== x.
Proof. by case: D s x=>S [[p]][/= b l H1 H2 H3 *]; apply: (H3). Qed.

End Laws.

End Exports.

End CPO.

Export CPO.Exports.

Hint Resolve botP.

(* common chain constructions *)

(* adding bot to a chain *)

Section LiftChain.
Variable (D : cpo) (s : chain D).

Hint Resolve botP.

Lemma lift_chainP : chain_axiom [Pred x : D | x = bot \/ x \In s].
Proof.
case: s=>p [[d H1] H2] /=; split=>[|x y]; first by exists d; right.
by case=>[->|H3][->|H4]; auto.
Qed.

Definition lift_chain := Chain lift_chainP.

End LiftChain.

(****************************)
(* common cpo constructions *)
(****************************)

(* pairs *)

Section PairCPO.
Variables (A B : cpo).
Local Notation tp := [poset of A * B].

Definition pair_bot : tp := (bot, bot).

Definition pair_lim (s : chain tp) : tp :=
  (lim (proj1_chain s), lim (proj2_chain s)).

Lemma pair_botP x : pair_leq pair_bot x.
Proof. by split; apply: botP. Qed.

Lemma pair_limP (s : chain tp) x : x \In s -> x <== pair_lim s.
Proof. by split; apply: limP; exists x. Qed.

Lemma pair_limM (s : chain tp) x :
        (forall y, y \In s -> y <== x) -> pair_lim s <== x.
Proof. by split; apply: limM=>y [z][->]; case/H. Qed.

Definition pairCPOMixin := CPOMixin pair_botP pair_limP pair_limM.
Canonical pairCPO := Eval hnf in CPO (A * B) pairCPOMixin.

End PairCPO.

(* functions *)

Section FunCPO.
Variable (A : Type) (B : cpo).
Local Notation tp := [poset of A -> B].

Definition fun_bot : tp := fun x => bot.

Definition fun_lim (s : chain tp) : tp :=
  fun x => lim (app_chain s x).

Lemma fun_botP x : fun_leq fun_bot x.
Proof. by move=>y; apply: botP. Qed.

Lemma fun_limP (s : chain tp) x : x \In s -> x <== fun_lim s.
Proof. by move=>H t; apply: limP; exists x. Qed.

Lemma fun_limM (s : chain tp) x :
        (forall y, y \In s -> y <== x) -> fun_lim s <== x.
Proof. by move=>H1 t; apply: limM=>y [f][->] H2; apply: H1. Qed.

Definition funCPOMixin := CPOMixin fun_botP fun_limP fun_limM.
Canonical funCPO := Eval hnf in CPO (A -> B) funCPOMixin.

End FunCPO.

(* dependent functions *)

Section DFunCPO.
Variable (A : Type) (B : A -> cpo).
Local Notation tp := (dfunPoset B).

Definition dfun_bot : tp := fun x => bot.

Definition dfun_lim (s : chain tp) : tp :=
  fun x => lim (dapp_chain s x).

Lemma dfun_botP x : dfun_bot <== x.
Proof. by move=>y; apply: botP. Qed.

Lemma dfun_limP (s : chain tp) x : x \In s -> x <== dfun_lim s.
Proof. by move=>H t; apply: limP; exists x. Qed.

Lemma dfun_limM (s : chain tp) x :
        (forall y, y \In s -> y <== x) -> dfun_lim s <== x.
Proof. by move=>H1 t; apply: limM=>y [f][->] H2; apply: H1. Qed.

Definition dfunCPOMixin := CPOMixin dfun_botP dfun_limP dfun_limM.
Definition dfunCPO := Eval hnf in CPO (forall x, B x) dfunCPOMixin.

End DFunCPO.

(* Prop *)

Section PropCPO.
Local Notation tp := [poset of Prop].

Definition prop_bot : tp := False.

Definition prop_lim (s : chain tp) : tp := exists p, p \In s /\ p.

Lemma prop_botP x : prop_bot <== x.
Proof. by []. Qed.

Lemma prop_limP (s : chain tp) p : p \In s -> p <== prop_lim s.
Proof. by exists p. Qed.

Lemma prop_limM (s : chain tp) p :
        (forall q, q \In s -> q <== p) -> prop_lim s <== p.
Proof. by move=>H [r][]; move/H. Qed.

Definition propCPOMixin := CPOMixin prop_botP prop_limP prop_limM.
Canonical propCPO := Eval hnf in CPO Prop propCPOMixin.

End PropCPO.

(* Pred *)

Section PredCPO.
Variable A : Type.

Definition predCPOMixin := funCPOMixin A propCPO.
Canonical predCPO := Eval hnf in CPO (Pred A) predCPOMixin.

End PredCPO.

(* every complete lattice is a cpo *)

Section LatticeCPO.
Variable A : lattice.
Local Notation tp := (Lattice.poset A).

Definition lat_bot : tp := lbot.

Definition lat_lim (s : chain tp) : tp := sup s.

Lemma lat_botP x : lat_bot <== x.
Proof. by apply: supM. Qed.

Lemma lat_limP (s : chain tp) x : x \In s -> x <== lat_lim s.
Proof. by apply: supP. Qed.

Lemma lat_limM (s : chain tp) x :
        (forall y, y \In s -> y <== x) -> lat_lim s <== x.
Proof. by apply: supM. Qed.

Definition latCPOMixin := CPOMixin lat_botP lat_limP lat_limM.
Definition latCPO := Eval hnf in CPO tp latCPOMixin.

End LatticeCPO.

(* sub-CPO's *)

(* every chain-closed subset of a cpo is a cpo *)

Section AdmissibleClosure.
Variable T : cpo.

Definition chain_closed :=
  [Pred s : Pred T |
     bot \In s /\ forall d : chain T, d <=p s -> lim d \In s].

(* admissible closure of s is the smallest closed set containing s *)
(* basically extends s to include the sups of chains *)
Definition chain_closure (s : Pred T) :=
  [Pred p : T | forall t : Pred T, s <=p t -> chain_closed t -> p \In t].

(* admissible closure contains s *)
Lemma chain_clos_sub (s : Pred T) : s <=p chain_closure s.
Proof. by move=>p H1 t H2 H3; apply: H2 H1. Qed.

(* admissible closure is smallest *)
Lemma chain_clos_min (s : Pred T) t :
        s <=p t -> chain_closed t -> chain_closure s <=p t.
Proof. by move=>H1 H2 p; move/(_ _ H1 H2). Qed.

(* admissible closure is closed *)
Lemma chain_closP (s : Pred T) : chain_closed (chain_closure s).
Proof.
split; first by move=>t _ [].
move=>d H1 t H3 H4; move: (chain_clos_min H3 H4)=>{H3} H3.
by case: H4=>_; apply=>// x; move/H1; move/H3.
Qed.

Lemma chain_clos_idemp (s : Pred T) :
        chain_closed s -> chain_closure s =p s.
Proof.
move=>p; split; last by apply: chain_clos_sub.
by apply: chain_clos_min=>//; apply: chain_closP.
Qed.

Lemma chain_clos_mono (s1 s2 : Pred T) :
        s1 <=p s2 -> chain_closure s1 <=p chain_closure s2.
Proof.
move=>H1; apply: chain_clos_min (chain_closP s2)=>p H2.
by apply: chain_clos_sub; apply: H1.
Qed.

(* intersection of admissible sets is admissible *)
Lemma chain_closI (s1 s2 : Pred T) :
       chain_closed s1 -> chain_closed s2 -> chain_closed (PredI s1 s2).
Proof.
move=>[H1 S1][H2 S2]; split=>// d H.
by split; [apply: S1 | apply: S2]=>// x; case/H.
Qed.

End AdmissibleClosure.

Arguments chain_closed [T].
Prenex Implicits chain_closed.

(* diagonal of an admissible set of pairs is admissible *)
Lemma chain_clos_diag (T : cpo) (s : Pred (T * T)) :
        chain_closed s -> chain_closed [Pred t : T | (t, t) \In s].
Proof.
move=>[B H1]; split=>// d H2.
rewrite InE /= -{1}(proj1_diagE d) -{2}(proj2_diagE d).
by apply: H1; case=>x1 x2 [x][[<- <-]]; apply: H2.
Qed.

Section SubCPO.
Variables (D : cpo) (s : Pred D) (C : chain_closed s).
Local Notation tp := (subPoset s).

Definition sub_bot := exist _ (@bot D) (proj1 C).

Lemma sub_botP (x : tp) : sval sub_bot <== sval x.
Proof. by apply: botP. Qed.

Lemma sval_mono : monotone (sval : tp -> D).
Proof. by move=>[x1 H1][x2 H2]; apply. Qed.

Lemma sub_limX (u : chain tp) : lim [sval ^^ u by sval_mono] \In s.
Proof. by case: C u=>P H u; apply: (H)=>t [[y]] H1 [->]. Qed.

Definition sub_lim (u : chain tp) : tp :=
  exist _ (lim [sval ^^ u by sval_mono]) (sub_limX u).

Lemma sub_limP (u : chain tp) x : x \In u -> x <== sub_lim u.
Proof. by move=>H; apply: limP; exists x. Qed.

Lemma sub_limM (u : chain tp) x :
        (forall y, y \In u -> y <== x) -> sub_lim u <== x.
Proof. by move=>H; apply: limM=>y [z][->]; apply: H. Qed.

Definition subCPOMixin := CPOMixin sub_botP sub_limP sub_limM.
Definition subCPO := Eval hnf in CPO {x : D | x \In s} subCPOMixin.

End SubCPO.

(***********************************************)
(* Continuity and Kleene's fixed point theorem *)
(***********************************************)

Lemma lim_mono (D : cpo) (s1 s2 : chain D) :
        s1 <=p s2 -> lim s1 <== lim s2.
Proof. by move=>H; apply: limM=>y; move/H; apply: limP. Qed.

Lemma limE (D : cpo) (s1 s2 : chain D) :
        s1 =p s2 -> lim s1 = lim s2.
Proof. by move=>H; apply: poset_asym; apply: lim_mono=>x; rewrite H. Qed.

Lemma lim_liftE (D : cpo) (s : chain D) :
        lim s = lim (lift_chain s).
Proof.
apply: poset_asym; apply: limM=>y H; first by apply: limP; right.
by case: H; [move=>-> | apply: limP].
Qed.

(* applied lim equals the lim of applications *)
(* ie., part of continuity of application *)
(* but is so often used, I give it a name *)

Lemma lim_appE A (D : cpo) (s : chain [cpo of A -> D]) (x : A) :
        lim s x = lim (app_chain s x).
Proof. by []. Qed.

Lemma lim_dappE A (D : A -> cpo) (s : chain (dfunCPO D)) (x : A) :
        lim s x = lim (dapp_chain s x).
Proof. by []. Qed.

Section Continuity.
Variables (D1 D2 : cpo) (f : D1 -> D2).

Definition continuous :=
  exists M : monotone f,
  forall s : chain D1, f (lim s) = lim [f ^^ s by M].

Lemma cont_mono : continuous -> monotone f.
Proof. by case. Qed.

Lemma contE (s : chain D1) (C : continuous) :
       f (lim s) = lim [f ^^ s by cont_mono C].
Proof.
case: C=>M E; rewrite E; congr (lim (image_chain _ _)).
exact: pf_irr.
Qed.

End Continuity.


Module Kleene.

(* just for this proof, we want that nat is a poset under <= *)
(* in other scopes, we'll use the equality as ordering *)
Section NatPoset.

Lemma nat_refl x : x <= x. Proof. by []. Qed.

Lemma nat_asym x y : x <= y -> y <= x -> x = y.
Proof. by move=>H1 H2; apply: anti_leq; rewrite H1 H2. Qed.

Lemma nat_trans x y z : x <= y -> y <= z -> x <= z.
Proof. by apply: leq_trans. Qed.

Definition natPosetMixin := PosetMixin nat_refl nat_asym nat_trans.
Canonical natPoset := Eval hnf in Poset nat natPosetMixin.

End NatPoset.

Section NatChain.

Lemma nat_chain_axiom : chain_axiom (@PredT nat).
Proof.
split=>[|x y _ _]; first by exists 0.
rewrite /Poset.leq /= [y <= x]leq_eqVlt.
by case: leqP; [left | rewrite orbT; right].
Qed.

Definition nat_chain := Chain nat_chain_axiom.

End NatChain.

Section Kleene.
Variables (D : cpo) (f : D -> D) (C : continuous f).

Fixpoint pow m := if m is n.+1 then f (pow n) else bot.

Lemma pow_mono : monotone pow.
Proof.
move=>m n; elim: n m=>[|n IH] m /=; first by case: m.
rewrite {1}/Poset.leq /= leq_eqVlt ltnS.
case/orP; first by move/eqP=>->.
move/IH=>{IH} H; apply: poset_trans H _.
by elim: n=>[|n IH] //=; apply: cont_mono IH.
Qed.

Definition pow_chain := [pow ^^ nat_chain by pow_mono].

Lemma reindex : pow_chain =p lift_chain [f ^^ pow_chain by cont_mono C].
Proof.
move=>x; split.
- case; case=>[|n][->] /=; first by left.
  by right; exists (pow n); split=>//; exists n.
case=>/=; first by move=>->; exists 0.
by case=>y [->][n][->]; exists n.+1.
Qed.

Definition kleene_lfp := lim pow_chain.

Lemma kleene_lfp_fixed : f kleene_lfp = kleene_lfp.
Proof. by rewrite (@contE _ _ f) lim_liftE; apply: limE; rewrite reindex. Qed.

Lemma kleene_lfp_least : forall x, f x = x -> kleene_lfp <== x.
Proof.
move=>x H; apply: limM=>y [n][->] _.
by elim: n=>[|n IH] //=; rewrite -H; apply: cont_mono IH.
Qed.

End Kleene.

Module Exports.
Notation kleene_lfp := kleene_lfp.
Notation kleene_lfp_fixed := kleene_lfp_fixed.
Notation kleene_lfp_least := kleene_lfp_least.
End Exports.

End Kleene.

Export Kleene.Exports.

(**********************************)
(* Continuity of common functions *)
(**********************************)

Lemma id_cont (D : cpo) : continuous (@id D).
Proof. by exists id_mono; move=>d; rewrite id_chainE. Qed.

Arguments id_cont [D].
Prenex Implicits id_cont.

Lemma const_cont (D1 D2 : cpo) (y : D2) : continuous (fun x : D1 => y).
Proof.
exists const_mono; move=>s; apply: poset_asym.
- by apply: limP; case: s=>[p][[d H1] H2]; exists d.
by apply: limM=>_ [x][->].
Qed.

Arguments const_cont [D1 D2 y].
Prenex Implicits const_cont.

Lemma comp_cont (D1 D2 D3 : cpo) (f1 : D2 -> D1) (f2 : D3 -> D2) :
        continuous f1 -> continuous f2 -> continuous (f1 \o f2).
Proof.
case=>M1 H1 [M2 H2]; exists (comp_mono M1 M2); move=>d.
by rewrite /= H2 H1 comp_chainE.
Qed.

Arguments comp_cont [D1 D2 D3 f1 f2].
Prenex Implicits comp_cont.

Lemma proj1_cont (D1 D2 : cpo) : continuous (@fst D1 D2).
Proof. by exists proj1_mono. Qed.

Lemma proj2_cont (D1 D2 : cpo) : continuous (@snd D1 D2).
Proof. by exists proj2_mono. Qed.

Arguments proj1_cont [D1 D2].
Arguments proj2_cont [D1 D2].
Prenex Implicits proj1_cont proj2_cont.

Lemma diag_cont (D : cpo) : continuous (fun x : D => (x, x)).
Proof.
exists diag_mono=>d; apply: poset_asym;
by split=>/=; [rewrite proj1_diagE | rewrite proj2_diagE].
Qed.

Arguments diag_cont [D].
Prenex Implicits diag_cont.

Lemma app_cont A (D : cpo) x : continuous (fun f : A -> D => f x).
Proof. by exists (app_mono x). Qed.

Lemma dapp_cont A (D : A -> cpo) x : continuous (fun f : dfunCPO D => f x).
Proof. by exists (dapp_mono x). Qed.

Arguments app_cont [A D].
Arguments dapp_cont [A D].
Prenex Implicits app_cont dapp_cont.

Lemma prod_cont (S1 S2 T1 T2 : cpo) (f1 : S1 -> T1) (f2 : S2 -> T2) :
        continuous f1 -> continuous f2 -> continuous (f1 \* f2).
Proof.
case=>M1 H1 [M2 H2]; exists (prod_mono M1 M2)=>d; apply: poset_asym;
by (split=>/=; [rewrite proj1_prodE H1 | rewrite proj2_prodE H2]).
Qed.

Arguments prod_cont [S1 S2 T1 T2 f1 f2].
Prenex Implicits prod_cont.

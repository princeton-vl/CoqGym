Set Implicit Arguments.
Global Set Asymmetric Patterns.

Require Import Relations.
Require Export Basics.
Require Import Setoid.

Arguments eq {A}.
Arguments fst {A B}.

Hint Unfold compose.

Definition proj1_conj (A B: Prop) (c: A /\ B): A :=
  match c with conj x _ => x end.

Definition proj2_conj (A B: Prop) (c: A /\ B): B :=
  match c with conj _ x => x end.

Lemma eq_trans (X: Set) (a b c: X): a = b -> b = c -> a = c.
Proof. intros. subst. reflexivity. Qed.

Definition cmp_cmp (x y: comparison): { x = y } + { x <> y } :=
  (* instead of being lazy with tactics, let's try to make as short a term as possible *)
  match x, y return { x = y } + { x <> y } with
  | Lt, Lt | Gt, Gt | Eq, Eq => left _ (refl_equal _)
  | a, b => right _ (
      match a, b
      return match a, b with Lt, Lt | Gt, Gt | Eq, Eq => True | _, _ => ~(a = b) end with
      | Lt, Lt | Gt, Gt | Eq, Eq => I
      | Lt, _ => fun q => match q in _ = Lt with refl_equal => I end
      | Gt, _ => fun q => match q in _ = Gt with refl_equal => I end
      | Eq, _ => fun q => match q in _ = Eq with refl_equal => I end
      end
    )
  end. (* todo: derive this using the new equality Schemes *)

Fixpoint nat_cmp (x y: nat) {struct x}: comparison :=
  match x, y with
  | 0, 0 => Eq
  | 0, S _ => Lt
  | S _, 0 => Gt
  | S x', S y' => nat_cmp x' y'
  end.

Ltac cset e := let v := fresh in set (v := e); clearbody v.
Ltac cset' e := let v := fresh in set (v := e) in *; clearbody v.

Ltac extro x := generalize x; clear x.

Definition unsum_bool (A B: Prop) (sb: sumbool A B): bool := if sb then true else false.

Definition decision (P: Prop): Set := { P } + { ~ P }.
Definition predDecider (T: Set) (P: T -> Prop): Type := forall t, decision (P t).

Lemma negb_inv (b b': bool): negb b = negb b' -> b = b'.
Proof. destruct b; destruct b'; auto. Qed.

Lemma negb_negb (b: bool): negb (negb b) = b.
Proof. destruct b; auto. Qed.

Definition id {X} (x: X): X := x.

(* extensional equality on simple functions *)

Definition ext_eq {A B: Type} (f g: A -> B): Prop := forall x, f x = g x.

Lemma ext_eq_trans: forall A B, transitive _ (@ext_eq A B).
Proof. intros. unfold transitive. intros. intro. rewrite H. rewrite H0. reflexivity. Qed.

Lemma ext_eq_refl: forall A B, reflexive _ (@ext_eq A B).
Proof. intros. unfold reflexive. intros. intro. reflexivity. Qed.

Lemma ext_eq_sym: forall A B, symmetric _ (@ext_eq A B).
Proof. intros. unfold symmetric. intros. intro. rewrite H. reflexivity. Qed.

Add Parametric Relation X Y: (X -> Y) (@ext_eq X Y)
  reflexivity proved by (@ext_eq_refl X Y)
  symmetry proved by (@ext_eq_sym X Y)
  transitivity proved by (@ext_eq_trans X Y)
    as ext_eq_rel.

Lemma ext_eq_rw (A B: Type) (f g: A -> B): ext_eq f g -> forall x, f x = g x.
Proof. intros. apply H. Qed.

(* function composition *)

Notation " g ∘ f " := (compose g f) (at level 40, left associativity).

Lemma comp_apply (A B C: Set) (f: B -> C) (g: A -> B) (x: A): (f ∘ g) x = f (g x).
Proof. reflexivity. Qed.

Lemma comp_ass (A B C D: Set) (f: A -> B) (g: B -> C) (h: C -> D): h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. reflexivity. Qed.

Definition compose_lunit A B (f: A -> B): ext_eq (@id B ∘ f) f.
Proof. intros. intro. reflexivity. Qed.

Definition compose_runit A B (f: A -> B): ext_eq (f ∘ @id A) f.
Proof. intros. intro. reflexivity. Qed.

Add Parametric Morphism (X Y Z: Set): (@compose X Y Z) with signature (@ext_eq Y Z) ==> (@ext_eq X Y) ==> (@ext_eq X Z) as compose_ext_eq_morph.
Proof.
  intros.
  intro.
  unfold compose.
  unfold ext_eq in *.
  rewrite H0.
  rewrite H.
  reflexivity.
Qed.

Definition map_snd (A B: Set) (f: A -> B) (C: Set) (p: C * A): C * B := (fst p, f (snd p)).

Lemma fst_map_snd (A B: Set) (f: A -> B) (C: Set) (p: C * A): fst (map_snd f p) = fst p.
Proof. destruct p. auto. Qed.

Definition on {A B: Type} {C: B -> B -> Type} (g: A -> B) (f: forall b b', C b b') (x y: A): C (g x) (g y) := f (g x) (g y).

Definition unsumbool {A B}: { A } + { B } -> bool := fun x => if x then true else false.

Definition dep_flip {A B: Type} {C: A -> B -> Type} (f: forall a b, C a b) (b: B) (a: A): C a b := f a b.

Coercion conj_prod (A B: Prop): A /\ B -> A * B.
  firstorder.
Qed.

Definition uncurry A B C (f: A -> B -> C) (ab: A * B): C := f (fst ab) (snd ab).

Section well_founded_pairs.

  Variables (A B: Type)
    (Ra: relation A) (Rb: relation B).

  Inductive pair_rel: relation (A * B) :=
    | pair_rel_l a a' b: Ra a a' -> pair_rel (a, b) (a', b)
    | pair_rel_r a b b': Rb b b' -> pair_rel (a, b) (a, b').

  Fixpoint acc_pairs a (Aa: Acc Ra a) {struct Aa}: forall b (Ab: Acc Rb b), Acc pair_rel (a, b) :=
    fix G b (Ab: Acc Rb b) {struct Ab}: Acc pair_rel _ := @Acc_intro _ pair_rel _
      match Aa, Ab with
      | Acc_intro x, Acc_intro y =>  fun z (za: pair_rel z (a, b)) =>
          match za in pair_rel z ab return
            (forall (p: A) (q: Ra p (fst ab)), Acc pair_rel (p, (snd ab))) -> (forall p, Rb p (snd ab) -> Acc pair_rel (fst ab, p)) -> Acc pair_rel z with
          | pair_rel_l v w c d => fun fr gr => fr _ d
          | pair_rel_r v w c d => fun fr gr => gr _ d
          end
          (fun (p: A) (q: Ra p (fst (a, b))) => @acc_pairs p (x p q) b Ab : Acc pair_rel (p, b))
          (fun (p: B) (q: Rb p (snd (a, b))) => @G p (y p q): Acc pair_rel (a, p))
      end.

   Lemma well_founded_pairs (Wa: well_founded Ra) (Wb: well_founded Rb): well_founded pair_rel.
     unfold well_founded.
     intros.
     destruct a.
     apply (acc_pairs (Wa a) (Wb b)).
   Qed.

End well_founded_pairs.

Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.Injection.

Fixpoint pmap_lookup' (ts : pmap Type) (p : positive) : option Type :=
  match p with
    | xH => pmap_here ts
    | xI p => pmap_lookup' (pmap_right ts) p
    | xO p => pmap_lookup' (pmap_left ts) p
  end.

Record OneOf (ts : pmap Type) : Type := mkOneOf
{ index : positive
; value : match pmap_lookup' ts index with
            | None => Empty_set
            | Some T => T
          end
}.

Definition Into {ts} {T : Type} (n : positive) (pf : pmap_lookup' ts n = Some T)
: T -> OneOf ts :=
  match pf in _ = X return match X with
                           | Some T => T
                           | None => Empty_set
                           end -> OneOf ts
  with
  | eq_refl => @mkOneOf ts n
  end.

Fixpoint asNth' {ts : pmap Type} (p p' : positive)
: match pmap_lookup' ts p' with
    | None => Empty_set
    | Some T => T
  end -> option (match pmap_lookup' ts p with
                   | None => Empty_set
                   | Some T => T
                 end) :=
  match p as p , p' as p'
        return match pmap_lookup' ts p' with
                 | None => Empty_set
                 | Some T => T
               end -> option (match pmap_lookup' ts p with
                                | None => Empty_set
                                | Some T => T
                              end)
  with
    | xH , xH => Some
    | xI p , xI p' => asNth' p p'
    | xO p , xO p' => asNth' p p'
    | _ , _ => fun _ => None
  end.

Definition asNth {ts : pmap Type} (p : positive) (oe : OneOf ts)
: option (match pmap_lookup' ts p with
            | None => Empty_set
            | Some T => T
          end) :=
  @asNth' ts p oe.(index ts) oe.(value ts).

Definition OutOf {ts} {T : Type} (n : positive)
           (pf : pmap_lookup' ts n = Some T)
: OneOf ts -> option T :=
  match pf in _ = X return OneOf ts -> option match X with
                                              | None => Empty_set:Type
                                              | Some T => T
                                              end
  with
  | eq_refl => @asNth ts n
  end.

Lemma asNth'_get_lookup : forall p ts v, asNth' (ts:=ts) p p v = Some v.
Proof.
  induction p; simpl; intros; auto.
Qed.

Theorem Outof_Into : forall ts T p pf v,
    @OutOf ts T p pf (@Into ts T p pf v) = Some v.
Proof using.
  unfold OutOf, Into.
  intros.
  repeat rewrite (eq_Arr_eq pf).
  repeat rewrite (eq_Const_eq pf).
  repeat rewrite (eq_Const_eq (eq_sym pf)).
  unfold asNth. simpl.
  rewrite asNth'_get_lookup.
  { generalize dependent (pmap_lookup' ts p).
    intros. subst. reflexivity. }
Qed.

Theorem asNth_eq
: forall ts p oe v,
    @asNth ts p oe = Some v ->
    oe = {| index := p ; value := v |}.
Proof.
  unfold asNth.
  destruct oe; simpl.
  revert value0. revert index0. revert ts.
  induction p; destruct index0; simpl; intros;
  solve [ congruence | eapply IHp in H; inversion H; clear H IHp; subst; auto ].
Qed.

Section elim.
  Context {T : Type}.
  Variable F : T -> Type.

  Fixpoint pmap_elim (R : Type) (ts : pmap T) : Type :=
    match ts with
      | Empty => R
      | Branch None l r => pmap_elim (pmap_elim R r) l
      | Branch (Some x) l r => F x -> pmap_elim (pmap_elim R r) l
    end.
End elim.

Fixpoint pmap_lookup'_Empty (p : positive) : pmap_lookup' Empty p = None :=
  match p with
    | xH => eq_refl
    | xO p => pmap_lookup'_Empty p
    | xI p => pmap_lookup'_Empty p
  end.

Definition OneOf_Empty (f : OneOf Empty) : False.
Proof.
  destruct f. rewrite pmap_lookup'_Empty in *.
  intuition congruence.
Defined.

Lemma pmap_lookup'_eq p m : pmap_lookup p m = pmap_lookup' m p.
Proof.
  generalize dependent m. induction p; intuition.
  simpl. destruct m. simpl. rewrite pmap_lookup'_Empty. reflexivity.
  simpl in *. apply IHp.
  simpl in *. destruct m. simpl. rewrite pmap_lookup'_Empty. reflexivity.
  simpl. apply IHp.
Defined.

Global Instance Injective_OneOf m i1 i2 v1 v2
: Injective (@eq (OneOf m)
                 {| index := i1 ; value := v1 |}
                 {| index := i2 ; value := v2 |}) :=
{ result := exists pf : i2 = i1,
    v1 = match pf in _ = T return match pmap_lookup' m T with
                                  | None => Empty_set
                                  | Some T => T
                                  end with
         | eq_refl => v2
         end
; injection :=
    fun H =>
      match H in _ = h
            return exists pf : index _ h = i1 ,
          v1 = match
            pf in (_ = T)
            return
            match pmap_lookup' m T with
            | Some T0 => T0
            | None => Empty_set
            end
          with
          | eq_refl => value _ h
          end
      with
      | eq_refl => @ex_intro _ _ eq_refl eq_refl
      end
}.

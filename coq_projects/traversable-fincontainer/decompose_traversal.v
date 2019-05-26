(* Copyright 2012 Google Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Authors: Russell O'Connor
 *)

Require Vector.
Require Import Arith List Eqdep_dec.
Require Import FunctionalExtensionality.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma Vector_map_id n a (f : a -> a) (v : Vector.t a n) :
  (forall x, f x = x) -> (Vector.map f v) = v.
Proof.
intros H.
induction v.
  reflexivity.
simpl.
rewrite IHv, H.
reflexivity.
Qed.

Lemma Vector_map_compose n a b c (g : b -> c) (f : a -> b) (h : a -> c) (v : Vector.t a n) :
  (forall x, g (f x) = h x) -> Vector.map g (Vector.map f v) = Vector.map h v.
Proof.
intros H.
induction v.
  reflexivity.
simpl.
rewrite IHv, H.
reflexivity.
Qed.

Lemma Vector_map_append n m a b (f : a -> b) (v1 : Vector.t a n) (v2 : Vector.t a m) :
  Vector.map f (Vector.append v1 v2) = Vector.append (Vector.map f v1) (Vector.map f v2).
Proof.
induction v1.
  reflexivity.
simpl.
rewrite IHv1.
reflexivity.
Qed.

Lemma append_inj a n m (v1 v1' : Vector.t a n) (v2 v2' : Vector.t a m) : 
  Vector.append v1 v2 = Vector.append v1' v2' -> v1 = v1' /\ v2 = v2'.
Proof.
revert n v1 v1'.
apply (Vector.rect2 (fun n v1 v1' => Vector.append v1 v2 = Vector.append v1' v2' -> v1 = v1' /\ v2 = v2')).
  intros H; split.
    reflexivity.
  assumption.
simpl.
intros n t t' IH h h' H.
injection H.
intros dep1 Hh.
rewrite Hh; clear Hh.
destruct IH as [IH1 IH2].
  refine (inj_pair2_eq_dec _ _ _ _ _ _ dep1).
  decide equality.
rewrite IH1.
split.
  reflexivity.
assumption.
Qed.  

Lemma append_assoc a n m p (v1 : Vector.t a n) (v2 : Vector.t a m) (v3 : Vector.t a p)
  (e : n + (m + p) = n + m + p) : 
  eq_rect _ _ (Vector.append v1 (Vector.append v2 v3)) _ e = Vector.append (Vector.append v1 v2) v3.
Proof.
induction v1; simpl in *.
  pattern e.
  apply K_dec_set.
    decide equality.
  reflexivity.
injection e.
intros e'.
rewrite <- (IHv1 e').
clear IHv1.
revert e.
generalize e'.
rewrite <- e'.
clear e'; intros e'.
pattern e'.
apply K_dec_set.
  decide equality.
apply K_dec_set.
  decide equality.
reflexivity.
Qed.

Lemma to_list_eq A n m (e: n = m) : forall (v1 : Vector.t A n) (v2 : Vector.t A m),
   Vector.to_list v1 = Vector.to_list v2 -> eq_rect _ (Vector.t A) v1 _ e = v2.
Proof.
rewrite e. (* magical *)
simpl.
clear n e.
revert m.
apply (Vector.rect2 (fun m (v1 v2 : Vector.t A m) => Vector.to_list v1 = Vector.to_list v2 -> v1 = v2)).
  reflexivity.
intros n v1 v2 IH a b H.
injection H; intros H1 H2.
rewrite IH.
  rewrite H2.
  reflexivity.
assumption.
Qed.

Record KleeneStore i j a := kleeneStore
 { dim : nat
 ; peek : Vector.t j dim -> a
 ; pos : Vector.t i dim
 }.

Definition extract i a (s : KleeneStore i i a) : a :=
  peek (pos s).

Definition KSmap i j a b (f : a -> b) (s : KleeneStore i j a) : KleeneStore i j b :=
  kleeneStore (fun v => f (peek v)) (pos s).

Definition duplicate i j k a (s : KleeneStore i k a) : 
  KleeneStore i j (KleeneStore j k a) :=
  kleeneStore (fun v => kleeneStore (peek (k:=s)) v) (pos s).

Record KleeneCoalg (i o : Type -> Type) := kleeneCoalg
  { coalg :> forall a b, (o a) -> KleeneStore (i a) (i b) (o b)
  ; coalg_extract : forall a (x:o a), extract (coalg _ x) = x
  ; coalg_duplicate : forall a b c (x:o a), 
       duplicate (i b) (coalg c x) = KSmap (coalg c) (coalg b x)
  }.

Lemma free_b_dim i o (k : KleeneCoalg i o) a b b' (x : o a) : dim (coalg k b x) = dim (coalg k b' x).
Proof.
apply (f_equal (fun x=> dim x) (@coalg_duplicate i o k a b' b x)).
Qed.

Lemma free_b_pos i o (k : KleeneCoalg i o) a b b' (x : o a) : 
      eq_rect _ _ (pos (coalg k b x)) _ (free_b_dim k _ _ x) = pos (coalg k b' x).
Proof.
assert (H := (@coalg_duplicate i o k a b' b x)).
change (pos (k a b' x)) with (pos (KSmap (k b' b) (k a b' x))).
change (pos (k a b x)) with (pos (duplicate (i b') (k a b x))).
generalize (free_b_dim k b b' x).
change (dim (k a b' x)) with (dim (KSmap (k b' b) (k a b' x))).
change (dim (k a b x)) with (dim (duplicate (i b') (k a b x))).
rewrite H.
apply K_dec_set.
  decide equality.
reflexivity.
Qed.

(*
Definition KCmap i o (k : KleeneCoalg i o) a b (f : i a -> i b) (x : o a) : o b :=
  let s := k _ _ x in peek (Vector.map f (pos s)).
*)
Section Traversable.

Variable t : Type -> Type.
Variable traverse : KleeneCoalg (fun x => x) t.

Definition size a (x:t a) : nat := dim (traverse a a x).

Lemma size_preservation a b (x: t a) v : 
  size (peek (k:=traverse a b x) v) = size x.
Proof.
unfold size.
replace (coalg traverse (a:=b) b (peek (k:=traverse a b x) v))
 with (peek (k:=(duplicate b (coalg traverse b x))) v).
  rewrite (free_b_dim traverse a b).
  reflexivity.
change v with (eq_rect (dim (traverse a b x)) (Vector.t b) v (dim (duplicate b (traverse a b x))) (refl_equal _)) at 1.
generalize (eq_refl (dim (traverse a b x))).
change (dim (traverse a b x)) with (dim (duplicate b (traverse a b x))) at 2.
rewrite (coalg_duplicate traverse b b x).
apply K_dec_set; [ decide equality |].
reflexivity.
Qed.

Lemma dim_preservation a a' b b' (x: t a) v : 
  dim (traverse b b' (peek (k:=traverse a b x) v)) = dim (traverse a a' x).
Proof.
change (dim (peek (k:=KSmap (traverse b b') (traverse a b x)) v) = dim (traverse a a' x)).
change (Vector.t b (dim (KSmap (traverse b b') (traverse a b x)))) in v.
revert v.
rewrite <- (coalg_duplicate traverse b b').
simpl.
intros _.
rewrite (free_b_dim traverse a' b').
reflexivity.
Qed.

Definition iso1 a (x: t a) : {x : t unit & Vector.t a (size x)} :=
 let s := coalg traverse unit x in
 existT (fun x : t unit => Vector.t a (size x)) (peek (k:=s) (Vector.const tt _)) 
 (eq_rect _ (Vector.t a) (pos s) _ (eq_sym (dim_preservation _ _ _))).

Definition iso2 a (y : {x : t unit & Vector.t a (size x)}) : t a :=
 let (t,s) := y in
 peek (k:=coalg traverse a t) (eq_rect _ (Vector.t a) s _ (eq_sym (free_b_dim _ _ _ _))).

Lemma iso2_iso1 a (x : t a) : iso2 (iso1 x) = x.
Proof.
simpl.
unfold size.
set (e1 := (eq_sym (dim_preservation _ _ _))).
set (e2 := (eq_sym (free_b_dim traverse (a:=unit) a unit
           (peek (k:=traverse a unit x)
              (Vector.const tt (dim (traverse a unit x))))))).
generalize e1 e2.
rewrite <- e1.
clear e1 e2.
(* turn this into a match goal *)
apply (fun H => K_dec_set H
 (fun e1 : dim (traverse a unit x) = dim (traverse a unit x) =>
forall e2 : dim (traverse a unit x) =
        dim
          (traverse unit a
             (peek (k:=traverse a unit x)
                (Vector.const tt (dim (traverse a unit x))))),
peek
  (k:=traverse unit a
        (peek (k:=traverse a unit x)
           (Vector.const tt (dim (traverse a unit x)))))
  (eq_rect (dim (traverse a unit x)) (Vector.t a)
     (eq_rect (dim (traverse a unit x)) (Vector.t a)
        (pos (traverse a unit x)) (dim (traverse a unit x)) e1)
     (dim
        (traverse unit a
           (peek (k:=traverse a unit x)
              (Vector.const tt (dim (traverse a unit x)))))) e2) = x)).
  decide equality.
simpl.
pose (Z0 := KSmap (traverse unit a) (traverse a unit x)).
pose (Z1 := peek (k:=Z0) (Vector.const tt _)).
change (traverse unit a (peek (k:= traverse a unit x) (Vector.const tt _)))
  with (peek (k:=Z0) (Vector.const tt _)).
unfold Z0.
rewrite <- (coalg_duplicate traverse).
simpl.
rewrite <- (free_b_pos traverse a unit x).
generalize (free_b_dim traverse a unit x).
intros e.
generalize e.
rewrite <- e.
(* turn this into a match goal *)
apply (fun H => K_dec_set H
 (fun e0 : dim (traverse a a x) = dim (traverse a a x) =>
  forall e2 : dim (traverse a a x) = dim (traverse a a x),
peek (k:=traverse a a x)
  (eq_rect (dim (traverse a a x)) (Vector.t a)
     (eq_rect (dim (traverse a a x)) (Vector.t a) (pos (traverse a a x))
        (dim (traverse a a x)) e0) (dim (traverse a a x)) e2) = x)).
  decide equality.
apply K_dec_set.
  decide equality.
simpl.
change (extract (traverse a a x) = x).
apply (coalg_extract traverse x).
Qed.

Lemma iso1_iso2_1 a (y : {x : t unit & Vector.t a (size x)}) : 
  projT1 (iso1 (iso2 y)) = projT1 y.
Proof.
destruct y as [x v].
simpl.
set (a' := (eq_rect (size x) (Vector.t a) v (dim _) _)).
clearbody a'.
pose (X := KSmap (traverse a unit) (traverse unit a x)).
change (Vector.t a (dim X)) in a'.
change (peek (k:=(peek (k:=X) a')) (Vector.const tt _) = x).
generalize a'.
unfold X.
rewrite <- (coalg_duplicate traverse a unit).
simpl.
intros _.
replace (Vector.const tt (dim (traverse unit unit x)))
  with (pos (traverse unit unit x)).
  apply (coalg_extract traverse).
generalize (pos (traverse unit unit x)).
clear - x.
induction t0.
  reflexivity.
rewrite IHt0.
destruct h.
reflexivity.
Qed.

Lemma iso1_iso2_2 a (y : {x : t unit & Vector.t a (size x)}) : 
  eq_rect _ (Vector.t a) (projT2 (iso1 (iso2 y))) _ (f_equal (@size unit) (iso1_iso2_1 y)) = projT2 y.
Proof.
set (e := (f_equal _ _)).
clearbody e.
destruct y.
set (t1 := projT1 (iso1 _)) in *.
simpl in *.
set (e1 := (eq_sym (dim_preservation _ _ _))).
clearbody e1.
fold t1 in e1 |- *.
change (dim (traverse unit unit t1)) with (size t1) in e1 |- *.
generalize e e1.
rewrite e.
(* turn this into a match goal *)
apply (fun H => K_dec_set H
 (fun e0 : size x = size x =>
  forall (e2 : dim
          (traverse a unit
             (peek (k:=traverse unit a x)
                (eq_rect (size x) (Vector.t a) t0 (dim (traverse unit a x))
                   (eq_sym
                      (free_b_dim traverse (a:=unit) a unit x))))) =
        size x),
eq_rect (size x) (Vector.t a)
  (eq_rect
     (dim
        (traverse a unit
           (peek (k:=traverse unit a x)
              (eq_rect (size x) (Vector.t a) t0 (dim (traverse unit a x))
                 (eq_sym (free_b_dim traverse (a:=unit) a unit x))))))
     (Vector.t a)
     (pos
        (traverse a unit
           (peek (k:=traverse unit a x)
              (eq_rect (size x) (Vector.t a) t0 (dim (traverse unit a x))
                 (eq_sym (free_b_dim traverse (a:=unit) a unit x))))))
     (size x) e2) (size x) e0 = t0)).
  decide equality.
simpl.
clear e e1 t1.
pose (X := KSmap (traverse a unit) (traverse unit a x)).
set (e :=(eq_sym (free_b_dim traverse (a:=unit) a unit x))).
clearbody e.
change (dim (traverse unit a x)) with (dim X) in  e|- *.
set (a' := eq_rect (size x) _ _ (dim X) e).
change (traverse a unit _) with (peek (k:=X) a').
unfold a'; clear a'.
revert e.
replace X with (duplicate a (traverse unit unit x));
  [|rewrite (coalg_duplicate traverse); reflexivity].
(* turn this into a match goal *)
apply (fun H => K_dec_set H
 (fun e : dim (traverse unit unit x) = dim (duplicate a (traverse unit unit x)) =>
  forall (e1 : dim
          (peek (k:=duplicate a (traverse unit unit x))
             (eq_rect (size x) (Vector.t a) t0
                (dim (duplicate a (traverse unit unit x))) e)) =
        dim (traverse unit unit x)),
eq_rect
  (dim
     (peek (k:=duplicate a (traverse unit unit x))
        (eq_rect (size x) (Vector.t a) t0
           (dim (duplicate a (traverse unit unit x))) e))) (Vector.t a)
  (pos
     (peek (k:=duplicate a (traverse unit unit x))
        (eq_rect (size x) (Vector.t a) t0
           (dim (duplicate a (traverse unit unit x))) e)))
  (dim (traverse unit unit x)) e1 = t0)).
  decide equality.
apply K_dec_set.
  decide equality.
reflexivity.
Qed.

Lemma iso1_iso2 a (y : {x : t unit & Vector.t a (size x)}) : 
  (iso1 (iso2 y)) = y.
Proof.
assert (H2 := iso1_iso2_2 y).
revert H2.
set (e:= (f_equal _ _)).
generalize e; clear e.
assert (H2 := iso1_iso2_1 y).
revert H2.
destruct (iso1 (iso2 y)).
destruct y.
simpl.
intros e.
revert t0.
rewrite e.
intros t0.
(* turn this into a match goal *)
apply (fun H => K_dec_set H
 (fun e0 : size x0 = size x0 =>eq_rect (size x0) (Vector.t a) t0 (size x0) e0 = t1 ->
existT (fun x1 : t unit => Vector.t a (size x1)) x0 t0 =
existT (fun x1 : t unit => Vector.t a (size x1)) x0 t1)).
  decide equality.
simpl.
intros e0; rewrite e0.
reflexivity.
Qed.

Lemma iso_coalg a b (x : t a) : (let (s,v) := iso1 x in
   kleeneStore (fun b => iso2 (existT _ s b)) v) = traverse a b x.
Proof.
unfold iso1; simpl.
unfold size; simpl.
generalize (eq_sym
            (dim_preservation unit unit (x:=x)
               (Vector.const tt (dim (traverse a unit x))))).
set (e' := (eq_sym
                (free_b_dim traverse (a:=unit) b unit
                   (peek (k:=traverse a unit x)
                      (Vector.const tt (dim (traverse a unit x))))))).
generalize e'.
clear e'.
rewrite (dim_preservation unit unit (Vector.const tt (dim (traverse a unit x)))).
set (d:= dim (traverse a unit x)).
unfold d at 1 3 4 5 6 8 10 11.
intros e.
apply K_dec_set.
  decide equality.
simpl.
revert e.
rewrite <- (free_b_pos traverse (a:=a) b unit x).
generalize (free_b_dim traverse (a:=a) b unit x).
intros e; generalize e; rewrite <- e; clear e.
(* turn this into a match goal *)
apply (fun H => K_dec_set H
 (fun e : dim (traverse a b x) = dim (traverse a b x) =>
 forall (e0 : dim (traverse a b x) =
        dim
          (traverse unit b (peek (k:=traverse a unit x) (Vector.const tt d)))),
{|
dim := dim (traverse a b x);
peek := fun b0 : Vector.t b (dim (traverse a b x)) =>
        peek
          (k:=traverse unit b
                (peek (k:=traverse a unit x) (Vector.const tt d)))
          (eq_rect (dim (traverse a b x)) (Vector.t b) b0
             (dim
                (traverse unit b
                   (peek (k:=traverse a unit x) (Vector.const tt d)))) e0);
pos := eq_rect (dim (traverse a b x)) (Vector.t a) (pos (traverse a b x))
         (dim (traverse a b x)) e |} = traverse a b x)).
  decide equality.
simpl.
intros e.
transitivity (kleeneStore (peek (k:=traverse a b x)) (pos (traverse a b x)));
[|destruct (traverse a b x); reflexivity].
f_equal.
apply functional_extensionality; intros v.
revert e.
change (forall
  e : dim (traverse a b x) =
      (dim (peek (k:=(KSmap (traverse unit b) (traverse a unit x))) (Vector.const tt d))),
  peek (k:=(peek (k:=KSmap (traverse unit b) (traverse a unit x)) (Vector.const tt d))) (eq_rect (dim (traverse a b x)) (Vector.t b) v
     (dim (peek (k:=(KSmap (traverse unit b) (traverse a unit x))) (Vector.const tt d)))
     e) =
  peek (k:=traverse a b x) v).
change d with (dim (KSmap (traverse unit b) (traverse a unit x))).
clear d.
set (X:=(KSmap (traverse unit b) (traverse a unit x))).
replace X with
  (duplicate unit (traverse a b x)) by
  apply (coalg_duplicate traverse unit b x).
clear X.
simpl.
apply K_dec_set.
  decide equality.
reflexivity.
Qed.

End Traversable.

(******************************************************************************)

Record Applicative := applicative
 { carrier :> Type -> Type
 ; pure : forall a, a -> carrier a
 ; ap : forall a b, carrier (a -> b) -> carrier a -> carrier b
 ; map := fun a b (f : a -> b) x => ap (pure f) x
 ; _ : forall (a : Type) x, map (fun (y : a) => y) x = x
 ; _ : forall a b c x y z,
    ap (ap (map (fun (f : b -> c) (g : a -> b) (w:a) => f (g w)) x) y) z =
    ap x (ap y z)
 ; _ : forall a b (f : a -> b) x, map f (pure x) = pure (f x)
 ; _ : forall a b (f : carrier (a -> b)) x, 
    ap f (pure x) = map (fun g => g x) f
 }.

Fixpoint sequenceVector n a (F:Applicative) (v: Vector.t (F a) n) : F (Vector.t a n) :=
match v in Vector.t _ n return F (Vector.t a n) with
| Vector.nil => pure _ (Vector.nil _)
| Vector.cons h m t => 
   ap (map (fun x => Vector.cons _ x m) h) (sequenceVector t)
end.

Definition traverseVector n a b (F:Applicative) (f : a -> F b) (v : Vector.t a n) : F (Vector.t b n) :=
  sequenceVector (Vector.map f v).

Lemma identity_law (F : Applicative) a (x : F a) : map (fun (y : a) => y) x = x.
Proof.
destruct F.
auto.
Qed.

Lemma composition_law (F : Applicative) a b c x y (z : F a) :
    ap (ap (map (fun (f : b -> c) (g : a -> b) (w:a) => f (g w)) x) y) z =
    ap x (ap y z).
Proof.
destruct F.
auto.
Qed.

Lemma homomorphism_law (F : Applicative) a b (f : a -> b) x :
  ap (pure F f) (pure F x) = pure F (f x).
Proof.
fold (map f (pure F x)).
destruct F.
auto.
Qed.

Lemma interchange_law (F : Applicative) a b (f : F (a -> b)) x : 
  ap f (pure F x) = map (fun g => g x) f.
Proof.
destruct F.
auto.
Qed.

Lemma map_compose a b c (F : Applicative) (g : b -> c) (f: a -> b) (h : a -> c) (x : F a) :
  (forall x, g (f x) = h x) -> map g (map f x) = map h x.
Proof.
intros H.
unfold map; rewrite <- composition_law.
unfold map; rewrite !homomorphism_law.
repeat f_equal.
apply functional_extensionality.
assumption.
Qed.

Definition IdApplicative : Applicative.
exists (fun A => A) (fun a (x : a) => x) (fun a b (f : a -> b) => f);
  try reflexivity.
Defined.

Definition NatPlusApplicative : Applicative.
exists (fun _ => nat) (fun _ _ => 0) (fun a b => plus).
   reflexivity.
  intros _ _ _ x y z.
  apply plus_assoc_reverse.
 reflexivity.
intros _ _ x _.
apply plus_0_r.
Defined.

Definition ConstListApplicative (a : Type) : Applicative.
exists (fun _ => list a) (fun _ _ => nil) (fun _ _ => (@app a)).
   reflexivity.
  intros _ _ _ x y z.
  apply app_assoc_reverse.
 reflexivity.
intros _ _ x _.
apply app_nil_r.
Defined.

Definition KSpure i j a (x : a) : KleeneStore i j a :=
  kleeneStore (fun v => x) (Vector.nil _).

Definition append_view A n p (P : Vector.t A (n + p) -> Type) :
  (forall v1 v2, P (Vector.append v1 v2)) ->
  forall v, P v.
induction n.
 intros f v.
 apply (f (Vector.nil _)).
intros f v.
replace v with (Vector.cons _ (Vector.hd v) (n + p) (Vector.tl v)).
  destruct (Vector.tl v) as [v1 v2] using IHn.
  apply (f (Vector.cons _ (Vector.hd v) _ v1)).
assert (forall m (v : Vector.t A (S m)), Vector.cons A (Vector.hd v) m (Vector.tl v) = v).
  clear -A.
  apply Vector.caseS.
  reflexivity.
apply H.
Defined.

Lemma append_view_append A n p (P : Vector.t A (n + p) -> Type) f v1 v2 :
  append_view (P:=P) f (Vector.append v1 v2) = f v1 v2.
Proof.
induction v1.
  reflexivity.
simpl.
rewrite IHv1.
reflexivity.
Qed.

Definition KSap i j a b (g : KleeneStore i j (a -> b)) (k : KleeneStore i j a) :
  KleeneStore i j b :=
  kleeneStore (fun v => append_view (P := fun _ => b) (fun v1 v2 => (peek (k:=g) v1) (peek (k:=k) v2)) v)
              (Vector.append (pos g) (pos k)).

Lemma KSpure_KSap_KSmap i j a b (f : a -> b) (k : KleeneStore i j a) :
  KSap (KSpure i j f) k = KSmap f k.
Proof.
reflexivity.
Qed.

Lemma KSpure_id i j a (k : KleeneStore i j a) : 
  KSap (KSpure i j (fun x => x)) k = k.
Proof.
destruct k.
reflexivity.
Qed.

Lemma equivalent_KS i j a (dim1 dim2 : nat) (peek1 : Vector.t j dim1 -> a) (peek2 : Vector.t j dim2 -> a)
  (pos1 : Vector.t i dim1) (pos2 : Vector.t i dim2) (e : dim1 = dim2) :
  (forall (v1 : Vector.t j dim1) (v2 : Vector.t j dim2), (eq_rect _ _ v1 _ e) = v2 -> peek1 v1 = peek2 v2) ->
  eq_rect _ _ pos1 _ e = pos2 -> kleeneStore peek1 pos1 = kleeneStore peek2 pos2.
Proof.
intros Hpeek Hpos.
transitivity (kleeneStore (fun v => peek1 (eq_rect _ _ v _ (eq_sym e))) (eq_rect _ _ pos1 _ e)).
  clear Hpeek Hpos.
  generalize e.
  rewrite <- e.
  apply K_dec_set.
    decide equality.
  reflexivity.
rewrite Hpos.
f_equal.
apply functional_extensionality; intros v.
apply Hpeek.
generalize e.
rewrite e.
apply K_dec_set.
  decide equality.
reflexivity.
Qed.

Lemma composition_KS i j a b c x y (z : KleeneStore i j a) : 
  KSap (KSap (KSap (KSpure i j (fun (f : b -> c) (g : a -> b) (x : a) => f (g x))) x) y) z =
  KSap x (KSap y z).
Proof.
destruct x; destruct y; destruct z.
unfold KSap.
simpl.
apply (equivalent_KS (e:=(eq_sym (plus_assoc dim0 dim1 dim2)))).
  intros v1 v2.
  pattern v1; apply append_view; intros v1' v1c.
  pattern v1'; apply append_view; intros v1a v1b.
  pattern v2; apply append_view; intros v2a v2'.
  pattern v2'; apply append_view; intros v2b v2c.
  repeat rewrite append_view_append.
  clear -v2c.
  rewrite <- (append_assoc _ _ _ (plus_assoc _ _ _)).
  generalize (eq_sym (plus_assoc dim0 dim1 dim2)).
  generalize (plus_assoc dim0 dim1 dim2).
  intros e; generalize e; rewrite <- e; clear e.
  intros e; pattern e; apply K_dec_set; clear e.
    decide equality.
  intros e; pattern e; apply K_dec_set; clear e.
    decide equality.
  simpl; intros H.
  destruct (append_inj H) as [H0 H'].
  destruct (append_inj H') as [H1 H2].
  rewrite H0, H1, H2.
  reflexivity.
clear -i.
apply to_list_eq.
induction pos0.
 reflexivity.
simpl.
unfold Vector.to_list in *.
rewrite IHpos0.
reflexivity.
Qed.

Lemma KSpure_KSpure i j a b (f : a -> b) (x : a): 
  KSap (KSpure i j f) (KSpure i j x) = KSpure i j (f x).
Proof.
reflexivity.
Qed.

Lemma interchange_KSpure i j a b (f : KleeneStore i j (a -> b)) (x : a): 
  KSap f (KSpure i j x) = KSap (KSpure i j (fun f => f x)) f.
Proof.
destruct f as [dimf peekf posf].
unfold KSap.
simpl.
symmetry.
apply (equivalent_KS (e:=(eq_sym (plus_0_r dimf)))).
 intros v1 v2 Hv.
 replace v2 with (Vector.append v1 (Vector.nil _)).
   rewrite append_view_append; reflexivity.
 rewrite <- Hv.
 clear -v1.
 symmetry.
 apply to_list_eq.
 induction v1.
  reflexivity.
 simpl.
 unfold Vector.to_list in *.
 rewrite IHv1.
 reflexivity.
apply to_list_eq.
clear -posf.
induction posf.
 reflexivity.
simpl.
unfold Vector.to_list in *.
rewrite IHposf.
reflexivity.
Qed.

Definition KSApplicative (i j : Type) : Applicative.
exists (KleeneStore i j) (KSpure i j) (@KSap i j).
   apply KSpure_id.
  apply composition_KS.
 apply KSpure_KSpure.
apply interchange_KSpure.
Defined.

Section ComposeApplicative.

Variable (F G :Applicative).

Let FG (a:Type) := F (G a).

Definition Compose_pure (a:Type) (x:a) : FG a :=
  pure F (pure G x).

Definition Compose_ap (a b:Type) (f:FG (a -> b)) (x:FG a) : FG b :=
 ap (ap (pure F (fun g x => ap g x)) f) x.

Lemma Compose_identity (a:Type) (x : FG a):
 Compose_ap (Compose_pure (fun y : a => y)) x = x.
Proof.
unfold Compose_ap, Compose_pure.
rewrite homomorphism_law.
replace (fun x0 : G a => ap (a:=G) (a0:=a) (b:=a) (pure G (fun y : a => y)) x0)
  with (fun (y : G a) => y).
  apply identity_law.
apply functional_extensionality; intro y.
symmetry.
apply identity_law.
Qed.

Lemma Compose_composition (a b c:Type) x y (z : FG a) :
 Compose_ap (Compose_ap (Compose_ap (Compose_pure (fun (f : b -> c) (g : a -> b) (w:a) => f (g w)))
  x) y) z =
 Compose_ap x (Compose_ap y z).
Proof.
unfold Compose_ap, Compose_pure.
repeat rewrite homomorphism_law.
repeat (unfold map; simpl; (repeat rewrite homomorphism_law); rewrite <- composition_law).
unfold map; simpl; repeat rewrite homomorphism_law.
repeat rewrite interchange_law.
repeat (unfold map; simpl; (repeat rewrite homomorphism_law); rewrite <- composition_law).
unfold map; simpl; repeat rewrite homomorphism_law.
replace (fun (w : G (b -> c)) (w0 : G (a -> b)) (x0 : G a) =>
            ap (a:=G) (a0:=a) (b:=c)
              (ap (a:=G) (a0:=a -> b) (b:=a -> c)
                 (ap (a:=G) (a0:=b -> c) (b:=(a -> b) -> a -> c)
                    (pure G
                       (fun (f : b -> c) (g : a -> b) (w1 : a) => f (g w1)))
                    w) w0) x0)
  with (fun (w : G (b -> c)) (w0 : G (a -> b)) (w1 : G a) =>
            ap (a:=G) (a0:=b) (b:=c) w (ap (a:=G) (a0:=a) (b:=b) w0 w1)).
  reflexivity.
repeat (apply functional_extensionality; intro).
symmetry.
apply composition_law.
Qed.

Lemma Compose_homomorphism a b (f : a -> b) x :
  Compose_ap (Compose_pure f) (Compose_pure x) = Compose_pure (f x).
Proof.
unfold Compose_ap, Compose_pure.
repeat rewrite homomorphism_law.
reflexivity.
Qed.

Lemma Compose_interchange a b (f : FG (a -> b)) x : 
  Compose_ap f (Compose_pure x) = Compose_ap (Compose_pure (fun g => g x)) f.
Proof.
unfold Compose_ap, Compose_pure.
repeat rewrite homomorphism_law.
repeat rewrite interchange_law.
repeat (unfold map; simpl; (repeat rewrite homomorphism_law); rewrite <- composition_law).
repeat rewrite interchange_law.
unfold map; simpl; repeat rewrite homomorphism_law.
replace (fun w : G (a -> b) => ap (a:=G) (a0:=a) (b:=b) w (pure G x))
  with (fun x0 : G (a -> b) =>
      ap (a:=G) (a0:=a -> b) (b:=b) (pure G (fun g : a -> b => g x)) x0).
  reflexivity.
apply functional_extensionality; intro.
symmetry.
apply interchange_law.
Qed.

Definition ComposeApplicative : Applicative.
exists FG Compose_pure Compose_ap.
apply Compose_identity.
apply Compose_composition.
apply Compose_homomorphism.
apply Compose_interchange.
Defined.

End ComposeApplicative.

Lemma sequenceVector_Id  n a (v: Vector.t a n) :
  sequenceVector (F:=IdApplicative) v = v.
Proof.
induction v.
  reflexivity.
simpl.
rewrite IHv.
reflexivity.
Qed.

Lemma sequenceVector_map n a b (F:Applicative) (f : a -> b) (v :Vector.t (F a) n) :
  map (Vector.map f) (sequenceVector v) = sequenceVector (Vector.map (map f) v).
Proof.
induction v.
  unfold map; simpl.
  rewrite homomorphism_law.
  reflexivity.
simpl.
rewrite <- IHv.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
rewrite interchange_law.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
reflexivity.
Qed.

Lemma sequenceVector_compose n a (F G:Applicative) (v :Vector.t (F (G a)) n) :
  sequenceVector (F:=ComposeApplicative F G) v = map (fun x => sequenceVector x) (sequenceVector v).
Proof.
induction v.
  simpl.
  unfold map.
  rewrite homomorphism_law.
  reflexivity.
simpl.
rewrite IHv.
unfold map.
unfold Compose_ap, Compose_pure.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
rewrite interchange_law.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
reflexivity.
Qed.

Lemma sequenceVector_append n m a (F:Applicative) (v1:Vector.t (F a) n) (v2:Vector.t (F a) m) :
  sequenceVector (Vector.append v1 v2) = 
    ap (map (fun x y => Vector.append x y) (sequenceVector v1)) (sequenceVector v2).
Proof.
induction v1; simpl.
  unfold map; rewrite homomorphism_law; simpl.
  symmetry; apply identity_law.
rewrite IHv1; clear IHv1.
unfold map.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
rewrite interchange_law.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
reflexivity.
Qed.

Record IdiomaticTransformation (F G:Applicative) := idiomaticTransformation 
 { transform :> forall a, F a -> G a
 ; _ : forall a (x:a), transform (pure F x) = pure G x
 ; _ : forall a b (f : F (a -> b)) x, transform (ap f x) = ap (transform f) (transform x)
 }.

Section IdiomaticTransformation.

Variables (F G:Applicative).
Variable (eta : IdiomaticTransformation F G).

Lemma idiomaticTransform_pure a (x:a) : eta _ (pure F x) = pure G x.
Proof.
destruct eta.
auto.
Qed.

Lemma idiomaticTransform_ap a b (f: F (a -> b)) (x: F a) :
  eta _ (ap f x) = ap (eta _ f) (eta _ x).
Proof.
destruct eta.
auto.
Qed.

Lemma idiomaticTransform_map a b (f: a -> b) (x: F a) :
  eta _ (map f x) = map f (eta _ x).
Proof.
unfold map.
rewrite idiomaticTransform_ap, idiomaticTransform_pure.
reflexivity.
Qed.

Lemma idiomaticTransform_sequenceVector n a (v : Vector.t (F a) n) : 
  eta _ (sequenceVector v) = sequenceVector (Vector.map (eta _) v).
Proof.
induction v.
  apply idiomaticTransform_pure.
simpl; rewrite idiomaticTransform_ap, idiomaticTransform_map, IHv.
reflexivity.
Qed.

Lemma idiomaticTransform_traverseVector n a b (f : a -> F b) (v : Vector.t a n) :
  eta _ (traverseVector f v) = traverseVector (fun y => eta _ (f y)) v.
Proof.
unfold traverseVector.
rewrite idiomaticTransform_sequenceVector.
f_equal.
apply Vector_map_compose.
reflexivity.
Qed.

End IdiomaticTransformation.

Lemma extract_pure i a (x : a) : extract (KSpure i i x) = x.
Proof.
reflexivity.
Qed.

Lemma extract_ap i a b (f : KleeneStore i i (a -> b)) (x : KleeneStore i i a) :
 extract (KSap f x) = extract f (extract x).
Proof.
destruct f; destruct x.
simpl.
rewrite append_view_append.
reflexivity.
Qed.

Definition extractIT i : IdiomaticTransformation (KSApplicative i i) IdApplicative.
exists (@extract i).
  exact (@extract_pure i).
exact (@extract_ap i).
Defined.

Lemma duplicate_pure i j k a (x : a) :
  duplicate j (KSpure i k x) = KSpure i j (KSpure j k x).
Proof.
unfold KSpure, duplicate.
simpl.
f_equal.
apply functional_extensionality.
apply Vector.case0.
reflexivity.
Qed.

Lemma duplicate_ap i j k a b (f : KleeneStore i k (a -> b)) (x : KleeneStore i k a):
  duplicate j (KSap f x) = 
    ap (a:=ComposeApplicative (KSApplicative i j) (KSApplicative j k)) (duplicate j f) (duplicate j x).
Proof.
simpl.
unfold KSap, duplicate.
simpl.
f_equal.
apply functional_extensionality.
apply append_view; intros v1 v2.
rewrite append_view_append.
reflexivity.
Qed.

Definition duplicateIT i j k : IdiomaticTransformation (KSApplicative i k) 
  (ComposeApplicative (KSApplicative i j) (KSApplicative j k)).
exists (@duplicate i j k).
  exact (@duplicate_pure i j k).
exact (@duplicate_ap i j k).
Defined.

Definition dimIT i j : IdiomaticTransformation (KSApplicative i j) NatPlusApplicative.
exists (@dim i j).
  reflexivity.
reflexivity.
Defined.

Lemma pos_ap i j a b (f : KleeneStore i j (a -> b)) (x : KleeneStore i j a) :
  Vector.to_list (pos (KSap f x)) = app (Vector.to_list (pos f)) (Vector.to_list (pos x)).
Proof.
simpl.
induction (pos f).
  reflexivity.
unfold Vector.to_list in *.
simpl.
rewrite IHt.
reflexivity.
Qed.

Definition posIT i j : IdiomaticTransformation (KSApplicative i j) (ConstListApplicative i).
exists (fun a (x : KSApplicative i j a) => Vector.to_list (pos x)).
  reflexivity.
apply (@pos_ap i j).
Defined.

Section Research.

Variables (F:Applicative) (a b : Type) (h : a -> F b).

Definition research c (k : KSApplicative a b c) : F c :=
map (peek (k:=k)) (sequenceVector (Vector.map h (pos k))).

Lemma research_pure c (x : c) : research (pure _ x) = pure _ x.
Proof.
apply homomorphism_law.
Qed.

Lemma research_ap c d (f : KSApplicative a b (c -> d)) (x : KSApplicative a b c): 
  research (ap f x) = ap (research f) (research x).
Proof.
unfold research; simpl.
unfold map; simpl.
rewrite Vector_map_append, sequenceVector_append.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
rewrite interchange_law.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
repeat f_equal.
apply functional_extensionality_dep; intros v1.
apply functional_extensionality; intros v2.
rewrite append_view_append.
reflexivity.
Qed.

Definition Research : IdiomaticTransformation (KSApplicative a b) F.
exists research.
  exact research_pure.
exact research_ap.
Defined.

End Research. 

Record Traversal := traversal 
 { container :> Type -> Type
 ; traverse : forall a b (F : Applicative), (a -> F b) -> container a -> F (container b)
 ; free_applicative : forall a b (F G : Applicative) (eta : IdiomaticTransformation F G) (f : a -> F b) (x : container a),
       eta _ (traverse f x) = traverse (fun y => eta _ (f y)) x
 ; traverse_identity : forall a (x : container a),
       traverse (F:=IdApplicative) (fun y => y) x = x
 ; traverse_compose :
   forall a b c (F G : Applicative) (f : a -> F b) (g : b -> G c) (x : container a),
       traverse (F:=ComposeApplicative F G) (fun y => map g (f y)) x =
       map (traverse g) (traverse f x)
 }.

Lemma traverseVector_free_applicative n a b (F G : Applicative) (eta :IdiomaticTransformation F G)
  (f : a -> F b) (x : Vector.t a n) :
  eta _ (traverseVector f x) = traverseVector (fun y => eta _ (f y)) x.
Proof.
induction x.
  unfold traverseVector; simpl.
  rewrite idiomaticTransform_pure.
  reflexivity.
unfold traverseVector in *; simpl.
rewrite idiomaticTransform_ap, idiomaticTransform_map.
rewrite IHx.
reflexivity.
Qed.

Lemma traverseVector_identity n a (x : Vector.t a n) : traverseVector (F:=IdApplicative) (fun y => y) x = x.
Proof.
unfold traverseVector.
simpl.
rewrite Vector_map_id.
  apply (sequenceVector_Id x).
reflexivity.
Qed.

Lemma traverseVector_compose n a b c (F G : Applicative) (f : a -> F b) (g : b -> G c) (x : Vector.t a n) :
  traverseVector (F:=ComposeApplicative F G) (fun y => map g (f y)) x =
  map (traverseVector g) (traverseVector f x).
Proof.
unfold traverseVector.
simpl.
rewrite (sequenceVector_compose (Vector.map (fun y : a => map (a:=F) g (f y)) x)).
rewrite <- (Vector_map_compose (g:=map (a:=F) g) (f:=f) (h:= (fun y : a => map (a:=F) g (f y))));
[|reflexivity].
rewrite <- sequenceVector_map.
simpl.
apply map_compose.
reflexivity.
Qed.

Definition Vector (n : nat) : Traversal.
exists (fun a => Vector.t a n) (@traverseVector n).
  apply traverseVector_free_applicative.
 apply traverseVector_identity.
apply traverseVector_compose.
Defined.

Section Traversal.

Definition impure a b (x : a) : KleeneStore a b b :=
  kleeneStore (fun v => Vector.hd v) (Vector.cons _ x _ (Vector.nil _)).

Lemma research_impure (F:Applicative) a b (h : a -> F b) (x : a) :
  research h (impure b x) = h x.
Proof.
unfold research; simpl; unfold map.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
rewrite interchange_law.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
replace (fun w : b => Vector.hd (Vector.cons b w 0 (Vector.nil b))) with (fun y : b => y).
  apply identity_law.
apply functional_extensionality.
reflexivity.
Qed.

Variable T : Traversal.
(*
Definition liftT a b (f : a -> b) := traverse (t:=T) (F:=IdApplicative) f.

Lemma free_traversal_b a b b' (h : b -> b') (F : Applicative) (f : a -> F b) (x : T a) :
       map (liftT h) (traverse f x) = traverse (fun y => map h (f y)) x.
Proof.
unfold liftT.
rewrite <- (traverse_compose (G:=IdApplicative) f h).
assert (etaH : (forall (a b : Type) (f : F (a -> b)) (x : F a),
       Compose_ap (F:=F) (G:=IdApplicative) (a:=a) (b:=b) f x =
       ap (a:=F) (a0:=a) (b:=b) f x)).
  intros a0 b0; intros.
  unfold Compose_ap.
  simpl.
  replace ((fun (g : a0 -> b0) (x1 : a0) => g x1)) with (fun x : (a0 -> b0) => x).
    change (ap (pure F _) f0) with (map (fun x => x) f0).
    rewrite identity_law.
    reflexivity.
  apply functional_extensionality.
  reflexivity.
pose (eta := @idiomaticTransformation (ComposeApplicative F IdApplicative) F 
  (fun a x => x) (fun a x => refl_equal _) etaH).
change (eta _ (traverse (t:=T) (b:=b') (F:=ComposeApplicative F IdApplicative)
  (fun y : a => map (a:=F) h (f y)) x) =
traverse (t:=T) (b:=b') (F:=F) (fun y : a => map (a:=F) h (f y)) x).
rewrite free_applicative.
reflexivity.
Qed.
*)
Let traversal_coalg a b := traverse (t:=T) (F:=KSApplicative a b) (impure (a:=a) b).

Lemma traversal_coalg_extract a (x: T a) : extractIT _ _ (traversal_coalg _ x) = x.
Proof.
unfold traversal_coalg.
rewrite free_applicative.
apply traverse_identity.
Qed.

Lemma traversal_coalg_duplicate a b c (x: T a) : 
  duplicateIT a b c _ (traversal_coalg c x) = KSmap (traversal_coalg c) (traversal_coalg b x).
Proof.
unfold traversal_coalg.
rewrite free_applicative.
replace (fun y : a => (duplicateIT a b c) c (impure c y)) with
        (fun y : a => (KSmap (impure c) (impure b y))).
  rewrite (@traverse_compose T a b c (KSApplicative a b) (KSApplicative b c) (impure b) (impure c)).
  reflexivity.
apply functional_extensionality; intros y.
simpl; unfold KSmap, duplicate; simpl.
f_equal.
apply functional_extensionality; intros v; clear -v.
unfold impure.
f_equal.
transitivity (Vector.cons b (Vector.hd v) 0 (Vector.tl v)).
  f_equal.
  apply Vector.case0.
  reflexivity.
(* this is a little screwy *)
apply (Vector.caseS (fun n v => forall (t : Vector.t b n), Vector.cons b (Vector.hd v) n (Vector.tl v) = v)).
  reflexivity.
constructor.
Qed.
(*
Lemma traversal_free_b_dim a b b' (h : b -> b') (x:  T a) :
  dimIT _ _ _ (traversal_coalg b x) = dimIT _ _ _ (traversal_coalg b' x).
Proof.
unfold traversal_coalg.
do 2 rewrite free_applicative.
simpl.
change (map (liftT h) (traverse (t:=T) (b:=b) (F:=NatPlusApplicative)
  (fun y : a => (dimIT a b) b (impure b y)) x) =
traverse (t:=T) (b:=b') (F:=NatPlusApplicative)
  (fun y : a => (dimIT a b') b' (impure b' y)) x).
rewrite (@free_traversal_b a b b' h).
reflexivity.
Qed.

Lemma traversal_free_b_pos a b b' (h : b -> b') (x:  T a) :
  eq_rect _ _ (pos (traversal_coalg b x)) _ (traversal_free_b_dim h x) = pos (traversal_coalg b' x).
Proof.
apply to_list_eq.
unfold traversal_coalg.
change (posIT _ _ _ (traverse (t:=T) (b:=b) (F:=KSApplicative a b) (impure b) x) =
        posIT _ _ _ (traverse (t:=T) (b:=b') (F:=KSApplicative a b') (impure b') x)).
do 2 rewrite free_applicative.
change (map (liftT h) (traverse (t:=T) (b:=b) (F:=ConstListApplicative a)
  (fun y : a => (posIT a b) b (impure b y)) x) =
traverse (t:=T) (b:=b') (F:=ConstListApplicative a)
  (fun y : a => (posIT a b') b' (impure b' y)) x).
rewrite (@free_traversal_b a b b' h).
reflexivity.
Qed.
*)
Definition traversal_is_coalg : KleeneCoalg (fun a => a) T.
exists traversal_coalg.
 exact traversal_coalg_extract.
exact traversal_coalg_duplicate.
Defined.

End Traversal.

Record FinContainerSpec := finContainerSpec
{ shape : Type
; card : shape -> nat
}.

Section FinContainer.

Variable spec : FinContainerSpec.

Definition finContainer (a:Type) := {x : shape spec & Vector (card x) a}.

Definition finContainer_traverse a b (F : Applicative) (f : a -> F b) (x : finContainer a) : F (finContainer b) :=
  let (s, v) := x in map (existT _ s) (traverse f v).

Lemma finContainer_free_applicative a b (F G : Applicative) (eta : IdiomaticTransformation F G) (f : a -> F b) (x : finContainer a) :
  eta _ (finContainer_traverse f x) = finContainer_traverse (fun y => eta _ (f y)) x.
Proof.
destruct x as [s v].
simpl.
change (traverseVector (b:=b) (F:=G) (fun y : a => eta b (f y)) v)
  with (traverse (fun y : a => eta b (f y)) v).
rewrite <- free_applicative.
rewrite idiomaticTransform_map.
reflexivity.
Qed.

Lemma finContainer_traverse_identity a (x : finContainer a) :
  finContainer_traverse (F:=IdApplicative) (fun y => y) x = x.
Proof.
destruct x as [s v].
simpl.
unfold traverseVector.
simpl.
rewrite Vector_map_id;[| reflexivity].
rewrite (sequenceVector_Id v).
reflexivity.
Qed.

Lemma finContainer_traverse_compose a b c (F G : Applicative) (f : a -> F b) (g : b -> G c) (x : finContainer a) :
  finContainer_traverse (F:=ComposeApplicative F G) (fun y => map g (f y)) x =
  map (finContainer_traverse g) (finContainer_traverse f x).
Proof.
destruct x as [s v].
simpl.
change (traverseVector (b:=b) (F:=F) f v) with (traverse f v).
pose (h:= fun y => finContainer_traverse (b:=c) (F:=G) g (existT (fun x : shape spec => Vector.t b (card (f:=spec) x)) s y)).
rewrite (map_compose (h:= h));[|reflexivity].
unfold h; simpl.
rewrite <- (map_compose (g:=map (a:=G) (existT (fun x : shape spec => Vector.t c (card (f:=spec) x)) s)) (f:=traverseVector (b:=c) (F:=G) g) (h:= h));[|reflexivity].
change (map (a:=F) (traverseVector (b:=c) (F:=G) g)
     (traverseVector (b:=b) (F:=F) f v))
  with (map (a:=F) (traverse (b:=c) (F:=G) g)
     (traverse (b:=b) (F:=F) f v)).
rewrite <- (traverse_compose f g).
unfold Compose_ap, Compose_pure, map.
rewrite interchange_law.
repeat (repeat rewrite homomorphism_law; repeat rewrite <- composition_law; unfold map).
reflexivity.
Qed.

Definition FinContainer : Traversal.
exists finContainer finContainer_traverse.
  apply finContainer_free_applicative.
 apply finContainer_traverse_identity.
apply finContainer_traverse_compose.
Defined.

End FinContainer.

(*============================================================================*)
(*The main result                                                             *)
(*============================================================================*)

Theorem Traversal_is_finite_container :
  forall (T:Traversal), exists (spec : FinContainerSpec)
         (f : forall a, T a -> FinContainer spec a)
         (g : forall a, FinContainer spec a -> T a),
  (forall a, (forall x, g a (f a x) = x) /\ forall y, f a (g a y) = y) /\
  (forall a b (F : Applicative) (h: a -> F b) (x : T a),
         map (f b) (traverse h x) = traverse h (f a x)).
Proof.
intros T.
pose (K := traversal_is_coalg T).
exists (finContainerSpec (size K (a:=unit))).
exists (iso1 K).
exists (iso2 (traverse:=K)).
split.
  intros a.
  split.
    apply iso2_iso1.
  apply iso1_iso2.
intros a b F h x.
rewrite <- identity_law.
replace (fun y : (FinContainer {| shape := T unit; card := size K (a:=unit) |}) b =>
   y) with (fun y => iso1 K (iso2 (traverse:=K) (a:=b) y)) by
  (apply functional_extensionality; apply iso1_iso2).
rewrite <- (map_compose (g:=iso1 K (a:=b)) (f:=iso2 (traverse:=K) (a:=b)));
[|reflexivity].
f_equal.
unfold traverse at 2; simpl.
unfold traverseVector; simpl.
(* close your eyes for a moment *)
set (z := (fun
          b0 : Vector.t b
                 (size K (a:=unit)
                    (peek
                       (k:=traverse (t:=T) (b:=unit)
                             (F:=KSApplicative a unit) (impure unit) x)
                       (Vector.const tt
                          (dim
                             (traverse (t:=T) (b:=unit)
                                (F:=KSApplicative a unit) (impure unit) x))))) =>
        peek
          (k:=traverse (t:=T) (b:=b) (F:=KSApplicative unit b) (impure b)
                (peek
                   (k:=traverse (t:=T) (b:=unit) (F:=KSApplicative a unit)
                         (impure unit) x)
                   (Vector.const tt
                      (dim
                         (traverse (t:=T) (b:=unit) (F:=KSApplicative a unit)
                            (impure unit) x)))))
          (eq_rect
             (size K (a:=unit)
                (peek
                   (k:=traverse (t:=T) (b:=unit) (F:=KSApplicative a unit)
                         (impure unit) x)
                   (Vector.const tt
                      (dim
                         (traverse (t:=T) (b:=unit) (F:=KSApplicative a unit)
                            (impure unit) x))))) (Vector.t b) b0
             (dim
                (traverse (t:=T) (b:=b) (F:=KSApplicative unit b) (impure b)
                   (peek
                      (k:=traverse (t:=T) (b:=unit) (F:=KSApplicative a unit)
                            (impure unit) x)
                      (Vector.const tt
                         (dim
                            (traverse (t:=T) (b:=unit)
                               (F:=KSApplicative a unit) (impure unit) x))))))
             (eq_sym
                (free_b_dim K (a:=unit) b unit
                   (peek
                      (k:=traverse (t:=T) (b:=unit) (F:=KSApplicative a unit)
                            (impure unit) x)
                      (Vector.const tt
                         (dim
                            (traverse (t:=T) (b:=unit)
                               (F:=KSApplicative a unit) (impure unit) x))))))))).
rewrite (map_compose (h:=z));[|reflexivity].
change (traverse h x =
  research h (let (s,v) := iso1 K (a:=a) x in
   kleeneStore (fun b => iso2 (existT _ s b)) v)).
clear z.
transitivity (Research h _ (K a b x)).
  unfold K.
  simpl ((traversal_is_coalg T) a b x).
  rewrite free_applicative.
  f_equal.
  apply functional_extensionality; intros y.
  simpl.
  rewrite research_impure.
  reflexivity.
simpl ((Research (F:=F) (b:=b) h) (T b)).
f_equal.
symmetry.
apply iso_coalg.
Qed.

Print Assumptions Traversal_is_finite_container.

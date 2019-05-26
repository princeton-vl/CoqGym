(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(*****************)
(** * Universes  *)
(*****************)

(** In what follows, we will work with explicit universes rather than
    with Coq-style implicit universes.

    For that, we define two universes Typ1 and Typ2 as shorthands for
    the generic universe Type by enforcing the constraint Typ1 : Typ2
    so that Coq knows that the implicit index associated to Typ1 is
    smaller than the implicit index associated to Typ2. *)

Definition Typ2 := Type.
Definition Typ1 : Typ2 := Type. (* enforce Typ1 : Typ2 *)

(** Intuitively:

    - Typ1 is the universe of small types, which contains the type
      Prop of propositions, and is closed under dependent product.

    - Typ2 is the top-universe of large types, which contains the
      universe Typ1, and is closed under dependent product again.

    In the following, small types (i.e. the inhabitants of Typ1) will
    be used as the carriers of pointed graphs (for representing sets). *)

(** The type of binary relations: *)

Definition Rel (X : Typ1) : Typ1 := X -> X -> Prop.

(***************************)
(** * Logical connectives  *)
(***************************)

(** To avoid the use of Coq-style inductive definitions, we redefine
    all the logical connectives from their second-order encoding and
    give their introduction rules.  Except in a few cases, it is not
    necessary to give the corresponding elimination rules whose
    behaviour is mimicked by using the tactic [Apply H] (instead of
    [Elim H]) in the subsequent proof-scripts. *)

(** ** Truth and falsity **)

Definition top : Prop := forall E : Prop, E -> E.

Lemma top_intro : top.
Proof fun E e => e.

Definition bot : Prop := forall E : Prop, E.

(** ** Conjunction **)

Definition and (A B : Prop) : Prop := forall E : Prop, (A -> B -> E) -> E.

Lemma and_intro : forall A B : Prop, A -> B -> and A B.
Proof fun A B a b E f => f a b.

Lemma and_fst : forall A B : Prop, and A B -> A.
Proof fun A B p => p A (fun a _ => a).

Lemma and_snd : forall A B : Prop, and A B -> B.
Proof fun A B p => p B (fun _ b => b).

(** ** Disjunction **)

Definition or (A B : Prop) : Prop :=
  forall E : Prop, (A -> E) -> (B -> E) -> E.

Lemma or_inl : forall A B : Prop, A -> or A B.
Proof fun A B a E f g => f a.

Lemma or_inr : forall A B : Prop, B -> or A B.
Proof fun A B b E f g => g b.

(** ** Logical equivalence **)

Definition iff (A B : Prop) : Prop := and (A -> B) (B -> A).

(****************************************************)
(** * Existential quantifiers and Leibniz equality  *)
(****************************************************)

(** ** Existential quantification in a given small type **)

Definition ex (X : Typ1) (P : X -> Prop) : Prop :=
  forall E : Prop, (forall x : X, P x -> E) -> E.

Lemma ex_intro : forall (X : Typ1) (P : X -> Prop) (x : X), P x -> ex X P.
Proof fun X P x p E f => f x p.

(** We define a variant of the former existential quantification in
    order to express the existence of an object that fulfills the
    conjunction of two predicates P and Q.  *)

Definition ex2 (X : Typ1) (P Q : X -> Prop) : Prop :=
  forall E : Prop, (forall x : X, P x -> Q x -> E) -> E.

Lemma ex2_intro :
 forall (X : Typ1) (P Q : X -> Prop) (x : X), P x -> Q x -> ex2 X P Q.
Proof fun X P Q x p q E f => f x p q.

(** ** Existential quantification over all small types **)

Definition exT (P : Typ1 -> Prop) : Prop :=
  forall E : Prop, (forall X : Typ1, P X -> E) -> E.

Lemma exT_intro : forall (P : Typ1 -> Prop) (X : Typ1), P X -> exT P.
Proof fun P X p E f => f X p.

(** ** Existential quantification over all pointed graphs **)

Definition exG (P : forall X : Typ1, Rel X -> X -> Prop) : Prop :=
  forall E : Prop, (forall (X : Typ1) (A : Rel X) (a : X), P X A a -> E) -> E.

Lemma exG_intro :
 forall (P : forall X : Typ1, Rel X -> X -> Prop) (X : Typ1) 
   (A : Rel X) (a : X), P X A a -> exG P.

Proof fun P X A a p E f => f X A a p.

(** ** Leibniz equality **)

Definition eq (X : Typ1) (x y : X) : Prop := forall P : X -> Prop, P x -> P y.

Lemma eq_refl : forall (X : Typ1) (x : X), eq X x x.
Proof fun X x P p => p.

Lemma eq_sym : forall (X : Typ1) (x y : X), eq X x y -> eq X y x.
Proof fun X x y e => e (fun z => eq X z x) (eq_refl X x).

Lemma eq_trans :
 forall (X : Typ1) (x y z : X), eq X x y -> eq X y z -> eq X x z.
Proof fun X x y z e1 e2 P p => e2 P (e1 P p).

(****************************)
(** * Some data structures  *)
(****************************)

(** ** Option type **)

(** The option type (opt X) : Typ1 (parametrized by X : Typ1) that
    would be inductively defined in Coq by

      Inductive opt [X:Typ1] : Typ1 :=
      | some : X->(opt X)
      | none : (opt X).

    is mimicked by the following definitions: *)

Definition opt (X : Typ1) : Typ1 := (X -> Prop) -> Prop.
Definition some (X : Typ1) (x : X) : opt X := fun f => f x.
Definition none (X : Typ1) : opt X := fun _ => bot.

(** These definitions fulfill the expected properties of injectivity
    and non-confusion: *)

Lemma eq_some_some :
 forall (X : Typ1) (x1 x2 : X),
 eq (opt X) (some X x1) (some X x2) -> eq X x1 x2.

Proof fun X x1 x2 e => e (fun z => z (fun x => eq X x1 x)) (eq_refl X x1).

Lemma eq_some_none :
 forall (X : Typ1) (x : X), eq (opt X) (some X x) (none X) -> bot.

Proof fun X x e => e (fun z => z (fun _ => top)) top_intro.

Lemma eq_none_some :
 forall (X : Typ1) (x : X), eq (opt X) (none X) (some X x) -> bot.

Proof
  fun X x e => e (fun z => z (fun _ => top) -> bot) (fun p => p) top_intro.

(** On the other hand, the corresponding elimination scheme does not
    hold, due to the existence of inhabitants of the type (opt X)
    that are neither of the form (some X x) nor of the form (none X),
    such as the term  [f:X->Prop]top : (opt X)  for instance.

    In practice, the existence of such parasitic elements will not
    pose a problem.  When defining edge relations on data-types such
    as (opt X), we will simply ignore these extra elements so that
    they will become invisible up to a bisimulation. *)

(** ** Extended sum type **)

(** The (extended) sum type (sum X Y) : Typ1 (parametrized by the
    types X,Y : Typ1) that would be inductively defined in Coq by

      Inductive sum [X,Y:Typ1] : Typ1 :=
      | inl : X->(sum X Y)                  (left injection)
      | inr : Y->(sum X Y)                  (right injection)
      | out : (sum X Y).                    (extra element)

    is mimicked by the following definitions: *)

Definition sum (X Y : Typ1) : Typ1 := (X -> Prop) -> (Y -> Prop) -> Prop.
Definition inl (X Y : Typ1) (x : X) : sum X Y := fun f _ => f x.
Definition inr (X Y : Typ1) (y : Y) : sum X Y := fun _ g => g y.
Definition out (X Y : Typ1) : sum X Y := fun _ _ => bot.

(** Again, these definitions fulfill the expected properties of
    injectivity and non-confusion: *)

Lemma eq_inl_inl :
 forall (X Y : Typ1) (x1 x2 : X),
 eq (sum X Y) (inl X Y x1) (inl X Y x2) -> eq X x1 x2.

Proof
  fun X Y x1 x2 e =>
  e (fun z => z (fun x => eq X x1 x) (fun _ => bot)) (eq_refl X x1).

Lemma eq_inr_inr :
 forall (X Y : Typ1) (y1 y2 : Y),
 eq (sum X Y) (inr X Y y1) (inr X Y y2) -> eq Y y1 y2.

Proof
  fun X Y y1 y2 e =>
  e (fun z => z (fun _ => bot) (fun y => eq Y y1 y)) (eq_refl Y y1).

Lemma eq_inl_inr :
 forall (X Y : Typ1) (x : X) (y : Y),
 eq (sum X Y) (inl X Y x) (inr X Y y) -> bot.

Proof fun X Y x y e => e (fun z => z (fun _ => top) (fun _ => bot)) top_intro.

Lemma eq_inr_inl :
 forall (X Y : Typ1) (x : X) (y : Y),
 eq (sum X Y) (inr X Y y) (inl X Y x) -> bot.

Proof fun X Y x y e => e (fun z => z (fun _ => bot) (fun _ => top)) top_intro.

Lemma eq_inl_out :
 forall (X Y : Typ1) (x : X), eq (sum X Y) (inl X Y x) (out X Y) -> bot.

Proof fun X Y x e => e (fun z => z (fun _ => top) (fun _ => top)) top_intro.

Lemma eq_out_inl :
 forall (X Y : Typ1) (x : X), eq (sum X Y) (out X Y) (inl X Y x) -> bot.

Proof
  fun X Y x e =>
  e (fun z => z (fun _ => top) (fun _ => top) -> bot) (fun p => p) top_intro.

Lemma eq_inr_out :
 forall (X Y : Typ1) (y : Y), eq (sum X Y) (inr X Y y) (out X Y) -> bot.

Proof fun X Y y e => e (fun z => z (fun _ => top) (fun _ => top)) top_intro.

Lemma eq_out_inr :
 forall (X Y : Typ1) (y : Y), eq (sum X Y) (out X Y) (inr X Y y) -> bot.

Proof
  fun X Y y e =>
  e (fun z => z (fun _ => top) (fun _ => top) -> bot) (fun p => p) top_intro.

(** The corresponding elimination scheme does not hold here, for the
    same reason as for the option type (see above). *)

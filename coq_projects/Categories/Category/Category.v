From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.

(** The basic definition of a category *)
Cumulative Class Category : Type :=
{
  (** Type of Objects *)
  Obj : Type;

  (** Type of morphism beween two objects *)
  Hom : Obj → Obj → Type where "a –≻ b" := (Hom a b);

  (** composition of morphisms: *)
  compose : ∀ {a b c : Obj}, (a –≻ b) → (b –≻ c) → (a –≻ c) where "f ∘ g" := (compose g f);

  (** associativity of composition: *)
  assoc : ∀ {a b c d : Obj} (f : a –≻ b) (g : b –≻ c) (h : c –≻ d),
            ((h ∘ g) ∘ f) = (h ∘ (g ∘ f));

  (** symmetric form of associativity: *)
  assoc_sym : ∀ {a b c d : Obj} (f : a –≻ b) (g : b –≻ c) (h : c –≻ d),
                ((h ∘ (g ∘ f) = (h ∘ g) ∘ f));

  (** identity morphisms: *)
  id : ∀ {a : Obj}, a –≻ a;

  (** id left unit: *)
  id_unit_left : ∀ (a b : Obj) (h : a –≻ b), id ∘ h = h;

  (** id right unit: *)
  id_unit_right : ∀ (a b : Obj) (h : a –≻ b), h ∘ id = h
}.

Arguments Obj {_}, _.
Arguments id {_ _}, {_} _, _ _.
Arguments Hom {_} _ _, _ _ _.
Arguments compose {_} {_ _ _} _ _, _ {_ _ _} _ _, _ _ _ _ _ _.
Arguments assoc {_ _ _ _ _} _ _ _.
Arguments assoc_sym {_ _ _ _ _} _ _ _.

Notation "f ∘ g" := (compose g f) : morphism_scope.
Notation "a –≻ b" := (Hom a b) : morphism_scope.

Bind Scope category_scope with Category.

Bind Scope morphism_scope with Hom.

Bind Scope object_scope with Obj.

Coercion Obj : Category >-> Sortclass.

Hint Resolve id_unit_left id_unit_right.

(* basic tactics for categories *)

(** We can't write reveal_comp tactic more efficiently without a mechanism to match
with a pattern and get back also the matched term. This is currently impossible in Coq. *)
(**
#
<pre>
Ltac reveal_make_rightmost f term :=
  let rec RMR termx :=
      lazymatch termx with
        | (_ ∘ f)%morphism => apply (eq_refl termx)
        | (?A ∘ ?B)%morphism =>
          match type of $(RMR B)$ with
              _ = (?C ∘ f)%morphism =>
              exact (
                  eq_trans
                  (match $(RMR B)$ in _ = Y return termx = (A ∘ Y)%morphism with
                      eq_refl => eq_refl
                  end)
                    (assoc_sym f C A)
                )
          end
        | _ => fail
      end
  in
  RMR term.

Ltac reveal_make_leftmost f term :=
  let rec RML termx :=
      lazymatch termx with
        | (f ∘ _)%morphism => apply (eq_refl termx)
        | (?A ∘ ?B)%morphism =>
          match type of $(RML A)$ with
              _ = (f ∘ ?C)%morphism =>
              exact (
                  eq_trans
                  (match $(RML A)$ in _ = Y return termx = (Y ∘ B)%morphism with
                      eq_refl => eq_refl
                  end)
                    (assoc B C f)
                )
          end
        | _ => fail
      end
  in
  RML term.

Ltac reveal_prepare_equality_term f g A B term :=
  match type of $(reveal_make_rightmost f A)$ with
      _ = (?C ∘ f)%morphism =>
      match type of $(reveal_make_leftmost g B)$ with
          _ = (g ∘ ?D)%morphism =>
          exact (eq_trans
                   (match $(reveal_make_rightmost f A)$ in _ = X return term = (X ∘ _)%morphism with
                        eq_refl =>
                        match $(reveal_make_leftmost g B)$ in _ = Y return term = (_ ∘ Y)%morphism with
                            eq_refl => eq_refl
                        end
                    end)
                   (eq_trans
                       (assoc (g ∘ D) f C)
                       (match assoc_sym D g f in _ = Z return (C ∘ f ∘ g ∘ D = C ∘ Z)%morphism with
                            eq_refl => eq_refl
                        end)
                   )
                )
      end
  end
.

Ltac reveal_prepare_equality_term_left_explicit f g B term :=
  match type of $(reveal_make_leftmost g B)$ with
      _ = (g ∘ ?D)%morphism =>
      exact (eq_trans
               (
                 match $(reveal_make_leftmost g B)$ in _ = Y return term = (_ ∘ Y)%morphism with
                     eq_refl => eq_refl
                 end
               )
               (assoc_sym D g f)
            )
  end
.

Ltac reveal_prepare_equality_term_right_explicit f g A term :=
  match type of $(reveal_make_rightmost f A)$ with
      _ = (?C ∘ f)%morphism =>
      exact (eq_trans
               (
                 match $(reveal_make_rightmost f A)$ in _ = Y return term = (Y ∘ _)%morphism with
                     eq_refl => eq_refl
                 end
               )
               (assoc g f C)
            )
  end
.

Ltac reveal_comp_in_goal f g :=
  match goal with
    | [|- context[?term]] =>
      match term with
          context [f] =>
          match term with
              context [g] =>
              match term with
                | (f ∘ g)%morphism => idtac
                | (?A ∘ ?B)%morphism =>
                  match A with
                      context [f] =>
                      match B with
                          context [g] =>
                          rewrite $(reveal_prepare_equality_term f g A B term)$
                      end
                  end
                | (f ∘ ?B)%morphism =>
                  rewrite $(reveal_prepare_equality_term_left_explicit f g B term)$
                | (?A ∘ g)%morphism =>
                  rewrite $(reveal_prepare_equality_term_right_explicit f g A term)$
              end
          end
      end
    | _ => fail
  end.

Ltac reveal_comp_in_I f g I :=
  match type of I with
    | context[?term] =>
      match term with
          context [f] =>
          match term with
              context [g] =>
              match term with
                | (f ∘ g)%morphism => idtac
                | (?A ∘ ?B)%morphism =>
                  match A with
                      context [f] =>
                      match B with
                          context [g] =>
                          rewrite $(reveal_prepare_equality_term f g A B term)$ in I
                      end
                  end
                | (f ∘ ?B)%morphism =>
                  rewrite $(reveal_prepare_equality_term_left_explicit f g B term)$ in I
                | (?A ∘ g)%morphism =>
                  rewrite $(reveal_prepare_equality_term_right_explicit f g A term)$ in I
              end
          end
      end
    | _ => fail
  end.

Tactic Notation "reveal_comp" constr(f) constr(g) := reveal_comp_in_goal f g.

Tactic Notation "reveal_comp" constr(f) constr(g) "in" hyp(I) := reveal_comp_in_I f g I.

</pre>
#
 *)

Ltac simpl_ids :=
  let id_detected B :=
      let J := fresh "H" in
      cut (B = id); [intros J; rewrite J; clear J | trivial]
  in
  repeat(
      match goal with
        | [|- context[(?A ∘ id)%morphism] ] => rewrite id_unit_right
        | [|- context[(id ∘ ?A)%morphism] ] => rewrite id_unit_left
        | [|- (?A ∘ ?B)%morphism = ?A] => id_detected B
        | [|- (?A = ?A ∘ ?B) %morphism] => id_detected B
        | [|- (?B ∘ ?A = ?A)%morphism] => id_detected B
        | [|- (?A = ?B ∘ ?A)%morphism] => id_detected B
      end
    )
.

Ltac simpl_ids_in_I I :=
  repeat(
      match type of I with
        | context[(?A ∘ id)%morphism] => rewrite id_unit_right in I
        | context[(id ∘ ?A)%morphism] => rewrite id_unit_left in I
      end
    )
.

Tactic Notation "simpl_ids" := simpl_ids.

Tactic Notation "simpl_ids" "in" hyp(I) := simpl_ids_in_I I.

Hint Extern 1 => progress simpl_ids.

Hint Extern 3 => progress (dohyps (fun H => simpl_ids in H)).

Hint Extern 2 =>
match goal with
    [|- ?A = ?B :> Hom _ _ _] =>
    repeat rewrite assoc; trivial; fail
end.

Hint Extern 2 =>
match goal with
  [H : _ = _ :> Hom _ _ _ |- _ = _ :> Hom _ _ _] =>
  repeat rewrite assoc in H;
    repeat rewrite assoc;
    (idtac + symmetry); apply H
end.

(* Julien Narboux *)
(* Formalization of *)
(* Tarski's axiomatic *)

(* Some general tactics *)
Ltac ex_elim H x := elim H; intros x ; intro; clear H.

Ltac DecompEx H P := elim H;intro P;intro;clear H.

Ltac DecompExAnd H P :=
  elim H;intro P;let id:=fresh in
(intro id;decompose [and] id;clear id;clear H).

Ltac exist_hyp t := match goal with
  | H1:t |- _ => idtac
 end.

Ltac hyp_of_type t := match goal with
  | H1:t |- _ => H1
end.

Ltac clean_duplicated_hyps :=
  repeat match goal with
      | H:?X1 |- _ => clear H; exist_hyp X1
end.

Ltac suppose H := cut H;[intro|idtac].

Ltac not_exist_hyp t := match goal with
  | H1:t |- _ => fail 2
 end || idtac.

Ltac DecompAndAll :=
 repeat
 match goal with
   | H:(?X1 /\ ?X2) |- _ => decompose [and] H;clear H
end.

Ltac assert_if_not_exist H :=
  not_exist_hyp H;assert H.

Ltac absurde :=
match goal with
   |H : (?X <> ?X) |- _ => apply False_ind; apply H; reflexivity
end.

Ltac spliter := repeat
match goal with
   | H:(?X1 /\ ?X2) |- _ => induction H
end.

Ltac ex_and H x := elim H; intro x; intros; clear H;spliter.
(* Ltac ex_and H x := ex_elim H x; spliter. *)

Ltac use H := decompose [and] H;clear H.

Ltac try_or T :=
 match goal with
 | |- ?A \/ ?B =>
   (left; try_or T) || (right;try_or T)
 | |- _ => T
 end.

(* Tactics to hide and show hypothesis from context taken from libtactics of Software foundations. *)

Tactic Notation "generalizes" hyp(X) :=
  generalize X; clear X.

Ltac sort_tactic :=
  try match goal with H: ?T |- _ =>
  match type of T with Prop =>
    generalizes H; (try sort_tactic); intro
  end end.

Tactic Notation "sort" :=
  sort_tactic.

Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" :=
  (@ltac_something _ _).

Lemma ltac_something_eq : forall (e:Type),
  e = (@ltac_something _ e).
Proof.
auto.
Qed.

Lemma ltac_something_hide : forall (e:Type),
  e -> (@ltac_something _ e).
Proof. auto.
Qed.

Lemma ltac_something_show : forall (e:Type),
  (@ltac_something _ e) -> e.
Proof. auto.
Qed.

(* hide_def x and show_def x can be used to hide/show the body of the definition x. *)

Tactic Notation "hide_def" hyp(x) :=
  let x' := constr:(x) in
  let T := eval unfold x in x' in
  change T with (@ltac_something _ T) in x.

Tactic Notation "show_def" hyp(x) :=
  let x' := constr:(x) in
  let U := eval unfold x in x' in
  match U with @ltac_something _ ?T =>
    change U with T in x end.

(* show_def unfolds Something in the goal *)
Tactic Notation "show_def" :=
  unfold ltac_something.

Tactic Notation "show_def" "in" "*" :=
  unfold ltac_something in *.

(* hide_defs and show_defs applies to all definitions *)

Tactic Notation "hide_defs" :=
  repeat match goal with H := ?T |- _ =>
    match T with
    | @ltac_something _ _ => fail 1
    | _ => change T with (@ltac_something _ T) in H
    end
  end.

Tactic Notation "show_defs" :=
  repeat match goal with H := (@ltac_something _ ?T) |- _ =>
    change (@ltac_something _ T) with T in H end.

(* hide_hyp H replaces the type of H with the notation Something and show_hyp H reveals the type of the hypothesis. Note that the hidden type of H remains convertible the real type of H. *)

Tactic Notation "show_hyp" hyp(H) :=
  apply ltac_something_show in H.

Tactic Notation "hide_hyp" hyp(H) :=
  apply ltac_something_hide in H.

(* hide_hyps and show_hyps can be used to hide/show all hypotheses of type Prop. *)

Tactic Notation "show_hyps" :=
  repeat match goal with
    H: @ltac_something _ _ |- _ => show_hyp H end.

Tactic Notation "hide_hyps" :=
  repeat match goal with H: ?T |- _ =>
    match type of T with
    | Prop =>
      match T with
      | @ltac_something _ _ => fail 2
      | _ => hide_hyp H
      end
    | _ => fail 1
    end
  end.

(* hide H and show H automatically select between hide_hyp or hide_def, and show_hyp or show_def. Similarly hide_all and show_all apply to all. *)

Tactic Notation "hide" hyp(H) :=
  first [hide_def H | hide_hyp H].

Tactic Notation "show" hyp(H) :=
  first [show_def H | show_hyp H].

Tactic Notation "hide_all" :=
  hide_hyps; hide_defs.

Tactic Notation "show_all" :=
  unfold ltac_something in *.

(* hide_term E can be used to hide a term from the goal. show_term or show_term E can be used to reveal it. hide_term E in H can be used to specify an hypothesis.*)

Tactic Notation "hide_term" constr(E) :=
  change E with (@ltac_something _ E).
Tactic Notation "show_term" constr(E) :=
  change (@ltac_something _ E) with E.
Tactic Notation "show_term" :=
  unfold ltac_something.

Tactic Notation "hide_term" constr(E) "in" hyp(H) :=
  change E with (@ltac_something _ E) in H.
Tactic Notation "show_term" constr(E) "in" hyp(H) :=
  change (@ltac_something _ E) with E in H.
Tactic Notation "show_term" "in" hyp(H) :=
  unfold ltac_something in H.

(* Tactics.v *)

(*********************)
(* Some user tactics *)
(*********************)

Require Export ArithCompl.

Ltac elim_hyps :=
  repeat
    match goal with
    | id : (exists x : _, _) |- _ => elim id; clear id; intros
    | id : _ /\ _ |- _ => elim id; clear id; intros
    | id : _ \/ _ |- _ => elim id; clear id; intros
    end.

Ltac elim_hyps_no_or :=
  repeat
    match goal with
    | id : (exists x : _, _) |- _ => elim id; clear id; intros
    | id : _ /\ _ |- _ => elim id; clear id; intros
    end.

Ltac fold_Zminus :=
  repeat
    match goal with
    | |- context[?x1 + (- ?x2)] => fold (x1 - x2)
    end.

Ltac Zparity_hyps :=
  repeat
    match goal with
    | id : Zeven _ |- _ => generalize (Zeven_def1 _ id); clear id; intro
    | id : Zodd _ |- _ => generalize (Zodd_def1 _ id); clear id; intro
    end; elim_hyps.

Ltac atomic_IZR :=
  repeat rewrite plus_IZR || rewrite mult_IZR || rewrite Ropp_Ropp_IZR ||
    rewrite <- Z_R_minus.

Ltac head_IZR :=
  replace 1%R with (IZR 1);
    [ repeat rewrite <- plus_IZR || rewrite <- mult_IZR ||
      rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus
    | simpl; auto ].

Ltac neq_0 :=
  (repeat progress head_IZR; replace 0%R with (IZR 0);
      [ apply IZR_neq; fold_Zminus | auto ]).

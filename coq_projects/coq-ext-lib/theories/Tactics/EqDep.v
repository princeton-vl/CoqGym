Require Import Coq.Classes.EquivDec.
Require Import ExtLib.Structures.EqDep.
Require Coq.Logic.Eqdep_dec.

Set Implicit Arguments.
Set Strict Implicit.

Section Classes.
  Context {A : Type}.
  Context {dec : EqDec A (@eq A)}.

  Theorem UIP_refl : forall {x : A} (p1 : x = x), p1 = refl_equal _.
    intros.
    eapply Eqdep_dec.UIP_dec. apply equiv_dec.
  Qed.

  Theorem UIP_equal : forall {x y : A} (p1 p2 : x = y), p1 = p2.
    eapply Eqdep_dec.UIP_dec. apply equiv_dec.
  Qed.

  Lemma inj_pair2 :
    forall (P:A -> Type) (p:A) (x y:P p),
      existT P p x = existT P p y -> x = y.
  Proof.
    intros. eapply Eqdep_dec.inj_pair2_eq_dec; auto.
  Qed.

End Classes.

Ltac notVar X :=
  match X with
    | _ _ => idtac
    | _ _ _ => idtac
    | _ _ _ _ => idtac
    | _ _ _ _ _ => idtac
    | _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.

Ltac gen_refl :=
  repeat match goal with
           | H : context [ @eq_refl ?X ?Y ] |- _ =>
             generalize dependent (@eq_refl X Y)
           | |- context [ @eq_refl ?X ?Y ] =>
             generalize dependent (@eq_refl X Y)
         end.

Ltac uip_all :=
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
           | [ |- context [ match ?X in _ = t return _ with
                              | refl_equal => _
                            end ] ] => notVar X; generalize X
           | [ |- context [ eq_rect_r _ _ ?X ] ] => notVar X; generalize X
         end;
  intros;
    repeat match goal with
             | [ H : ?X = ?X |- _ ] => rewrite (UIP_refl H) in *
             | [ _ : context [ ?H ] |- _ ] =>
               rewrite (UIP_refl H) in *
             | [ |- context [ ?H ] ] =>
               rewrite (UIP_refl H) in *
           end.

Ltac uip_all' :=
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
           | [ |- context [ match ?X in _ = t return _ with
                              | refl_equal => _
                            end ] ] => notVar X; generalize X
           | [ |- context [ eq_rect_r _ _ ?X ] ] => notVar X; generalize X
         end;
  intros;
    repeat match goal with
             | [ H : ?X = ?X |- _ ] =>
               generalize dependent H;
                 let pf := fresh in
                 intro pf; rewrite (UIP_refl pf) in * ;
                 try clear pf
           end.

Export EquivDec.

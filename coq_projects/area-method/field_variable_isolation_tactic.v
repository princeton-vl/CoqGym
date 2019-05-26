(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export field.
Require Export general_tactics.

(*************************************************)
(* Variable isolation tactic                     *)
(*************************************************)

(* 
This module defines a few tactics :

   IsoleVar x H isolates one occurence of x in H 
   Warning it does not factorize, but it is still usefull.

   NormalizeRing H normalize the hypothesis H using ring.
   RewriteVar x H, isolates x in H and then substitutes x 
   everywhere.     
*)


Ltac NormalizeRing H :=
  match goal with
  | i:(?X1 = ?X2) |- _ =>
      match constr:(i) with
      | H => generalize H; ring_simplify X1 X2; clear H; intro H
      | _ => fail
      end
  end. 

Lemma Lc : forall a b : F, a = b -> a - b = 0.
intros.
rewrite H.
ring.
Qed.

Lemma Lcinv : forall a b : F, a - b = 0 -> a = b.
intros.
assert (a - b + b = 0 + b).
rewrite H.
auto.
NormalizeRing H0.
auto.
Qed.

Lemma Lcp1 : forall a b c : F, a + b = c -> a = c - b.
intros.
rewrite <- H.
ring.
Qed.

Lemma Lcp2 : forall a b c : F, a + b = c -> b = c - a.
intros.
rewrite <- H.
ring.
Qed.

Lemma Lcm1 : forall a b c : F, a - b = c -> a = c + b.
intros.
rewrite <- H.
ring.
Qed.

Lemma Lcm2 : forall a b c : F, a - b = c -> b = a - c.
intros.
rewrite <- H.
ring.
Qed.

Lemma Lcop1 : forall a b : F, - a = b -> a = - b.
intros.
rewrite <- H.
ring.
Qed.

Lemma Lcmult1 : forall a b c : F, b <> 0 -> a * b = c -> a = c / b.
intros; field_simplify_eq; auto.
Qed.

Lemma Lcmult2 : forall a b c : F, a <> 0 -> a * b = c -> b = c / a.
intros.
rewrite <- H0; field_simplify_eq; trivial.
Qed.

Lemma Lcdiv1 : forall a b c : F, b <> 0 -> a / b = c -> a = b * c.
intros.
rewrite <- H0.
field.
trivial.
Qed.

Lemma Lcdiv2 : forall a b c : F, b <> 0 -> c <> 0 -> a / b = c -> b = a / c.
intros.
rewrite <- H1.
field.
split; trivial.
intuition.
apply H0.
rewrite <- H1 in |- *.
rewrite H2 in |- *.
unfold Fdiv in |- *;  ring.
Qed.


Ltac IsoleVarAux1 var H T Hyp :=
  match constr:(T) with
  | (var = ?X2 :>?X1) =>
      assert (Hypazerty : T);
       [ exact H | clear Hyp; rename Hypazerty into Hyp ]
  | (?X1 + ?X2 = ?X3 :>?X4) =>
      IsoleVarAux1 var (Lcp1 X1 X2 X3 H) (X1 = X3 - X2 :>X4) Hyp ||
        IsoleVarAux1 var (Lcp2 X1 X2 X3 H) (X2 = X3 - X1 :>X4) Hyp
  | (?X1 - ?X2 = ?X3 :>?X4) =>
      IsoleVarAux1 var (Lcm1 X1 X2 X3 H) (X1 = X3 + X2 :>X4) Hyp ||
        IsoleVarAux1 var (Lcm2 X1 X2 X3 H) (X2 = X1 - X3 :>X4) Hyp
  | (?X1 / ?X2 = ?X3 :>?X4) =>
      match goal with
      | Hop:(?X2 <> 0) |- _ =>
          IsoleVarAux1 var (Lcdiv1 X1 X2 X3 Hop H) (X1 = X2 * X3 :>X4) Hyp
      | _ =>
          cut (X2 <> 0);
           [ intro;
              match goal with
              | Hop:(?X2 <> 0) |- _ =>
                  IsoleVarAux1 var (Lcdiv1 X1 X2 X3 Hop H)
                   (X1 = X2 * X3 :>X4) Hyp
              end
           | idtac ]
      end ||
        match goal with
        | Hop1:(?X2 <> 0),Hop2:(?X3 <> 0) |- _ =>
            IsoleVarAux1 var (Lcdiv2 X1 X2 X3 Hop1 Hop2 H)
             (X2 = X1 / X3 :>X4) Hyp
        | Hop1:(?X2 <> 0) |- _ =>
            cut (X3 <> 0);
             [ intro;
                match goal with
                | Hop2:(?X3 <> 0) |- _ =>
                    IsoleVarAux1 var (Lcdiv2 X1 X2 X3 Hop1 Hop2 H)
                     (X2 = X1 / X3 :>X4) Hyp
                end
             | idtac ]
        | Hop2:(?X3 <> 0) |- _ =>
            cut (X2 <> 0);
             [ intro;
                match goal with
                | Hop1:(?X2 <> 0) |- _ =>
                    IsoleVarAux1 var (Lcdiv2 X1 X2 X3 Hop1 Hop2 H)
                     (X2 = X1 / X3 :>X4) Hyp
                end
             | idtac ]
        | _ =>
            cut (X2 <> 0);
             [ intro; cut (X3 <> 0);
                [ intro;
                   match goal with
                   | Hop1:(?X2 <> 0),Hop2:(?X3 <> 0) |- _ =>
                       IsoleVarAux1 var (Lcdiv2 X1 X2 X3 Hop1 Hop2 H)
                        (X2 = X1 / X3 :>X4) Hyp
                   end
                | trivial ]
             | trivial ]
        end
  | (?X1 * ?X2 = ?X3 :>?X4) =>
      match goal with
      | Hop:(?X2 <> 0) |- _ =>
          IsoleVarAux1 var (Lcmult1 X1 X2 X3 Hop H) (X1 = X3 / X2 :>X4) Hyp
      | _ =>
          cut (X2 <> 0);
           [ intro;
              match goal with
              | Hop:(?X2 <> 0) |- _ =>
                  IsoleVarAux1 var (Lcmult1 X1 X2 X3 Hop H)
                   (X1 = X3 / X2 :>X4) Hyp
              end
           | idtac ]
      end ||
        match goal with
        | Hop:(?X1 <> 0) |- _ =>
            IsoleVarAux1 var (Lcmult2 X1 X2 X3 Hop H) (X2 = X3 / X1 :>X4) Hyp
        | _ =>
            cut (X1 <> 0);
             [ intro;
                match goal with
                | Hop:(?X1 <> 0) |- _ =>
                    IsoleVarAux1 var (Lcmult2 X1 X2 X3 Hop H)
                     (X2 = X3 / X1 :>X4) Hyp
                end
             | idtac ]
        end
  | (- ?X1 = ?X3 :>?X4) =>
      IsoleVarAux1 var (Lcop1 X1 X3 H) (X1 = - X3 :>X4) Hyp
  | _ => fail
  end.


Ltac IsoleVarAux var H T Hyp :=
  match constr:(T) with
  | (?X2 = ?X3 :>?X1) =>
      IsoleVarAux1 var H T Hyp ||
        IsoleVarAux1 var (sym_eq H) (X3 = X2 :>X1) Hyp
  end.

Ltac TypeOf H :=
  match goal with
  | id:?X1 |- _ => match constr:(id) with
                   | H => constr:(X1)
                   | _ => fail
                   end
  end.

Ltac IsoleVar var H := let T := TypeOf H in
                       IsoleVarAux var H T H.

(* Tactic Definition IsoleVar var H := (IsoleVarAux 'var 'H (TypeOf ? H) H). *)

Ltac IsoleVarRing var H := IsoleVar var H; NormalizeRing H.

Ltac RewriteVar var H := IsoleVarRing var H; try rewrite H in *.

(* Tests *)
(*
Lemma test_isole_var_1 : forall a b,  a+b=0 -> a = -b.
Proof.
intros.
IsoleVar a H.
rewrite H; ring.
Qed.

Lemma test_isole_var_2 : forall a b,  a-b=0 -> a = b.
Proof.
intros.
IsoleVar a H.
NormalizeRing H.
assumption.
Qed.

Lemma test_isole_var_3 : forall a b,  b<>0 -> a*b=0 -> a = 0.
Proof.
intros.
IsoleVar a H0.
rewrite H0.
field.
assumption.
Qed.

Lemma test_isole_var_4 : forall a b,  b<>0 -> a/b=0 -> a = 0.
Proof.
intros.
IsoleVar a H0.
NormalizeRing H0.
assumption.
Qed.

Theorem premier_degre : forall a b x,  a<>0 -> a*x+b=0 -> x = -b/a.
Proof.
intros.
IsoleVar x H0.
rewrite H0.
field.
assumption.
Qed.

*)

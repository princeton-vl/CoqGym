Require Import Arith.
Require Import folProof.
Require Import folProp.
Require Import PA.
Require Import model.

Definition natModel : Model LNT :=
  model LNT nat
    (fun f : Functions LNT =>
     match f return (naryFunc nat (arity LNT (inr (Relations LNT) f))) with
     | Languages.Plus => fun x y : nat => y + x
     | Languages.Times => fun x y : nat => y * x
     | Languages.Succ => S
     | Languages.Zero => 0
     end) (fun r : Relations LNT => match r with
                                    end).

Theorem PAconsistent : Consistent LNT PA.
Proof.
apply ModelConsistent with (M := natModel) (value := fun _ : nat => 0).
generalize (fun _ : nat => 0).
intros.
do 8 try induction H; try solve [ simpl in |- *; auto ].
rewrite H.
clear H.
unfold PA7 in |- *.
unfold close in |- *.
unfold nnTranslate in |- *.
simpl in |- *.
intros.
apply H.
clear H.
generalize n.
clear n.
induction
 (ListExt.no_dup nat eq_nat_dec
    (List.app (freeVarFormula LNT (substituteFormula LNT x0 x1 Zero))
       (List.app
          (ListExt.list_remove nat eq_nat_dec x1
             (List.app (freeVarFormula LNT x0)
                (freeVarFormula LNT
                   (substituteFormula LNT x0 x1 (Succ (var x1))))))
          (ListExt.list_remove nat eq_nat_dec x1 (freeVarFormula LNT x0)))));
 intros.
simpl in |- *.
intros.
induction x2 as [| x2 Hrecx2].
apply H1.
replace 0 with (interpTerm LNT natModel n Zero).
apply subInterpFormula2.
rewrite subNNHelp.
assumption.
reflexivity.
apply H0 with x2.
clear H0.
intros.
apply Hrecx2.
intros.
clear Hrecx2.
apply H1.
clear H1.
rewrite <- subNNHelp in H0.
assert
 (interpFormula LNT natModel
    (updateValue LNT natModel (updateValue LNT natModel n x1 x2) x1
       (interpTerm LNT natModel (updateValue LNT natModel n x1 x2)
          (Succ (var x1)))) (nnHelp LNT x0)).
apply subInterpFormula2.
auto.
clear H0 H2.
apply
 freeVarInterpFormula
  with
    (updateValue LNT natModel (updateValue LNT natModel n x1 x2) x1
       (interpTerm LNT natModel (updateValue LNT natModel n x1 x2)
          (Succ (var x1)))).
intros.
unfold updateValue in |- *.
induction (eq_nat_dec x1 x3).
replace
 (interpTerm LNT natModel
    (fun x4 : nat =>
     match eq_nat_dec x1 x4 with
     | left _ => x2
     | right _ => n x4
     end) (Succ (var x1))) with
 (interpTerm LNT natModel (fun _ : nat => x2) (Succ (var x1))).
reflexivity.
apply freeVarInterpTerm.
intros.
induction H2 as [H2| H2].
rewrite H2.
induction (eq_nat_dec x4 x4).
reflexivity.
elim b.
reflexivity.
induction H2.
reflexivity.
assumption.
simpl in |- *.
auto.
simpl in |- *.
intros.
apply H.
intros.
apply H0.
intros.
clear H0 H.
compute in H1.
discriminate H1.
Qed.
(** * Definition of functions and constructors *)

Require Export Relations.
Set Implicit Arguments.

Section Global.

  Section Def.

    Variables X Y X' Y': Type.

(*
    Record function: Type := mkfun {
      body:> relation2 X Y -> relation2 X Y;
      Hmon: forall R S, incl R S -> incl (body R) (body S)
    }.
*)

    Definition function2 := relation2 X Y -> relation2 X' Y'.
    Definition function  := relation2 X Y -> relation2 X Y.

    Definition increasing (F: function) := 
      forall R S, incl R S -> incl (F R) (F S).

    Definition contains (F G: function2) := forall R, incl (F R) (G R).

    (** Constant and identity functions *)
    Definition constant S: function2 := fun _ => S.
    Definition identity: function := fun R => R.

    (** Binary and general union functions *)
    Definition Union2 F G: function2 := fun R => union2 (F R) (G R).
    Definition Union I H: function2 := fun R => union (fun i: I => H i R).

  End Def.

  Section Def'.

    Variables X Y Z X' Y' Z' X'' Y'': Type.

    Definition transparent (B: relation X) (F: function2 X Y X Y') := 
      forall R, incl (F (comp (star B) R)) (comp (star B) (F R)).

    (** Chaining functions *)
    Definition chaining_l (S: relation2 X Y): function2 Y Z X Z := comp S.
    Definition chaining_r (S: relation2 Y Z): function2 X Y X Z := fun R => comp R S.
    Definition Chain (F: function2 X Y X' Y') (G: function2 X Y Y' Z') := fun R => comp (F R) (G R).

    (** Composition *)
    Definition Comp (G: function2 X' Y' X'' Y'') (F: function2 X Y X' Y') := fun R => G (F R).
    

    Variable F: function X Y.   
    Variable R: relation2 X Y.

    (** Simple iteration function *)
    Fixpoint Exp(n: nat): relation2 X Y :=
      match n with
	| O => R
	| S n => F (Exp n)
      end.
    Definition Iter := union Exp.

    (** Increasing iteration function *)
    (* inverser n et R ? *)
    Fixpoint UExp(n: nat): relation2 X Y := 
      match n with
	| O => R
	| S n => union2 (UExp n) (F (UExp n))
      end.
    Definition UIter := union UExp.

    Lemma UExp_incl: forall n, incl (UExp n) (UExp (S n)).
    Proof. intros n x y H; left; auto. Qed.

    Lemma UIter_incl: incl R UIter.
    Proof. intros x y H; exists 0; auto. Qed.
  
  End Def'.

  Section UIter.
    Variables X Y: Type.
    Variable F: function X Y.
    Hypothesis HF: increasing F.

    Lemma UExp_inc: forall n R S, incl R S -> incl (UExp F R n) (UExp F S n).
    Proof.
      intros n R S H; induction n as [ | n IH ]; intros x y XY; simpl; auto.
      celim XY; intro XY. 
      left; exact (IH _ _ XY).
      right; apply (HF IH XY).
    Qed.

    (* begin hide *)
    Lemma UIter_inc: increasing (UIter F).
    Proof.
      intros R S H x y XY; destruct XY as [ n XY ].
      exists n; apply (UExp_inc n H _ _ XY).
    Qed.

    Lemma UExp_UExp: forall R m n, UExp F (UExp F R n) m = UExp F R (m+n).
    Proof.
      intros R m; induction m as [ | m IH ]; intros n.
      reflexivity.
      simpl; rewrite IH; reflexivity.
    Qed.

    Hypothesis HF0: forall R, incl R (F R).
    Hypothesis HF2: forall R, incl (F (F R)) (F R).
    Lemma UIter_02: contains (UIter F) F.
    Proof.
      intros R x y H; destruct H as [ n H ]; cgen H; cgen y; cgen x; 
	induction n as [ | n IH ]; intros x y H.
      apply HF0; exact H.
      celim H; intro H; auto.
      apply HF2; exact (HF IH H).
    Qed. 
    (* end hide *)

  End UIter.
 
  Section UIter'.
    Variable X: Type.
    Variable F: function X X.
    Hypothesis HF: forall R, eeq (trans (F R)) (F (trans R)) .
    Hypothesis HF': increasing F.

    Lemma UExp_trans: forall n R, eeq (trans (UExp F R n)) (UExp F (trans R) n).
      intros n R; induction n as [ | n IH ]; split; intros x y H; auto; celim H; intro H.
      left; exact (proj1 IH _ _ H).
      right; apply (HF' (proj1 IH)); apply (proj1 (HF (UExp F R n))); auto.
      left; exact (proj2 IH _ _ H).
      right; apply (proj2 (HF (UExp F R n))); apply (HF' (proj2 IH) H).
    Qed.

    Lemma UIter_trans: forall R, eeq (trans (UIter F R)) (UIter F (trans R)).
      intro R; split; intros x y H; destruct H as [ i H ]; exists i.
      exact (proj1 (UExp_trans i R) _ _ H).
      exact (proj2 (UExp_trans i R) _ _ H).
    Qed.
  End UIter'.
End Global.

Hint Immediate UExp_incl.
Hint Immediate UIter_incl.

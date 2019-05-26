(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import utils.

Set Implicit Arguments.

Section subcode.

  Variable (X : Type).
  
  Definition code := (nat * list X)%type.

  Implicit Type P : code.
  
  Definition code_start P := fst P.
  Definition code_end P := fst P + length (snd P).
  Definition code_length P := length (snd P).
 
  Definition in_code i P := code_start P <= i < code_end P.
  Definition out_code i P := i < code_start P \/ code_end P <= i.
  
  Fact in_out_code i P : in_code i P -> out_code i P -> False.
  Proof. unfold in_code, out_code; omega. Qed.

  Definition subcode P Q := 
    match P, Q with (i,li), (n,code) => exists l r, code = l ++ li ++ r /\ i = n+length l end.
    
  Arguments code_start P /.
  Arguments code_end P /.
  Arguments code_length P /.
  Arguments in_code i P /.
  Arguments out_code i P /.
  Arguments subcode P Q /.
 
  Fact in_out_code_dec i P : { in_code i P } + { out_code i P }.
  Proof. destruct P as (n,c); simpl; apply interval_dec. Qed.
  
  Infix "<sc" := subcode (at level 70, no associativity).

  Fact subcode_cons_inj i ρ δ P : (i,ρ::nil) <sc P -> (i,δ::nil) <sc P -> ρ = δ.
  Proof.
    destruct P as (j, P).
    intros (l1 & r1 & H1 & H2) (l2 & r2 & H3 & H4).
    rewrite H1 in H3.
    apply list_app_inj, proj2 in H3; try omega.
    inversion H3; trivial.
  Qed.

  Fact subcode_length P Q : P <sc Q -> code_start Q <= code_start P /\ code_end P <= code_end Q.
  Proof.
   destruct P as (iP,cP); destruct Q as (iQ,cQ); simpl.
   intros (l & r & H1 & H2).
   apply f_equal with (f := @length _) in H1.
   revert H1; rew length; split; omega.
  Qed.

  Fact subcode_length' P Q : P <sc Q -> length (snd P) <= length (snd Q).
  Proof.
    revert P Q; intros [] [] (? & ? & ? & ?); simpl; subst; rew length; omega.
  Qed.

  Fact subcode_length_le : forall P Q, P <sc Q -> fst Q <= fst P 
                                               /\ fst P + length (snd P) <= fst Q + length (snd Q).
  Proof.
    intros (iP,cP) (iQ,cQ) (l & r & ? & ?); subst; simpl; rew length; omega.
  Qed.
  
  Fact subcode_start_in_code : forall P Q, 0 < code_length P -> P <sc Q -> in_code (code_start P) Q.
  Proof.
    intros (iP,cP) (iQ,cQ) H (l & r & H1 & H2); simpl in *; subst; revert H; rew length; intro; omega.
  Qed.

  Fact subcode_refl P : P <sc P.
  Proof.
    destruct P; exists nil, nil; split; simpl.
    rewrite <- app_nil_end; auto.
    omega.
  Qed.

  Fact subcode_trans P Q R : P <sc Q -> Q <sc R -> P <sc R.
  Proof.
    revert P Q R; intros (iP,cP) (iQ,cQ) (iR,cR).
    intros (ll1 & rr1 & H1 & H2) (ll2 & rr2 & H3 & H4); subst.
    exists (ll2++ll1), (rr1++rr2); split.
    solve list eq.
    rew length; omega.
  Qed.
  
  Fact subcode_in_code P Q i : P <sc Q -> in_code i P -> in_code i Q.
  Proof. 
    revert P Q; intros (iP,cP) (iQ,cQ) (l & r & H1 & H2); simpl.
    subst; rew length; omega.
  Qed.
  
  Fact subcode_out_code P Q i : P <sc Q -> out_code i Q -> out_code i P.
  Proof. 
    revert P Q; intros (iP,cP) (iQ,cQ) (l & r & H1 & H2); simpl.
    subst; rew length; omega.
  Qed.
  
  Fact subcode_left n m l r : n = m -> (n,l) <sc (m,l++r).
  Proof. exists nil, r; simpl; split; auto; omega. Qed.
  
  Fact subcode_right n m l r : n = m+length l -> (n,r) <sc (m,l++r).
  Proof.
    exists l, nil; split; auto.
    rewrite <- app_nil_end; auto.
  Qed.

  Fact subcode_app_end P n l r : P <sc (n,l) -> P <sc (n,l++r).
  Proof.
    intros; apply subcode_trans with (1 := H).
    exists nil, r; auto.
  Qed.

  Fact subcode_cons P n x l : P <sc (1+n,l) -> P <sc (n,x::l).
  Proof.
    intros; apply subcode_trans with (1 := H).
    exists (x::nil), nil; split.
    solve list eq.
    rew length; omega.
  Qed.
  
  Fact in_code_subcode i P : in_code i P -> exists a, (i,a::nil) <sc P.
  Proof.
    destruct P as (iP,cP); simpl; intros H.
    destruct (list_split_length cP) with (k := i-iP) as (l & [ | a r ] & H1 & H2).
    omega.
    exfalso; subst; solve list eq in H; omega.
    exists a, l, r; split; auto; omega.
  Qed.

  Fact subcode_app_invert_right j Q1 Q2 i I : 
        (i,I::nil) <sc (j,Q1++Q2) -> (i,I::nil) <sc (j,Q1)
                                  \/ (i,I::nil) <sc (length Q1+j,Q2).
  Proof.
    intros (l & r & H1 & H2); simpl in *.
    apply list_app_cons_eq_inv in H1.
    destruct H1 as [ (m & G1 & G2) | (m & G1 & G2) ]; subst.
    + right; exists m, r; rew length; split; auto; omega.
    + left; exists l, m; rew length; split; auto; omega.
  Qed.

  Fact subcode_cons_invert_right j J Q i I : 
        (i,I::nil) <sc (j,J::Q) -> i = j /\ I = J
                                \/ (i,I::nil) <sc (S j,Q).
  Proof.
    intros ([ | K l ] & r & H1 & H2); simpl in *.
    + inversion H1; left; split; auto; omega.
    + right; inversion H1; exists l, r; split; auto; omega.
  Qed.

  Variable Q : code.

  Fact subcode_app_inv i j a l r : j = i+length l -> (i,l++a++r) <sc Q -> (j,a) <sc Q.
  Proof.
    intro; apply subcode_trans.
    exists l, r; auto.
  Qed.
  
  Fact subcode_cons_inv i j a r : j = i -> (i,a++r) <sc Q -> (j,a) <sc Q.
  Proof.
    intro; apply subcode_app_inv with (l := nil); simpl; omega.
  Qed.

  Fact subcode_snoc_inv i j a l : j = i+length l -> (i,l++a) <sc Q -> (j,a) <sc Q.
  Proof.
    intros H.
    apply subcode_trans.
    exists l, nil; split; auto.
    solve list eq.
  Qed.

  Fact subcode_cons_invert_left i I l : (i,I::l) <sc Q -> (i,I::nil) <sc Q /\ (S i,l) <sc Q.
  Proof.
    intros H1; split.
    + revert H1; apply subcode_cons_inv with (a := _::nil); auto.
    + revert H1; apply subcode_snoc_inv with (l := _::nil); simpl; omega.
  Qed.

End subcode.

Arguments code_start {X} P /.
Arguments code_end {X} P /.
Arguments in_code {X} i P /.
Arguments out_code {X} i P /.
Arguments subcode {X} P Q /.

Infix "<sc" := subcode (at level 70, no associativity).


(* Solve many subcode goals looking for a solution into hyps *)
      
Ltac subcode_tac := 
       unfold fst, snd;
       try match goal with | H: subcode (_,?l) ?c |- subcode (_,?i) ?c 
            => (match i with ?j::nil => match type of H with context[j] => apply subcode_trans with (2 := H) end end ||
                match type of H with context[i] => apply subcode_trans with (2 := H) end)
       end;
       match goal with
         | |- subcode (_,?i) (_,?c) => focus_goal i c 
       end;
       match goal with 
         | |- subcode (_,?i::nil) (_,?l++?i::?r) => exists l, r 
         | |- subcode _ (_,?l++_++?r)            => exists l, r 
         | |- subcode (_,?i) (_,?l++?i)          => exists l, nil 
       end;
       split; auto; rew length; try omega.

(* Add it to auto so that fam sss * will try it to solve the subcode goal it generates *)

Hint Extern 4 (subcode _ _) => subcode_tac.

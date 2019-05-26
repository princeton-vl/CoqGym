(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import utils subcode.

Set Implicit Arguments.

(** * A certified low-level compiler *)

Tactic Notation "dest" "eq" "nat" "dec" "as" intropattern(H) :=
    match goal with 
      |- context[eq_nat_dec ?x ?y] => destruct (eq_nat_dec x y) as H
    end; auto.

Tactic Notation "solve" "eq" "nat" "dec" := 
    match goal with 
      |- context[eq_nat_dec ?x ?x] => destruct (eq_nat_dec x x) as [ | [] ]; [ | reflexivity ]
    end; auto.
    
Section linker.
 
  Variable (X Y : Type)
           (c : (nat -> nat) -> nat -> X -> list Y) (* instruction compiler w.r.t. a given linker & a position *)
           (lc : X -> nat)                          (* compiled code length does not depend on linker or position *)
           (Hc : forall f n x, length (c f n x) = lc x).

  Fixpoint length_compiler lx :=
    match lx with
      | nil   => 0
      | x::lx => lc x+length_compiler lx
    end.
    
  Fact length_compiler_app ll mm : length_compiler (ll++mm) = length_compiler ll + length_compiler mm.
  Proof.
    induction ll as [ | x ll IH ]; simpl; auto.
    rewrite IH; omega.
  Qed.
    
  Notation lsum := length_compiler.

  Fixpoint link i ll j : list (nat*nat) :=
    match ll with
      | nil   => nil
      | x::ll => (i,j)::link (S i) ll (lc x+j)
    end.
    
  Fact link_app i ll mm j : link i (ll++mm) j = link i ll j ++ link (length ll+i) mm (lsum ll+j).
  Proof.
    revert i j; induction ll as [ | x ll IH ]; simpl; intros i j; f_equal.
    rewrite IH; do 2 f_equal; omega.
  Qed.
  
  Fact link_fst i ll j : map fst (link i ll j) = list_an i (length ll).
  Proof.
    revert i j; induction ll; simpl; intros; f_equal; auto.
  Qed.
  
  Section comp.
  
    Variable lnk : nat -> nat.

    Fixpoint comp i ll j :=
      match ll with
        | nil   => nil
        | x::ll => c lnk i x ++ comp (S i) ll (lc x+j)
      end.
    
    Fact comp_app i ll mm j : comp i (ll++mm) j = comp i ll j ++ comp (length ll+i) mm (lsum ll+j).
    Proof.
      revert i j; induction ll as [ | x ll IH ]; simpl; intros i j; auto.
      rewrite IH; solve list eq; do 3 f_equal; omega.
    Qed.
    
    Fact comp_length i ll j : length (comp i ll j) = lsum ll.
    Proof.
      revert i j; induction ll as [ | x ll IH ]; simpl; intros i j; auto.
      rew length; rewrite IH, Hc; trivial.
    Qed.
  
  End comp.

  Variable (P : nat * list X) (i : nat) (err : nat).

  Definition linker :=
    let ll := (length (snd P) + fst P,lsum (snd P)+i)::link (fst P) (snd P) i
    in fun j => match list_assoc eq_nat_dec j ll with
        | None   => err
        | Some p => p
    end.
    
  (* These two lemmas specify the linker *)
    
  Fact linker_app ll mm : snd P = ll++mm -> linker (length ll+fst P) = lsum ll + i.
  Proof.
    intros H; unfold linker.
    destruct P as (iP,lP).
    rewrite H; simpl in H |- *.
    destruct mm as [ | x mm ].
    * rewrite <- app_nil_end.
      solve eq nat dec.
    * rew length.
      dest eq nat dec as [ H1 | H1 ]; [ omega | clear H1 ].
      rewrite link_app, list_assoc_app.
      generalize (list_assoc_In eq_nat_dec (length ll + iP) (link iP ll i)).
      destruct (list_assoc eq_nat_dec (length ll + iP) (link iP ll i)) as [ j | ].
      - intros H1.
        apply in_map with (f := @fst _ _) in H1.
        rewrite link_fst, list_an_spec in H1; simpl in H1; omega.
      - intros; simpl; solve eq nat dec.
  Qed.
  
  Fact linker_err_code j : j < fst P \/ length (snd P) + fst P < j -> linker j = err.
  Proof.
    unfold linker.
    destruct P as (iP,lP); simpl; intros H.
    dest eq nat dec as [ H1 | _ ]; [ omega | ].
    generalize (list_assoc_In eq_nat_dec j (link iP lP i)).
    destruct (list_assoc eq_nat_dec j (link iP lP i)); auto.
    intros H1.
    apply in_map with (f := @fst _ _) in H1.
    rewrite link_fst, list_an_spec in H1; simpl in H1; omega.
  Qed.

  Definition compiler := comp linker (fst P) (snd P) i.
  
  Fact compiler_length : length compiler = length_compiler (snd P).
  Proof. apply comp_length. Qed.

  Section linker_in_code.

    Hypothesis (Hlc : forall x, 1 <= lc x).

    Fact linker_in_code j : in_code j P -> in_code (linker j) (i,compiler).
    Proof.
      intros H; red in H; simpl in H.
      destruct (@list_split_length _ (snd P) (j - fst P)) as (ll & mm & H1 & H2);
        try omega.
      replace j with (length ll+fst P) by omega.
      rewrite (linker_app _ _ H1).
      red; simpl; rewrite compiler_length, H1, length_compiler_app.
      rewrite H1, app_length in H.
      destruct mm. 
      simpl in H; omega.
      simpl.
      generalize (Hlc x); omega.
    Qed.

  End linker_in_code.
  
  Fact compiler_subcode j x : 
          (j,x::nil) <sc P 
       -> (linker j, c linker j x) <sc (i,compiler)
       /\  linker (1+j) = lc x + linker j.
  Proof.
    case_eq P; intros iP lP HP (l & r & H1 & H2); simpl in H1.
    assert (linker j = lsum l + i) as Hj.
    { generalize (linker_app l (x::r)).
      rewrite HP; simpl; intros E.
      rewrite <- E; auto; f_equal; omega. }
    assert (linker (1+j) = lc x + linker j) as HSj.
    {  generalize (linker_app (l++x::nil) r).
      rewrite HP, app_ass; simpl; intros H3.
      specialize (H3 H1).
      eq goal H3; f_equal.
      f_equal.
      rew length; omega.
      rewrite length_compiler_app; simpl; omega. }
    split; auto.
    unfold compiler; rewrite HP, H1; simpl.
    exists (comp linker iP l i), (comp linker (1+length l+iP) r (lc x+lsum l+i)); split.
    rewrite comp_app; simpl; do 3 f_equal; omega.
    rewrite comp_length; omega.
  Qed.
  
  Fact linker_code_start : linker (code_start P) = i.
  Proof. apply (linker_app nil (snd P)); auto. Qed.
  
  Fact linker_middle ll x mm : snd P = ll++x::mm -> linker (length ll+fst P) = lsum ll+i.
  Proof. apply linker_app. Qed.
  
  Fact linker_code_end : linker (code_end P) = lsum (snd P)+i.
  Proof.
    unfold code_end; rewrite plus_comm.
    apply (linker_app _ nil), app_nil_end.
  Qed.
  
   Fact linker_out_code j : err < i \/ length_compiler (snd P) + i <= err 
                        -> out_code j P -> out_code (linker j) (i,compiler).
  Proof.
    intros H1 H2.
    red in H2.
    destruct (eq_nat_dec j (code_end P)) as [ H | H ].
    rewrite H, linker_code_end; simpl.
    rewrite compiler_length; omega.
    rewrite linker_err_code.
    simpl; rewrite compiler_length; omega.
    simpl in H2, H; omega.
  Qed.

  Fact linker_out_err j : err = lsum (snd P) + i -> out_code j P -> linker j = err.
  Proof.
    intros H1 H2.
    destruct (eq_nat_dec j (code_end P)) as [ H | H ].
    + rewrite H1, H; unfold code_end.
      rewrite plus_comm, linker_app with (mm := nil); auto.
      rewrite <- app_nil_end; auto.
    + apply linker_err_code; red in H2; unfold code_end, code_start in *; omega.
  Qed.

End linker.

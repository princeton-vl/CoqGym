(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Trying an abstract compiler with labels instead of nats as source code addressing *)

Require Import List Arith Omega.

Require Import utils subcode.

Set Implicit Arguments.

Section linker_compiler.
 
  Variable (L X Y : Type) (eqL_dec : eqdec L)
           (c : (L -> nat) -> L -> X -> list Y)     (* instruction compiler w.r.t. a given linker & a label *)
           (lc : X -> nat)                          (* compiled code length does not depend on linker or label *)
           (Hc : forall f l x, length (c f l x) = lc x)
           (Hlc : forall x, 1 <= lc x).
           
  (* ll is of a list of labels and each label is possibly followed by one instruction *)

  Implicit Type (ll : list (L* option X)).
  
  Notation labels := (map fst).
  
  Definition olc (ox : option X) := match ox with None => 0 | Some x => lc x end.

  Fixpoint length_compiler ll :=
    match ll with
      | nil        => 0
      | (_,ox)::ll => olc ox + length_compiler ll
    end.

  Fact length_compiler_app ll mm : length_compiler (ll++mm) = length_compiler ll + length_compiler mm.
  Proof.
    induction ll as [ | (?,[|]) ll IH ]; simpl; auto.
    rewrite IH; omega.
  Qed.
    
  Notation lsum := length_compiler.

  Fixpoint link ll j : list (L*nat) :=
    match ll with
      | nil          => nil
      | (l,ox)::ll   => (l,j)::link ll (olc ox+j)
    end.
    
  Fact link_app ll mm j : link (ll++mm) j = link ll j ++ link mm (lsum ll+j).
  Proof.
    revert j; induction ll as [ | (?,[|]) ? IH ]; simpl; intros ?; f_equal;
    rewrite IH; do 2 f_equal; omega.
  Qed.
  
  Fact map_fst_link ll j : map fst (link ll j) = labels ll.
  Proof.
    revert j; induction ll as [ | (?,[|]) ll IH ]; intros j; simpl; f_equal; auto.
  Qed.

  Section comp.
  
    Variable lnk : L -> nat.
    
    Definition ocomp l (ox : option X) := match ox with None => nil | Some x => c lnk l x end.

    Fixpoint comp ll j :=
      match ll with
        | nil        => nil
        | (l,ox)::ll => ocomp l ox ++ comp ll (olc ox+j)
      end.
    
    Fact comp_app ll mm j : comp (ll++mm) j = comp ll j ++ comp mm (lsum ll+j).
    Proof.
      revert j; induction ll as [ | (l,[|]) ll IH ]; simpl; intros j; auto.
      rewrite IH; solve list eq; do 3 f_equal; omega.
    Qed.
    
    Fact comp_length ll j : length (comp ll j) = lsum ll.
    Proof.
      revert j; induction ll as [ | (l,[|]) ll IH ]; simpl; intros j; auto.
      rew length; rewrite IH, Hc; trivial.
    Qed.
  
  End comp.

  Variable (P : list (L* option X)) (i : nat) (err : nat).

  Definition linker :=
    let lf := link P i
    in fun j => match list_assoc eqL_dec j lf with
        | None   => err
        | Some p => p
    end.
    
  (* These two lemmas specify the linker *)
    
  Fact linker_app lP rP l ox : P = lP++(l,ox)::rP -> ~ In l (labels lP) -> linker l = lsum lP + i.
  Proof.
    intros H1 H2; unfold linker.
    rewrite H1, link_app, list_assoc_app.
    rewrite <- map_fst_link with (j := i) in H2.
    rewrite (not_In_list_assoc eqL_dec _ _ H2).
    simpl link; rewrite list_assoc_eq; auto.
  Qed.
  
  Fact linker_err_code l : ~ In l (labels P) -> linker l = err.
  Proof.
    intros H1.
    unfold linker.
    rewrite <- map_fst_link with (j := i) in H1.
    rewrite (not_In_list_assoc eqL_dec _ _ H1).
    auto.
  Qed.

  Definition compiler := comp linker P i.
  
  Fact compiler_length : length compiler = length_compiler P.
  Proof. apply comp_length. Qed.
  
  Fact linker_in_code j ii : In (j, Some ii) P -> in_code (linker j) (i,compiler).
  Proof.
    intros H.
    assert (In j (map fst P)) as H1.
    { apply in_map_iff; exists (j,Some ii); auto. }
    apply list_first_dec with (P := fun x => x = j) in H1; auto.
    destruct H1 as (l & x & r & H1 & H2 & H3); subst x.
    destruct map_middle_inv with (1 := H1) as (l' & (j',ox') & r' & H4 & H5 & H6 & H7).
    unfold compiler.
    simpl in H6; subst j'.
    assert (~ In j (map fst l')) as H8.
    { rewrite H5.
      intros E.
      apply H3 in E; destruct E; auto. }
    rewrite linker_app with (1 := H4); auto.
    rewrite H4.
    simpl; rew length.
    rewrite comp_length, length_compiler_app.
    simpl.
    rewrite H4 in H.
    apply in_app_or in H.
    destruct H as [ H | [ H | H ] ].
    * exfalso.
      apply H8.
      apply in_map_iff.
      exists (j, Some ii); auto.
    * inversion H; subst.
      simpl.
      generalize (Hlc ii); omega.
    * apply in_split in H.
      destruct H as (l1 & l2 & H); subst r'.
      rewrite length_compiler_app; simpl.
      generalize (Hlc ii); omega.
  Qed.

  Fact linker_subcode_2 lP rP j ox1 k ox2 : 
          ~ In j (map fst lP)
       -> ~ In k (map fst lP)
       -> j <> k
       -> P = lP++(j,ox1)::(k,ox2)::rP 
       -> linker k = olc ox1 + linker j.
  Proof.
    intros H1 H2 H3 H4.
    rewrite linker_app with (1 := H4); auto.
    focus (k,ox2) in H4.
    rewrite linker_app with (1 := H4); auto.
    rewrite length_compiler_app; simpl; omega.
    rewrite map_app; intros H.
    apply in_app_or in H.
    destruct H as [ H | [ H | [] ] ].
    apply H2; auto.
    apply H3; auto.
  Qed.

  Fact compiler_subcode lP rP j x : 
          ~ In j (map fst lP)
       -> P = lP++(j,Some x)::rP  
       -> (linker j, c linker j x) <sc (i,compiler).
  Proof.
    intros H1 H2.
    rewrite linker_app with (1 := H2); auto.
    unfold compiler.
    rewrite H2.
    rewrite comp_app; simpl.
    exists (comp linker lP i), (comp linker rP (lc x + (lsum lP + i))); split; auto.
    rewrite comp_length; omega.
  Qed.
  
  Fact linker_first rP l ox : P = (l,ox)::rP -> linker l = i.
  Proof.
    intros H.
    focus (l,ox) in H.
    rewrite linker_app with (1 := H); auto.
  Qed.
  
  Definition linker_middle := linker_app.
  
  Fact linker_last lP l : ~ In l (labels lP) -> P = lP++(l,None)::nil -> linker l = lsum P+i.
  Proof.
    intros H1 H2.
    rewrite linker_app with (1 := H2); auto.
    rewrite H2, length_compiler_app; simpl; omega.
  Qed.

End linker_compiler.

Section label_program.

  Variable X : Type.

  Fixpoint label_program i (l : list X) : list (nat * option X) := 
    match l with
      | nil  => nil
      | x::l => (i,Some x)::label_program (S i) l
    end.
   
  Fact label_program_fst i l : map fst (label_program i l) = list_an i (length l).
  Proof. revert i; induction l; simpl; intros; f_equal; auto. Qed.
  
  Fact label_program_app i l m : label_program i (l++m) = label_program i l ++ label_program (length l+i) m.
  Proof.
    revert i; induction l as [ | x l IH ]; simpl; intros; auto; rewrite IH; do 3 f_equal; omega.
  Qed.
  
  Fact label_program_length i l : length (label_program i l) = length l.
  Proof. revert i; induction l; simpl; intros; f_equal; auto. Qed.
  
End label_program.

Section comp.

  Variable (X Y : Type)
           (c : (nat -> nat) -> nat -> X -> list Y) (* instruction compiler w.r.t. a given linker & a position *)
           (lc : X -> nat)                          (* compiled code length does not depend on linker or position *)
           (Hc : forall f n x, length (c f n x) = lc x)
           (Hlc : forall x, 1 <= lc x).
           
  Fixpoint lsum lx :=
    match lx with
      | nil   => 0
      | x::lx => lc x+lsum lx
    end.
    
  Fact length_compiler_lsum j ll : length_compiler lc (label_program j ll) = lsum ll.
  Proof. revert j; induction ll; simpl; intros; f_equal; auto. Qed.
           
  Variable (P : nat * list X) (j err : nat).
           
   Let Q := label_program (fst P) (snd P) ++ (length (snd P)+fst P,None) :: nil.
           
   Definition lnk := @linker _ X eq_nat_dec lc Q j err.
   Definition cmp := @compiler _ _ _ eq_nat_dec c lc Q j err.
   
   Fact lnk_app ll mm : snd P = ll++mm -> lnk (length ll+fst P) = lsum ll + j.
   Proof.
    unfold lnk, Q.
    destruct P as (i,lP); simpl.
    intros H.
    rewrite H.
    destruct mm as [ | x mm ].
    * rewrite <- app_nil_end.
      rewrite linker_app with (1 := eq_refl).
      rewrite length_compiler_lsum; auto.
      rewrite label_program_fst, list_an_spec.
      omega.
    * rewrite label_program_app; simpl.
      focus (length ll+i,Some x).
      rewrite linker_app with (1 := eq_refl).
      rewrite length_compiler_lsum; auto.
      rewrite label_program_fst, list_an_spec.
      omega.
  Qed.
 
  Fact lnk_err_code k : k < fst P \/ length (snd P) + fst P < k -> lnk k = err.
  Proof.
    unfold lnk, Q.
    destruct P as (i,lP); simpl; intros H.
    rewrite linker_err_code; auto.
    rewrite map_app; simpl; intros E.
    apply in_app_or in E.
    destruct E as [ E | [ E | [] ] ].
    * rewrite label_program_fst, list_an_spec in E.
      omega.
    * omega.
  Qed.

  Fact cmp_length : length cmp = lsum (snd P).
  Proof.
    unfold cmp.
    rewrite compiler_length; auto.
    unfold Q.
    rewrite length_compiler_app, length_compiler_lsum; simpl; omega.
  Qed.
 
  Fact lnk_in_code k : in_code k P -> in_code (lnk k) (j,cmp).
  Proof.
    intros H.
    apply in_code_subcode in H.
    destruct H as (ii & H).
    unfold cmp, lnk, Q.
    apply linker_in_code with ii; auto.
    destruct P as (i & llP); simpl.
    destruct H as (lP & rP & H1 & H2).
    rewrite H1.
    rewrite label_program_app.
    apply in_or_app; left.
    apply in_or_app; right.
    left; f_equal; omega.
  Qed.

  Fact cmp_subcode i x : 
          (i,x::nil) <sc P 
       -> (lnk i, c lnk i x) <sc (j,cmp)
       /\  lnk (1+i) = lc x + lnk i.
  Proof.
    intros H.
    case_eq P; intros iP llP HP.
    rewrite HP in H.
    destruct H as (lP & rP & H1 & H2).
    split.
    unfold cmp, lnk, Q; rewrite HP; unfold fst, snd.
    rewrite H1, label_program_app; simpl.
    eapply  compiler_subcode.
    apply f_equal with (f := label_program iP) in H1.
    rewrite label_program_app in H1; simpl in H1.
    apply compiler_subcode with (eqL_dec := eq_nat_dec) (c := c) (lc := lc) (i := i) (err := err) in H1; auto.
    2: rewrite label_program_fst, list_an_spec; omega.
    unfold cmp, lnk, Q; rewrite HP; unfold fst, snd.
    apply H1.
    apply compiler_subcode with (lP rP.
    unfold cmp, lnk, Q; split.
    
 
    destruct H as (ii & H).
  
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

   
   
     




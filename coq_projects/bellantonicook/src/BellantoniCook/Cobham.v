(** The language of Cobham *)

Require Import Bool Arith List.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.MultiPoly.

(** * Syntax and induction principle

  - [Cobham_ind2] is a handmade induction principle because the one generated automatically by Coq
    ignores the type [list BC] in the constructor [Comp].
*)

Inductive Cobham : Type :=
| Zero : Cobham
| Proj : nat -> nat -> Cobham
| Succ : bool -> Cobham
| Smash : Cobham
| Rec  : Cobham -> Cobham -> Cobham -> Cobham -> Cobham
| Comp : nat -> Cobham -> list Cobham -> Cobham.

Definition Rec2 g h j := Rec g h h j.

Lemma Cobham_ind2' :
  forall P : Cobham -> Prop,
  forall Q : list Cobham -> Prop,
  Q nil ->
  (forall e l, P e -> Q l -> Q (e :: l)) ->
  P Zero ->
  (forall n i, P (Proj n i)) ->
  (forall b, P (Succ b)) ->
  P Smash ->
  (forall j g h0 h1, P j -> P g -> P h0 -> P h1 -> P (Rec j g h0 h1)) ->
  (forall n h l, P h -> Q l -> P (Comp n h l)) ->
  forall e, P e.
Proof.
 fix Cobham_ind2' 11; intros.
 destruct e; auto.
 apply H5; eapply Cobham_ind2'; eauto.
 apply H6.
 eapply Cobham_ind2'; eauto.
 revert l.
 fix Cobham_ind2'0 1.
 intro.
 destruct l.
 apply H.
 apply H0.
 eapply Cobham_ind2'; eauto.
 apply Cobham_ind2'0.
Qed.

Lemma Cobham_ind2 :
  forall P : Cobham -> Prop,
  P Zero ->
  (forall n i, P (Proj n i)) ->
  (forall b, P (Succ b)) ->
  P Smash ->
  (forall j g h0 h1, P j -> P g -> P h0 -> P h1 -> P (Rec j g h0 h1)) ->
  (forall n h l, P h -> (forall e, In e l -> P e) ->
    P (Comp n h l)) ->
  forall e, P e.
Proof.
 intros.
 induction e using Cobham_ind2' 
   with (Q := fun l => forall e, In e l -> P e); auto.
 simpl;intros; tauto.
 simpl.
 intros e' [ | ]; intros; subst; auto.
Qed.

(** * Arity

  - [arity e] returns the arity (i.e., the number variables)
    of the expression [e] if it is well formed, or an error including the arity of the subterms.
*)

Inductive Arity : Set :=
| error_Rec : Arity -> Arity -> Arity -> Arity -> Arity
| error_Comp : Arity -> list Arity -> Arity
| error_Proj : nat -> nat -> Arity
| ok_arity : nat -> Arity.

Definition arity_eq (a1 a2 : Arity) :=
  match a1, a2 with
    | ok_arity n1, ok_arity n2 => beq_nat n1 n2
    | _, _ => false
  end.

Lemma arity_eq_true x1 x2 :
  arity_eq x1 x2 = true -> x1 = x2.
Proof.
 intros; unfold arity_eq in H.
 destruct x1; try discriminate.
 destruct x2; try discriminate.
 apply beq_nat_true in H; subst; trivial.
Qed.

Lemma arity_eq_refl : forall n, arity_eq (ok_arity n) (ok_arity n) = true.
Proof.
  intros; case (ok_arity n); simpl; intros.
  rewrite beq_nat_true_iff; trivial.
Qed.

Fixpoint arity (e : Cobham) : Arity :=
  match e with
    | Zero => ok_arity 0
    | Proj n j => if leb (S j) n 
      then ok_arity n else error_Proj n j 
    | Succ _ => ok_arity 1
    | Smash => ok_arity 2
    | Rec g h0 h1 j => 
      match arity g, arity h0, arity h1, arity j with
        | ok_arity gn, ok_arity h0n, ok_arity h1n, ok_arity jn =>
          if beq_nat (S (S gn)) h0n && 
             beq_nat h1n h0n &&
             beq_nat (S jn) h1n 
            then ok_arity jn 
            else error_Rec (ok_arity gn) (ok_arity h0n) 
              (ok_arity h1n) (ok_arity jn)
        | ag, ah0, ah1, aj => error_Rec ag ah0 ah1 aj 
      end
    | Comp n h l => 
      match arity h, map arity l with
        | ok_arity nh, al => 
          if beq_nat nh (length l) &&
            forallb (fun e => arity_eq e (ok_arity n)) al then
              ok_arity n else error_Comp (ok_arity nh) al
        | e , le => error_Comp e le 
      end
  end.

Lemma Cobham_ind_inf' :
  forall (P : nat -> Cobham -> Prop),
  forall Q : nat -> list Cobham -> Prop,
  (forall n, Q n nil) ->
  (forall e n l, P n e -> Q n l -> Q n (e :: l)) ->
  P 0 Zero ->
  (forall n i, i < n  ->  P n (Proj n i)) ->
  (forall b, P 1 (Succ b)) ->
  (P 2 Smash) ->
  (forall n g h0 h1 j, 
    arity g = ok_arity n ->
    arity h0 = ok_arity (S (S n)) ->
    arity h1 = ok_arity (S (S n)) ->
    arity j = ok_arity (S n) ->
    P n g -> 
    P (S (S n)) h0 -> 
    P (S (S n)) h1 -> 
    P (S n) j -> 
    P (S n) (Rec g h0 h1 j)) ->
  (forall n h rl, 
    arity h = ok_arity (length rl)  ->
    (forall e, In e rl -> arity e = ok_arity n) ->
    P (length rl)  h -> 
    Q n rl ->
    P n (Comp n h rl)) ->
  forall e n , arity e = ok_arity n -> P n e.
Proof.
 fix Cobham_ind_inf' 11; intros.
 destruct e; simpl in *.

 injection H7; intros; subst; auto.

 destruct n0; try discriminate.
 case_eq (leb n1 n0); intros; rewrite H8 in H7; try discriminate.
 injection H7; intros; subst; auto.
 apply H2.
 apply leb_complete in H8; omega.

 injection H7; intros; subst; auto.
 injection H7; intros; subst; auto.

 case_eq (arity e1); intros; rewrite H8 in H7; try discriminate.
 case_eq (arity e2); intros; rewrite H9 in H7; try discriminate.
 case_eq (arity e3); intros; rewrite H10 in H7; try discriminate.
 case_eq (arity e4); intros; rewrite H11 in H7; try discriminate.
 destruct n1; simpl; intros; try discriminate; auto.
 destruct n1; simpl; intros; try discriminate; auto.
 case_eq (beq_nat n0 n1); intros; rewrite H12 in H7; try discriminate.
 apply beq_nat_true in H12; subst.
 case_eq (beq_nat n2 (S (S n1))); intros; rewrite H12 in H7; try discriminate.
 apply beq_nat_true in H12; subst.
 case_eq (beq_nat n3 (S n1)); intros; rewrite H12 in H7; try discriminate.
 apply beq_nat_true in H12; subst.
 simpl in H7.
 injection H7; intros; subst.
 apply H5; auto.
 eapply Cobham_ind_inf'; eauto.
 eapply Cobham_ind_inf'; eauto.
 eapply Cobham_ind_inf'; eauto.
 eapply Cobham_ind_inf'; eauto.

 case_eq (arity e); intros; rewrite H8 in H7; try discriminate.
 case_eq (beq_nat n1 (length l)); intros; rewrite H9 in H7; try discriminate.
 case_eq (forallb (fun e : Arity => arity_eq e (ok_arity n0)) (map arity l)); 
 intros; rewrite H10 in H7;try discriminate.
 simpl in H7.
 injection H7; intros; subst.
 rewrite forallb_forall in H10.
 apply beq_nat_true in H9; subst.
 apply H6; trivial.
 intros.
 apply arity_eq_true. 
 apply H10.
 apply in_map_iff.
 exists e0; split; trivial.
 eapply Cobham_ind_inf'; eauto.
 clear H8.
 revert l H10.
 fix Cobham_ind_inf'0 1.
 intros.
 destruct l.
 auto.
 eapply H0.
 eapply Cobham_ind_inf'; eauto.
 apply arity_eq_true.
 apply H10.
 simpl; auto.
 apply Cobham_ind_inf'0.
 intros.
 apply H10.
 simpl; auto.
Qed.

Lemma Cobham_ind_inf :
  forall (P : nat -> Cobham -> Prop),
  P 0 Zero ->
  (forall n i, i < n  ->  P n (Proj n i)) ->
  (forall b, P 1 (Succ b)) ->
  (P 2 Smash) ->
  (forall n g h0 h1 j, 
    arity g = ok_arity n ->
    arity h0 = ok_arity (S (S n)) ->
    arity h1 = ok_arity (S (S n)) ->
    arity j = ok_arity (S n) ->
    P n g -> 
    P (S (S n)) h0 -> 
    P (S (S n)) h1 -> 
    P (S n) j ->
    P (S n) (Rec g h0 h1 j)) ->
  (forall n h rl, 
    arity h = ok_arity (length rl)  ->
    (forall e, In e rl -> arity e = ok_arity n) ->
    P (length rl) h -> 
    (forall r, In r rl -> P n r) ->
    P n (Comp n h rl)) ->
  forall e n , arity e = ok_arity n -> P n e.
Proof.
  intros.
  apply Cobham_ind_inf'
    with (Q := fun n l => forall e , In e l -> P n e); auto; simpl in *; intros.
  tauto.
  destruct H8; subst; auto.
Qed.

(** * Semantics

  - [Sem e vl] is the evaluation of the expression [e] where the [i]th variable is
    instantiated with the [i]th value of [vl].
    If a variable is not assigned a value, then it is assumed to be the empty bitstring [nil].
    Values in [vl] that do not correspond to a variable are ignored.

  - [Cobham_ind_inf] is an induction principle that makes easier dealing with arity in inductive proofs.
*)

Fixpoint sem_Rec (sem_g sem_h0 sem_h1 : list bs -> bs) (v : bs) (vl : list bs) : bs :=
  match v with
    | nil => sem_g vl
    | b::v' => if b then 
      sem_h1 (v' :: (sem_Rec sem_g sem_h0 sem_h1 v' vl) :: vl)
      else sem_h0 (v' :: (sem_Rec sem_g sem_h0 sem_h1 v' vl) :: vl)
  end.

Fixpoint smash' (x y : bs) :=
  match x with 
    | nil => y
    | _ :: x' => false :: smash' x' y
  end.

Lemma length_smash' x y :
  length (smash' x y) = length x + length y.
Proof.
  induction x; simpl; trivial.
  intros; rewrite IHx; trivial.
Qed.

Fixpoint smash_bs (x y : bs) : bs :=
  match x with
    | nil => true :: nil
    | _ :: x' => smash' y (smash_bs x' y)
  end.

Lemma length_smash x y :
  length (smash_bs x y) = 1 + length x * length y.
Proof.
  induction x; simpl; trivial; intros.
  rewrite length_smash', IHx; omega.
Qed.

Fixpoint Sem (e: Cobham) (vl:list bs) : bs :=
  match e with
  | Zero => nil
  | Proj n j => nth j vl nil
  | Succ b => b :: hd nil vl
  | Smash => smash_bs (hd nil vl) (hd nil (tl vl))
  | Rec g h0 h1 j =>  
    sem_Rec (Sem g) (Sem h0) (Sem h1) (hd nil vl) (tail vl)
  | Comp _ h l => Sem h (List.map (fun e => Sem e vl) l)
  end.

Lemma simpl_Rec : forall g h0 h1 j l,
  Sem (Rec g h0 h1 j) l = sem_Rec (Sem g) (Sem h0) (Sem h1) (hd nil l) (tl l).
Proof.
 intros; simpl; trivial.
Qed.

Lemma Sem_add_zero : forall e n,
  arity e = ok_arity n ->
  forall l,
  length l <= n ->
  Sem e l = Sem e (l ++ (map (fun e => nil) (seq 0 (n - length l)))).
Proof.
 refine (Cobham_ind_inf (fun n e =>  forall l : list bs,
   length l <= n ->
   Sem e l = Sem e (l ++ map (fun _ : nat => nil) (seq 0 (n - length l)))) _ _ _ _ _ _); simpl; auto; intros.

 destruct (le_lt_dec (length l) i).
 rewrite nth_overflow; trivial.
 rewrite app_nth2; trivial.
 rewrite nth_map_cst; trivial. 
 rewrite app_nth1; trivial.
 f_equal; destruct l; simpl; trivial.
 f_equal; destruct l; simpl; trivial.
 destruct l0; simpl; trivial.
 destruct l; simpl in *; try discriminate.
 rewrite <- app_nil_l with (l := (map (fun _ : nat => nil) (seq 1 n))).
 rewrite <- seq_shift, map_map.
 replace n with (n - length (@nil bs)).
 apply H3; trivial.
 simpl; omega.
 simpl; omega.
 induction l; simpl.
 apply H3; trivial; omega.
 rewrite <- IHl.
 replace (l :: sem_Rec (Sem g) (Sem h0) (Sem h1) l l0
   :: l0 ++ map (fun _ : nat => nil) (seq 0 (n - length l0))) with
 ((l :: sem_Rec (Sem g) (Sem h0) (Sem h1) l l0 :: l0) ++ 
   (map (fun _ : nat => nil) (seq 0 (n - length l0)))); trivial.
 case a.
 erewrite H5; eauto; simpl; trivial; omega.
 erewrite H4; eauto; simpl; trivial; omega. 
 f_equal.
 apply map_ext2; intros.
 eapply H2; trivial.
Qed.

Lemma Sem_remove_zero : forall e n,
  arity e = ok_arity n ->
  forall l l',  n = length l ->
    Sem e l = Sem e (l ++ l').
Proof.
 refine (Cobham_ind_inf (fun n e => 
   forall l l',  n = length l -> Sem e l = Sem e (l ++ l')) _ _ _ _ _ _); simpl; auto; intros.
 rewrite app_nth1; trivial; omega.
 destruct l; simpl in *; try discriminate; trivial.
 destruct l; simpl in *; try discriminate; trivial.
 destruct l0; simpl in *; try discriminate; trivial.
 destruct l; simpl in *; try discriminate.
 induction l; simpl.
 eapply H3; eauto; omega.
 rewrite <- IHl.
 replace (l :: sem_Rec (Sem g) (Sem h0) (Sem h1) l l0 :: l0 ++ l') with
   ((l :: sem_Rec (Sem g) (Sem h0) (Sem h1) l l0 :: l0) ++ l'); trivial.
 case a.
 eapply H5; eauto; simpl; omega.
 eapply H4; eauto; simpl; omega.
 f_equal.
 apply map_ext2; intros.
 eapply H2; trivial.
Qed.

(** * Length-bounding condition that must hold for a Cobham expression to be valid *)

Fixpoint rec_bounded' (e : Cobham) : Prop :=
  match e with
    | Rec g h0 h1 j =>
      rec_bounded' j  /\ 
      rec_bounded' g /\ 
      rec_bounded' h0 /\ 
      rec_bounded' h1 /\
      (match (arity e) with
         | ok_arity n => forall l, length l = n ->
           length (Sem e l) <= length (Sem j l)
        | _ => True (* never happen *)
       end)
    | Comp n h l => rec_bounded' h /\
        andl rec_bounded' l
    | _ => True
  end.

Fixpoint rec_bounded (e : Cobham) : Prop :=
  match e with
    | Rec g h0 h1 j =>
      rec_bounded j  /\ 
      rec_bounded g /\ 
      rec_bounded h0 /\ 
      rec_bounded h1 /\
      (forall l, 
        length (Sem e l) <= length (Sem j l))
    | Comp n h l => rec_bounded h /\
        andl rec_bounded l
    | _ => True
  end.

Lemma rec_bounded_spec (e : Cobham) :
  rec_bounded e -> rec_bounded' e.
Proof.
 induction e using Cobham_ind2; simpl; auto; intros.
 decompose [and] H; clear H.
 repeat (split; try tauto).
 case_eq (arity e1); intros; try discriminate; auto.
 case_eq (arity e2); intros; try discriminate; auto.
 case_eq (arity e3); intros; try discriminate; auto.
 case_eq (arity e4); intros; try discriminate; auto.
 destruct n0; simpl; intros; try discriminate; auto.
 destruct n0; simpl; intros; try discriminate; auto.
 case_eq (beq_nat n n0); simpl; intros; try discriminate; auto.
 case_eq (beq_nat n1 (S (S n0))); simpl; intros; 
   try discriminate; auto.
 destruct n1; simpl; intros; try discriminate; auto.
 case_eq (beq_nat n2 n1); simpl; intros; try discriminate; auto.
 split; try tauto.
 revert e IHe H0.
 induction l; simpl; intros; trivial.
 split.
 apply H.
simpl; tauto.
tauto.
eapply IHl.
intros.
apply H.
simpl.
tauto.
trivial.
auto.
tauto.
Qed.

Lemma rec_bounded'_spec : forall (e : Cobham) n,
  arity e = ok_arity n ->
  rec_bounded' e -> 
  rec_bounded e.
Proof.
 refine (Cobham_ind_inf (fun n e => 
   rec_bounded' e -> rec_bounded e) _ _ _ _ _ _); simpl; auto; intros.
 decompose [and] H7; clear H7.
 rewrite H, H0, H1,H2 in H13.
 simpl in H13. 
 rewrite <- beq_nat_refl in H13.
 simpl in H13.
 repeat (split; try tauto).
 intros.
 rewrite <- simpl_Rec with (j := j).
 destruct (le_lt_dec (length l) (S n)).
 rewrite Sem_add_zero with (n := S n); trivial.
 rewrite Sem_add_zero with (e := j) (n := S n); trivial.
 apply H13; trivial.
 rewrite app_length, map_length, seq_length.
 omega.
 simpl.
 rewrite H, H0, H1, H2.
 repeat rewrite <- beq_nat_refl; simpl; trivial.

 rewrite <- firstn_skipn with (n := S n) (l := l).
 rewrite <- Sem_remove_zero with (n := S n); trivial.
 rewrite <- Sem_remove_zero with (n := S n); trivial.
 apply H13; trivial; trivial.
 rewrite firstn_length.
 rewrite min_l; trivial; omega.
 rewrite firstn_length.
 rewrite min_l; trivial; omega.
 simpl.
 rewrite H, H0, H1, H2.
 repeat rewrite <- beq_nat_refl; simpl.
 trivial.
 rewrite firstn_length.
 rewrite min_l; trivial; omega.

 split.
 tauto.
 apply forall_andl; intros.
 destruct H3.
 rewrite <- forall_andl in H5; auto.
Qed.

(** * Length-bounding polynomial for Cobham expressions

  - The lemma [poly_Cobham_correct] states that the output of an expression [e]
    is bounded by the polynomial [poly_Cobham e].
*)

Fixpoint poly_Cobham (e : Cobham) :=
  match e with
    | Zero => pcst 0 0
    | Proj n i => pproj n i
    | Succ b => pplus (pcst 0 1) (pproj 1 0)
    | Smash => pplus (pcst 0 1) (pmult (pproj 2 0) (pproj 2 1))
    | Rec g h0 h1 j => poly_Cobham j
    | Comp n h l => 
      pplus (pcst n 0) 
      (pcomp (poly_Cobham h) (map poly_Cobham l))
  end.

Lemma parity_poly_Cobham : forall (e : Cobham) n,
  arity e = ok_arity n ->
  parity (poly_Cobham e) = n.
Proof.
  apply Cobham_ind_inf; simpl; auto; intros.
  apply max_l.
  apply maxl_map.
  intros.
  apply in_map_iff in H3.
  destruct H3 as (? & ? & ?); subst.
  apply H2; trivial.
Qed.

Lemma pWF_poly_Cobham : forall (e : Cobham) n,
  arity e = ok_arity n ->
  pWF (poly_Cobham e).
Proof.
  apply Cobham_ind_inf; simpl; auto; intros; try pWF.
  apply in_map_iff in H3.
  destruct H3 as (? & ? & ?); subst.
  apply H2; trivial.
Qed.

Lemma poly_Cobham_correct : forall (e : Cobham) xl,
  rec_bounded e ->  
  length (Sem e xl) <= 
  peval (poly_Cobham e) (map (@length _) xl).
Proof.
 induction e using Cobham_ind2; intros; simpl in *; trivial.

 rewrite <- (@map_nth _ _ (@length _) xl); simpl; trivial.
 rewrite pproj_correct; trivial.

 rewrite pplus_correct, pproj_correct.
 rewrite <- hd_nth_0, (map_hd _ _ (@length _)); simpl; omega.

 rewrite length_smash, pplus_correct, pmult_correct, pcst_correct, 
   pproj_correct, pproj_correct, <- hd_nth_0, hd_nth_1, (map_hd _ _ (@length _)); simpl.
 rewrite <- (@map_nth _ _ (@length _) xl); simpl.
 trivial.
 
 decompose [and] H; clear H.
 apply le_trans with (1 := H5 xl).
 apply IHe4; trivial.
 rewrite pplus_correct.
 rewrite pcst_correct.
 rewrite pcomp_correct.
 eapply le_trans.
 apply IHe.
 tauto.
 repeat rewrite map_map.
 apply peval_monotonic.
 intros.
 rewrite map_nth2 with (d := Zero);[ | simpl; trivial].
 rewrite map_nth2 with (d := Zero);[ | simpl; trivial].
 clear IHe.
 assert (rec_bounded (nth i l Zero)).
 clear H.
 revert i.
 induction l; simpl in *; intros; case i; simpl; trivial.
 tauto.
 intros.
 apply IHl.
 tauto.
 destruct (lt_dec i (length l)).
 apply H.
 apply nth_In; trivial.
 trivial.
 rewrite nth_overflow; simpl.
 trivial.
 omega.
Qed.

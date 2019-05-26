(** The language of Bellantoni and Cook *)

Require Import Bool Arith List.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.MultiPoly.

(** * Syntax and induction principle

  - [BC_ind2] is a handmade induction principle because the one generated automatically by Coq
    ignores the types [list BC] in the constructor [comp].
*)

Inductive BC : Set :=
| zero : BC
| proj : nat -> nat -> nat -> BC
| succ : bool -> BC
| pred : BC
| cond : BC
| rec : BC -> BC -> BC -> BC
| comp : nat -> nat -> BC -> list BC -> list BC -> BC.  

Lemma BC_ind2' :
  forall P : BC -> Prop,
  forall Q : list BC -> Prop,
  Q nil ->
  (forall e l, P e -> Q l -> Q (e :: l)) ->
  P zero ->
  (forall n s i, P (proj n s i)) ->
  (forall b, P (succ b)) ->
  P pred ->
  P cond ->
  (forall g h0 h1, P g -> P h0 -> P h1 -> P (rec g h0 h1)) ->
  (forall n s h rl tl, P h -> Q rl -> Q tl ->
    P (comp n s h rl tl)) ->
  forall e, P e.
Proof.
 fix BC_ind2' 12; intros.
 destruct e; auto.
 apply H6; eapply BC_ind2'; eauto.
 apply H7.
 eapply BC_ind2'; eauto.
 revert l.
 fix BC_ind2'0 1.
 intro.
 destruct l.
 auto.
 apply H0.
 eapply BC_ind2'; eauto.
 apply BC_ind2'0.
 revert l0.
 fix BC_ind2'0 1.
 intro.
 destruct l0.
 auto.
 apply H0.
 eapply BC_ind2'; eauto.
 apply BC_ind2'0.
Qed.

Lemma BC_ind2 :
  forall P : BC -> Prop,
  P zero ->
  (forall n s i, P (proj n s i)) ->
  (forall b, P (succ b)) ->
  P pred ->
  P cond ->
  (forall g h0 h1, P g -> P h0 -> P h1 -> P (rec g h0 h1)) ->
  (forall n s h rl tl, P h -> (forall r, In r rl -> P r) -> 
    (forall s, In s tl -> P s) ->
    P (comp n s h rl tl)) ->
  forall e, P e.
Proof.
  intros; apply BC_ind2' with (Q := fun l => forall e, In e l -> P e); intros; auto; simpl in *.
  tauto.
  destruct H8.
  subst; auto.
  auto.
Qed.

(** * Arities

  - [arities e] returns the arities (i.e., the number of normal and safe variables)
    of the expression [e] if it is well formed, or an error including the arities of the subterms.
*)

Inductive Arities : Set :=
| error_rec : Arities -> Arities -> Arities -> Arities
| error_comp : Arities -> list Arities -> list Arities -> Arities
| error_proj : nat -> nat -> nat -> Arities
| ok_arities : nat -> nat -> Arities.

Definition aeq (x y:Arities) : bool :=
  match x, y with
  | ok_arities xn xs, ok_arities yn ys => beq_nat xn yn && beq_nat xs ys
  | _, _ => false
  end.

Lemma aeq_eq (x y : Arities) :
  aeq x y = true -> x = y.
Proof.
  destruct x; destruct y; simpl; intros; try discriminate.
  apply andb_true_iff in H; destruct H.
  apply beq_nat_true in H.
  apply beq_nat_true in H0.
  subst; trivial.
Qed.  

Lemma aeq_eq_conv xn yn xs ys :
  aeq (ok_arities xn xs) (ok_arities yn ys) = false -> xn <> yn \/ xs <> ys.
Proof.
  simpl; intros.
  apply andb_false_elim in H.
  destruct H as [H | H]; apply beq_nat_false in H; tauto.
Qed.

Fixpoint arities (e:BC) : Arities :=
  match e with
  | zero => ok_arities 0 0
  | proj n s i => 
    if leb (S i) (n + s) then ok_arities n s
      else error_proj n s i
  | succ _ => ok_arities 0 1
  | pred => ok_arities 0 1
  | cond => ok_arities 0 4
  | rec g h0 h1 =>
      match arities g, arities h0, arities h1 
        with | ok_arities gn gs, ok_arities h0n h0s, ok_arities h1n h1s =>
          if beq_nat (S gn) h0n && beq_nat h0n h1n &&
            beq_nat (S gs) h0s && beq_nat h0s h1s 
          then ok_arities h0n gs 
            else error_rec (ok_arities gn gs) (ok_arities h0n h0s) (ok_arities h1n h1s)
        | e1, e2, e3 => error_rec e1 e2 e3
      end
    | comp n s h nl sl =>
      match arities h, map arities nl, map arities sl with
      | ok_arities hn hs, anl, asl =>
        if beq_nat hn (length nl) && beq_nat hs (length sl) && 
          forallb (fun ne => aeq (arities ne) (ok_arities n 0)) nl &&
          forallb (fun se => aeq (arities se) (ok_arities n s)) sl
          then ok_arities n s
          else error_comp (ok_arities hn hs) anl asl 
      | e , anl, asl => error_comp e anl asl
      end
  end.

Definition arities2 e :=
  match arities e with
    | ok_arities n s => (n, s)
    | _ => (0, 0)
  end.

Lemma proj_arities : forall n s i, 
  i < n+s -> 
  arities (proj n s i) = ok_arities n s.
Proof.
 intros n s i Hi; simpl.
 case_eq (n+s).
 intro H; contradict Hi; omega.
 intros ns Hns.
 case_eq (leb i ns); intros H0.
 apply leb_complete in H0; trivial.
 apply leb_complete_conv in H0; contradict Hi; omega.
Qed.

Lemma comp_arities : forall n s e nel sel,
  arities e = ok_arities (length nel) (length sel) ->
  andl (fun ne => arities ne = ok_arities n 0) nel ->
  andl (fun se => arities se = ok_arities n s) sel ->
  arities (comp n s e nel sel) = ok_arities n s.
Proof.
 intros b s e nel sel He Hnel Hsel; simpl.
 rewrite He.
 rewrite <- !beq_nat_refl.
 case_eq (forallb (fun ne : BC => aeq (arities ne) (ok_arities b 0)) nel).
 intros _.
 case_eq (forallb (fun se : BC => aeq (arities se) (ok_arities b s)) sel).
 intros _; trivial.
 intro Hsel'.
 rewrite forallb_forall_conv in Hsel'.
 destruct Hsel' as [e' [H1 H2] ].
 contradict H2.
 rewrite <- forall_andl in Hsel.
 rewrite Hsel; simpl.
 do 2 rewrite <- beq_nat_refl.
 simpl; congruence.
 trivial.
 intro Hnel'.
 rewrite forallb_forall_conv in Hnel'.
 destruct Hnel' as [e' [H1 H2] ].
 contradict H2.
 rewrite <- forall_andl in Hnel.
 rewrite Hnel.
 simpl.
 rewrite <- beq_nat_refl.
 simpl; congruence.
 trivial.
Qed.

Lemma arities_nth :
  forall l i e n s,
  (forall e, In e l -> arities e = ok_arities n s) ->
  arities e = ok_arities n s ->
  arities (nth i l e) = ok_arities n s.
Proof.
induction l as [ | e1 l IH]; simpl; intros [ | i]; trivial; auto.
Qed.

Lemma BC_ind_inf' :
  forall (P : nat -> nat -> BC -> Prop),
  forall Q : nat -> nat -> list BC -> Prop,
  (forall n s, Q n s nil) ->
  (forall e n s l, P n s e -> Q n s l -> Q n s (e :: l)) ->
  P 0 0 zero ->
  (forall n s i, i < n + s ->  P n s (proj n s i)) ->
  (forall b, P 0 1 (succ b)) ->
  P 0 1 pred ->
  P 0 4 cond ->
  (forall n s g h0 h1, 
    arities g = ok_arities n s ->
    arities h0 = ok_arities (S n) (S s) ->
    arities h1 = ok_arities (S n) (S s) ->
    P n s g -> 
    P (S n) (S s) h0 -> 
    P (S n) (S s) h1 -> 
    P (S n) s (rec g h0 h1)) ->
  (forall n s h rl tl, 
    arities h = ok_arities (length rl) (length tl) ->
    (forall e, In e rl -> arities e = ok_arities n 0) ->
    (forall e, In e tl -> arities e = ok_arities n s) ->
    P (length rl) (length tl) h -> 
    Q n 0 rl -> 
    Q n s tl ->
    P n s (comp n s h rl tl)) ->
  forall e n s , arities e = ok_arities n s -> P n s e.
Proof.
 fix BC_ind_inf' 12; intros.
 destruct e; simpl in *.
 
 injection H8; intros; subst; auto.

 case_eq (n0 + n1); intros; rewrite H9 in H8; try discriminate.
 case_eq (leb n2 n3); intros; rewrite H10 in H8; try discriminate.
 injection H8; intros; subst; auto.
 apply H2.
 apply leb_complete in H10; omega.

 injection H8; intros; subst; auto.
 injection H8; intros; subst; auto.
 injection H8; intros; subst; auto.

 case_eq (arities e1); intros; rewrite H9 in H8;
   try discriminate.
 case_eq (arities e2); intros; rewrite H10 in H8;
   try discriminate.
 case_eq (arities e3); intros; rewrite H11 in H8;
   try discriminate.
 destruct n2; simpl in *; try discriminate.
 case_eq (beq_nat n0 n2); intros; rewrite H12 in H8; simpl in *;
   try discriminate.
 apply beq_nat_true in H12; subst.
 destruct n4; simpl in *; try discriminate.
 case_eq (beq_nat n2 n4); intros; rewrite H12 in H8; simpl in *;
   try discriminate.
 apply beq_nat_true in H12; subst.
 destruct n3; simpl in *; try discriminate.
 case_eq (beq_nat n1 n3); intros; rewrite H12 in H8; simpl in *;
   try discriminate.
 apply beq_nat_true in H12; subst.
 destruct n5; simpl in *; try discriminate.
 case_eq (beq_nat n3 n5); intros; rewrite H12 in H8; simpl in *;
   try discriminate.
 apply beq_nat_true in H12; subst.
 injection H8; intros; subst.
 apply (@H6 n4 s); auto.
 eapply BC_ind_inf'; eauto.
 eapply BC_ind_inf'; eauto.
 eapply BC_ind_inf'; eauto.

 case_eq (arities e); intros; rewrite H9 in H8;
   try discriminate.
 case_eq (beq_nat n2 (length l)); intros; rewrite H10 in H8;
   try discriminate.
 apply beq_nat_true in H10.
 case_eq (beq_nat n3 (length l0)); intros; rewrite H11 in H8;
   try discriminate.
 apply beq_nat_true in H11.
 case_eq (forallb (fun ne : BC => aeq (arities ne) 
   (ok_arities n0 0)) l); intros; rewrite H12 in H8; 
 try discriminate.
 case_eq (forallb (fun se : BC => aeq (arities se) 
   (ok_arities n0 n1)) l0); intros; rewrite H13 in H8; 
 try discriminate.
 simpl in H8.
 injection H8; intros; subst.

 rewrite forallb_forall in H12.
 rewrite forallb_forall in H13.
 apply H7; trivial.
 intros; apply aeq_eq.
 apply H12; trivial.
 intros; apply aeq_eq.
 apply H13; trivial.

 eapply BC_ind_inf'; eauto.

 clear H9.
 revert l H12.
 fix BC_ind_inf'0 1.
 intros.
 destruct l.
 auto.
 eapply H0.
 eapply BC_ind_inf'; eauto.
 apply aeq_eq.
 apply H12.
 simpl; auto.
 apply BC_ind_inf'0.
 intros.
 apply H12.
 simpl; auto.
 clear H9.
 revert l0 H13.
 fix BC_ind_inf'0 1.
 intros.
 destruct l0.
 auto.
 eapply H0.
 eapply BC_ind_inf'; eauto.
 apply aeq_eq.
 apply H13.
 simpl; auto.
 apply BC_ind_inf'0.
 intros.
 apply H13.
 simpl; auto.
Qed.

Lemma BC_ind_inf :
  forall (P : nat -> nat -> BC -> Prop),
  P 0 0 zero ->
  (forall n s i, i < n + s ->  P n s (proj n s i)) ->
  (forall b, P 0 1 (succ b)) ->
  P 0 1 pred ->
  P 0 4 cond ->
  (forall n s g h0 h1, 
    arities g = ok_arities n s ->
    arities h0 = ok_arities (S n) (S s) ->
    arities h1 = ok_arities (S n) (S s) ->
    P n s g -> 
    P (S n) (S s) h0 -> 
    P (S n) (S s) h1 -> 
    P (S n) s (rec g h0 h1)) ->
  (forall n s h rl tl, 
    arities h = ok_arities (length rl) (length tl) ->
    (forall e, In e rl -> arities e = ok_arities n 0) ->
    (forall e, In e tl -> arities e = ok_arities n s) ->
    P (length rl) (length tl) h -> 
    (forall r, In r rl -> P n 0 r) ->
    (forall r, In r tl -> P n s r) ->
    P n s (comp n s h rl tl)) ->
  forall e n s , arities e = ok_arities n s -> P n s e.
Proof.
  intros.
  apply BC_ind_inf'
    with (Q := fun n s l => forall e , In e l -> P n s e); auto; simpl in *; intros.
  tauto.
  destruct H9; subst; auto.
Qed.

(** * Semantics

  - [sem e vnl vsl] is the evaluation of the expression [e] where the [i]th normal variable is
    instantiated with the [i]th value of [vnl], and the [i]th safe variable is
    instantiated with the [i]th value of [vsl].
    If a variable is not assigned a value, then it is assumed to be the empty bitstring [nil].
    Values in [vnl] and [vsl] that do not correspond to a variable are ignored.

  - [BC_ind_inf] is an induction principle that makes easier dealing with arities in inductive proofs.
*)

Fixpoint sem_rec (sem_g sem_h0 sem_h1:list bs->list bs->bs)(v:bs)(vnl vsl:list bs) :=
  match v with
    | nil => sem_g vnl vsl
    | b::v' =>
      if b then sem_h1 (v'::vnl) (sem_rec sem_g sem_h0 sem_h1 v' vnl vsl :: vsl)
      else sem_h0 (v'::vnl) (sem_rec sem_g sem_h0 sem_h1 v' vnl vsl :: vsl)
  end.

Fixpoint sem (e:BC)(vnl vsl:list bs) : bs :=
  match e with
  | zero => nil
  | proj n s j => 
    if leb (S j) n then
      nth j vnl nil
      else nth (j-n) vsl nil
  | succ b => b :: hd nil vsl
  | pred => tail (hd nil vsl)
  | cond =>
      match vsl with
      | a :: b :: c :: d :: _ => 
        match a with 
          | nil => b
          | true :: _ => c
          | false :: _ => d
        end
      | a :: b :: c :: _ => 
        match a with 
          | nil => b
          | true :: _ => c
          | false :: _ => nil
        end
      | a :: b :: _ => 
        match a with 
          | nil => b
          | _ => nil
        end
      | _ => nil
      end
  | rec g h0 h1 => sem_rec (sem g) (sem h0) (sem h1) (hd nil vnl) (tail vnl) vsl
  | comp _ _ h nl sl => 
    sem h (List.map (fun ne => sem ne vnl nil) nl) 
          (List.map (fun se => sem se vnl vsl) sl)
  end.

Lemma sem_comp :
  forall n s f nel sel nl sl, 
  sem (comp n s f nel sel) nl sl =
  sem f (map (fun ne => sem ne nl nil) nel) (map (fun se => sem se nl sl) sel).
Proof.
 trivial.
Qed.

(** * Some properties of [cond] *)

Lemma cond_simpl_nil n s fn fc ff ft l1 l2 :
  sem fc l1 l2 = nil ->
  sem (comp n s cond nil [fc; fn; ft; ff]) l1 l2 = sem fn l1 l2.
Proof.
 simpl; intros; rewrite H; simpl; trivial.
Qed.

Lemma cond_simpl_notnil n s fn fc ft ff l1 l2 :
  sem fc l1 l2 <> nil ->
  sem (comp n s cond nil [fc; fn; ft; ff]) l1 l2 = 
  match sem fc l1 l2 with
    | nil => nil 
    | true :: _ => sem ft l1 l2 
    | false :: _ => sem ff l1 l2
  end.
Proof.
  simpl; intros.
  destruct (sem fc l1 l2); intros; auto.
  elim H; trivial.
Qed.

Lemma cond_simpl_true n s fn fc ff ft l1 l2 :
  hd false (sem fc l1 l2) = true ->
  sem (comp n s cond nil [fc; fn; ft; ff]) l1 l2 = sem ft l1 l2.
Proof.
 simpl; intros.
 destruct (sem fc l1 l2).
 simpl in H.
 discriminate.
 destruct b; simpl in *; trivial.
 discriminate.
Qed.

Lemma cond_simpl_false n s fn fc ff ft l1 l2 l :
  sem fc l1 l2 = false :: l ->
  sem (comp n s cond nil [fc; fn; ft; ff]) l1 l2 = sem ff l1 l2.
Proof.
 simpl; intros.
 rewrite H; simpl; trivial.
Qed.

Lemma sem_nth :
  forall i start len f d vnl vsl,
  0 <= i < len ->
  sem (nth i (map f (seq start len)) d) vnl vsl = sem (f (i+start)) vnl vsl.
Proof.
intros i start len.
revert i start.
induction len as [ | len IH]; simpl; intros.
contradict H.
omega.
destruct i as [ | i].
trivial.
rewrite IH.
do 2 f_equal.
ring.
omega.
Qed.

Lemma map_sem_nth :
  forall i f1 f2 vnl vsl d,
  map (fun f => sem f vnl vsl) f1 = map (fun f => sem f vnl vsl) f2 ->
  sem (nth i f1 d) vnl vsl = sem (nth i f2 d) vnl vsl.
Proof.
induction i as [ | i IH]; simpl; intros [ | e1 f1] [ | e2 f2] vnl vsl d H; simpl in *; trivial; try congruence.
apply IH.
congruence.
Qed.

Lemma sem_proj_S_normal :
  forall n s i f vsl vnl,
  i < n ->
  sem (proj (S n) s (S i)) (f::vnl) vsl =
  sem (proj n s i) vnl vsl.
Proof.
trivial.
Qed.

Lemma sem_proj_S_safe :
  forall n s i f vsl vnl,
  n <= i ->
  sem (proj n (S s) (S i)) vnl (f::vsl) =
  sem (proj n s i) vnl vsl.
Proof.
intros.
simpl.
destruct n as [ | n].
f_equal.
omega.
destruct n as [ | n].
cutrewrite (i-0 = S (i-1)).
case_eq (leb i 0); intro Hi.
apply leb_complete in Hi.
contradict Hi.
omega.
trivial.
omega.
case_eq (leb i n); intro Hi.
apply leb_complete in Hi.
contradict Hi.
omega.
clear Hi.
case_eq (leb i (S n)); intro Hi.
apply leb_complete in Hi.
contradict Hi.
omega.
clear Hi.
case_eq (i - S n).
intro Hi.
contradict Hi.
omega.
intros j Hi.
f_equal.
omega.
Qed.

Lemma sem_firstn_safe :
  forall f n s vnl vsl,
  arities f = ok_arities n s ->
  sem f vnl vsl = sem f vnl (firstn s vsl).
Proof.
intros.
revert f n s H vnl vsl.
refine (BC_ind_inf _ _ _ _ _ _ _ _); simpl; intros.

trivial.

destruct n as [ | n]; simpl in *; intros.
rewrite <- minus_n_O.
rewrite nth_firstn.
trivial.
trivial.
case_eq (leb i n); intro H0.
destruct vnl as [ | v vnl].
trivial.
destruct i as [ | i].
trivial.
simpl.
apply leb_complete in H0.
trivial.
rewrite nth_firstn.
trivial.
apply leb_complete_conv in H0.
omega.

f_equal.
destruct vsl as [ | v vsl].
trivial.
trivial.

destruct vsl as [ | v vsl].
trivial.
trivial.

destruct vsl as [ | v vsl].
trivial.
destruct vsl as [ | v' vsl].
trivial.
destruct vsl as [ | v'' vsl].
trivial.
destruct vsl as [ | v''' vsl].
trivial.
trivial.

destruct vnl as [ | v vnl]; simpl.
rewrite H2.
trivial.
induction v as [ | [ | ] v IH]; simpl.
trivial.
rewrite H4.
congruence.
rewrite H3.
congruence.

clear H H2.
f_equal.
apply map_ext2.
intros.
apply H4.
trivial.
Qed.

Lemma sem_firstn_normal :
  forall f n s vnl vsl,
  arities f = ok_arities n s ->
  sem f vnl vsl = sem f (firstn n vnl) vsl.
Proof.
intros.
revert f n s H vnl vsl.
refine (BC_ind_inf _ _ _ _ _ _ _ _); simpl; intros.

trivial.

destruct n as [ | n]; simpl in *; intros.
rewrite <- minus_n_O.
trivial.
case_eq (leb i n); intro H0.
destruct vnl as [ | v vnl].
trivial.
destruct i as [ | i].
trivial.
simpl.
apply leb_complete in H0.
rewrite nth_firstn.
trivial.
trivial.
trivial.

trivial.
trivial.

destruct vsl as [ | v vsl].
trivial.
destruct vsl as [ | v' vsl].
trivial.
destruct vsl as [ | v'' vsl].
trivial.
destruct vsl as [ | v''' vsl].
trivial.
trivial.

destruct vnl as [ | v vnl]; simpl.
rewrite H2, firstn_nil.
trivial.
induction v as [ | [ | ] v IH]; simpl.
trivial.
rewrite H4.
congruence.
rewrite H3.
congruence.

clear H H2.
f_equal.
apply map_ext2.
auto.
apply map_ext2.
auto.
Qed.


Lemma sem_firstn :
  forall f n s vnl vsl,
  arities f = ok_arities n s ->
  sem f vnl vsl = sem f (firstn n vnl) (firstn s vsl).
Proof.
intros.
erewrite sem_firstn_safe; eauto.
erewrite sem_firstn_normal; eauto.
Qed.

Lemma sem_repeat :
  forall f vnl vsl n s,
  arities f = ok_arities n s ->
  sem f vnl vsl = sem f (vnl ++ repeat (n - length vnl) nil) (vsl ++ repeat (s - length vsl) nil).
Proof.
intros.
revert f n s H vnl vsl.
refine (BC_ind_inf _ _ _ _ _ _ _ _); simpl; intros.

trivial.

destruct n as [ | n]; simpl in *; intros.
rewrite <- minus_n_O.
destruct (le_dec (length vsl) i).
rewrite app_nth2,nth_repeat, nth_overflow.
trivial.
trivial.
omega.
trivial.
rewrite app_nth1.
trivial.
omega.
case_eq (leb i n); intro Hleb.
destruct (le_dec (length vnl) i).
rewrite app_nth2,nth_repeat, nth_overflow.
trivial.
trivial.
apply leb_complete in Hleb.
destruct (length vnl); omega.
trivial.
rewrite app_nth1.
trivial.
omega.
destruct (le_dec (length vsl) (i - S n)).
rewrite app_nth2,nth_repeat, nth_overflow.
trivial.
trivial.
apply leb_complete_conv in Hleb.
omega.
trivial.
rewrite app_nth1.
trivial.
omega.

f_equal.
destruct vsl as [ | v vsl].
trivial.
trivial.

destruct vsl as [ | v vsl].
trivial.
trivial.

destruct vsl as [ | v vsl].
trivial.
destruct vsl as [ | v' vsl].
simpl.
destruct v as [ | [ | ] v]; trivial.
destruct vsl as [ | v'' vsl].
simpl.
destruct v as [ | [ | ] v]; trivial.
destruct vsl as [ | v''' vsl].
simpl.
destruct v as [ | [ | ] v]; trivial.
destruct v as [ | [ | ] v]; trivial.

destruct vnl as [ | v vnl]; simpl.
rewrite H2.
f_equal.
simpl.
cutrewrite (n-0 = n).
trivial.
omega.
induction v as [ | [ | ] v IH]; simpl.
trivial.
rewrite H4.
simpl; congruence.
rewrite H3.
simpl; congruence.

clear H H2.
f_equal.
induction rl as [ | r rl IH]; simpl.
trivial.
f_equal.
apply H3.
simpl; tauto.
apply IH.
auto with *.
auto with *.
induction tl as [ | t tl IH]; simpl.
trivial.
f_equal.
auto with *.
apply IH.
auto with *.
auto with *.
Qed.

Lemma map_sem_repeat :
  forall fl vnl vsl n s,
  (forall f, In f fl -> arities f = ok_arities n s) ->
  map (fun f => sem f vnl vsl) fl =
  map (
    fun f =>
      sem f
        (vnl ++ repeat (n - length vnl) nil)
        (vsl ++ repeat (s - length vsl) nil)
  ) fl.
Proof.
induction fl as [ | f fl IH]; intros vnl vsl n s H; simpl.
trivial.
f_equal.
apply sem_repeat.
apply H; simpl; tauto.
apply IH.
intros.
apply H.
simpl; tauto.
Qed.

Lemma map_proj_seq_normal_gen :
  forall n i vnl,
  n+i <= length vnl ->
  map (fun f : BC => sem f vnl nil) (map (proj (n+i) 0) (seq i n)) =
  firstn n (skipn i vnl).
Proof.
induction n as [ | n IH]; simpl; intros i vnl Hn.
trivial.
destruct vnl as [ | v vnl]; simpl in *.
contradict Hn.
omega.
case_eq (leb i (n+i)); intro Hi.
destruct i as [ | i]; simpl.
f_equal.
cutrewrite (S (n+0) = n+1).
apply IH.
simpl; omega.
trivial.
trivial.
cutrewrite (S (n + S i) = n + S (S i)).
rewrite IH.
simpl.
destruct vnl as [ | v1 vnl]; simpl in *.
contradict Hn.
omega.
destruct i as [ | i]; simpl.
trivial.
rewrite <- cons_skipn with (d:=nil).
trivial.
omega.
simpl; omega.
trivial.
apply leb_complete_conv in Hi.
contradict Hi.
omega.
Qed.

Lemma map_proj_seq_normal :
  forall n vnl,
  map (fun f : BC => sem f vnl nil) (map (proj n 0) (seq 0 n)) =
  firstn n vnl ++ repeat (n - length vnl) nil.
Proof.
intros n vnl.
destruct (le_gt_dec (n+0) (length vnl)) as [H | H].
cutrewrite (n - length vnl = 0).
generalize (map_proj_seq_normal_gen n 0 vnl H).
simpl_list.
rewrite <- plus_n_O.
trivial.
omega.
transitivity (firstn n (vnl ++ repeat (n - length vnl) nil)).
assert (n + 0 <= length (vnl ++ repeat (n - length vnl) nil)) as H0.
rewrite app_length.
rewrite length_repeat.
omega.
generalize (map_proj_seq_normal_gen n 0 (vnl ++ repeat (n - length vnl) nil) H0).
simpl.
rewrite <- plus_n_O.
intro H1.
rewrite <- H1.
clear H H0 H1.
rewrite map_sem_repeat with (n:=n) (s:=0).
trivial.
intros f H.
rewrite in_map_iff in H.
destruct H as [i [H1 H2] ].
rewrite in_seq_iff in H2.
subst f.
simpl.
rewrite <- plus_n_O.
destruct n.
contradict H2.
omega.
case_eq (leb i n).
trivial.
intro H.
rewrite leb_iff_conv in H.
contradict H.
omega.
clear H.
revert vnl.
induction n as [ | n IH]; simpl in *; intro vnl.
trivial.
destruct vnl; simpl.
clear IH.
f_equal.
apply firstn_repeat_le.
trivial.
congruence.
Qed.

Lemma map_proj_seq_safe_gen :
  forall n s i vnl vsl,
  s+i <= length vsl ->
  map (fun f : BC => sem f vnl vsl) (map (proj n (s+i)) (seq (n+i) s)) =
  firstn s (skipn i vsl).
Proof.
intros n s.
revert n.
induction s as [ | s IH]; simpl; intros n i vnl vsl Hs.
trivial.
destruct vsl as [ | v vsl]; simpl in *.
contradict Hs.
omega.
destruct n as [ | n].
cutrewrite (0+i-0 = i).
destruct i as [ |i]; simpl.
f_equal.
cutrewrite (S (s+0) = s+1).
apply IH.
simpl; omega.
trivial.
rewrite <- cons_skipn with (d:=nil).
f_equal.
cutrewrite (S (s + S i) = s + S (S i)).
rewrite IH.
f_equal.
simpl; omega.
trivial.
omega.
omega.
case_eq (leb (S n + i) n); intro H.
apply leb_complete in H.
contradict H.
omega.
cutrewrite (S n + i - S n = i).
destruct i as [ | i]; simpl.
f_equal.
cutrewrite (S (s+0) = s+1).
cutrewrite (S (S (n+0)) = S n + 1).
apply IH.
simpl; omega.
ring.
trivial.
rewrite <- cons_skipn with (d:=nil).
f_equal.
cutrewrite (S (s + S i) = s + S (S i)).
cutrewrite (S (S (n + S i)) = (S n + S (S i))).
rewrite IH.
trivial.
simpl; omega.
ring.
trivial.
omega.
omega.
Qed.

Lemma map_proj_seq_safe :
  forall n s vnl vsl,
  map (fun f : BC => sem f vnl vsl) (map (proj n s) (seq n s)) =
  firstn s vsl ++ repeat (s - length vsl) nil.
Proof.
intros n s vnl vsl.
destruct (le_gt_dec (s+0) (length vsl)) as [H | H].
cutrewrite (s - length vsl = 0).
generalize (map_proj_seq_safe_gen n s 0 vnl vsl H).
simpl_list.
do 2 rewrite <- plus_n_O.
trivial.
omega.

transitivity (firstn s (vsl ++ repeat (s - length vsl) nil)).
assert (s + 0 <= length (vsl ++ repeat (s - length vsl) nil)) as H0.
rewrite app_length.
rewrite length_repeat.
omega.
generalize (map_proj_seq_safe_gen n s 0 vnl (vsl ++ repeat (s - length vsl) nil) H0).
simpl.
do 2 rewrite <- plus_n_O.
intro H1.
rewrite <- H1.
clear H H0 H1.
apply map_ext2.
intros f Hf.
rewrite in_map_iff in Hf.
destruct Hf as [i [H1 H2] ].
rewrite in_seq_iff in H2.
rewrite sem_repeat with (n:=n) (s:=s).
symmetry.
rewrite sem_repeat with (n:=n) (s:=s).
f_equal.
rewrite <- app_assoc.
f_equal.
transitivity (repeat (s - length vsl) nil (A:=list bool) ++  nil).
f_equal.
rewrite app_length, length_repeat.
cutrewrite (s - (length vsl + (s - length vsl)) = 0).
trivial.
omega.
simpl_list.
trivial.
subst f.
simpl.
case_eq (n+s).
intro H.
contradict H.
omega.
intros p H.
case_eq (leb i p).
trivial.
intro Hleb.
rewrite leb_iff_conv in Hleb.
contradict Hleb.
omega.
subst f.
simpl.
case_eq (n+s).
intro H.
contradict H.
omega.
intros p H.
case_eq (leb i p).
trivial.
intro Hleb.
rewrite leb_iff_conv in Hleb.
contradict Hleb.
omega.
clear H.
revert vsl.
induction s as [ | s IH]; simpl in *; intro vsl.
trivial.
destruct vsl; simpl.
clear IH.
f_equal.
apply firstn_repeat_le.
trivial.
congruence.
Qed.

Definition zero_e (n s:nat) : BC :=
  comp n s zero nil nil.

Lemma sem_comp_proj_normal : forall n1 n2 f1 vnl i,
n2 <> 0 -> i < n2 ->
sem (comp n1 0 (proj n2 0 i) f1 nil) vnl nil =
sem (nth i f1 (zero_e n1 0)) vnl nil.
Proof.
 intros.
 simpl.
 destruct n2; simpl.
 elim H; auto.
 rewrite leb_correct; [ | omega].
 rewrite map_nth2 with (d := zero_e n1 0).
 auto.
 simpl; auto.
Qed.

Lemma sem_comp_proj_safe : forall n1 s1 n2 s2 f1 f2 vnl vsl i,
n2 <= i ->
sem (comp n1 s1 (proj n2 s2 i) f1 f2) vnl vsl =
sem (nth (i - n2) f2 (zero_e n1 s1)) vnl vsl.
Proof.
 intros.
 simpl.
 destruct n2; simpl.
 rewrite map_nth2 with (d := (zero_e n1 s1)).
 auto.
 simpl; auto.
 rewrite leb_correct_conv; [ | omega].
 rewrite map_nth2 with (d := zero_e n1 s1).
 auto.
 auto.
Qed.

(** * Polymax Bounding

  - The lemma [polymax_bounding] states that the output of an expression [e] with [n] normal variables
    is bounded by the sum of the polynomial [poly_BC n e] and of the size of its longest safe input.
*)

Fixpoint poly_BC n (e : BC) : pol :=
  match e with 
    | zero => pcst 0 0
    | proj n s i => if (leb (S i) n) then pproj n i else (pcst n 0)
    | succ b => pcst 0 1
    | pred => pcst 0 0
    | cond => pcst 0 0
    | rec g h0 h1 =>
        pplus (pshift (poly_BC (n - 1) g)) 
        (pmult (pproj n 0) (pplus (poly_BC n h0) (poly_BC n h1)))
    | comp n s h rl tl =>
      (pplus (pcst n 0)
        (pplus (pcomp (poly_BC (length rl) h) (map (poly_BC n) rl ))
          (pplusl (map (poly_BC n) tl))))
  end.

Lemma arity_poly_BC : forall e n s,
  arities e = ok_arities n s ->
  parity (poly_BC n e) = n.
Proof.
  apply BC_ind_inf; simpl; intros; auto.
  destruct n.
  rewrite parity_pcst; trivial.
  case_eq (leb i n); intros.
  rewrite parity_pproj; trivial.
  rewrite parity_pcst; trivial.
  rewrite H3, H4, <- minus_n_O, H2.
  repeat rewrite Nat.max_idempotent; trivial.
  apply max_l.
  apply Nat.max_lub.
  apply maxl_map; intros.
  rewrite in_map_iff in H5.
  destruct H5 as [p [Hp1 Hp2]]; subst; auto.
  rewrite parity_pplusl.
  apply maxl_map; intros.
  rewrite in_map_iff in H5.
  destruct H5 as [p [Hp1 Hp2]]; subst; auto.
Qed.

Lemma pWF_poly_BC : forall e n s,
  arities e = ok_arities n s -> pWF (poly_BC n e).
Proof.
  apply BC_ind_inf; simpl; intros; auto; try pWF; auto.
  destruct n; [ pWF | ].
  case_eq (leb i n); intros; pWF.
  apply leb_complete in H0; omega.
  rewrite <- minus_n_O; auto.
  rewrite in_map_iff in H5.
  destruct H5 as [p [Hp1 Hp2]]; subst; auto.
  rewrite in_map_iff in H5.
  destruct H5 as [p [Hp1 Hp2]]; subst; auto.
Qed.
  
Lemma polymax_bounding : forall (e : BC) xl yl n s,
  arities e = ok_arities n s ->
  length (sem e xl yl) <= 
  peval (poly_BC n e) (map (@length _) xl) + maxl (map (@length _) yl).
Proof.
  intros.
  revert e n s H xl yl.
  refine (BC_ind_inf ((fun n s e => forall xl yl : list bs,
   length (sem e xl yl) <=
   peval (poly_BC n e) (map (@length _) xl) + maxl (map (@length _) yl))) _ _ _ _ _ _ _); simpl; intros.
  omega.  
  destruct n.
  eapply le_trans;[ apply nth_maxl_bound | ]; trivial.
  case_eq (leb i n); intros.
  apply leb_complete in H0.
  revert i H H0.
  induction xl; simpl; intros; simpl; destruct i; simpl; try omega.
  rewrite pproj_correct; simpl; omega.
  eapply le_trans;[ apply IHxl | ]; trivial; omega.
  eapply le_trans;[ apply nth_maxl_bound | ]; trivial.
  
  rewrite hd_nth_0; apply le_n_S; apply nth_maxl_bound; trivial.
  
  eapply le_trans;[ | apply nth_maxl_bound].
  instantiate (1:=nil).
  rewrite hd_nth_0.
  instantiate (1:= 0).
  destruct (@nth (list bool) Datatypes.O yl (@nil bool)); simpl; omega.
  trivial.
  
  do 3 (destruct yl; simpl; try omega).
  destruct l; simpl; auto with arith.
  destruct yl.
  destruct l; simpl.
  auto with arith.
  destruct b; simpl.
  rewrite Nat.max_0_r.
  case_eq (max (length l0) (length l1)); intros.
  apply Nat.max_lub_r with (n := length l0).
  rewrite H;  omega.
  rewrite Nat.succ_max_distr, <- H.
  eapply le_trans;[ | apply Nat.le_max_r].
  apply Nat.le_max_r.
  omega.
  destruct l; simpl.
  apply Nat.le_max_l.
  destruct b; simpl;
    case_eq ( max (length l0)
      (max (length l1) (max (length l2) (maxl (map (@length _) yl))))); intros.
  apply Nat.max_lub_l with (m := length l2).
  apply Nat.max_lub_r with (n := length l0).
  apply Nat.max_lub_l with (m := (maxl (map (@length _) yl))).
  rewrite <- Nat.max_assoc, <- Nat.max_assoc, H; omega.
  rewrite Nat.succ_max_distr, <- H.
  eapply le_trans;[ | apply Nat.le_max_r].
  eapply le_trans;[ | apply Nat.le_max_r].
  eapply le_trans;[ | apply Nat.le_max_l]; auto.
  apply Nat.max_lub_r with (n := length l1).
  apply Nat.max_lub_r with (n := length l0).
  apply Nat.max_lub_l with (m := (maxl (map (@length _) yl))).
  rewrite <- Nat.max_assoc, <- Nat.max_assoc, H; omega.
  rewrite Nat.succ_max_distr, <- H.
  eapply le_trans;[ | apply Nat.le_max_r].
  eapply le_trans;[ | apply Nat.le_max_r].
  eapply le_trans;[ | apply Nat.le_max_r].
  apply Nat.le_max_l.

  simpl; rewrite <- minus_n_O.
  destruct xl as [ | z xl]; simpl.
  eapply le_trans;[ apply H2 |]; simpl.
  rewrite pplus_correct, pmult_correct, pshift_correct; simpl; omega.
  induction z as [ | i z IHz ]; simpl.
  eapply le_trans; [apply H2 |].
  rewrite pplus_correct, pshift_correct; simpl; auto with arith.
  
  set (qh1 := peval (poly_BC (S n) h1) (length z :: map (@length _) xl)).
  set (qh0 := peval (poly_BC (S n) h0) (length z :: map (@length _) xl)).
  set (qg := peval (poly_BC n g)  (map (@length _) xl)).
  set (qh1S := 
    peval (poly_BC (S n) h1) (S (length z) :: map (@length _) xl)).
  set (qh0S := 
    peval (poly_BC (S n) h0) (S (length z) :: map (@length _) xl)).
  assert (qh1 <= qh1S).
  apply peval_monotonic; simpl; intros.
  case i0; trivial; omega.
  assert (qh0 <= qh0S).
  apply peval_monotonic; simpl; intros.
  case i0; trivial; omega.
  assert ( length z * (qh0 + qh1) <=  length z * (qh0S + qh1S)).
  apply mult_le_compat_l.
  omega.

  case i.
  eapply le_trans.
  eapply H4; eauto.
  simpl.
  eapply le_trans.
  apply plus_le_compat_l.
  apply Nat.max_le_compat_r.
  apply IHz.
  rewrite max_l; auto with arith.
  rewrite pplus_correct, pplus_correct, pmult_correct, pmult_correct, pplus_correct, pplus_correct,
    pshift_correct, pshift_correct, pproj_correct, pproj_correct; simpl;
      unfold qh0, qh1, qh0S, qh1S in *; omega.

  eapply le_trans.
  eapply H3; eauto.
  simpl.
  eapply le_trans.
  apply plus_le_compat_l.
  apply Nat.max_le_compat_r.
  apply IHz.
  rewrite max_l; auto with arith.
  rewrite pplus_correct, pplus_correct, pmult_correct, pmult_correct, pplus_correct, pplus_correct,
    pshift_correct, pshift_correct, pproj_correct, pproj_correct; simpl;
      unfold qh0, qh1, qh0S, qh1S in *; omega.

  rewrite pplus_correct, pcst_correct, pplus_correct, pcomp_correct, map_map; simpl.
  eapply le_trans.
  apply H2.
  rewrite <- plus_assoc.
  apply plus_le_compat.
  rewrite map_map.
  apply peval_monotonic.
  intros.
  destruct (lt_dec i (length rl)).
  erewrite map_nth2.
  eapply le_trans.
  eapply H3.
  apply nth_In; trivial.
  simpl.
  rewrite plus_0_r.
  erewrite (@map_nth2 _ _ _ _ 0 _ i).
  apply le_refl.
  instantiate (1 := zero).
  simpl; trivial.
  simpl; trivial.
  rewrite nth_overflow, nth_overflow; trivial.
  rewrite map_length; omega.
  rewrite map_length; omega.
  edestruct maxl_nth.
  destruct (lt_dec x (length tl)).
  rewrite H5. 
  erewrite map_nth2.
  eapply le_trans.
  erewrite map_nth2.
  eapply H4.
  apply nth_In; trivial.
  instantiate (2 := zero).
  simpl; trivial.
  apply plus_le_compat_r.
  erewrite <- (@map_nth2 _ _ (poly_BC n)).
  apply peval_nth_pplus.
  simpl; trivial.
  simpl; trivial.
  rewrite nth_overflow in H5.
  rewrite H5.
  omega.
  rewrite map_length, map_length.
  omega.
Qed.

Lemma proj_seq_shift_safe : forall n m ln ls d,
 map (fun x : BC => sem x ln (d :: ls)) (map (proj n (S m)) (seq (S n) m)) =
 map (fun x : BC => sem x ln ls) (map (proj n m) (seq n m)).
Proof.
 intros.
 rewrite <- seq_shift.
 rewrite map_map with (f := S).
 rewrite map_map with (f := (proj n m)).
 rewrite map_map with (f := (fun x : nat => proj n (S m) (S x))).
 apply map_ext2; intros.
 simpl.
 rewrite in_seq_iff in H.
 destruct n; simpl in *.
 rewrite <- minus_n_O; trivial.
 destruct n; simpl in *.
 rewrite <- minus_n_O; trivial.
 destruct a; simpl in *.
 elimtype False; omega.
 rewrite <- minus_n_O; trivial.
 rewrite leb_correct_conv; [ | omega ].
 case_eq (a - S n); intros.
 elimtype False; omega.
 rewrite leb_correct_conv; [ | omega ].
 f_equal.
 omega.
Qed.

Lemma proj_seq_shift_normal : forall n ln ls d,
 map (fun x : BC => sem x (d :: ln) ls) (map (proj (S n) 0) (seq 1 n)) =
 map (fun x : BC => sem x ln ls) (map (proj n 0) (seq 0 n)).
Proof.
 intros.
 rewrite <- seq_shift.
 rewrite map_map with (f := S).
 rewrite map_map with (f := (proj n 0)).
 rewrite map_map with (f := (fun x : nat => proj (S n) 0 (S x))).
 apply map_ext2; intros.
 simpl.
 rewrite in_seq_iff in H.
 destruct n; simpl in *.
 rewrite <- minus_n_O; trivial.
 trivial.
Qed.

(** * Time complexity

  We consider an obvious implementation of the language [BC] on a stack machine,
  as described in Section 3.4.2 of Bellantoni's PhD thesis.

  - The polynomial [polytime n e] is an upper for the execution time.

  - [sem_cost e vnl vsl] differs from above [sem e vnl vsl] by also computing the running time.
*)

Section TIME.

  Variable ptime_zero_cost ptime_succ_cost ptime_pred_cost ptime_cond_cost: nat.
  Variable ptime_proj_cost : nat -> nat -> nat -> nat.

  Fixpoint sem_cost_rec (sem_g sem_h0 sem_h1:list bs->list bs->bs*nat)(v:bs)(vnl vsl:list bs) :
    bs * nat :=
    match v with
      | nil => sem_g vnl vsl
      | b::v' =>
        if b
          then
            let sem_cost := sem_cost_rec sem_g sem_h0 sem_h1 v' vnl vsl in
              let sem_cost_h := sem_h1 (v'::vnl) (fst sem_cost :: vsl) in
                (fst sem_cost_h, snd sem_cost + snd sem_cost_h)
          else
            let sem_cost := sem_cost_rec sem_g sem_h0 sem_h1 v' vnl vsl in
              let sem_cost_h := sem_h0 (v'::vnl) (fst sem_cost :: vsl) in
                (fst sem_cost_h, snd sem_cost + snd sem_cost_h)
    end.

Fixpoint sem_cost (e:BC)(vnl vsl:list bs) : bs*nat :=
 match e with
 | zero => (nil, ptime_zero_cost)
 | proj n s j => (
   if leb (S j) n then
     nth j vnl nil
     else nth (j-n) vsl nil, ptime_proj_cost n s j
   )
 | succ b => (b :: hd nil vsl, ptime_succ_cost)
 | pred => (tail (hd nil vsl), ptime_pred_cost)
 | cond => (
     match vsl with
     | a :: b :: c :: d :: _ =>
       match a with
         | nil => b
         | true :: _ => c
         | false :: _ => d
       end
     | a :: b :: c :: _ =>
       match a with
         | nil => b
         | true :: _ => c
         | false :: _ => nil
       end
     | a :: b :: _ =>
       match a with
         | nil => b
         | _ => nil
       end
     | _ => nil
     end, ptime_cond_cost
   )
 | rec g h0 h1 =>
     sem_cost_rec (sem_cost g) (sem_cost h0) (sem_cost h1) (hd nil vnl) (tail vnl) vsl
 | comp _ _ h nl sl =>
   let sem_cost_nl := List.map (fun ne => sem_cost ne vnl nil) nl in
   let sem_cost_sl := List.map (fun se => sem_cost se vnl vsl) sl in
   let sem_nl := List.map (@fst _ _) sem_cost_nl in
   let sem_sl := List.map (@fst _ _) sem_cost_sl in
   let cost_nl := List.map (@snd _ _) sem_cost_nl in
   let cost_sl := List.map (@snd _ _) sem_cost_sl in
   let sem_cost_h := sem_cost h sem_nl sem_sl in
   (fst sem_cost_h, snd sem_cost_h + plusl cost_nl + plusl cost_sl)
 end.

Lemma sem_cost_correct :
 forall e n s,
 arities e = ok_arities n s ->
 forall vnl vsl,
 fst (sem_cost e vnl vsl) = sem e vnl vsl.
Proof.
 refine (BC_ind_inf _ _ _ _ _ _ _ _); simpl; trivial; intros.
 induction (hd nil vnl) as [ | [ | ] ]; simpl; trivial; congruence.
 rewrite H2.
 do 2 rewrite map_map.
 clear H.
 f_equal.
 induction rl; simpl; intros; trivial.
 rewrite H3, IHrl; auto with *.
 induction tl; simpl; intros; trivial.
 rewrite H4, IHtl; auto with *.
Qed.

  Variable ptime_zero ptime_succ ptime_pred ptime_cond: pol.
  Variable ptime_proj : nat -> nat -> nat -> pol.

  Hypothesis ptime_zero_spec : 
    snd (sem_cost zero nil nil) <= peval ptime_zero nil.

  Hypothesis ptime_zero_wf : pWF ptime_zero.

  Hypothesis ptime_zero_arity : parity ptime_zero = 0.

  Hypothesis ptime_succ_spec : forall b,
    snd (sem_cost (succ b) nil nil) <= peval ptime_succ nil.

  Hypothesis ptime_succ_wf : pWF ptime_succ.

  Hypothesis ptime_succ_arity : parity ptime_succ = 0.

  Hypothesis ptime_proj_spec : forall n s i l,
    length l = n ->
    snd (sem_cost (proj n s i) l nil) <= peval (ptime_proj n s i) (map (@length _) l).

  Hypothesis ptime_proj_wf : forall n s i, pWF (ptime_proj n s i).

  Hypothesis ptime_proj_arity : forall n s i, parity (ptime_proj n s i) = n.

  Hypothesis ptime_cond_spec : 
    snd (sem_cost cond nil nil) <= peval ptime_cond nil.

  Hypothesis ptime_cond_wf : pWF ptime_cond.

  Hypothesis ptime_cond_arity : parity ptime_cond = 0.

  Hypothesis ptime_pred_spec : 
    snd (sem_cost pred nil nil) <= peval ptime_pred nil.

  Hypothesis ptime_pred_wf : pWF ptime_pred.

  Hypothesis ptime_pred_arity : parity ptime_pred = 0.

Fixpoint poly_time n (e:BC) : pol :=
  match e with
    | zero => ptime_zero
    | succ _ => ptime_succ
    | pred => ptime_pred
    | cond  => ptime_cond
    | proj n s i => ptime_proj n s i
    | rec g h0 h1 => 
      pplus (pshift (poly_time (n - 1) g))
      (pmult (pproj n 0) (pplus (poly_time n h0) (poly_time n h1)))
    | comp n0 s h rl tl =>
      pplus (pplus (pcst n0 0) (pcomp (poly_time (length rl) h) (map (poly_BC n0) rl)))
      (pplus (pplusl (map (poly_time n0) rl)) (pplusl (map (poly_time n0) tl)))
  end.
 
Lemma poly_time_WF : forall e n s, arities e = ok_arities n s -> pWF (poly_time n e).
Proof.
 refine (BC_ind_inf _ _ _ _ _ _ _ _); simpl; trivial; intros; try pWF; auto.
 rewrite <- minus_n_O; auto.
 apply in_map_iff in H5.
 destruct H5 as [e2 [H5 H7] ]; subst.
 eapply pWF_poly_BC; eauto.
 apply in_map_iff in H5.
 destruct H5 as [e2 [H5 H7] ]; subst; auto.
 apply in_map_iff in H5.
 destruct H5 as [e2 [H5 H7] ]; subst; auto.
Qed.

Lemma arity_poly_time : forall e n s,
  arities e = ok_arities n s ->
  parity (poly_time n e) = n.
Proof.
  apply BC_ind_inf; simpl; intros; auto.
  rewrite H3, H4, <- minus_n_O, H2.
  rewrite !Nat.max_idempotent; trivial.
  rewrite !parity_pplusl, !map_map.
  rewrite max_l; auto.
  rewrite max_l; auto.
  apply maxl_map; intros.
  eapply arity_poly_BC; eauto.
  apply Nat.max_lub.
  apply maxl_bound_in; intros.
  rewrite in_map_iff in H5.
  destruct H5 as [p [Hp1 Hp2]].
  rewrite <- Hp1.
  rewrite H3; trivial.
  apply Nat.le_max_l.
  apply le_trans with n.
  apply maxl_map; intros.  
  apply H4; auto.
  apply Nat.le_max_l.
Qed.

Lemma sem_cost_bounded : forall e n s,
 arities e = ok_arities n s ->
 (forall vnl vsl,
   length vnl = n -> 
   length vsl = s -> 
   snd (sem_cost e vnl vsl) <=
   peval (poly_time n e) (List.map (@length _) vnl)).
Proof.
refine (BC_ind_inf _ _ _ _ _ _ _ _); simpl; intros; trivial; try omega.

rewrite (@length_nil _ _ H); apply ptime_zero_spec.
apply (ptime_proj_spec n s i vnl); trivial.
rewrite (@length_nil _ _ H); apply (ptime_succ_spec b).
rewrite (@length_nil _ _ H); apply ptime_pred_spec.
rewrite (@length_nil _ _ H); apply ptime_cond_spec.

rewrite !pplus_correct, pshift_correct.
rewrite pmult_correct, pplus_correct, pproj_correct.
rewrite <- minus_n_O.
destruct vnl as [ | x vnl]; simpl in *;[ discriminate | ].
induction x; simpl.
rewrite <- plus_n_O; auto.
destruct a; simpl.
eapply le_trans.
apply plus_le_compat.
apply IHx.
apply H4; simpl; omega.
rewrite <- !plus_assoc; simpl.
apply plus_le_compat; trivial.
match goal with 
  [ |- ?a + ?b <= ?c + (?d + ?e) ] => apply le_trans with (e + d);[ | omega ]
end.
apply plus_le_compat; trivial.
apply mult_le_compat; trivial.
apply plus_le_compat; trivial.
apply peval_monotonic; intros; simpl.
destruct i; simpl; try omega.
apply peval_monotonic; intros; simpl.
destruct i; simpl; try omega.
apply peval_monotonic; intros; simpl.
destruct i; simpl; try omega.
eapply le_trans.
apply plus_le_compat.
apply IHx.
apply H3; simpl; omega.
rewrite <- !plus_assoc; simpl.
apply plus_le_compat; trivial.
match goal with 
  [ |- ?a + ?b <= ?c + (?d + ?e) ] => apply le_trans with (e + c);[ | omega]
end.
apply plus_le_compat; trivial.
apply mult_le_compat; trivial.
apply plus_le_compat; trivial.
apply peval_monotonic; intros; simpl.
destruct i; simpl; try omega.
apply peval_monotonic; intros; simpl.
destruct i; simpl; try omega.
apply peval_monotonic; intros; simpl.
destruct i; simpl; try omega.

rewrite !pplus_correct, pcst_correct, pcomp_correct, !pplusl_correct; simpl.
rewrite !plus_assoc.
apply plus_le_compat.
apply plus_le_compat.
eapply le_trans.
apply H2.
rewrite !map_length; trivial.
rewrite !map_length; trivial.
rewrite !map_map; simpl.
apply peval_monotonic.
intros.
destruct (lt_dec i (length rl)).
erewrite map_nth2.
eapply le_trans.
erewrite sem_cost_correct.
eapply polymax_bounding.
apply H0; apply nth_In; trivial.
apply H0; apply nth_In; trivial.
erewrite map_nth2.
simpl.
instantiate (1 := zero).
instantiate (1 := zero).
omega.
simpl; rewrite pcst_correct; trivial.
simpl; trivial.
rewrite !nth_overflow; trivial; rewrite map_length; omega.
rewrite !map_map.
apply plusl_compat.
intros.
apply H3; auto.
rewrite !map_map.
apply plusl_compat.
intros.
apply H4; auto.
Qed.

End TIME.

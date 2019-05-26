Require Import InfSeqExt.infseq.
Require Import InfSeqExt.exteq.

(* map *)
Section sec_map.

Variable A B: Type.

CoFixpoint map (f: A->B) (s: infseq A): infseq B :=
  match s with
    | Cons x s => Cons (f x) (map f s)
  end.

Lemma map_Cons: forall (f:A->B) x s, map f (Cons x s) = Cons (f x) (map f s).
Proof using.
intros. pattern (map f (Cons x s)). rewrite <- recons. simpl. reflexivity.
Qed.

End sec_map.

Arguments map [A B] _ _.
Arguments map_Cons [A B] _ _ _.

(* --------------------------------------------------------------------------- *)
(* Zipping two infseqs: useful for map theory *)
Section sec_zip.

Variable A B: Type.

CoFixpoint zip (sA: infseq A) (sB: infseq B) : infseq (A*B) := 
  match sA, sB with
    | Cons a sA0, Cons b sB0 => Cons (a, b) (zip sA0 sB0)
  end.

Lemma zip_Cons: forall (a:A) (b:B) sA sB, zip (Cons a sA) (Cons b sB) = Cons (a, b) (zip sA sB). 
Proof using.
intros. pattern (zip (Cons a sA) (Cons b sB)); rewrite <- recons. simpl. reflexivity. 
Qed.

End sec_zip.

Arguments zip [A B] _ _.
Arguments zip_Cons [A B] _ _ _ _.

(* --------------------------------------------------------------------------- *)
(* map and_tl temporal logic *)

Section sec_map_modalop.

Variable A B: Type.

Lemma and_tl_map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   (forall s, P' s -> Q' (map f s)) ->
   forall (s: infseq A),
   (P /\_ P') s -> (Q /\_ Q') (map f s).
Proof using.
unfold and_tl; intuition. 
Qed.

Lemma and_tl_map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   (forall s, Q' (map f s) -> P' s) ->
   forall (s: infseq A),
   (Q /\_ Q') (map f s) -> (P /\_ P') s.
Proof using.
unfold and_tl; intuition. 
Qed.

Lemma or_tl_map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   (forall s, P' s -> Q' (map f s)) ->
   forall (s: infseq A),
   (P \/_ P') s -> (Q \/_ Q') (map f s).
Proof using.
unfold or_tl; intuition. 
Qed.

Lemma or_tl_map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   (forall s, Q' (map f s) -> P' s) ->
   forall (s: infseq A),
   (Q \/_ Q') (map f s) -> (P \/_ P') s.
Proof using.
unfold or_tl; intuition. 
Qed.

Lemma impl_tl_map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   (forall s, P' s -> Q' (map f s)) ->
   forall (s: infseq A),
   (P ->_ P') s -> (Q ->_ Q') (map f s).
Proof using.
unfold impl_tl; intuition. 
Qed.

Lemma impl_tl_map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   (forall s, Q' (map f s) -> P' s) ->
   forall (s: infseq A),
   (Q ->_ Q') (map f s) -> (P ->_ P') s.
Proof using.
unfold impl_tl; intuition. 
Qed.

Lemma not_tl_map :
   forall (f: A->B) (P : infseq A->Prop) (Q: infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), (~_ P) s -> (~_ Q) (map f s).
Proof using.
unfold not_tl; intuition. 
Qed.

Lemma not_tl_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), (~_ Q) (map f s) -> (~_ P) s.
Proof using.
unfold not_tl; intuition. 
Qed.

Lemma now_map :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   now (fun x => P (f x)) s -> now P (map f s).
Proof using.
intros f P (x, s) nP; assumption. 
Qed.

Lemma now_map_conv :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   now P (map f s) -> now (fun x => P (f x)) s.
Proof using.
intros f P (x, s) nP; assumption. 
Qed.

Lemma next_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), next P s -> next Q (map f s).
Proof using.
intros f P Q PQ [x s]; apply PQ.
Qed.

Lemma next_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), next Q (map f s) -> next P s.
Proof using.
intros f P Q QP [x s]; apply QP.
Qed.

Lemma consecutive_map :
   forall (f: A->B) (P: B->B->Prop) (s: infseq A),
   consecutive (fun x y => P (f x) (f y)) s -> consecutive P (map f s).
Proof using.
intros f P (x, (y, s)) nP; assumption. 
Qed.

Lemma consecutive_map_conv :
   forall (f: A->B) (P: B->B->Prop) (s: infseq A),
   consecutive P (map f s) -> consecutive (fun x y => P (f x) (f y)) s.
Proof using.
intros f P (x, (y, s)) nP; assumption. 
Qed.

Lemma always_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), always P s -> always Q (map f s).
Proof using.
intros f P Q PQ. cofix cf.
intros (x, s) a. case (always_Cons a); intros a1 a2. constructor.
- apply PQ. assumption.
- rewrite map_Cons; simpl. apply cf; assumption.
Qed.

Lemma always_map_conv_ext :
  forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop) (J : infseq A -> Prop),
    (forall x s, J (Cons x s) -> J s) ->
    (forall s, J s -> Q (map f s) -> P s) ->
    forall s, J s -> always Q (map f s) -> always P s.
Proof using.
intros f J P Q inv JQP. cofix c.
intros [x s] Js a.
rewrite map_Cons in a. case (always_Cons a); intros a1 a2. constructor.
- apply JQP. assumption.
  rewrite map_Cons; assumption.
- simpl. apply c.
  * apply (inv x). assumption.
  * assumption.
Qed.

Lemma always_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), always Q (map f s) -> always P s.
Proof using.
intros f P Q QP s.
apply (always_map_conv_ext f P Q True_tl); auto.
Qed.

Lemma weak_until_map :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, J s -> K (map f s)) ->
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A),
   weak_until J P s -> weak_until K Q (map f s).
Proof using.
intros f J P K Q JK PQ. cofix cf.
intros (x, s) un. case (weak_until_Cons un); clear un.
- intro Pxs; constructor 1. apply PQ. assumption.
- intros (Jxs, un). rewrite map_Cons. constructor 2.
  * rewrite <- map_Cons. auto.
  * simpl. auto.
Qed.

Lemma weak_until_map_conv :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, K (map f s) -> J s) ->
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A),
   weak_until K Q (map f s) -> weak_until J P s.
Proof using.
intros f J P K Q KJ QP. cofix cf.
intros (x, s) un.
rewrite map_Cons in un; case (weak_until_Cons un); clear un; rewrite <- map_Cons.
- intro Qxs; constructor 1. apply QP. assumption.
- intros (Kxs, un). constructor 2; simpl; auto.
Qed.

Lemma until_map :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, J s -> K (map f s)) ->
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A),
   until J P s -> until K Q (map f s).
Proof using.
intros f J P K Q JK PQ s un.
induction un.
- apply U0, PQ. assumption.
- rewrite map_Cons.
  apply U_next.
  * rewrite <- map_Cons.
    apply JK.
    assumption.
  * assumption.
Qed.

Lemma release_map :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, J s -> K (map f s)) ->
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A),
   release J P s -> release K Q (map f s).
Proof using.
intros f J P K Q JK PQ. cofix cf.
intros (x, s) rl. case (release_Cons rl); clear rl.
intros Pxs orR.
case orR; intro cR.
- apply R0.
  * apply PQ. assumption.
  * apply JK. assumption.
- apply R_tl.
  * apply PQ. assumption.
  * apply cf. assumption.
Qed.

Lemma release_map_conv :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, K (map f s) -> J s) ->
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A),
   release K Q (map f s) -> release J P s.
Proof using.
intros f J P K Q KJ QP. cofix cf.
intros (x, s) rl.
rewrite map_Cons in rl; case (release_Cons rl); clear rl; rewrite <- map_Cons; intros QC orR; case orR; intro cR.
- apply R0.
  * apply QP. assumption.
  * apply KJ. assumption.
- apply R_tl.
  * apply QP. assumption.
  * apply cf. assumption.
Qed.

Lemma eventually_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall s, eventually P s -> eventually Q (map f s).
Proof using.
intros f P Q PQ s e. induction e as [s ok | x s e induc_hyp].
- destruct s as (x, s); simpl in *. rewrite map_Cons. constructor 1.
  rewrite <- map_Cons. apply PQ. exact ok.
- rewrite map_Cons. constructor 2. exact induc_hyp.
Qed.

(* The converse seems to require much more work *)

Definition fstAB := fst (A:=A) (B:=B).

Lemma exteq_fst_zip:
  forall sA sB, exteq (map fstAB (zip sA sB)) sA.
Proof using.
cofix cf. intros (a, sA) (b, sB). 
rewrite zip_Cons. rewrite map_Cons. constructor. apply cf.
Qed.

Lemma exteq_zip_map :
   forall (f: A->B) (sA: infseq A) (sB: infseq B),
   always (now (fun c: A*B => let (x, y) := c in y = f x)) (zip sA sB) ->
   exteq sB (map f (map fstAB (zip sA (map f sA)))).
Proof using. 
intros f. cofix cf. 
intros (a, sA) (b, sB).
repeat rewrite map_Cons; repeat rewrite zip_Cons; repeat rewrite map_Cons; simpl. 
intro al; case (always_Cons al); clear al; simpl. intros e al. case e. constructor. 
apply cf. exact al. 
Qed.

Lemma eventually_map_conv_aux :
   forall (f: A->B) (Q: infseq B->Prop), extensional Q ->
   forall (s: infseq A) (sB: infseq B),
   always (now (fun c: A*B => let (x, y) := c in y = f x)) (zip s sB) ->
   eventually Q sB ->
   eventually (fun sc => Q (map f (map fstAB sc))) (zip s (map f s)).
Proof using.
intros f Q extQ s sB al ev. genclear al; genclear s.
induction ev as [(b, sB) QbsB | b sB ev induc_hyp].
- intros (a, sA) al.
  constructor 1. apply extQ with (Cons b sB); try assumption.
  apply exteq_zip_map. apply al.
- intros (a, sA). repeat rewrite map_Cons. repeat rewrite zip_Cons.
  intro al. case (always_Cons al); simpl. clear al; intros e al. 
  constructor 2. apply induc_hyp. exact al. 
Qed.

Lemma eventually_map_conv_ext :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop) (J : infseq A -> Prop),
   extensional P -> extensional Q -> extensional J ->
   (forall x s, J (Cons x s) -> J s) ->
   (forall s, J s -> Q (map f s) -> eventually P s) ->
   forall s, J s -> eventually Q (map f s) -> eventually P s.
Proof using.
intros f P Q J extP extQ extJ inv QP s Js ev.
revert Js.
assert (efst: J (map fstAB (zip s (map f s))) -> eventually P (map fstAB (zip s (map f s)))).
- assert (evzip : eventually (fun sc => Q (map f (map fstAB sc))) (zip s (map f s))).
  * clear extP QP P.
     assert (alzip : (always (now (fun c : A * B => let (x, y) := c in y = f x)) (zip s (map f s)))).
     + clear ev extQ. generalize s. cofix cf. intros (x, s0). constructor.
       -- simpl. reflexivity.
       -- simpl. apply cf.
     + apply (eventually_map_conv_aux f Q extQ s (map f s) alzip ev).
  * clear ev. induction evzip as [((a, b), sAB) QabsAB | c sAB _ induc_hyp].
    + intros Js.
      apply QP; assumption.
    + intros Js.
      rewrite map_Cons.
      apply E_next.
      apply induc_hyp.
      rewrite map_Cons in Js.
      apply (inv (fstAB c)).
      assumption.
- intros Js.
  assert (emJ: J (map fstAB (zip s (map f s)))).
  * unfold extensional in extJ.
    apply (extJ s).
    + apply exteq_sym. apply exteq_fst_zip.
    + assumption.
  * apply efst in emJ.
    genclear emJ.
    apply extensional_eventually.
    + exact extP.
    + apply exteq_fst_zip.
Qed.

Lemma eventually_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   extensional P -> extensional Q ->
   (forall s, Q (map f s) -> P s) ->
   forall s, eventually Q (map f s) -> eventually P s.
Proof using.
intros f P Q extP extQ QP s.
apply eventually_map_conv_ext with (J := True_tl); auto.
- apply extensional_True_tl.
- intros. apply E0. apply QP. assumption.
Qed.

Lemma eventually_map_monotonic :
   forall (f: A->B) (P Q J: infseq A->Prop) (K : infseq B -> Prop),
   (forall x s, J (Cons x s) -> J s) ->
   (forall x s, K (map f (Cons x s)) -> K (map f s)) ->
   (forall s, J s -> K (map f s) -> Q s -> P s) ->
   forall s, J s -> K (map f s) -> eventually Q s -> eventually P s.
Proof using.
intros f P Q J K Jinv Kinv JKQP s invJ invK ev.
induction ev as [s Qs | x s ev IHev].
- apply E0.
  apply JKQP; assumption.
- apply E_next.
  apply IHev.
  * apply (Jinv x); assumption.
  * apply (Kinv x); assumption.
Qed.

Lemma inf_often_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), inf_often P s -> inf_often Q (map f s).
Proof using.
intros f P Q PQ.
apply always_map; apply eventually_map; assumption.
Qed.

Lemma inf_often_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   extensional P -> extensional Q -> 
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), inf_often Q (map f s) -> inf_often P s.
Proof using.
intros f P Q eP eQ QP.
apply always_map_conv; apply eventually_map_conv; trivial.
Qed.

Lemma continuously_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), continuously P s -> continuously Q (map f s).
Proof using.
intros f P Q PQ.
apply eventually_map; apply always_map; assumption.
Qed.

Lemma continuously_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   extensional P -> extensional Q -> 
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), continuously Q (map f s) -> continuously P s.
Proof using.
intros f P Q eP eQ QP.
apply eventually_map_conv.
- apply extensional_always; assumption.
- apply extensional_always; assumption.
- apply always_map_conv; assumption.
Qed.

(* Some corollaries *)

Lemma eventually_now_map :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   eventually (now (fun x => P (f x))) s -> eventually (now P) (map f s).
Proof using.
intros f P. apply eventually_map. apply now_map.
Qed.

Lemma eventually_now_map_conv :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   eventually (now P) (map f s) -> eventually (now (fun x => P (f x))) s.
Proof using.
intros f P s. apply eventually_map_conv.
- apply extensional_now. 
- apply extensional_now. 
- clear s. intros (x, s). repeat rewrite map_Cons. simpl. trivial.
Qed.

Lemma eventually_map_now_eq :
  forall (f: A -> B) a s, eventually (now (eq a)) s -> 
  eventually (now (eq (f a))) (map f s).
Proof using.
intros f a. apply eventually_map.
intros s noa. apply now_map.
genclear noa. monotony. apply f_equal.
Qed.

End sec_map_modalop. 

Arguments and_tl_map [A B f P P' Q Q'] _ _ [s] _.
Arguments and_tl_map_conv [A B f P P' Q Q'] _ _ [s] _.
Arguments or_tl_map [A B f P P' Q Q'] _ _ [s] _.
Arguments or_tl_map_conv [A B f P P' Q Q'] _ _ [s] _.
Arguments impl_tl_map [A B f P P' Q Q'] _ _ [s] _ _.
Arguments impl_tl_map_conv [A B f P P' Q Q'] _ _ [s] _ _.
Arguments not_tl_map [A B f P Q] _ [s] _ _.
Arguments not_tl_map_conv [A B f P Q] _ [s] _ _.
Arguments now_map [A B f P s] _.
Arguments now_map_conv [A B f P s] _.
Arguments next_map [A B f P Q] _ [s] _.
Arguments next_map_conv [A B f P Q] _ [s] _.
Arguments consecutive_map [A B f P s] _.
Arguments consecutive_map_conv [A B f P s] _.
Arguments always_map [A B f P Q] _ [s] _.
Arguments always_map_conv_ext [A B f P Q J] _ _ [s] _ _.
Arguments always_map_conv [A B f P Q] _ [s] _.
Arguments weak_until_map [A B f J P K Q] _ _ [s] _.
Arguments weak_until_map_conv [A B f J P K Q] _ _ [s] _.
Arguments until_map [A B f J P K Q] _ _ [s] _.
Arguments release_map [A B f J P K Q] _ _ [s] _.
Arguments release_map_conv [A B f J P K Q] _ _ [s] _.
Arguments eventually_map [A B f P Q] _ [s] _.
Arguments eventually_map_conv_ext [A B f P Q J] _ _ _ _ _ [s] _ _.
Arguments eventually_map_conv [A B f P Q] _ _ _ [s] _.
Arguments eventually_map_monotonic [A B f P Q] _ _ _ _ _ [s] _ _ _.
Arguments inf_often_map [A B f P Q] _ [s] _.
Arguments inf_often_map_conv [A B f P Q] _ _ _ [s] _.
Arguments continuously_map [A B f P Q] _ [s] _.
Arguments continuously_map_conv [A B f P Q] _ _ _ [s] _.
Arguments eventually_now_map [A B f P s] _.
Arguments eventually_now_map_conv [A B f P s] _.
Arguments eventually_map_now_eq [A B f a s] _.

From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
Require FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ProtocolWithInvariant.
Section ProtocolWithInvariant.

Variable p : protocol.

(* Decompose the initial protocol *)
Notation l := (plab p).
Notation coh := (coh p).

(* User-provided (supposedly inductive) invariant *)
Variable I : dstatelet -> pred nid -> Prop.
(* "Initial" state *)
Variable d0 : dstatelet.

Definition W := mkWorld p.

Notation toSt d := (l \\-> d).

(* TODO: prove relation between stability and reachability *)

(* New coherence predicate: includes only reachable states *)
Definition cohI :=
  [Pred d | coh d /\ I d (nodes p d)].

(* The usual coherence properties all hold *)
Lemma cohIVd d : cohI d -> valid (dstate d).
Proof. by case=>/cohVl. Qed.

Lemma cohIVs d : cohI d -> valid (dsoup d).
Proof. by case=>/cohVs. Qed.

Lemma cohIDom d : cohI d -> dom (dstate d) =i nodes p d.
Proof. by case=>/cohDom. Qed.

(* Define it as a coherence *)
Definition CohI := CohPred (CohPredMixin cohIVd cohIVs cohIDom).

(* Some helper lemmas *)
Lemma st_helper d : (getStatelet (toSt d) l) = d.
Proof. by rewrite /getStatelet findPt. Qed.

Lemma cohSt d : coh d -> Coh W (toSt d).
Proof.
move=>C; split.
- by apply/andP; rewrite valid_unit; split=>//; apply: validPt.
- by apply: validPt.
- by move=>z lc ls st; rewrite dom0.
- by move=>z; rewrite !domPt inE.
move=>k; case B: (k \in dom (toSt d)); last first.
- rewrite /getProtocol /getStatelet.
  case: (dom_find k (toSt d))=>[->|v /find_some]; last by rewrite B.
  rewrite domPt inE/= in B.
  by case: (dom_find k (toSt p))=>[->|? /find_some]//; rewrite domPt inE/= B.
rewrite domPt inE/= in B; move/eqP: B=>B; subst k.
by rewrite /getProtocol /getStatelet !findPt.
Qed.

Section SendInvWrapper.

Variable st : send_trans coh.

Definition send_safeI this to d m :=
  send_safe st this to d m /\ I d (nodes p d).

Lemma s_safe_cohI this to d m : send_safeI this to d m -> CohI d.
Proof. by case=>/s_safe_coh=>[H1]H2. Qed.

Lemma s_safe_inI this to d m : send_safeI this to d m ->
                               this \in nodes p d /\ to \in nodes p d.
Proof. by case=>/s_safe_in. Qed.

Definition send_stepI: send_step_t (send_safeI) :=
  fun this to d msg S => (@send_step _ _ st this to d msg (proj1 S)).

Lemma s_safe_defI this to d msg :
  send_safeI this to d msg <->
  exists b pf, @send_stepI this to d msg pf = Some b.
Proof.
move: (s_safe_def st this to d msg)=>H; split.
- move=>S; case: (S)=>/H[b][pf]E H1; exists b.
  exists (conj pf H1).
  by rewrite /send_stepI (pf_irr (proj1 (conj pf H1)) pf). 
by case=>b[pf]E.
Qed.

(* Inducitve step - prove that the invariant indeed holds *)
Definition S_inv := forall this to d msg (S : send_safe st this to d msg) b,
    I d (nodes p d) -> Some b = send_step S ->
    let: f' := upd this b (dstate d) in
    let: s' := (post_msg (dsoup d) (Msg (TMsg (t_snd st) msg) this to true)).1 in
    let: d' := DStatelet f' s' in
    (forall z, z == this = false -> getLocal z d' = getLocal z d) ->
    I d' (nodes p d').

Hypothesis HIstep : S_inv.

Lemma s_step_cohI : s_step_coh_t CohI (t_snd st) send_stepI.
Proof.
have E1: (getProtocol W l) = p by rewrite /getProtocol/W/=findPt.
move/s_step_coh: (st)=>H.
move=>this to d msg [S]H1 b.
rewrite /send_stepI (pf_irr (proj1 (conj S H1)) S)=>E.
split=>//= ; first by apply: (H this to d msg S b E).
apply: (HIstep H1 E _)=>//.
by move=>z N; rewrite /getLocal/= findU N.
Qed.

(* Assemble a new send-transition for the rich coherence *)
Definition snd_transI := SendTrans s_safe_cohI s_safe_inI s_safe_defI s_step_cohI.

End SendInvWrapper.


Section ReceiveInvWrapper.

Variable rt : receive_trans coh.

Definition receive_stepI: receive_step_t CohI :=
  fun this from m d C pf => receive_step rt from m (proj1 C) pf.

Definition R_inv := forall d from this i (C : coh d) m
                           (pf: this \in nodes p d),
    I d (nodes p d) ->
    find i (dsoup d) = Some (Msg m from this true) ->
    this \in dom (dstate d) ->
    msg_wf rt C this from m -> tag m = t_rcv rt ->
    let: loc' := receive_step rt from m C pf in
    let: s'' := consume_msg (dsoup d) i in
    let: f' := upd this loc' (dstate d) in
    let: d' := (DStatelet f' s'') in
    (forall z, z == this = false -> getLocal z d' = getLocal z d) ->
    I d' (nodes p d').

Hypothesis HIstep : R_inv.

Notation msg_wfI := (fun d (C : CohI d) => msg_wf rt (proj1 C)).

Lemma r_step_cohI :
  r_step_coh_t msg_wfI (t_rcv rt) receive_stepI.
Proof. 
have E1: (getProtocol W l) = p by rewrite /getProtocol/W/=findPt.
move=>d from this i C F m D N Wf T.
rewrite /receive_stepI/=.
set d' := {| dstate := upd this (receive_step rt from m (proj1 C) F) (dstate d);
             dsoup := consume_msg (dsoup d) i |}.
split; first by apply: (r_step_coh F D N Wf T).
- apply: (HIstep (proj2 C) N D Wf T)=>//z N'.
  by rewrite /getLocal findU N'.
Qed.

Definition rcv_transI := @ReceiveTrans _ CohI _ msg_wfI _ r_step_cohI.

End ReceiveInvWrapper.

(* The client has to provide instances of the following 
   two structures along with the proofs of Hs and Hr. *)

Structure SendInv := SI {
  st : send_trans coh;
  st_inv : S_inv st;
}.

Structure ReceiveInv := RI {
  rt : receive_trans coh;
  rt_inv : R_inv rt;
}.

Structure InductiveInv := II {
  sts : seq SendInv;
  rts : seq ReceiveInv;
  _ : map st sts = snd_trans p;
  _ : map rt rts = rcv_trans p
}.

(* Obtain new send/receive transitions *)
Definition stsI sts := map (fun stt =>
                          @snd_transI (st stt) (@st_inv stt)) sts.
Definition rtsI rts := map (fun rtt =>
                          @rcv_transI (rt rtt) (@rt_inv rtt)) rts.

Import FunctionalExtensionality.

Variable ii : InductiveInv.

Lemma us : uniq (map (@t_snd _ _) (stsI (sts ii))).
Proof.
case: ii=>sts rts Hs Hr; rewrite /stsI -seq.map_comp/=.
suff E: (t_snd (coh:=CohI) \o
               (fun stt : SendInv => snd_transI (st_inv (s:=stt))))
        = fun stt => t_snd (st stt).
by rewrite E seq.map_comp; rewrite Hs; apply: snd_uniq.
(* TODO: can we do without this? *)
by apply: functional_extensionality=>z. 
Qed.

Lemma ur : uniq (map (@t_rcv _ _) (rtsI (rts ii))).
Proof.
case: ii=>sts rts Hs Hr; rewrite /stsI -seq.map_comp/=.
suff E: (t_rcv (coh:=CohI) \o
               (fun rtt : ReceiveInv => rcv_transI (rt_inv (r:=rtt))))
        = fun rtt => t_rcv (rt rtt).
by rewrite E seq.map_comp; rewrite Hr; apply: rcv_uniq.
(* TODO: can we do without this? *)
by apply: functional_extensionality=>z. 
Qed.

Definition ProtocolWithIndInv := @Protocol _ l _ _ _ us ur.

Lemma stIn (s : SendInv) :
  s \In (sts ii) ->
  (snd_transI (@st_inv s)) \In (snd_trans ProtocolWithIndInv).
Proof. by move=>H; rewrite /stsI/=; apply/Mem_map. Qed.

Lemma rtIn (r : ReceiveInv) :
  r \In (rts ii) ->
  (rcv_transI (@rt_inv r)) \In (rcv_trans ProtocolWithIndInv).
Proof. by move=>H; rewrite /rtsI/=; apply/Mem_map. Qed.

Lemma getInvSendTrans st z to msg s1 h :
  st \In (snd_trans ProtocolWithIndInv) ->
  forall (S : send_safe st z to (getStatelet s1 (plab p)) msg),
  Some h = send_step S ->
  exists st', [/\ st' \In get_st (mkWorld p) (plab p),
     t_snd st' = t_snd st,
     all_hooks_fire (mkWorld p) (plab p) (t_snd st') s1 z msg to &          
     exists S': (send_safe st' z to (getStatelet s1 (plab p)) msg),
       Some h = send_step S'].
Proof.
simpl; case: ii=>sts rts HS HR/=; rewrite /stsI.
case/Mem_map_inv; case=>st' stI/= [->]H1; case=>S Is E.
rewrite /get_st/InMem!prEq; exists st'. split=>//.
- by rewrite -HS/=; apply: (Mem_map ProtocolWithInvariant.st H1).
rewrite/send_step/=/Transitions.send_step/=/send_stepI in E.
- move=>??? F.
  apply sym_eq in F.
  move: F.
  by move/find_some; rewrite dom0.
by exists (proj1 (conj S Is)).
Qed.

End ProtocolWithInvariant.

Section InductiveInvConj.

Variable p : protocol.

Definition s_inv_conj (I1 I2 : dstatelet -> pred nid -> Prop)
           (st : send_trans (coh p)) :=
  S_inv (fun d n => I1 d n /\ I2 d n) st.

Lemma s_inv_conjC I1 I2 st :
  s_inv_conj I1 I2 st <-> s_inv_conj I2 I1 st.
Proof.
by split; move=>H this to d msg S b /and_comm G E N; apply/and_comm; apply: H.
Qed.

Lemma s_inv_conjA I1 I2 I3 st :
  s_inv_conj I1 (fun d n => I2 d n /\ I3 d n) st <->
  s_inv_conj (fun d n => I1 d n /\ I2 d n) I3 st.
Proof.
by split=>H this to d msg S b /and_assoc G E N; apply/and_assoc; apply: H.
Qed.

Definition r_inv_conj (I1 I2 : dstatelet -> pred nid -> Prop)
           (rt : receive_trans (coh p)) :=
  R_inv (fun d n => I1 d n /\ I2 d n) rt.

Lemma r_inv_conjC I1 I2 rt :
  r_inv_conj I1 I2 rt <-> r_inv_conj I2 I1 rt.
Proof.
by split=>H d from this i C m pf/and_comm G E D W T N; apply/and_comm; apply: H.
Qed.

Lemma r_inv_conjA I1 I2 I3 rt :
  r_inv_conj I1 (fun d n => I2 d n /\ I3 d n) rt <->
  r_inv_conj (fun d n => I1 d n /\ I2 d n) I3 rt.
Proof.
by split=>H d from this i C m pf/and_assoc G E D W T N; apply/and_assoc; apply: H.
Qed.

(* Definition ii_conj (I1 I2 : dstatelet -> pred nid -> Prop) *)
(*            (ii1 : InductiveInv p I1) *)
(*            (ii2 : InductiveInv p I2) : *)
(*   InductiveInv p (fun d n => I1 d n /\ I2 d n). *)
(* Proof. *)
(* case: ii1 ii2=>sts1 rts1 Es1 Er1 [sts2] rts2 Es2 Er2. *)
(* Qed. *)

End InductiveInvConj.

End ProtocolWithInvariant.

Module PWIExports.
Section PWIExports.

Import ProtocolWithInvariant.

Definition st_helper := st_helper.
Definition cohSt := cohSt.

Definition S_inv := ProtocolWithInvariant.S_inv.
Definition R_inv := ProtocolWithInvariant.R_inv.

Definition SendInv := SendInv.
Definition SI := SI.
Definition ReceiveInv := ReceiveInv.
Definition RI := RI.

Definition InductiveInv := InductiveInv.

Lemma with_inv_coh pr I (ii : InductiveInv pr I) s:
  s \In Coh (mkWorld (ProtocolWithIndInv ii)) ->    
  s \In Coh (mkWorld pr).
Proof.
case=>G1 G2 Gh G3 G4; split=>//.
- by apply/andP; rewrite valid_unit; split=>//; rewrite !validPt in G1 *.
- by move=>???? ;rewrite dom0.
- by move=>z; move: (G3 z); rewrite !domPt !inE.
move=>l; move: (G4 l).
case X: (l == plab pr); first by move/eqP:X=>X; subst l; rewrite !prEq; case.
rewrite /getProtocol/mkWorld/=.
suff [X1 X2]: l \notin dom (plab pr \\-> ProtocolWithIndInv ii) /\
              l \notin dom (plab pr \\-> pr).
- by case: dom_find X1 X2=>//=->_; case: dom_find=>//=->. 
rewrite !domPt !inE/=; suff: plab pr != l by [].
by apply/negbT; apply/negP=>/eqP Z; subst l; rewrite eqxx in X.
Qed.

Lemma with_inv_nodes pr I (ii : InductiveInv pr I) l :
  nodes (getProtocol (mkWorld (ProtocolWithIndInv ii)) l) =
  nodes (getProtocol (mkWorld pr) l).
Proof.
rewrite /getProtocol/mkWorld/=.
case X: (l == plab pr);
  first by move/eqP:X=>X; subst l; rewrite !findPt.
rewrite /getProtocol/mkWorld/=.
suff [X1 X2]: l \notin dom (plab pr \\-> ProtocolWithIndInv ii) /\
              l \notin dom (plab pr \\-> pr).
by case: dom_find X1 X2=>//=->_; case: dom_find=>//=->. 
rewrite !domPt !inE/=; suff: plab pr != l by [].
by apply/negbT; apply/negP=>/eqP Z; subst l; rewrite eqxx in X.
Qed.

Lemma with_inv_labE pr I (ii : InductiveInv pr I):
  plab (ProtocolWithIndInv ii) = plab pr.
Proof. by []. Qed.

Lemma with_inv_step pr I (ii : InductiveInv pr I) z s1 s2:
  s1 \In Coh (mkWorld (ProtocolWithIndInv ii)) ->
  network_step (mkWorld pr) z s1 s2 ->
  network_step (mkWorld (ProtocolWithIndInv ii)) z s1 s2.
Proof.
move=>C'; move: (with_inv_coh C')=>C.
case; first by case=>_<-; apply: Idle. 

(*** Send-transition of the host protocol ***)
move=>l st Hs to msg h H1 H2 _ S A E ->/=.
have Y : l = plab pr
  by rewrite -(cohD C) domPt inE/= in H2; move/eqP:H2. 
subst l; move: st Hs H1 S E A; rewrite /get_st/InMem!prEq/==>st Hs H1 S E A.
suff X: exists st',
    [/\ st' \In get_st (mkWorld (ProtocolWithIndInv ii)) (plab pr),
     t_snd st' = t_snd st,
     all_hooks_fire (mkWorld (ProtocolWithIndInv ii)) (plab pr) (t_snd st') s1 z msg to &
     exists S': (send_safe st' z to (getStatelet s1 (plab pr)) msg),
                Some h = send_step S'].
case:X=>st'[Hs']Et A'[S']E'; rewrite -Et.
move: (with_inv_nodes ii (plab pr)); rewrite !prEq=>P.
by rewrite -P in H1; apply: (SendMsg (to:=to)(this:=z)(b:=h)(msg:=msg) Hs').

(* Finding the corresponding send-transition of rich protocol *)
rewrite -(with_inv_labE ii)/get_st/InMem!prEq.
case: ii (@stIn _ _ ii) C' =>sts rts HS HR/= Hi C'.
rewrite -HS in Hs; move/Mem_map_inv: Hs=>[[st' stI]]/=[Es]Si; subst st'.
have G: I (getStatelet s1 (plab pr)) (nodes pr (getStatelet s1 (plab pr))).
+ by case: C'=>_ _ _ _/(_ (plab pr)); rewrite prEq; case.
move:(Hi _ Si)=>/={Hi Si}Hi; exists (@snd_transI pr I st stI); split=>//=.
rewrite /send_safeI /send_stepI/=.
by exists (conj S G); rewrite (pf_irr (proj1 (conj S G)) S).

(*** Receive-transition of the host protocol ***)
move=>l rt  Hr i from H1 H2 C1 msg E[F]Hw/=.
have Y : l = plab pr by rewrite -(cohD C) domPt inE/= in H2; move/eqP:H2. 
subst l; move: rt Hr H1 E (coh_s _ C1) Hw.
rewrite /get_rt/InMem/=!prEq=>rt Hr H1 E C1' Hw .
have Hi: (coh (getProtocol (mkWorld (ProtocolWithIndInv ii)) (plab pr)))
           (getStatelet s1 (plab pr)) by case:C'=>_ _ _/(_ (plab pr)).
have Hz : z \in nodes
          (getProtocol (mkWorld (ProtocolWithIndInv ii)) (plab pr))
          (getStatelet s1 (plab pr)) by rewrite (with_inv_nodes ii (plab pr)) prEq.
suff X: exists rt',
     [/\ rt' \In get_rt (mkWorld (ProtocolWithIndInv ii)) (plab pr),
      tag msg = t_rcv rt', msg_wf rt' Hi z from msg &
      receive_step rt from msg C1' H1 = receive_step rt' from msg Hi Hz].
case:X=>rt'[Hr']E' Hw' Gr G.
have pf: (z \in nodes (getProtocol (mkWorld (ProtocolWithIndInv ii)) (plab pr))
                  (getStatelet s1 (plab pr))) by rewrite prEq. 
move: (@ReceiveMsg _ z s1 s2 (plab pr) rt' Hr' i from pf)=>/=.
rewrite -(cohD C) /= domPt inE eqxx/=; move/(_ is_true_true C' msg E')=>X.
subst s2; apply X; split=>//; clear X.
- by rewrite (pf_irr (coh_s (plab pr) C') Hi).
congr (upd _ _); congr {| dstate := _ ; dsoup := _ |}; congr (upd _ _).
rewrite Gr; clear E E' Hw Hw' Hr Hr' Gr rt F H2 H1 C1 C.
rewrite (pf_irr pf Hz).
by rewrite (pf_irr Hi (coh_s (plab pr) C')).

(* Finding the corresponding receive-transition of rich protocol *)
rewrite /get_rt/InMem/=; move: C1' H1 Hi Hz Hw; rewrite !prEq=>C1' H1 Hi Hz Hw.
case: ii (@rtIn _ _ ii) C' Hi Hz=>/=sts rts HS HR/= Hi C'.
rewrite -HR in Hr; move/Mem_map_inv: Hr=>[[rt' rtI]]/=[Er]Ri; subst rt'.
case=>C1'' Inv Hz. exists (@rcv_transI pr I rt rtI); split=>//.
- by move: (@Hi _ Ri).
rewrite /receive_step/=/receive_stepI/=/receive_step/=.
- by rewrite -(pf_irr C1' (proj1 (conj C1'' Inv))).
by rewrite ?(pf_irr C1' (proj1 (conj C1'' Inv)))
           ?(pf_irr H1 Hz).
Qed.

Lemma with_inv_step' pr I (ii : InductiveInv pr I) z s1 s2:
  network_step (mkWorld (ProtocolWithIndInv ii)) z s1 s2 ->
  network_step (mkWorld pr) z s1 s2.
Proof.
case.
- by case=>C'<-; apply: Idle; split=>//; apply: with_inv_coh C'.
(* Emulating send-transition *)
move=>l st Hs to msg h H1 H2 C' S A E->{s2}.
have Y : l = plab pr
  by rewrite -(cohD C') domPt inE/= in H2; move/eqP:H2. 
subst l; move: st Hs H1 S E A; rewrite /get_st/InMem!prEq/==>st Hs H1 S E A.
suff X: exists st',
    [/\ st' \In get_st (mkWorld pr) (plab pr),
     t_snd st' = t_snd st,
     all_hooks_fire (mkWorld (ProtocolWithIndInv ii)) (plab pr) (t_snd st') s1 z msg to &
     exists S': (send_safe st' z to (getStatelet s1 (plab pr)) msg),
                Some h = send_step S'].
case:X=>st'[Hs']Et A'[S']E'; rewrite -Et.
apply: (SendMsg (to:=to)(this:=z)(b:=h)(msg:=msg) Hs')=>//;
  [by rewrite prEq| by apply: (with_inv_coh C')].
by apply: (getInvSendTrans (ii := ii)).

(* Emulating a receive-transition *)  
move=>l rt  Hr i from H1 H2 C1 msg E[F]Hw/=.
have Y : l = plab pr by rewrite -(cohD C1) domPt inE/= in H2; move/eqP:H2. 
subst l; move: rt Hr H1 E (coh_s _ C1) Hw.
rewrite /get_rt/InMem/=!prEq=>rt Hr H1 E C1' Hw.
have Hi: (coh (getProtocol (mkWorld pr) (plab pr)))
           (getStatelet s1 (plab pr)) by case:(C1'); rewrite prEq.
have Hz : z \in nodes (getProtocol (mkWorld pr) (plab pr))
                      (getStatelet s1 (plab pr))
  by rewrite -(with_inv_nodes ii (plab pr)) prEq.
suff X: exists rt',
     [/\ rt' \In get_rt (mkWorld pr) (plab pr),
      tag msg = t_rcv rt', msg_wf rt' Hi z from msg &
      receive_step rt from msg C1' H1 = receive_step rt' from msg Hi Hz].
case:X=>rt'[Hr']E' Hw' Gr G.
have pf: (z \in nodes (getProtocol (mkWorld pr) (plab pr))
                  (getStatelet s1 (plab pr))) by rewrite prEq. 
move: (@ReceiveMsg _ z s1 s2 (plab pr) rt' Hr' i from pf)=>/=.
rewrite -(cohD C1) domPt inE eqxx/=.
move/(_ is_true_true (with_inv_coh C1) msg E')=>X.
subst s2; apply X; split=>//; clear X.
- by rewrite (pf_irr (coh_s (plab pr) (with_inv_coh C1)) Hi).
congr (upd _ _); congr {| dstate := _ ; dsoup := _ |}; congr (upd _ _).
rewrite Gr; clear E E' Hw Hw' Hr Hr' Gr rt F H2 H1.
rewrite (pf_irr pf Hz).
by rewrite (pf_irr Hi (coh_s (plab pr) (with_inv_coh C1))).
(* Identifying the appropriate receive transition *)
case: ii C1 H2 rt Hr E H1 C1' Hw=>sts rts HS HR/=C1 H2 rt Hr E H1 C1' Hw.
move: Hr; rewrite /rtsI. 
case/Mem_map_inv; case=>rt' rtI/= [Z] H1'; subst rt.
rewrite /get_rt/InMem; move: C1' H1 Hi Hz Hw; rewrite !prEq=>C1' H1 Hi Hz Hw.
exists rt'; split=>//; last first.
- rewrite {1}/receive_step /rcv_transI /receive_stepI/=.
  rewrite (pf_irr H1 Hz).
  by rewrite (pf_irr (proj1 C1') Hi).
- by rewrite -(pf_irr (proj1 C1') Hi).
by rewrite -HR; apply: (Mem_map (@ProtocolWithInvariant.rt pr I) H1').
Qed.

Lemma with_inv_rely' pr I (ii : InductiveInv pr I) z s1 s2:
  network_rely (mkWorld (ProtocolWithIndInv ii)) z s1 s2 ->
  network_rely (mkWorld pr) z s1 s2.
Proof.
case=>n; elim: n s1=>[|n Hi] s1; first by move=>[<-]/with_inv_coh=>C; exists 0. 
case=>z'[s3][N]H/Hi; move/with_inv_step':H=>S; case=>n' R.
by exists n'.+1, z', s3. 
Qed.

(* The following definition requires the proofs, for each transitions
   of p that it satisfies the corresponding two-state invariants with
   respect to the supposedly inductive I. *)

Definition ProtocolWithIndInv := ProtocolWithIndInv.

End PWIExports.
End PWIExports.

Export PWIExports.

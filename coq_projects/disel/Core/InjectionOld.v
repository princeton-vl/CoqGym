From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding.
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem.
Require Import Actions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Framing with respect to the world *)

Module Injection.
Section Injection.

Variable W : world.

Structure injects (U V : world) := Inject {
  E : world;

  _ : V = U \+ E;
  
  (* These all should be easy to prove given a standard world disentanglement *)
  _ : forall s, Coh V s <-> exists s1 s2,
        [/\ s = s1 \+ s2, Coh U s1 & Coh E s2];

  _ : forall s1 s2 s this,
      s1 \+ s \In Coh V -> s2 \+ s \In Coh V ->
      network_step U this s1 s2 -> network_step V this (s1 \+ s) (s2 \+ s);

  _ : forall s1 s2 s1' s2' this,
      s1 \In Coh U -> s2 \In Coh U ->
      network_step V this (s1 \+ s1') (s2 \+ s2') ->
      (network_step U this s1 s2   /\ s1' = s2') \/
      (network_step E this s1' s2' /\ s1 = s2); }.

End Injection.

Module Exports.
Section Exports.

Definition inj_ext := E. 
Definition injects := injects. 
Definition Inject := Inject.

Variables (U V : world).

Lemma cohK (w : injects U V) : V = U \+ inj_ext w.
Proof. by case: w=>E/=. Qed.

Lemma cohE (w : injects U V) s :
  Coh V s <-> exists s1 s2,
      [/\ s = s1 \+ s2, Coh U s1 & Coh (inj_ext w) s2].
Proof. by case: w=>W ? cohE sL sR; apply: cohE. Qed.

Lemma sem_extend (w : injects U V) s1 s2 s this: 
      s1 \+ s \In Coh V -> s2 \+ s \In Coh V ->
      network_step U this s1 s2 -> network_step V this (s1 \+ s) (s2 \+ s).
Proof.
by case: w=>W _ cohE sL sR C G; apply: sL=>//.
Qed.

Lemma sem_split (w : injects U V) s1 s1' s2 s2' this: 
      s1 \In Coh U -> s2 \In Coh U ->
      network_step V this (s1 \+ s1') (s2 \+ s2') ->
      (network_step U this s1 s2   /\ s1' = s2') \/
      (network_step (inj_ext w) this s1' s2' /\ s1 = s2).
Proof. by case: w=>W ? cohE sl sR; apply: sR. Qed.

Definition extends (U V : world) (w : injects U V) s s1 := 
  exists s2, [/\ s = s1 \+ s2, s1 \In Coh U & s \In Coh V].

Notation dom_filt W := (fun k => k \in dom W).

Definition projectS (W : world) (s : state) :=
  um_filter (dom_filt W) s.

Lemma projectS_cohL W1 W2 s :
  s \In Coh (W1 \+ W2) -> projectS W1 s \In Coh W1.
Proof.
case=>V1 V2 D H; split; first by move/validL: V1.
- by rewrite valid_um_filter.
- move=>z; case B: (z \in dom W1).
  + by rewrite dom_um_filt !inE B/= -D domUn !inE B/=; rewrite V1.
  by rewrite dom_um_filt !inE B.
move=>l; move: (H l)=>{H}H.
case B: (l \in dom W1); last first.
- rewrite /getProtocol /getStatelet; move: (B).
  case: dom_find=>//-> _.
  suff X: ~~(l \in dom (projectS W1 s)) by case: dom_find X=>//-> _. 
  by rewrite /projectS dom_um_filt inE/= B.
have E1: find l s = find l (projectS W1 s).
- by rewrite /projectS/= find_um_filt B.
have E2: getProtocol (W1 \+ W2) l = getProtocol W1 l.
- by rewrite /getProtocol findUnL// B. 
by rewrite -E2 /getStatelet -E1 in H *.  
Qed.

Lemma projectS_cohR W1 W2 s :
  s \In Coh (W1 \+ W2) -> projectS W2 s \In Coh W2.
Proof. by rewrite joinC; apply: projectS_cohL. Qed.

Lemma projectSE W1 W2 s :
  s \In Coh (W1 \+ W2) -> s = projectS W1 s \+ projectS W2 s.
Proof.
case=>Vw Vs D H. rewrite /projectS.
have X: {in dom s, dom_filt W2 =1 predD (dom_filt W2) (dom_filt W1)}.
- move=>z _/=; case I : (z \in dom (W1 \+ W2)).
  + move: I; rewrite domUn !inE/==>/andP[V']/orP[]Z; rewrite Z/=.
    - by case: validUn V'=>//_ _/(_ z Z)/=G _;apply/negbTE. 
    rewrite joinC in V'; case: validUn V'=>//_ _/(_ z Z)G _.
    by rewrite andbC.
  move: I; rewrite domUn inE/==>/negbT; rewrite negb_and negb_or/=.
  have X: valid (W1 \+ W2) by [].
  by rewrite X/==>/andP[]->.
rewrite (eq_in_um_filt X) -um_filt_predU/=; clear X.
suff X: {in dom s, predU (dom_filt W1) (dom_filt W2) =1 predT}.
- by rewrite (eq_in_um_filt X) um_filt_predT. 
by move=>z; rewrite/= -D domUn inE=>/andP[].
Qed.

Lemma coh_split W1 W2 s :
  s \In Coh (W1 \+ W2) ->
  exists s1 s2 : state,
    [/\ s1 \In Coh W1, s2 \In Coh W2 & s = s1 \+ s2].
Proof.
move=>C; move/projectSE: (C)->.
exists (projectS W1 s), (projectS W2 s).
split=>//; [by apply: projectS_cohL C| by apply: projectS_cohR C].
Qed.

Lemma injExtL (W1 W2 : world) (pf : injects W1 (W1 \+ W2)) :
  valid (W1 \+ W2) -> inj_ext pf = W2.
Proof.
move=>H; case: pf=>W2' E/= _ _ _.
rewrite /PCM.join/=/= in H *.
rewrite /valid /= in H.
by rewrite (joinfK H E).
Qed.

Lemma injExtR (W1 W2 : world) (pf : injects W2 (W1 \+ W2)) :
  valid (W1 \+ W2) -> inj_ext pf = W1.
Proof.
move=>H; case: pf=>W2' E/= _ _ _.
by rewrite joinC in H E; rewrite (joinfK H E).
Qed.

End Exports.
End Exports.

End Injection.

Export Injection.Exports.


Module InjectExtra.

Lemma cohUnKR U W s s':
  s \+ s' \In Coh (U \+ W) -> s \In Coh U -> s' \In Coh W.
Proof.
move=>H C.
suff X: s' = projectS W (s \+ s').
- by rewrite X; apply: (projectS_cohR H).
suff X: s = projectS U (s \+ s').
- move: (cohS H)=>V; move/projectSE: (H)=>E.
  rewrite E in V. rewrite {1}X in E; move/sym: E=>E.
  by rewrite (joinfK V E).
rewrite /projectS.
suff X: {in dom (s \+ s'), dom U =1 dom s}.
- by rewrite (eq_in_um_filt X) um_filt_dom ?(cohS H)//.
by move=>z _; move: (cohD C z); rewrite /in_mem.
Qed.

Lemma cohUnKL U W s s':
  s \+ s' \In Coh (U \+ W) -> s' \In Coh W -> s \In Coh U .
Proof.
move=>H C.
by rewrite [U \+ W]joinC [s\+_]joinC in H; apply: (cohUnKR H).
Qed.

Lemma getPUn U W l :
  valid (U \+ W) -> l \in dom U ->
  getProtocol U l = getProtocol (U \+ W) l.
Proof.
move=>V; rewrite /getProtocol=>D.
by rewrite findUnL ?V// D.
Qed.

Lemma getSUn s1 s2 l :
  valid (s1 \+ s2) -> l \in dom s1 ->
  getStatelet s1 l = getStatelet (s1 \+ s2) l.
Proof.
move=>V; rewrite /getStatelet=>D.
by rewrite findUnL ?V// D.
Qed.

Lemma inject_frame U W this s1 s2 s:
  valid (U \+ W) ->
  s1 \+ s \In Coh (U \+ W) ->
  network_step U this s1 s2 ->
  network_step (U \+ W) this (s1 \+ s) (s2 \+ s).
Proof.
move=>V C1 S; move/step_coh: (S)=>[C1' C2'].
case: S; first by move=>[_ <-]; apply: Idle. 
- move=>l st H1 to msg h H2 H3 _ S H4 G.
  have E: getProtocol U l = getProtocol (U \+ W) l
    by rewrite (getPUn V)// (cohD C1').
  have E': getStatelet s1 l = getStatelet (s1 \+ s) l
    by rewrite (getSUn (cohS C1)).
  have X: l \in dom (s1 \+ s) by rewrite domUn inE H3 (cohS C1).
  move: (getProtocol U) (E) H2=>_ -> H2.
  rewrite /get_st /InMem/= in H1.
  rewrite E' in H2 G S H4; clear E'.
  move: (getProtocol U l) E st H1 S H4 G H2=>_->st H1 S H4 G H2.
  apply: (SendMsg H1 H2 X C1 H4 (s2 := s2 \+ s)).
  by rewrite updUnL H3; congr (_ \+ _).
move=> l rt H1 msg from H2 H3 C tms G [G1 G2/= G3].
have E: getProtocol U l = getProtocol (U \+ W) l
  by rewrite (getPUn V)// (cohD C1').
have E': getStatelet s1 l = getStatelet (s1 \+ s) l.
  by rewrite (getSUn (cohS C1)) -?(cohD C1')//.
have X: l \in dom (s1 \+ s) by rewrite domUn inE (cohS C1) -(cohD C1') H3.
rewrite /get_rt /InMem /= in H1.
move: (getProtocol U l) (getStatelet s1 l) E E' C H2
                        (coh_s l C) rt G3 G G2 H1 G1=>z1 z2 Z1 Z2.
subst z1 z2=>C pf C' G3 G G2 H1 H2 G1.
rewrite -(cohD C1) in X.
apply: (ReceiveMsg H2 X G2 (i := msg) (from := from) (s2 := s2 \+ s)).
split=>//=; first by rewrite (proof_irrelevance (coh_s l C1) C').
rewrite updUnL -(cohD C1') H3; congr (_ \+ _).
move: (NetworkSem.coh_s l C1)=>pf'. 
by rewrite (proof_irrelevance pf' C').
Qed.

Lemma inject_step U W this s1 s2 s1' s2' :
  valid (U \+ W) ->
  s1 \In Coh U -> s2 \In Coh U ->
  network_step (U \+ W) this (s1 \+ s1') (s2 \+ s2') ->
  network_step U this s1 s2 /\ s1' = s2' \/
  network_step W this s1' s2' /\ s1 = s2.
Proof.
move=>V C1 C2 S; move/step_coh: (S)=>[C1' C2'].
move: (cohUnKR C1' C1) (cohUnKR C2' C2)=>D1 D2.
case: S.
(* Idle Step *)
- case=>_ E; move: (coh_prec (cohS C1') E C1 C2)=>Z; subst s2.
  rewrite (joinC U) (joinC s1) in C1'; rewrite !(joinC s1) in E.
  move: (coh_prec (cohS C1') E D1 D2)=>Z; subst s2'.
  by left; split=>//; apply: Idle.

(* Send Step *)
- move=>l st H1 to msg h H2.
  rewrite domUn inE=>/andP[Vs]/orP; case=> D _ S H3;
  [rewrite updUnL D|rewrite updUnR D]=>G;[left|right];
  [| move: U W V s1 s2 s1' s2' C1 C2 C1' C2' D1 D2 st H1 H2 Vs D S H3 G;
     move=> W U V s1' s2' s1 s2 D1 D2 C1' C2' C1 C2 st H1 H2 Vs D S H3 G;
     rewrite (joinC W) in V C1' C2' st H1 S H3 G H2;
     rewrite -?(joinC s1) -?(joinC s2) in C1' C2' S G H3 Vs].
  + have X: s1' = s2'.
    - move: (C2'); rewrite (joinC U) G -[upd _ _ _ \+ s1'](joinC s1'). 
      move/cohUnKR/(_ D1)=>C1''.
      move: (coh_prec (cohS C2') G C2 C1'')=>Z; rewrite -Z in G; clear Z.
      by rewrite (joinfK (cohS C2') G).
    split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
    rewrite (joinC U) in C2'; move: (joinfK (cohS C2') G)=>{G}G.
    rewrite (joinC s1') in G.
    have E: getProtocol U l = getProtocol (U \+ W) l.
      by rewrite (getPUn V)// (cohD C1).
    have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
      by rewrite (getSUn Vs). 
    rewrite /get_st /InMem in H1. 
    move: (getProtocol (U \+ W) l) E st H1 S H2 H3 G =>_<- st H1 S H2 H3 G.
    move: (getStatelet (s1 \+ s1') l) E' H2 S H3 G=>_<- H2 S H3 G.
    by apply: (SendMsg H1 H2 D C1 H3 G).
  have X: s1' = s2'.
  - move: (C2'); rewrite (joinC U) G. 
    move/cohUnKR/(_ D1)=>C1''. rewrite (joinC s1') in G.
    move: (coh_prec (cohS C2') G C2 C1'')=>Z; rewrite -Z in G; clear Z.
    by rewrite (joinfK (cohS C2') G).
  split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
  rewrite (joinC U) in C2'; move: (joinfK (cohS C2') G)=>{G}G.
  rewrite (joinC s1') in G.
  have E: getProtocol U l = getProtocol (U \+ W) l.
    by rewrite (getPUn V)// (cohD C1).
  have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
    by rewrite (getSUn Vs). 
  rewrite /get_st /InMem in H1; rewrite (joinC s1') in H2.
  move: (getProtocol (U \+ W) l) E st H1 S H2 H3 G =>_<- st H1 S H2 H3 G.
  move: (getStatelet (s1 \+ s1') l) E' H2 S H3 G=>_<- H2 S H3 G.
  by apply: (SendMsg H1 H2 D C1 H3 G).

  (* Receive Step *)
move=>l rt R i from H1.
rewrite domUn inE=>/andP[Vs]/=/orP; case=>D C msg H2 [H3 H4]/=;
[rewrite (cohD C1) in D|rewrite (cohD D1) in D];
[rewrite updUnL D|rewrite updUnR D]=>G;[left|right].
- have X: s1' = s2'.
  + move: (C2'); rewrite (joinC U) G -[upd _ _ _ \+ s1'](joinC s1'). 
    move/cohUnKR/(_ D1)=>C1''.
    move: (coh_prec (cohS C2') G C2 C1'')=>Z; rewrite -Z in G; clear Z.
    by rewrite (joinfK (cohS C2') G).
  split=>//; subst s2'; rewrite -![_ \+ s1'](joinC s1') in G C2'.
  rewrite -[upd _ _ _ \+ s1'](joinC s1') in G; rewrite (joinC U) in C2'.
  move: (joinfK (cohS C2') G)=>{G}G. 
  have E: getProtocol U l = getProtocol (U \+ W) l.
    by rewrite (getPUn V)// (cohD C1).
  have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
    by rewrite (getSUn (cohS C1')). 
  rewrite /get_rt /InMem/= in R. 
  move: (getStatelet (s1 \+ s1') l) E' C (coh_s l C) H1 G H3 H4=>_<-_.
  move: (getProtocol (U \+ W) l) E rt R H2=>_<-rt R H2 coh_s H1 G H3 H4.
  rewrite -(cohD C1) in D.
  apply: (ReceiveMsg R D H2 (i := i) (from := from) (s2 := s2) (C := C1)). 
  split=>//=; move: (NetworkSem.coh_s l C1)=>coh_s';
  by rewrite -(proof_irrelevance coh_s coh_s').

move: U W V s1 s2 s1' s2' C1 C2 C1' C2' D1 D2 rt H1 H2 Vs D C R H3 H4 G.
move=>W U V s1' s2' s1 s2 D1 D2.
rewrite !(joinC W) -!(joinC s1) -!(joinC s2)=> C1' C2' C1 C2.
move=>rt H1 H2 Vs D C R H3 H4 G.
have X: s1' = s2'.
- move: (C2'); rewrite (joinC U) G. 
  move/cohUnKR/(_ D1)=>C1''. rewrite (joinC s1') in G.
  move: (coh_prec (cohS C2') G C2 C1'')=>Z; rewrite -Z in G; clear Z.
  by rewrite (joinfK (cohS C2') G).
split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
rewrite (joinC U) in C2'; move: (joinfK (cohS C2') G)=>{G}G.
rewrite joinC in V.
have E: getProtocol U l = getProtocol (U \+ W) l.
  by rewrite (getPUn V)// (cohD C1).
have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
  by rewrite (getSUn (cohS C1')). 
rewrite /get_rt /InMem/= in R. 
move: (getStatelet (s1 \+ s1') l) E' C (coh_s l C) H1 G H3 H4=>_<-_.
move: (getProtocol (U \+ W) l) E rt R H2=>_<-rt R H2 coh_s H1 G H3 H4.
rewrite -(cohD C1) in D.
apply: (ReceiveMsg R D H2 (i := i) (from := from) (s2 := s2) (C := C1)). 
split=>//=; move: (NetworkSem.coh_s l C1)=>coh_s';
by rewrite -(proof_irrelevance coh_s coh_s').
Qed.
  
Lemma injectL (U W : world) : valid (U \+ W) -> injects U (U \+ W).
Proof.
move=>H; exists W=>//[s|s1 s2 s this|s1 s2 s1' s2' this]; [split | |].
- move=>C; exists (projectS U s), (projectS W s).
  split; [by apply projectSE|by apply: (projectS_cohL C)|
          by apply: (projectS_cohR C)].
- case=>s1[s2][Z]C1 C2; subst s.
  have W1 : valid (s1 \+ s2).
  + case: validUn; rewrite ?(cohS C1) ?(cohS C2)//.
    move=>l; rewrite -(cohD C1)-(cohD C2).
    by case: validUn H=>//_ _/(_ l) G _/G; move/negbTE=>->.
  split=>//[|l].
  + move=>l; rewrite !domUn !inE/=.
    by rewrite H W1/= -(cohD C1)-(cohD C2).
  + rewrite /getProtocol/getStatelet !findUnL// (cohD C1).
    by case B: (l \in dom s1)=>//; apply: coh_coh.
- by move=>C1 C2; apply: inject_frame.
by move=>C1 C2; apply: inject_step.
Qed.

Lemma injectR (U W : world) : valid (W \+ U) -> injects U (W \+ U).
Proof. by rewrite (joinC W); apply: injectL. Qed.

Lemma locProjL W1 W2 l s1 s2:
  (s1 \+ s2) \In Coh (W1 \+ W2) -> l \in dom W1 ->
  s1 \In Coh W1 -> getStatelet (s1 \+ s2) l = getStatelet s1 l.
Proof.
move=>C D C1; rewrite (cohD C1) in D.
by rewrite (getSUn (cohS C) D).
Qed.

Lemma locProjR W1 W2 l s1 s2:
  (s1 \+ s2) \In Coh (W1 \+ W2) -> l \in dom W2 ->
  s2 \In Coh W2 -> getStatelet (s1 \+ s2) l = getStatelet s2 l.
Proof. by rewrite !(joinC W1) !(joinC s1); apply: locProjL. Qed.

End InjectExtra.

Export InjectExtra.

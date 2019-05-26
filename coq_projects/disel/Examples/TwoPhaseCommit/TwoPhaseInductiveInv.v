From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL
Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL
Require Import InductiveInv While StatePredicates.
From DiSeL
Require Import TwoPhaseProtocol.

Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Module TwoPhaseInductiveInv. *)
Section TwoPhaseInductiveInv.

Variable l : Label.
Variables (cn : nid) (pts : seq nid) (others : seq nid).
Hypothesis Hnin : cn \notin pts.
Hypothesis PtsNonEmpty : pts != [::].

Lemma pt_not_cn pt : pt \in pts -> pt != cn.
Proof.
  move => H.
  case X: (pt == cn)=>//.
  move /eqP in X.
  subst.
  move: (Hnin) => /negbTE.
    by rewrite H.
Qed.

Definition tpc := TwoPhaseCommitProtocol others Hnin l.

(* Take the transitions *)
Notation sts := (snd_trans tpc).
Notation rts := (rcv_trans tpc).

Notation loc z d := (getLocal z d).

Definition cn_state (d : dstatelet) (c : CStateT) (l : Log) : Prop :=
  loc cn d = st :-> c \+ log :-> l.

Definition pt_state (d : dstatelet) (p : PStateT) (l : Log) (pt : nid) : Prop :=
  loc pt d = st :-> p \+ log :-> l.

(*****************************************************)

(* Phase Zero *)

Definition EverythingInit (d : dstatelet) (round : nat) (l : Log) : Prop :=
  [/\ cn_state d (round, CInit) l &
      forall pt, pt \in pts ->
            [/\ pt_state d (round, PInit) l pt,
               no_msg_from_to pt cn (dsoup d) &
               no_msg_from_to cn pt (dsoup d)]].


(* Phase One *)

Definition pt_PhaseOne (d : dstatelet) (round : nat)
           (next_data : data) (l : Log) (pt : nid) : Prop :=
  [\/ [/\ pt_state d (round, PInit) l pt,
       no_msg_from_to pt cn (dsoup d) &
       msg_spec cn pt prep_req (round :: next_data) (dsoup d)]
   ,  [/\ pt_state d (round, PGotRequest next_data) l pt,
       no_msg_from_to pt cn (dsoup d) &
       no_msg_from_to cn pt (dsoup d)]
   ,  [/\ pt_state d (round, PRespondedYes next_data) l pt,
       no_msg_from_to cn pt (dsoup d) &
       msg_spec pt cn prep_yes [::round] (dsoup d)]
   |  [/\ pt_state d (round, PRespondedNo next_data) l pt,
       no_msg_from_to cn pt (dsoup d) &
       msg_spec pt cn prep_no [::round] (dsoup d)]].

Definition pt_PhaseOneResponded (d : dstatelet) (round : nat) (next_data : data)
           (l : Log) (committed : bool) (pt : nid) : Prop :=
  [/\ no_msg_from_to cn pt (dsoup d), no_msg_from_to pt cn (dsoup d) &
      if committed
      then pt_state d (round, PRespondedYes next_data) l pt
      else pt_state d (round, PRespondedNo next_data) l pt].


Definition pt_Init d round l pt :=
  [/\ pt_state d (round, PInit) l pt,
     no_msg_from_to pt cn (dsoup d) &
     no_msg_from_to cn pt (dsoup d)].

Definition cn_PhaseOneSend d round next_data l sent :=
    [/\ cn_state d (round, CSentPrep next_data sent) l,
     uniq sent, {subset sent <= pts} &
                forall pt, pt \in pts ->
                           if pt \in sent
                           then pt_PhaseOne d round next_data l pt
                           else pt_Init d round l pt].

Definition cn_PhaseOneReceive d round next_data l recvd :=
     let rps := map fst recvd in
     [/\ cn_state d (round, CWaitPrepResponse next_data recvd) l,
      uniq rps, {subset rps <= pts} ,
      forall pt b, pt \in pts -> (pt, b) \in recvd ->
                   pt_PhaseOneResponded d round next_data l b pt &
      forall pt,   pt \in pts -> pt \notin rps ->
                   pt_PhaseOne d round next_data l pt].

Definition PhaseOne (d : dstatelet) (round : nat) (next_data : data) (l : Log) :=
  (exists sent, cn_PhaseOneSend d round next_data l sent) \/
  (exists recvd, cn_PhaseOneReceive d round next_data l recvd).

(* Phase Two *)

Definition pt_PhaseTwoCommit d round next_data l pt :=
  [\/ [/\ pt_state d (round, PRespondedYes next_data) l pt,
       msg_spec cn pt commit_req [::round] (dsoup d) &
       no_msg_from_to pt cn (dsoup d)]
   , [/\ pt_state d (round, PCommitted next_data) (rcons l (true, next_data)) pt,
      no_msg_from_to cn pt (dsoup d) & no_msg_from_to pt cn (dsoup d)]
  | [/\ pt_state d (round.+1, PInit) (rcons l (true, next_data)) pt,
     no_msg_from_to cn pt (dsoup d) &
     msg_spec pt cn commit_ack [::round] (dsoup d)
  ]].

Definition pt_PhaseTwoAbort d round next_data l pt :=
  [\/ [/\ (pt_state d (round, PRespondedYes next_data) l pt \/
           pt_state d (round, PRespondedNo next_data) l pt),
       msg_spec cn pt abort_req [::round] (dsoup d) &
       no_msg_from_to pt cn (dsoup d)]
   , [/\ pt_state d (round, PAborted next_data) (rcons l (false, next_data)) pt,
      no_msg_from_to cn pt (dsoup d) & no_msg_from_to pt cn (dsoup d)]
  | [/\ pt_state d (round.+1, PInit) (rcons l (false, next_data)) pt,
     no_msg_from_to cn pt (dsoup d) &
     msg_spec pt cn abort_ack [::round] (dsoup d)
  ]].

Definition pt_PhaseTwoResponded d round next_data l b pt :=
  [/\ pt_state d (round.+1, PInit) (rcons l (b, next_data)) pt,
   no_msg_from_to cn pt (dsoup d) & no_msg_from_to pt cn (dsoup d)].


Definition cn_PhaseTwoSendCommits d round next_data l sent :=
     [/\ cn_state d (round, CSentCommit next_data sent) l,
      uniq sent, {subset sent <= pts} &
       forall pt, pt \in pts ->
       if pt \in sent
       then pt_PhaseTwoCommit d round next_data l pt
       else pt_PhaseOneResponded d round next_data l true pt].


Definition cn_PhaseTwoSendAborts d round next_data l sent :=
     [/\ cn_state d (round, CSentAbort next_data sent) l,
      uniq sent, {subset sent <= pts} &
      forall pt, pt \in pts ->
      if pt \in sent
      then pt_PhaseTwoAbort d round next_data l pt
      else exists b, pt_PhaseOneResponded d round next_data l b pt].

Definition cn_PhaseTwoReceiveCommits d round next_data l recvd :=
      [/\ cn_state d (round, CWaitAckCommit next_data recvd) l,
       uniq recvd, {subset recvd <= pts} &
       forall pt, pt \in pts ->
       if pt \in recvd
       then pt_PhaseTwoResponded d round next_data l true pt
       else pt_PhaseTwoCommit d round next_data l pt].

Definition cn_PhaseTwoReceiveAborts d round next_data l recvd :=
     [/\ cn_state d (round, CWaitAckAbort next_data recvd) l,
      uniq recvd, {subset recvd <= pts} &
      forall pt, pt \in pts ->
      if pt \in recvd
      then pt_PhaseTwoResponded d round next_data l false pt
      else pt_PhaseTwoAbort d round next_data l pt].

Definition PhaseTwoCommit d round next_data lg :=
  [\/ exists sent : seq nid, cn_PhaseTwoSendCommits d round next_data lg sent |
     exists recvd : seq nid, cn_PhaseTwoReceiveCommits d round next_data lg recvd ].

Definition PhaseTwoAbort d round next_data lg :=
  [\/ exists sent : seq nid, cn_PhaseTwoSendAborts d round next_data lg sent |
     exists recvd : seq nid, cn_PhaseTwoReceiveAborts d round next_data lg recvd ].

Definition PhaseTwo (d : dstatelet) (round : nat) (next_data : data) (l : Log) :=
  [\/ exists sent, cn_PhaseTwoSendCommits d round next_data l sent,
     exists sent, cn_PhaseTwoSendAborts d round next_data l sent,
     exists recvd, cn_PhaseTwoReceiveCommits d round next_data l recvd |
   exists recvd, cn_PhaseTwoReceiveAborts d round next_data l recvd].

Definition Inv (d : dstatelet) :=
  exists round l,
  [\/ EverythingInit d round l
   , exists next_data, PhaseOne d round next_data l
  | exists next_data, PhaseTwo d round next_data l].

(***********************************************************)
(* Elimination lemmas for the invariant to deal with cases *)
(***********************************************************)

Notation coh d := (coh tpc d).
Notation PI := pf_irr.
Export TPCProtocol.

Lemma inv_init d e (C : coh d):
  Inv d -> getStC C = (e, CInit) -> exists lg, EverythingInit d e lg.
Proof.
case=>e'[lg][]=>[|[nd]|[nd]];
do?[by case; case=>xs[]=>E1; rewrite (getStC_K C E1)].
by case=>E1 H; rewrite (getStC_K C E1); case=>Z; subst e'; exists lg.
Qed.

Lemma inv_prep_send d e dt ps (C : coh d):
  Inv d -> getStC C = (e, CSentPrep dt ps) ->
  exists lg sent, cn_PhaseOneSend d e dt lg sent.
Proof.
case=>e'[lg][]=>[|[nd]|[nd]];
 last by case; case=>xs[]=>E1; rewrite (getStC_K C E1).
- by case=>E1 H; rewrite (getStC_K C E1).
case; last by case=>[?]/=[]E1; rewrite (getStC_K C E1).
case=>xs[E1]H1 H2 H3; rewrite (getStC_K C E1); case=>Z1 Z2 Z3.
by subst e' nd xs; exists lg, ps.
Qed.

Lemma inv_waitprep d r (C : coh d) next_data recvd:
  Inv d -> getStC C = (r, CWaitPrepResponse next_data recvd) ->
  exists lg, cn_PhaseOneReceive d r next_data lg recvd.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
by move=>H1 H2 H3 H4; case=><-<-<-; eexists; split; eauto.
by case; case => x[]CS; rewrite (getStC_K C CS).
Qed.

Lemma inv_sentcommit d r (C : coh d) next_data sent:
  Inv d -> getStC C = (r, CSentCommit next_data sent) ->
  exists lg, cn_PhaseTwoSendCommits d r next_data lg sent.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
by case; case => x[]CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
move=>H1 H2 H3. case. intros. subst.
eexists; split; eauto.
Qed.

Lemma inv_sentabort d r (C : coh d) next_data sent:
  Inv d -> getStC C = (r, CSentAbort next_data sent) ->
  exists lg, cn_PhaseTwoSendAborts d r next_data lg sent.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
by case; case => x[]CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
move=>H1 H2 H3. case. intros. subst.
eexists; split; eauto.
Qed.

Lemma inv_waitcommit d r (C : coh d) next_data sent:
  Inv d -> getStC C = (r, CWaitAckCommit next_data sent) ->
  exists lg, cn_PhaseTwoReceiveCommits d r next_data lg sent.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
by case; case => x[]CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
move=>H1 H2 H3. case. intros. subst.
eexists; split; eauto.
Qed.

Lemma inv_waitabort d r (C : coh d) next_data sent:
  Inv d -> getStC C = (r, CWaitAckAbort next_data sent) ->
  exists lg, cn_PhaseTwoReceiveAborts d r next_data lg sent.
Proof.
case=>r'[lg][]=>[|[nd]|[nd]].
by case=> CS; rewrite (getStC_K C CS).
by case; case => x[]CS; rewrite (getStC_K C CS).
case; case => x[]CS; rewrite (getStC_K C CS)//.
move=>H1 H2 H3. case. intros. subst.
eexists; split; eauto.
Qed.



Lemma prep_no_pt_inv d i m pt round next_data lg :
  tag m = prep_no ->
  find i (dsoup d) =
  Some {| content := m; from := pt; to := cn; active := true |} ->
  pt_PhaseOne d round next_data lg pt ->
  [/\ pt_state d (round, PRespondedNo next_data) lg pt,
       no_msg_from_to cn pt (dsoup d) &
       msg_spec pt cn prep_no [::round] (dsoup d)].
Proof.
move=>T F[][]H1 H2 H3; do?[by move: (H2 _ _ _ F)]; split=>//;
by case : m F T=>t c/= F Z; subst t; case:H3=>_/(_ _ _ _ F).
Qed.

Lemma prep_yes_pt_inv d i m pt round next_data lg :
  tag m = prep_yes ->
  find i (dsoup d) =
  Some {| content := m; from := pt; to := cn; active := true |} ->
  pt_PhaseOne d round next_data lg pt ->
  [/\ pt_state d (round, PRespondedYes next_data) lg pt,
       no_msg_from_to cn pt (dsoup d) &
       msg_spec pt cn prep_yes [::round] (dsoup d)].
Proof.
move=>T F[][]H1 H2 H3; do?[by move: (H2 _ _ _ F)]; split=>//;
by case : m F T=>t c/= F Z; subst t; case:H3=>_/(_ _ _ _ F).
Qed.

Lemma commit_ack_pt_inv d i m pt round next_data lg :
  tag m = commit_ack ->
  find i (dsoup d) =
    Some {| content := m; from := pt; to := cn; active := true |} ->
  pt_PhaseTwoCommit d round next_data lg pt ->
  [/\ pt_state d (round.+1, PInit) (rcons lg (true, next_data)) pt,
        no_msg_from_to cn pt (dsoup d)
      & msg_spec pt cn Exports.commit_ack [:: round] (dsoup d)].
Proof.
  by move=>T F[][]// _ _ /(_ _ _ _ F).
Qed.

Lemma abort_ack_pt_inv d i m pt round next_data lg :
  tag m = abort_ack ->
  find i (dsoup d) =
    Some {| content := m; from := pt; to := cn; active := true |} ->
  pt_PhaseTwoAbort d round next_data lg pt ->
  [/\ pt_state d (round.+1, PInit) (rcons lg (false, next_data)) pt,
        no_msg_from_to cn pt (dsoup d)
      & msg_spec pt cn Exports.abort_ack [:: round] (dsoup d)].
Proof.
  by move=>T F[][]// _ _ /(_ _ _ _ F).
Qed.

Lemma prep_req_cn_inv d i m pt :
  tag m = prep_req ->
  pt \in pts ->
  find i (dsoup d) =
    Some {| content := m; from := cn; to := pt; active := true |} ->
  Inv d ->
  exists round lg next_data, PhaseOne d round next_data lg.
Proof.
  case: m=>t m /=T. subst t.
  move=>Hpt F [r][lg][].
  - by move=>[] _ /(_ _ Hpt)[] _ _ /(_ _ _ _ F).
  - move=>[nd]. by eauto.
  - move=>[nd][][l1][] _ _ _ /(_ _ Hpt); case: ifP => _ []; (try case); (try case);
    do?[by move=>_ /(_ _ _ _ F)];
    do?[by move=>/(_ _ _ _ F)];
    by move=>_ []_ /(_ _ _ _ F)/=.
Qed.

Lemma prep_req_pt_inv d i m pt round next_data lg :
  find i (dsoup d) =
  Some {| content := m; from := cn; to := pt; active := true |} ->
  pt_PhaseOne d round next_data lg pt ->
  [/\ pt_state d (round, PInit) lg pt, no_msg_from_to pt cn (dsoup d)
      & msg_spec cn pt Exports.prep_req (round :: next_data) (dsoup d)].
Proof.
by move=>F[][]H1 H2 H3; do?[by move: (H2 _ _ _ F)]; do?[by move: (H3 _ _ _ F)]; split=>//.
Qed.

Lemma commit_req_pt_inv d i m pt round next_data lg :
  find i (dsoup d) =
  Some {| content := m; from := cn; to := pt; active := true |} ->
  pt_PhaseTwoCommit d round next_data lg pt ->
  [/\ pt_state d (round, PRespondedYes next_data) lg pt,
        msg_spec cn pt Exports.commit_req [:: round] (dsoup d)
      & no_msg_from_to pt cn (dsoup d)].
Proof.
by move=>F[][]H1 H2 H3; do?[by move: (H2 _ _ _ F)]; do?[by move: (H3 _ _ _ F)]; split=>//.
Qed.

Lemma abort_req_pt_inv d i m pt round next_data lg :
  find i (dsoup d) =
  Some {| content := m; from := cn; to := pt; active := true |} ->
  pt_PhaseTwoAbort d round next_data lg pt ->
[/\ pt_state d (round, PRespondedYes next_data) lg pt \/
        pt_state d (round, PRespondedNo next_data) lg pt,
        msg_spec cn pt Exports.abort_req [:: round] (dsoup d)
      & no_msg_from_to pt cn (dsoup d)].
Proof.
 move=>F[][]H1 H2 H3; do?[by move: (H2 _ _ _ F)]; do?[by move: (H3 _ _ _ F)]; split=>//.
Qed.

Lemma in_map_exists (x : nid) xs :
  (exists b : bool, (x, b) \in xs) \/ x \notin map fst xs.
Proof.
  case H: (x \in map fst xs); last by right.
  left.
  case/mapP: H =>[][y b] H/=->.
  eauto.
Qed.

Lemma commit_req_cn_inv d i m pt :
  tag m = commit_req ->
  pt \in pts ->
  find i (dsoup d) =
    Some {| content := m; from := cn; to := pt; active := true |} ->
  Inv d ->
  exists round lg next_data,
    PhaseTwoCommit d round next_data lg.
Proof.
  case: m=>t m /=T. subst t.
  move=>Hpt F [r][lg][].
  - by move=>[] _ /(_ _ Hpt)[] _ _ /(_ _ _ _ F).
  - move=>[nd] [][l1][] _ _ _.
    + move/(_ _ Hpt).
      case: ifP=>_ [][];
      do?[by move=>_ _ /(_ _ _ _ F)];
      do?[by move=>_ /(_ _ _ _ F)];
      do?[by move=>/(_ _ _ _ F)];
      by move=>_ _ []_ /(_ _ _ _ F)/=.
    + case: (in_map_exists pt l1).
      * move=>[b] H /(_ _ _ Hpt H) [].
        by move=>/(_ _ _ _ F).
      * move=>H _ /(_ _ Hpt H) [][];
        do?[by move=>_ _ /(_ _ _ _ F)];
        do?[by move=>_ /(_ _ _ _ F)];
        do?[by move=>/(_ _ _ _ F)];
        by move=>_ _ []_ /(_ _ _ _ F)/=.
  - unfold PhaseTwoCommit.
    move=>[nd][][l1]; eauto 10 => [][] CS U S /(_ _ Hpt); case: ifP=> _ [][][];
    do?[by move=>_ _ /(_ _ _ _ F)];
    do?[by move=>_ /(_ _ _ _ F)];
    do?[by move=>/(_ _ _ _ F)];
    by move=>_ []_ /(_ _ _ _ F).
Qed.

Lemma abort_req_cn_inv d i m pt :
  tag m = abort_req ->
  pt \in pts ->
  find i (dsoup d) =
    Some {| content := m; from := cn; to := pt; active := true |} ->
  Inv d ->
  exists round lg next_data,
    PhaseTwoAbort d round next_data lg.
Proof.
  case: m=>t m /=T. subst t.
  move=>Hpt F [r][lg][].
  - by move=>[] _ /(_ _ Hpt)[] _ _ /(_ _ _ _ F).
  - move=>[nd] [][l1][] _ _ _.
    + move/(_ _ Hpt).
      case: ifP=>_ [][];
      do?[by move=>_ _ /(_ _ _ _ F)];
      do?[by move=>_ /(_ _ _ _ F)];
      do?[by move=>/(_ _ _ _ F)];
      by move=>_ _ []_ /(_ _ _ _ F)/=.
    + case: (in_map_exists pt l1).
      * move=>[b] H /(_ _ _ Hpt H) [].
        by move=>/(_ _ _ _ F).
      * move=>H _ /(_ _ Hpt H) [][];
        do?[by move=>_ _ /(_ _ _ _ F)];
        do?[by move=>_ /(_ _ _ _ F)];
        do?[by move=>/(_ _ _ _ F)];
        by move=>_ _ []_ /(_ _ _ _ F)/=.
  - unfold PhaseTwoAbort.
    move=>[nd][][l1]; eauto 10 => [][] CS U S /(_ _ Hpt); case: ifP=> _[]; (try case); (try case);
    do?[by move=>_ _ /(_ _ _ _ F)];
    do?[by move=>_ /(_ _ _ _ F)];
    do?[by move=>/(_ _ _ _ F)];
    try by move=>_ []_ /(_ _ _ _ F).
Qed.


Lemma PhaseTwoCommit_req_round d i m pt round lg next_data :
  tag m = commit_req ->
  pt \in pts ->
  find i (dsoup d) =
    Some {| content := m; from := cn; to := pt; active := true |} ->
  PhaseTwoCommit d round next_data lg ->
  exists ps, pt_state d (round, ps) lg pt.
Proof.
  move=>T Hpt F [][l1][] CS U S /(_ _ Hpt); case: ifP=>_[]; try case; eauto;
   do?[by move=>_ _ /(_ _ _ _ F)];
   do?[by move=>_ /(_ _ _ _ F)].
Qed.

Lemma PhaseTwoAbort_req_round d i m pt round lg next_data :
  tag m = abort_req ->
  pt \in pts ->
  find i (dsoup d) =
    Some {| content := m; from := cn; to := pt; active := true |} ->
  PhaseTwoAbort d round next_data lg ->
  exists ps, pt_state d (round, ps) lg pt.
Proof.
  move=>T Hpt F [][l1][] CS U S /(_ _ Hpt); case: ifP=>_[]; try case; try case; eauto;
   do?[by move=>_ _ /(_ _ _ _ F)];
   do?[by move=>_ /(_ _ _ _ F)].
Qed.

Lemma PhaseTwoAbort_round_cn d round lg next_data :
  PhaseTwoAbort d round next_data lg ->
  exists cs, cn_state d (round, cs) lg.
Proof.
  move=>[][l1][]; eauto.
Qed.


Lemma PhaseTwoCommit_round_cn d round lg next_data :
  PhaseTwoCommit d round next_data lg ->
  exists cs, cn_state d (round, cs) lg.
Proof.
  move=>[][l1][]; eauto.
Qed.

Lemma PhaseOne_round_cn d round lg next_data :
  PhaseOne d round next_data lg ->
  exists cs, cn_state d (round, cs) lg.
Proof.
  move=>[][l1][]; eauto.
Qed.

Lemma PhaseOne_round_pt d pt round lg next_data :
  pt \in pts ->
  PhaseOne d round next_data lg ->
  exists ps, pt_state d (round, ps) lg pt.
Proof.
  move=>Hpt [][l1][] CS U Sub.
  - move=>/(_ _ Hpt).
    case: ifP; move=>_ [][]; eauto.
  - case: (in_map_exists pt l1).
    + move=>[b] H /(_ _ _ Hpt H) [].
      case: b H; by eauto.
    + move=>H _ /(_ _ Hpt H) [][]; by eauto.
Qed.

Lemma c_matches_tag_prep_yes_inv cs :
  c_matches_tag cs prep_yes ->
  exists next_data recvd,
    cs = CWaitPrepResponse next_data recvd.
Proof.
  case: cs=>//=.
  eauto.
Qed.

Lemma c_matches_tag_prep_no_inv cs :
  c_matches_tag cs prep_no ->
  exists next_data recvd,
    cs = CWaitPrepResponse next_data recvd.
Proof.
  case: cs=>//=.
  eauto.
Qed.

Lemma c_matches_tag_commit_ack_inv cs :
  c_matches_tag cs commit_ack ->
  exists next_data recvd,
    cs = CWaitAckCommit next_data recvd.
Proof.
  case: cs=>//=.
  eauto.
Qed.

Lemma c_matches_tag_abort_ack_inv cs :
  c_matches_tag cs abort_ack ->
  exists next_data recvd,
    cs = CWaitAckAbort next_data recvd.
Proof.
  case: cs=>//=.
  eauto.
Qed.

Lemma pt_state_functional d pt ps1 lg1 ps2 lg2 :
  valid (loc pt d) ->
  pt_state d ps1 lg1 pt ->
  pt_state d ps2 lg2 pt ->
  ps1 = ps2 /\ lg1 = lg2.
Proof.
  move=>V.
  rewrite/pt_state=> H.
  move: V.
  rewrite H => V.
  move /(hcancelV V) => [] ?. subst.
  move=> V1.
  by move /(hcancelPtV V1)=>->.
Qed.

Lemma PhaseOne_PGotRequest_next_data_pt d pt round lg next_data r nd :
  coh d ->
  pt \in pts ->
  pt_state d (r, PGotRequest nd) lg pt ->
  PhaseOne d round next_data lg ->
  [/\ pt_state d (round, PGotRequest next_data) lg pt, no_msg_from_to pt cn (dsoup d)
      & no_msg_from_to cn pt (dsoup d)].
Proof.
move=>C Hpt PS [].
- move=>[sent][] _ _ _ /(_ pt Hpt).
  case: ifP=>_[][] PS';
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; try discriminate;
  by case.
- move=>[recvd][] _ _ _ Hrecvd1 Hrecvd2.
  case (in_map_exists pt recvd).
  + move=>[b] H.
    move: (Hrecvd1 _ _ Hpt H)=>[] _.
    case: ifP=>_ _ PS';
    move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
    move: (pt_state_functional V PS PS')=>[]; try discriminate;
    by case.
  + move=> H.
    move: (Hrecvd2 _ Hpt H)=>[][] PS';
    move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
    move: (pt_state_functional V PS PS')=>[]; try discriminate;
    by case.
Qed.

Lemma inv_gotrequest d r nd (C : coh d) this (Hthis : this \in nodes cn pts others) :
  this \in pts ->
  getStP Hnin C Hthis = (r, PGotRequest nd) ->
  Inv d ->
  exists lg, PhaseOne d r nd lg.
Proof.
  move=>HthisPt PS [r'][lg][].
  - move=>[]CS /( _ this HthisPt)[] H.
    move: PS.
    rewrite (getStP_K Hnin C Hthis HthisPt H) => [].
    discriminate.
  - move=>[nd'] PO.
    move: (PhaseOne_round_pt HthisPt PO)=>[ps] PS'.
    move: PS.
    rewrite (getStP_K Hnin C Hthis HthisPt PS').
    case=>? ?. subst.
    move: (PhaseOne_PGotRequest_next_data_pt C HthisPt PS' PO) => [] PS''.
    move: C=>[] _ _ _ /(_ _ (pts_in cn others HthisPt)) [] V _.
    move: (pt_state_functional V PS' PS'')=>[][] ? ?. subst.
    by eauto.
  - move=>[nd'] [][l1][] _ _ _ /(_ this HthisPt);
    case: ifP=> _[]; (try case); (try case); intros;
    match goal with
    | [ PS' : pt_state _ _ _ _ |- _ ] =>
      move: PS;
        rewrite (getStP_K Hnin C Hthis HthisPt PS')
    end; discriminate.
Qed.

Lemma inv_committed d r nd (C : coh d) this (Hthis : this \in nodes cn pts others) :
  this \in pts ->
  getStP Hnin C Hthis = (r, PCommitted nd) ->
  Inv d ->
  exists lg, PhaseTwo d r nd lg.
Proof.
  move=>HthisPt PS [r'][lg][].
  - move=>[]CS /( _ this HthisPt)[] H.
    move: PS.
    rewrite (getStP_K Hnin C Hthis HthisPt H) => [].
    discriminate.
  - move=>[nd'] [][l1][] _ _ _.
    + move /(_ this HthisPt).
      case: ifP=> _[]; (try case); (try case); intros;
      match goal with
      | [ PS' : pt_state _ _ _ _ |- _ ] =>
        move: PS;
          rewrite (getStP_K Hnin C Hthis HthisPt PS')
      end; discriminate.
    + case: (in_map_exists this l1).
      * move=>[b] H /(_ _ _ HthisPt H)[] _ _.
        case: ifP=> _[]; (try case); (try case); intros;
        match goal with
        | [ PS' : pt_state _ _ _ _ |- _ ] =>
          move: PS;
            rewrite (getStP_K Hnin C Hthis HthisPt PS')
        end; discriminate.
      * move=>H _ /(_ _ HthisPt H)[][];
        intros;
        match goal with
        | [ PS' : pt_state _ _ _ _ |- _ ] =>
          move: PS;
            rewrite (getStP_K Hnin C Hthis HthisPt PS')
        end; discriminate.
  - move=>[nd'] PT.
    exists lg.
    case: PT=>[][l1] I; [constructor 1|constructor 2|constructor 3|constructor 4];
    exists l1; case: I => CS U S H.
    + move: (H this HthisPt).
      case: ifP.
      * move=> _ [][] PS' _ _.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           case=>? ?. subst.
           done.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
      * move=> _ [] _ _ PS'.
        move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
        discriminate.
    + move: (H this HthisPt).
      case: ifP.
      * move=> _ [][] [] PS' _ _.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
      * move=> _ [b] [] _ _; case: ifP => _ PS';
        move: PS; rewrite (getStP_K Hnin C Hthis HthisPt PS');
        discriminate.
    + move: (H this HthisPt).
      case: ifP.
      * move=> _ [][] [] PS' _ _.
        move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
        discriminate.
      * move=> _ [][] PS' _ _;
        move: PS; rewrite (getStP_K Hnin C Hthis HthisPt PS');
        try discriminate.
        case=> ? ?. subst.
        done.
    + move: (H this HthisPt).
      case: ifP.
      * move=> _ [][] [] PS' _ _.
        move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
        discriminate.
      * move=> _ [][] [] PS' _ _;
        move: PS; rewrite (getStP_K Hnin C Hthis HthisPt PS');
        discriminate.
Qed.

Lemma inv_aborted d r nd (C : coh d) this (Hthis : this \in nodes cn pts others) :
  this \in pts ->
  getStP Hnin C Hthis = (r, PAborted nd) ->
  Inv d ->
  exists lg, PhaseTwo d r nd lg.
Proof.
  move=>HthisPt PS [r'][lg][].
  - move=>[]CS /( _ this HthisPt)[] H.
    move: PS.
    rewrite (getStP_K Hnin C Hthis HthisPt H) => [].
    discriminate.
  - move=>[nd'] [][l1][] _ _ _.
    + move /(_ this HthisPt).
      case: ifP=> _[]; (try case); (try case); intros;
      match goal with
      | [ PS' : pt_state _ _ _ _ |- _ ] =>
        move: PS;
          rewrite (getStP_K Hnin C Hthis HthisPt PS')
      end; discriminate.
    + case: (in_map_exists this l1).
      * move=>[b] H /(_ _ _ HthisPt H)[] _ _.
        case: ifP=> _[]; (try case); (try case); intros;
        match goal with
        | [ PS' : pt_state _ _ _ _ |- _ ] =>
          move: PS;
            rewrite (getStP_K Hnin C Hthis HthisPt PS')
        end; discriminate.
      * move=>H _ /(_ _ HthisPt H)[][];
        intros;
        match goal with
        | [ PS' : pt_state _ _ _ _ |- _ ] =>
          move: PS;
            rewrite (getStP_K Hnin C Hthis HthisPt PS')
        end; discriminate.
  - move=>[nd'] PT.
    exists lg.
    case: PT=>[][l1] I; [constructor 1|constructor 2|constructor 3|constructor 4];
    exists l1; case: I => CS U S H.
    + move: (H this HthisPt).
      case: ifP.
      * move=> _ [][][] PS' _ _.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
      * move=> _ [] _ _ PS'.
        move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
        discriminate.
    + move: (H this HthisPt).
      case: ifP.
      * move=> _ [][] [] PS' _ _.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           case=>? ?. subst.
           done.
        -- move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
           discriminate.
      * move=> _ [b] [] _ _; case: ifP => _ PS';
        move: PS; rewrite (getStP_K Hnin C Hthis HthisPt PS');
        discriminate.
    + move: (H this HthisPt).
      case: ifP.
      * move=> _ [][] [] PS' _ _.
        move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
        discriminate.
      * move=> _ [][] PS' _ _;
        move: PS; rewrite (getStP_K Hnin C Hthis HthisPt PS');
        try discriminate.
    + move: (H this HthisPt).
      case: ifP.
      * move=> _ [][] [] PS' _ _.
        move: PS. rewrite (getStP_K Hnin C Hthis HthisPt PS').
        discriminate.
      * move=> _ [][] [] PS' _ _;
        move: PS; rewrite (getStP_K Hnin C Hthis HthisPt PS');
          try discriminate.
        case=> ? ?. subst.
        done.
Qed.


(***********************************************************)
(* Lemmas about specific sub-predicates *)

Lemma pt_PhaseOneE d e dt lg pt to ds tms:
  let d' :=   {|
    dstate := upd cn ds (dstate d);
    dsoup := (post_msg (dsoup d) (Msg tms cn to true)).1
  |} in
  coh d -> pt \in pts -> pt == to = false ->
  (forall z : nat, (z == cn) = false -> loc z d' = loc z d) ->
  pt_PhaseOne d e dt lg pt ->
  pt_PhaseOne d' e dt lg pt.
Proof.
move=>d' C Hp N G.
have X : pt == cn = false.
+ by apply/negbTE/negP=>/eqP Z; subst pt; move: (Hnin); rewrite Hp.
move: (G _ X)=>{G}G.
case; rewrite /pt_state=>[[E1]]M1 M2;
[constructor 1|constructor 2|constructor 3|constructor 4];
rewrite /pt_state/= G; rewrite eq_sym in X.
- split=>//; first by apply: (no_msg_from_toE' (cohVs C)).
  by move: (msg_specE' tms (cohVs C) N M2)=>/=.
- split=>//; first by apply: (no_msg_from_toE' (cohVs C)).
  by apply: (no_msg_from_toE (cohVs C)).
- split=>//; first by apply: (no_msg_from_toE (cohVs C)).
  apply: (msg_specE'' to tms (cohVs C) _ M2).
  by rewrite eq_sym in X.
split=>//;first by apply: (no_msg_from_toE (cohVs C)).
by apply: (msg_specE'' to tms (cohVs C) _ M2); rewrite eq_sym in X.
Qed.

Lemma pt_PhaseOneRespondedE d e dt lg b pt to ds tms:
  let d' :=   {|
    dstate := upd cn ds (dstate d);
    dsoup := (post_msg (dsoup d) (Msg tms cn to true)).1
  |} in
  coh d -> pt \in pts -> pt == to = false ->
  (forall z : nat, (z == cn) = false -> loc z d' = loc z d) ->
  pt_PhaseOneResponded d e dt lg b pt ->
  pt_PhaseOneResponded d' e dt lg b pt.
Proof.
move=>d' C Hp N G.
have X : pt == cn = false.
+ by apply/negbTE/negP=>/eqP Z; subst pt; move: (Hnin); rewrite Hp.
move: (G _ X)=>{G}G; case=>M1 M2; case: b=> E1;
split=>//; rewrite /d/=; first by apply: (no_msg_from_toE (cohVs C)).
+ by apply: (no_msg_from_toE' (cohVs C))=>//; rewrite eq_sym.
+ by rewrite /pt_state in E1 *; rewrite G.
+ by apply: (no_msg_from_toE (cohVs C)).
+ by apply: (no_msg_from_toE' (cohVs C))=>//; rewrite eq_sym.
by rewrite /pt_state in E1 *; rewrite G.
Qed.

Lemma pt_PhaseTwoCommitE d e dt lg pt to ds tms:
  let d' :=   {|
    dstate := upd cn ds (dstate d);
    dsoup := (post_msg (dsoup d) (Msg tms cn to true)).1
  |} in
  coh d -> pt \in pts -> pt == to = false ->
  (forall z : nat, (z == cn) = false -> loc z d' = loc z d) ->
  pt_PhaseTwoCommit d e dt lg pt ->
  pt_PhaseTwoCommit d' e dt lg pt.
Proof.
move=>d' C Hp N G.
have X : pt == cn = false.
+ by apply/negbTE/negP=>/eqP Z; subst pt; move: (Hnin); rewrite Hp.
move: (G _ X)=>{G}G.
case; rewrite /pt_state=>[[E1]]M1 M2;
[constructor 1|constructor 2|constructor 3];
rewrite /pt_state/= G; rewrite eq_sym in X.
- split=>//; first by move: (msg_specE' tms (cohVs C) N M1)=>/=.
  by apply: (no_msg_from_toE' (cohVs C)).
- split=>//; first by apply: (no_msg_from_toE (cohVs C)).
  by apply: (no_msg_from_toE' (cohVs C)).
split=>//; first by apply: (no_msg_from_toE (cohVs C)).
by apply: (msg_specE'' to tms (cohVs C) _ M2); rewrite eq_sym.
Qed.

Lemma pt_PhaseTwoAbortE d e dt lg pt to ds tms:
  let d' :=   {|
    dstate := upd cn ds (dstate d);
    dsoup := (post_msg (dsoup d) (Msg tms cn to true)).1
  |} in
  coh d -> pt \in pts -> pt == to = false ->
  (forall z : nat, (z == cn) = false -> loc z d' = loc z d) ->
  pt_PhaseTwoAbort d e dt lg pt ->
  pt_PhaseTwoAbort d' e dt lg pt.
Proof.
move=>d' C Hp N G.
have X : pt == cn = false.
+ by apply/negbTE/negP=>/eqP Z; subst pt; move: (Hnin); rewrite Hp.
move: (G _ X)=>{G}G.
case; rewrite /pt_state=>[[E1]]M1 M2;
[constructor 1|constructor 2|constructor 3];
rewrite /pt_state/= G; rewrite eq_sym in X.
- split=>//; first by move: (msg_specE' tms (cohVs C) N M1)=>/=.
  by apply: (no_msg_from_toE' (cohVs C)).
- split=>//; first by apply: (no_msg_from_toE (cohVs C)).
  by apply: (no_msg_from_toE' (cohVs C)).
split=>//; first by apply: (no_msg_from_toE (cohVs C)).
by apply: (msg_specE'' to tms (cohVs C) _ M2); rewrite eq_sym.
Qed.

Lemma cn_state_consume d ds cs lg i n :
  let: d' := {|
       dstate := upd n ds (dstate d);
       dsoup := consume_msg (dsoup d) i
  |} in
  cn != n ->
  coh d ->
  cn_state d cs lg ->
  cn_state d' cs lg.
Proof.
  move=>N C.
  by rewrite /cn_state locU// (cohVl C).
Qed.

Lemma pt_state_consume d ds ps lg pt i n :
  let: d' := {|
       dstate := upd n ds (dstate d);
       dsoup := consume_msg (dsoup d) i
  |} in
  pt != n ->
  coh d ->
  pt_state d ps lg pt ->
  pt_state d' ps lg pt .
Proof.
  move => N C H.
  by rewrite /pt_state locU // (cohVl C).
Qed.

Lemma pt_InitE_consume d e lg pt ds i from to m:
  let: d' :=   {|
    dstate := upd to ds (dstate d);
    dsoup := consume_msg (dsoup d) i
  |} in
  coh d -> pt \in pts ->
  pt != from ->
  pt != to ->
  find i (dsoup d) =
  Some {| content := m; from := from; to := to; active := true |} ->
  pt_Init d e lg pt ->
  pt_Init d' e lg pt.
Proof.
  move=>C Hpt N1 N2 F [] PS NM1 NM2.
  have Vst := cohVs C.
  split.
  + by apply /pt_state_consume.
  + by apply /no_msg_from_to_consume.
  + by apply /no_msg_from_to_consume.
Qed.

Lemma pt_PhaseOneE_consume d e dt lg pt ds i from to m:
  let d' :=   {|
    dstate := upd to ds (dstate d);
    dsoup := consume_msg (dsoup d) i
  |} in
  coh d -> pt \in pts ->
  pt != from ->
  pt != to ->
  find i (dsoup d) =
  Some {| content := m; from := from; to := to; active := true |} ->
  pt_PhaseOne d e dt lg pt ->
  pt_PhaseOne d' e dt lg pt.
Proof.
  move => d' C Hpt.
  subst d'.
  have Npt: pt != cn by apply pt_not_cn.
  (* have Nfrom: from != cn by apply pt_not_cn. *)
  have Vst: valid (dsoup d) by apply /(cohVs C).
  move => N1 N2 F [][] PS NM1.
  - move => M.
    constructor 1.
    split.
    + by apply /pt_state_consume.
    + by apply /no_msg_from_to_consume.
    + by apply /(@msg_specE_consume2 (dsoup d) _ from pt to _ _ i m) => //.
  - move => NM2.
    constructor 2.
    split.
    + by apply /pt_state_consume.
    + by apply /no_msg_from_to_consume.
    + by apply /no_msg_from_to_consume.
  - move => M.
    constructor 3.
    split.
    + by apply /pt_state_consume.
    + by apply /no_msg_from_to_consume=>//.
    + by apply /(@msg_specE_consume1 (dsoup d) _ from _ to _ _ i m).
  - move => M.
    constructor 4.
    split.
    + by apply /pt_state_consume.
    + by apply /no_msg_from_to_consume.
    + by apply /(@msg_specE_consume1 (dsoup d) _ from _ to _ _ i m).
Qed.


Lemma pt_PhaseOneRespondedE_consume d e dt lg b pt ds i from:
  let: d' :=   {|
    dstate := upd from ds (dstate d);
    dsoup := consume_msg (dsoup d) i
  |} in
  coh d -> pt \in pts ->
  pt != from ->
  pt_PhaseOneResponded d e dt lg b pt ->
  pt_PhaseOneResponded d' e dt lg b pt.
Proof.
  move=>C Hpt N [] NM1 NM2 PS.
  have Vs: (valid (dsoup d)) by exact: (cohVs C).
  split.
  - exact: no_msg_from_to_consume.
  - exact: no_msg_from_to_consume.
  - case: b PS => PS; exact: pt_state_consume.
Qed.

Lemma cn_PhaseOneReceive_consume d round next_data lg recvd i m from :
  cn_PhaseOneReceive d round next_data lg recvd ->
  find i (dsoup d) = Some {| content := m; from := from; to := cn; active := true |} ->
  from \in pts ->
  from \in map fst recvd ->
  coh d ->
  let: d' :=
     {|
       dstate := upd cn (mkLocal (round, CWaitPrepResponse next_data recvd, lg)) (dstate d);
       dsoup := consume_msg (dsoup d) i |}
  in
  cn_PhaseOneReceive d' round next_data lg recvd.
Proof.
  move=>[] CS U Hsub Hrecvd1 Hrecvd2 F Hfrom Hold C.
  split=>//.
  - by rewrite /cn_state locE'// (cohVl C).
  - move=>pt b Hpt Hr.
    apply /(pt_PhaseOneRespondedE_consume _ i)=>//.
    by apply: pt_not_cn.
    exact : Hrecvd1.
  - move=>pt Hpt Hr.
    case H: (pt == from).
    + move/eqP in H. subst from.
      move: (Hrecvd2 _ Hpt Hr).
      move /negbTE in Hr.
      by rewrite Hr in Hold.
    + apply /(@pt_PhaseOneE_consume _ _ _ _ _ _ _ from cn m) =>//.
      by apply /negbT/H.
      by apply /pt_not_cn.
      exact: Hrecvd2.
Qed.

Lemma pt_PhaseTwoRespondedE_consume d e dt lg b pt ds i this:
  let: d' :=   {|
    dstate := upd this ds (dstate d);
    dsoup := consume_msg (dsoup d) i
  |} in
  coh d -> pt \in pts -> pt != this ->
  pt_PhaseTwoResponded d e dt lg b pt ->
  pt_PhaseTwoResponded d' e dt lg b pt.
Proof.
  move=>C Hpt N [] NM1 NM2 PS.
  have Vs: (valid (dsoup d)) by exact: (cohVs C).
  have N2: (pt != cn) by exact: pt_not_cn.
  split.
  - exact: pt_state_consume.
  - exact: no_msg_from_to_consume.
  - exact: no_msg_from_to_consume.
Qed.

Lemma pt_PhaseTwoCommitE_consume d e dt lg pt ds from to i m:
  let: d' :=   {|
    dstate := upd to ds (dstate d);
    dsoup := consume_msg (dsoup d) i
  |} in
  coh d ->
  pt != from ->
  pt != to ->
  find i (dsoup d) =
  Some {| content := m; from := from; to := to; active := true |} ->
  pt_PhaseTwoCommit d e dt lg pt ->
  pt_PhaseTwoCommit d' e dt lg pt.
Proof.
  move=>C  N1 N2 F I.
  have Vs: (valid (dsoup d)) by exact: (cohVs C).
  move: I => [][] PS H1 H2; [constructor 1|constructor 2|constructor 3]; split;
  do?[by apply: no_msg_from_to_consume];
  do?[by apply: pt_state_consume].
  - by apply /(msg_specE_consume2 _ F)=>//.
  - by apply /(msg_specE_consume1 _ F)=>//.
Qed.

Lemma pt_PhaseTwoAbortE_consume d e dt lg pt ds from to i m:
  let: d' :=   {|
    dstate := upd to ds (dstate d);
    dsoup := consume_msg (dsoup d) i
  |} in
  coh d ->
  pt != from ->
  pt != to ->
  find i (dsoup d) =
  Some {| content := m; from := from; to := to; active := true |} ->
  pt_PhaseTwoAbort d e dt lg pt ->
  pt_PhaseTwoAbort d' e dt lg pt.
Proof.
  move=>C N1 N2 F I.
  have Vs: (valid (dsoup d)) by exact: (cohVs C).
  move: I => [][] PS H1 H2; [constructor 1|constructor 2|constructor 3]; split;
  do?[by apply: no_msg_from_to_consume];
  do?[by apply: pt_state_consume].
  - case: PS=>PS; [left|right]; by apply: pt_state_consume.
  - by apply /(msg_specE_consume2 _ F)=>//.
  - by apply /(msg_specE_consume1 _ F)=>//.
Qed.

Lemma cn_state_soupE d ds this h cs lg :
  let: d' := {| dstate := upd this h (dstate d);
                dsoup := ds |} in
  coh d ->
  this != cn ->
  cn_state d cs lg ->
  cn_state d' cs lg.
Proof.
move=>C N.
have Vl := (cohVl C).
rewrite /cn_state locU//.
by apply/eqP/nesym/eqP.
Qed.

Lemma pt_state_soupE d ds h ps lg pt n :
  let: d' := {|
       dstate := upd n h (dstate d);
       dsoup := ds
  |} in
  coh d ->
  pt != n ->
  pt_state d ps lg pt ->
  pt_state d' ps lg pt .
Proof.
  move => C N H.
  by rewrite /pt_state locU // (cohVl C).
Qed.

Lemma pt_PhaseOneE' d r nd lg pt from h to m :
  let: d' := {| dstate := upd from h (dstate d);
                dsoup := (post_msg (dsoup d)
                  {| content := m; from := from; to := to; active := true |}).1 |} in
  coh d ->
  from != pt ->
  from != cn ->
  pt_PhaseOne d r nd lg pt ->
  pt_PhaseOne d' r nd lg pt.
Proof.
  move=>C N1 N2.
  have Vl := cohVl C.
  have Vs := cohVs C.
  move=>[][] H1 H2 H3;
  [constructor 1|constructor 2|constructor 3|constructor 4].
  - split.
    + apply /pt_state_soupE=>//.
      by apply /eqP/nesym/eqP.
    + apply no_msg_from_toE'=>//.
      by apply /negbTE.
    + apply msg_specE''=>//.
      by apply /eqP/nesym/eqP.
  - split.
    + apply /pt_state_soupE=>//.
      by apply /eqP/nesym/eqP.
    + apply no_msg_from_toE'=>//.
      by apply /negbTE.
    + apply no_msg_from_toE'=>//.
      by apply /negbTE.
  - split.
    + apply /pt_state_soupE=>//.
      by apply /eqP/nesym/eqP.
    + apply no_msg_from_toE'=>//.
      by apply /negbTE.
    + apply msg_specE''=>//.
      by apply /eqP/nesym/eqP.
  - split.
    + apply /pt_state_soupE=>//.
      by apply /eqP/nesym/eqP.
    + apply no_msg_from_toE'=>//.
      by apply /negbTE.
    + apply msg_specE''=>//.
      by apply /eqP/nesym/eqP.
Qed.

Lemma pt_InitE d r lg pt from h to m :
  let: d' := {| dstate := upd from h (dstate d);
                dsoup := (post_msg (dsoup d)
                  {| content := m; from := from; to := to; active := true |}).1 |} in
  coh d ->
  from != pt ->
  from != cn ->
  pt_Init d r lg pt ->
  pt_Init d' r lg pt.
Proof.
  move=>C N1 N2.
  have Vl := cohVl C.
  have Vs := cohVs C.
  move=>[] H1 H2 H3.
  split.
  - apply pt_state_soupE=>//.
    by apply /eqP/nesym/eqP.
  - apply /no_msg_from_toE'=>//.
    by apply /negbTE.
  - apply /no_msg_from_toE'=>//.
    by apply /negbTE.
Qed.

Lemma pt_PhaseOneRespondedE' d r nd lg pt from h to m b :
  let: d' := {| dstate := upd from h (dstate d);
                dsoup := (post_msg (dsoup d)
                  {| content := m; from := from; to := to; active := true |}).1 |} in
  coh d ->
  from != pt ->
  from != cn ->
  pt_PhaseOneResponded d r nd lg b pt ->
  pt_PhaseOneResponded d' r nd lg b pt.
Proof.
  move=>C N1 N2 [] NM1 NM2 H.
  have Vl := cohVl C.
  have Vs := cohVs C.
  split.
  - apply /no_msg_from_toE'=>//.
    by apply /negbTE.
  - apply /no_msg_from_toE'=>//.
    by apply /negbTE.
  - case: b H.
    + apply: pt_state_soupE=>//.
      by apply /eqP/nesym/eqP.
    + apply: pt_state_soupE=>//.
      by apply /eqP/nesym/eqP.
Qed.

Lemma PhaseTwo_PCommitted_pt d pt round lg next_data r nd (C : coh d)
      (Hpt : pt \in nodes _ _ _) :
  pt \in pts ->
  getStP Hnin C Hpt = (r, PCommitted nd) ->
  PhaseTwo d round next_data lg ->
  [/\ pt_state d (round, PCommitted next_data) (rcons lg (true, next_data)) pt,
        no_msg_from_to cn pt (dsoup d)
      & no_msg_from_to pt cn (dsoup d)].
Proof.
move=>HptP PS[][l1][] CS U S /(_ pt HptP); case: ifP=> _[]; (try case); (try case); intros => //.
all: match goal with
     | [ PS : getStP _ _ _ = _,
         PS' : pt_state _ _ _ _ |- _ ] =>
       rewrite (getStP_K _ _ _ _ PS')// in PS; try discriminate
     end.
Qed.


Lemma pt_PhaseTwoCommitE' d r nd lg pt from h to m :
  let: d' := {| dstate := upd from h (dstate d);
                dsoup := (post_msg (dsoup d)
                  {| content := m; from := from; to := to; active := true |}).1 |} in
  coh d ->
  from != pt ->
  from != cn ->
  pt_PhaseTwoCommit d r nd lg pt ->
  pt_PhaseTwoCommit d' r nd lg pt.
Proof.
move=>C /eqP/nesym/eqP N1 /eqP/nesym/eqP N2.
have Vs := cohVs C.
case=>[][] H1 H2 H3; [constructor 1|constructor 2|constructor 3]; split;
do?[by apply /pt_state_soupE];
do?[by apply /msg_specE''=>//; apply /negbTE];
do?[by apply/no_msg_from_toE'=>//; apply/eqP/nesym/eqP].
Qed.

Lemma pt_PhaseTwoAbortE' d r nd lg pt from h to m :
  let: d' := {| dstate := upd from h (dstate d);
                dsoup := (post_msg (dsoup d)
                  {| content := m; from := from; to := to; active := true |}).1 |} in
  coh d ->
  from != pt ->
  from != cn ->
  pt_PhaseTwoAbort d r nd lg pt ->
  pt_PhaseTwoAbort d' r nd lg pt.
Proof.
move=>C /eqP/nesym/eqP N1 /eqP/nesym/eqP N2.
have Vs := cohVs C.
case=>[][] H1 H2 H3; [constructor 1|constructor 2|constructor 3]; split;
do?[by apply /pt_state_soupE];
do?[by apply /msg_specE''=>//; apply /negbTE];
do?[by apply/no_msg_from_toE'=>//; apply/eqP/nesym/eqP].

case: H1; [left|right];
by apply /pt_state_soupE.
Qed.


Lemma pt_PhaseTwoRespondedE' d r nd lg pt from h to m b :
  let: d' := {| dstate := upd from h (dstate d);
                dsoup := (post_msg (dsoup d)
                  {| content := m; from := from; to := to; active := true |}).1 |} in
  coh d ->
  from != pt ->
  from != cn ->
  pt_PhaseTwoResponded d r nd lg b pt ->
  pt_PhaseTwoResponded d' r nd lg b pt.
Proof.
move=>C N1 N2 [] PS NM1 NM2.
have Vs := cohVs C.
split.
- apply /pt_state_soupE=>//.
  by apply /eqP/nesym/eqP.
- apply /no_msg_from_toE'=>//.
  by apply /negbTE.
- apply /no_msg_from_toE'=>//.
  by apply /negbTE.
Qed.

Lemma PhaseTwo_PAborted_pt d pt round lg next_data r nd (C : coh d)
      (Hpt : pt \in nodes _ _ _) :
  pt \in pts ->
  getStP Hnin C Hpt = (r, PAborted nd) ->
  PhaseTwo d round next_data lg ->
  [/\ pt_state d (round, PAborted next_data) (rcons lg (false, next_data)) pt,
        no_msg_from_to cn pt (dsoup d)
      & no_msg_from_to pt cn (dsoup d)].
Proof.
move=>HptP PS[][l1][] CS U S /(_ pt HptP); case: ifP=> _[]; (try case); (try case); intros => //.
all: match goal with
     | [ PS : getStP _ _ _ = _,
         PS' : pt_state _ _ _ _ |- _ ] =>
       rewrite (getStP_K _ _ _ _ PS')// in PS; try discriminate
     end.
Qed.

(************************************************************)

Definition coord_msg tag (from to : nid) : bool :=
  [&& from == cn, to \in pts & tagFromCoordinator tag].

Definition participant_msg tag (from to : nid) : bool :=
  [&& from \in pts, to == cn & tagFromParticipant tag].

Definition internal_msg (tag : nat) (from to : nid) : bool :=
  coord_msg tag from to || participant_msg tag from to.

Lemma internal_msg_tagFromParticipant_to_cn tag from to :
  internal_msg tag from to ->
  tagFromParticipant tag ->
  to == cn.
Proof.
case/orP; move=>/and3P[]//.
move=> _ _.
rewrite /tagFromCoordinator/tagFromParticipant !inE.
move/or3P=>[]/eqP ? /or4P[]/eqP ?; subst; discriminate.
Qed.

Lemma internal_msg_tagFromParticipant_from_pts tag from to :
  internal_msg tag from to ->
  tagFromParticipant tag ->
  from \in pts.
Proof.
case/orP; move=>/and3P[]//.
move=> _ _.
rewrite /tagFromCoordinator/tagFromParticipant !inE.
move/or3P=>[]/eqP ? /or4P[]/eqP ?; subst; discriminate.
Qed.

Lemma internal_msg_tagFromCoordinator_to_pts tag from to :
  internal_msg tag from to ->
  tagFromCoordinator tag ->
  to \in pts.
Proof.
case/orP; move=>/and3P[]//.
move=> _ _.
rewrite /tagFromCoordinator/tagFromCoordinator !inE.
move/or3P=>[]/eqP ? /or3P[]/eqP ?; subst; discriminate.
Qed.

Lemma internal_msg_tagFromCoordinator_from_cn tag from to :
  internal_msg tag from to ->
  tagFromCoordinator tag ->
  from == cn.
Proof.
case/orP; move=>/and3P[]//.
move=> _ _.
rewrite /tagFromCoordinator/tagFromCoordinator !inE.
move/or3P=>[]/eqP ? /or3P[]/eqP ?; subst; discriminate.
Qed.

Lemma internal_msg_to_cn tag from :
  internal_msg tag from cn ->
  participant_msg tag from cn.
Proof.
  move=>/orP[]// /and3P[] _ H.
  move: Hnin. by rewrite H.
Qed.

Lemma inv_msg_round d (C : coh d) i tag m from to round cs :
  find i (dsoup d) =
    Some {| content := {| tag := tag; tms_cont := m |};
            from := from;
            to := to;
            active := true |} ->
  internal_msg tag from to ->
  Inv d ->
  getStC C = (round, cs) ->
  head 0 m == round.
Proof.
  move=>F Hinternal I St.
  case/orP: Hinternal.
  - move=>/and3P[]/eqP ? Hto T. subst from.
    move: I=>[rd][lg][].
    + by move=>[]CS /(_ _ Hto) [] PS NM1 /(_ _ _ _ F).
    + move=>[next_data][].
      * move=>[sent][] CS U Sub /(_ _ Hto).
        case: ifP.
        -- move=>Hsent [][] PS.
           ++ move=>_[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
           ++ by move=>_ /(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
        -- by move=>Hsent[] PS _ /(_ _ _ _ F).
      * move=>[recvd][] CS U Sub Hrecvd1 Hrecvd2.
        case: (in_map_exists to recvd).
        -- move=>[b] Hr.
           by move: (Hrecvd1 _ _ Hto Hr)=>[] /(_ _ _ _ F).
        -- move=>Hr.
           move: (Hrecvd2 _ Hto Hr)=>[][] PS.
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
           ++ by move=>_ /(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
    + move=>[next_data][].
      * move=>[sent][] CS U Sub /(_ _ Hto).
        case: ifP.
        -- move=>Hsent [][] PS.
           ++ move=>[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
           ++ by move=>/(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
        -- by move=>_ [] /(_ _ _ _ F).
      * move=>[sent][] CS U Sub /(_ _ Hto).
        case: ifP.
        -- move=>Hsent [][] PS.
           ++ move=>[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
           ++ by move=>/(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
        -- by move=> _[b][] /(_ _ _ _ F).
      * move=>[recvd][] CS U Sub /(_ _ Hto).
        case: ifP.
        -- by move=>Hrecvd [] PS /(_ _ _ _ F).
        -- move=>Hrecvd[][] PS.
           ++ move=>[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
           ++ by move=>/(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
      * move=>[recvd][] CS U Sub /(_ _ Hto).
        case: ifP.
        -- by move=>Hrecvd [] PS /(_ _ _ _ F).
        -- move=>Hrecvd[][] PS.
           ++ move=>[] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
           ++ by move=>/(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
  - move=>/and3P[]Hfrom/eqP ? T. subst to.
    move: I=>[rd][lg][].
    + by move=>[]CS /(_ _ Hfrom) [] PS /(_ _ _ _ F).
    + move=>[next_data][].
      * move=>[sent][] CS U Sub /(_ _ Hfrom).
        case: ifP.
        -- move=>Hsent [][] PS.
           ++ by move=>/(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
        -- by move=>Hsent[] PS /(_ _ _ _ F).
      * move=>[recvd][] CS U Sub Hrecvd1 Hrecvd2.
        case: (in_map_exists from recvd).
        -- move=>[b] Hr.
           by move: (Hrecvd1 _ _ Hfrom Hr)=>[] _/(_ _ _ _ F).
        -- move=>Hr.
           move: (Hrecvd2 _ Hfrom Hr)=>[][] PS.
           ++ by move=>/(_ _ _ _ F).
           ++ by move=>/(_ _ _ _ F).
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
    + move=>[next_data][].
      * move=>[sent][] CS U Sub /(_ _ Hfrom).
        case: ifP.
        -- move=>Hsent [][] PS.
           ++ by move=>_ /(_ _ _ _ F).
           ++ by move=>_ /(_ _ _ _ F).
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
        -- by move=>Hsent [] _ /(_ _ _ _ F).
      * move=>[sent][] CS U Sub /(_ _ Hfrom).
        case: ifP.
        -- move=>Hsent [][] PS.
           ++ by move=>_ /(_ _ _ _ F).
           ++ by move=>_ /(_ _ _ _ F).
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
        -- by move=>Hsent [b][] _ /(_ _ _ _ F).
      * move=>[recvd][] CS U Sub /(_ _ Hfrom).
        case: ifP.
        -- by move=>Hrecvd [] PS _ /(_ _ _ _ F).
        -- move=>Hrecvd[][] PS.
           ++ by move=>_ /(_ _ _ _ F).
           ++ by move=>_ /(_ _ _ _ F).
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
      * move=>[recvd][] CS U Sub /(_ _ Hfrom).
        case: ifP.
        -- by move=>Hrecvd [] PS _ /(_ _ _ _ F).
        -- move=>Hrecvd[][] PS.
           ++ by move=>_ /(_ _ _ _ F).
           ++ by move=>_ /(_ _ _ _ F).
           ++ move=>_ [] _ /(_ _ _ _ F) /andP[] _ /eqP->/=.
              rewrite (getStC_K _ CS) in St.
              case: St=>->. by rewrite eqxx.
Qed.

Definition E_consume_external d i this tag m from P :=
  let: d' := {| dstate := upd this (loc this d) (dstate d);
                dsoup := consume_msg (dsoup d) i |} in
  coh d ->
  find i (dsoup d) =
    Some {| content := {| tag := tag; tms_cont := m |};
            from := from;
            to := this;
            active := true |} ->
  ~~ internal_msg tag from this ->
  P d ->
  P d'.

Lemma cn_stateE_consume_external d i this tag m from cs log :
  E_consume_external d i this tag m from (fun d => cn_state d cs log).
Proof.
  move=>C F Hext.
  have Vl := (cohVl C).
  rewrite /cn_state.
  case H: (this == cn).
  - move/eqP in H. subst this. by rewrite locE'.
  rewrite locU//.
  by apply /eqP/nesym/eqP/negbT.
Qed.

Lemma pt_stateE_consume_external d i this tag m from ps lg pt :
  E_consume_external d i this tag m from (fun d => pt_state d ps lg pt).
Proof.
  move=>C F Hext.
  have Vl := (cohVl C).
  rewrite /pt_state.
  case H: (this == pt).
  - move/eqP in H. subst this. by rewrite locE'.
  rewrite locU//.
  by apply /eqP/nesym/eqP/negbT.
Qed.

Lemma msg_specE_consume_external d i this tag m from from' to' tag' m' :
  internal_msg tag' from' to' ->
  E_consume_external d i this tag m from (fun d => msg_spec from' to' tag' m' (dsoup d)).
Proof.
  move=>Hint C F Hext [] [j] [][t][c] F' U H.
  have Vs := cohVs C.
  split.
  - exists j. split.
    + exists t, c. rewrite mark_other//.
      case E: (j == i)=>//.
      move/eqP in E. subst j.
      move: F.
      rewrite F'.
      case=> ? ? ? ?. subst.
      move: (F')=>/H/andP[]/eqP ? _. subst.
      by rewrite Hint in Hext.
    + move=>k[t'][c'] F''.
      case H2: (k == i).
      * move/eqP in H2. subst k.
        move: F''=> /(find_mark Vs)[msg'][F''].
        discriminate.
      * rewrite mark_other// in F''.
        apply /U. by eauto.
  - move=> k t' c' F''.
    case H2: (k == i).
    + move/eqP in H2. subst k.
      move: F''=> /(find_mark Vs)[msg'][F''].
      discriminate.
    + rewrite mark_other// in F''.
      apply /H. exact: F''.
Qed.

Lemma pt_PhaseOneE_consume_external d i this tag m from round next_data lg pt :
  pt \in pts ->
  E_consume_external d i this tag m from (fun d => pt_PhaseOne d round next_data lg pt).
Proof.
  move=>Hpt C F Hext.
  have Vs := (cohVs C).
  case=>[][]PS NM1 H; [constructor 1|constructor 2| constructor 3 | constructor 4].
  - split=>//.
    + by apply: (pt_stateE_consume_external _ F).
    + by apply: no_msg_from_to_consume.
    + apply: (msg_specE_consume_external _ _ F)=>//.
      apply/orP. left.
      by apply/and3P.
  - split=>//.
    + by apply: (pt_stateE_consume_external _ F).
    + by apply: no_msg_from_to_consume.
    + by apply: no_msg_from_to_consume.
  - split=>//.
    + by apply: (pt_stateE_consume_external _ F).
    + by apply: no_msg_from_to_consume.
    + apply: (msg_specE_consume_external _ _ F)=>//.
      apply/orP. right.
      by apply/and3P.
  - split=>//.
    + by apply: (pt_stateE_consume_external _ F).
    + by apply: no_msg_from_to_consume.
    + apply: (msg_specE_consume_external _ _ F)=>//.
      apply/orP. right.
      by apply/and3P.
Qed.

Lemma pt_InitE_consume_external d i this tag m from round lg pt :
  E_consume_external d i this tag m from (fun d => pt_Init d round lg pt).
Proof.
  move=>C F Hext [] PS NM1 NM2.
  have Vs := (cohVs C).
  split.
  - by apply: (pt_stateE_consume_external _ F).
  - by apply: no_msg_from_to_consume.
  - by apply: no_msg_from_to_consume.
Qed.

Lemma pt_PhaseOneRespondedE_consume_external d i this tag m from round next_data lg b pt :
  E_consume_external d i this tag m from (fun d => pt_PhaseOneResponded d round next_data lg b pt).
Proof.
  move=>C F Hext [] NM1 NM2 H.
  have Vs := (cohVs C).
  split.
  - by apply: no_msg_from_to_consume.
  - by apply: no_msg_from_to_consume.
  - case: b H; by apply: (pt_stateE_consume_external _ F).
Qed.

Lemma pt_PhaseTwoRespondedE_consume_external d i this tag m from round next_data lg b pt :
  E_consume_external d i this tag m from (fun d => pt_PhaseTwoResponded d round next_data lg b pt).
Proof.
  move=>C F Hext [] PS NM1 NM2.
  have Vs := (cohVs C).
  split.
  - by apply: (pt_stateE_consume_external _ F).
  - by apply: no_msg_from_to_consume.
  - by apply: no_msg_from_to_consume.
Qed.

Lemma pt_PhaseTwoCommitE_consume_external d i this tag m from round next_data lg pt :
  pt \in pts ->
  E_consume_external d i this tag m from (fun d => pt_PhaseTwoCommit d round next_data lg pt).
Proof.
  move=>Hpt C F Hext [][] PS H1 H2;
  have Vs := (cohVs C); [constructor 1|constructor 2|constructor 3]; split;
  do?[by apply: (pt_stateE_consume_external _ F)];
  do?[by apply: no_msg_from_to_consume].
  - apply: (msg_specE_consume_external _ _ F)=>//.
    apply/orP. left.
    by apply/and3P.
  - apply: (msg_specE_consume_external _ _ F)=>//.
    apply/orP. right.
    by apply/and3P.
Qed.

Lemma pt_PhaseTwoAbortE_consume_external d i this tag m from round next_data lg pt :
  pt \in pts ->
  E_consume_external d i this tag m from (fun d => pt_PhaseTwoAbort d round next_data lg pt).
Proof.
  move=>Hpt C F Hext [][] PS H1 H2;
  have Vs := (cohVs C); [constructor 1|constructor 2|constructor 3]; split;
  do?[by apply: (pt_stateE_consume_external _ F)];
  do?[by apply: no_msg_from_to_consume].
  - case: PS=>PS; [left|right]; by apply: (pt_stateE_consume_external _ F).
  - apply: (msg_specE_consume_external _ _ F)=>//.
    apply/orP. left.
    by apply/and3P.
  - apply: (msg_specE_consume_external _ _ F)=>//.
    apply/orP. right.
    by apply/and3P.
Qed.

Lemma invE_consume_external d i this tag m from :
  E_consume_external d i this tag m from Inv.
Proof.
  move=>C F Hext [round][lg] I.
  have Vs := cohVs C.
  have Vl := cohVl C.
  exists round, lg.
  case: I=>I; [constructor 1|constructor 2|constructor 3].
  - move: I=>[] CS Pts.
    split.
    + by apply: (cn_stateE_consume_external _ F).
    + move=>pt Hpt.
      move: (Pts pt Hpt)=>[] PS NM2.
      split.
      * by apply: (pt_stateE_consume_external _ F).
      * by apply: (no_msg_from_to_consume).
      * by apply: (no_msg_from_to_consume).
  - move: I=>[next_data][[sent]|[recvd]] I; exists next_data;
    [constructor 1; exists sent|constructor 2; exists recvd].
    + move: I=>[] CS U Sub Pts.
      split=>//.
      * by apply: (cn_stateE_consume_external _ F).
      * move=>pt Hpt.
        case: ifP.
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_PhaseOneE_consume_external _ _ F).
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_InitE_consume_external _ F).
    + move: I=>[] CS U Sub Hrecvd1 Hrecvd2.
      split=>//.
      * by apply: (cn_stateE_consume_external _ F).
      * move=>pt b Hpt Hr.
        move: (Hrecvd1 _ _ Hpt Hr).
        by apply: (pt_PhaseOneRespondedE_consume_external _ F).
      * move=>pt Hpt Hr.
        move: (Hrecvd2 _ Hpt Hr).
        by apply: (pt_PhaseOneE_consume_external _ _ F).
  - move: I=>[next_data][[sent]|[sent]|[recvd]|[recvd]] I; exists next_data;
    [constructor 1; exists sent|constructor 2; exists sent|
     constructor 3; exists recvd|constructor 4; exists recvd].
    + move: I=>[] CS U Sub Pts.
      split=>//.
      * by apply: (cn_stateE_consume_external _ F).
      * move=>pt Hpt.
        case: ifP.
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_PhaseTwoCommitE_consume_external _ _ F).
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_PhaseOneRespondedE_consume_external _ F).
    + move: I=>[] CS U Sub Pts.
      split=>//.
      * by apply: (cn_stateE_consume_external _ F).
      * move=>pt Hpt.
        case: ifP.
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_PhaseTwoAbortE_consume_external _ _ F).
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent=>[][b] I.
           exists b.
           by apply: (pt_PhaseOneRespondedE_consume_external _ F).
    + move: I=>[] CS U Sub Pts.
      split=>//.
      * by apply: (cn_stateE_consume_external _ F).
      * move=>pt Hpt.
        case: ifP.
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_PhaseTwoRespondedE_consume_external _ F).
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_PhaseTwoCommitE_consume_external _ _ F).
    + move: I=>[] CS U Sub Pts.
      split=>//.
      * by apply: (cn_stateE_consume_external _ F).
      * move=>pt Hpt.
        case: ifP.
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_PhaseTwoRespondedE_consume_external _ F).
        -- move=>Hsent.
           move: (Pts _ Hpt).
           rewrite Hsent.
           by apply: (pt_PhaseTwoAbortE_consume_external _ _ F).
Qed.

Lemma rc_step_external d (C : coh d) this (Hthis : this \in nodes cn pts others) tag from m i :
  ~~ internal_msg tag from this ->
   find i (dsoup d) =
    Some {| content := {| tag := tag; tms_cont := m |};
            from := from;
            to := this;
            active := true |} ->
 rc_step tag from m C Hthis = loc this d.
Proof.
  move/norP=>[]/and3P H1 /and3P H2 F.
  rewrite /rc_step.
  case: ifP=>// /eqP ?. subst this.
  pose proof C as C'.
  case: C'=>Hs _ _ /(_ cn Hthis)[] _.
  rewrite eqxx=>[][cs][lg] L.
  rewrite (getStC_K _ L) (getStL_Kc _ _ L).
  rewrite /cstep_recv.
  case: ifP=>// /negbFE Hfrom.
  case: cs L=>round cs L.
  case: ifP=>//.
  move: Hs=>[] _ /(_ _ _ F)[r].
  rewrite /cohMsg/=.
  case: ifP.
  - move=> _ []. by rewrite (negbTE Hnin).
  - move=>_. rewrite Hfrom.
    move=>[] _ /andP[] T.
    exfalso.
    apply/H2.
    by split.
Qed.

Lemma rp_step_external d (C : coh d) this (Hthis : this \in nodes cn pts others) tag from m i :
  ~~ internal_msg tag from this ->
   find i (dsoup d) =
    Some {| content := {| tag := tag; tms_cont := m |};
            from := from;
            to := this;
            active := true |} ->
 rp_step Hnin tag from m C Hthis = loc this d.
Proof.
  move/norP=>[] H1 H2 F.
  rewrite /rp_step.
  case: ifP=>//Hpts.
  pose proof C as C'.
  case: C'=>Hs _ _ /(_ this (pts_in _ _ Hpts)) [] _.
  rewrite (this_not_pts Hnin Hpts) Hpts =>[][ps][lg] L.
  rewrite (getStP_K _ _ _ _ L)//  (getStL_Kp _ _ L).
  rewrite /pstep_recv.
  case: ifP=>//.  move=>/norP[]/norP[] /negbNE H3 /negbNE H4 /negbNE H5.

  destruct ps as[round ps].

  move: H3 H1.
  rewrite /coord_msg H4 Hpts/=/tagFromCoordinator/p_matches_tag.
  destruct ps=>//.
  - move=>/eqP ?. subst tag. done.
  - case/orP=>/eqP ?; subst; done.
  - move=>/eqP ?. subst tag. done.
Qed.

Lemma internal_msg_from_cn tag to :
  internal_msg tag cn to ->
  coord_msg tag cn to.
Proof.
  move=>/orP[]// /and3P[] H.
  move: Hnin. by rewrite H.
Qed.

Lemma p_matches_tag_internal_inv d i t m pt r ps lg :
  coh d ->
  pt \in pts ->
  find i (dsoup d) =
    Some {| content := {| tag := t; tms_cont := m |};
            from := cn;
            to := pt;
            active := true |} ->
  internal_msg t cn pt ->
  pt_state d (r, ps) lg pt ->
  Inv d ->
  p_matches_tag ps t.
Proof.
  move=>C Hpt F /internal_msg_from_cn /and3P[] _ _ T PS.
  move=>[r'][lg'][].
  - by move=>[] _ /(_ pt Hpt) [] _ _ /(_ _ _ _ F).
  - move=>[nd][][l1][] _ _ _.
    + move=>/(_ _ Hpt).
      case: ifP=>_ [][] PS';
      do?[by move=>_ /(_ _ _ _ F)];
      do?[by move=>/(_ _ _ _ F)].
      move=>_[] _ /(_ _ _ _ F) /andP[] /eqP ? /eqP ?. subst.
      move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
      move: (pt_state_functional V PS PS')=>[][] ? ? ?. subst.
      done.
    + case: (in_map_exists pt l1).
      * by move=>[b] H /(_ _ _ Hpt H)[] /(_ _ _ _ F).
      * move=>H _ /(_ _ Hpt H)[][] PS';
        do?[by move=>_ /(_ _ _ _ F)];
        do?[by move=>/(_ _ _ _ F)].
        move=>_[] _ /(_ _ _ _ F) /andP[] /eqP ? /eqP ?. subst.
        move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
        move: (pt_state_functional V PS PS')=>[][] ? ? ?. subst.
        done.
  - move=>[nd][][l1][] _ _ _ /(_ _ Hpt); case: ifP=>_ []; (try case); (try case);
    do?[by move=>_ /(_ _ _ _ F)];
    do?[by move=>/(_ _ _ _ F)];
    move=> PS' [] _ /(_ _ _ _ F) /andP[] /eqP ? /eqP ? _; subst;
    move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
    move: (pt_state_functional V PS PS')=>[][] ? ? ?; subst; done.
Qed.

Lemma PhaseOne_msg_next_data d (C : coh d) i m pt round next_data lg  :
  find i (dsoup d) =
    Some {| content := {| tag := prep_req; tms_cont := m |};
            from := cn;
            to := pt;
            active := true |} ->
  internal_msg prep_req cn pt ->
  PhaseOne d round next_data lg ->
  behead m == next_data.
Proof.
  move=>F /internal_msg_from_cn /and3P[] _ Hpt _ [].
  - move=>[sent][] CS U S /(_ pt Hpt).
    case: ifP=>_ [][] PS;
        do?[by move=>_ /(_ _ _ _ F)];
        do?[by move=>/(_ _ _ _ F)].
    by move=>_ [] _ /(_ _ _ _ F)/andP [] _ /eqP ->.
  - move=>[recvd][] CS U S.
    case: (in_map_exists pt recvd).
    + by move=>[b] H /(_ _ _ Hpt H) [] /(_ _ _ _ F).
    + move=>H _ /(_ _ Hpt H) [][] _;
        do?[by move=>/(_ _ _ _ F)];
        do?[by move=>_ /(_ _ _ _ F)].
      by move=> _ [] _ /(_ _ _ _ F) /andP[] _ /eqP->.
Qed.


Lemma cn_state_functional d cs1 lg1 cs2 lg2 :
  valid (loc cn d) ->
  cn_state d cs1 lg1 ->
  cn_state d cs2 lg2 ->
  cs1 = cs2 /\ lg1 = lg2.
Proof.
  move=>V.
  rewrite/cn_state=> H.
  move: V.
  rewrite H => V.
  move /(hcancelV V) => [] ?. subst.
  move=> V1.
  by move /(hcancelPtV V1)=>->.
Qed.


Lemma pt_log_agreement d r lg pt :
  coh d ->
  pt \in pts ->
  pt_state d (r, PInit) lg pt ->
  Inv d ->
  forall pt' ps' r' lg',
    pt' \in pts ->
    pt_state d (r', ps') lg' pt' ->
    r' = r ->
    lg' = lg.
Proof.
move=>C Hpt PS [r0][lg0].
move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt)) [] V _.
case.
- move=>[] CS.
  move=>Pts pt' ps' r' lg' Hpt' PS'.
  move: (Pts pt Hpt)=>[].
  move /(pt_state_functional V PS)=>[][] ? ? _ _. subst.
  move: (Pts pt' Hpt')=>[].
  move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _.
  move /(pt_state_functional V' PS') =>[][] ? ? ? _.
  by subst.
- move=>[nd][[sent]|[recvd]][] _ _ _.
  + move=>Pts pt' ps' r' lg' Hpt' PS'.
    move: (Pts pt Hpt); case: ifP=>_[][];
    move /(pt_state_functional V PS)=>[]; try discriminate;
    move=>[] ? ? _ _; subst;
    move: (Pts pt' Hpt'); case: ifP=>_ [][]=>//;
    move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _;
    move /(pt_state_functional V' PS') =>[][] ? ? ? _; by subst.
  + move=>Hrecvd1 Hrecvd2.
    case: (in_map_exists pt recvd).
    * move=>[b] H.
      case: (Hrecvd1 _ _ Hpt H) => _ _.
      case: ifP=>_;
      move /(pt_state_functional V PS)=>[]; discriminate.
    * move=>H.
      case: (Hrecvd2 _ Hpt H)=>[][];
      move /(pt_state_functional V PS)=>[]; try discriminate.
      case=> ? ?. subst.
      move=> _ _ pt' ps' r' lg' Hpt' PS'.
      case: (in_map_exists pt' recvd).
      -- move=>[b] H'.
         move: (Hrecvd1 _ _ Hpt' H')=>[]; case: ifP=> _ _ _;
         move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _;
         move /(pt_state_functional V' PS') =>[][] ? ? ? _; by subst.
      -- move=>H'.
         case: (Hrecvd2 _ Hpt' H')=>[][];
         move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _;
         move /(pt_state_functional V' PS') =>[][] ? ? ? _; by subst.
- move=>[nd][[sent]|[sent]|[recvd]|[recvd]][] _ _ _ Pts;
  move: (Pts _ Hpt); case: ifP=>_ []; (try case); (try case); intros H1 H2 H3;
  match goal with
  | [ H : pt_state _ _ _ pt |- _ ] =>
    move: H =>/(pt_state_functional V PS)[]; try discriminate
  end;
  case=> ? ?; subst;
  move=> pt' ps' r' lg' Hpt' PS';
  move: (Pts _ Hpt'); case: ifP=>_[]; (try case); (try case); intros H4 H5 H6;
  move: (C)=>[] _ _ _ /(_ _ (pts_in _ _ Hpt')) [] V' _;
  match goal with
  | [ H : pt_state _ _ _ _ |- _ ] =>
    move: H =>/(pt_state_functional V' PS')[]; try discriminate
  end; case; intros; subst; auto; try omega.
Qed.

Lemma cn_log_agreement d r lg pt :
  coh d ->
  cn_state d (r, CInit) lg ->
  Inv d ->
  pt \in pts ->
  pt_state d (r, PInit) lg pt.
Proof.
move=>C CS [r'][lg'].
move: C=>[] _ _ _ /(_ _ (cn_in _ _ _)) [] V _.
case.
- move=>[].
  move /(cn_state_functional V CS)=>[][] ? ?. subst.
  move=>H Hpt.
  by move: (H pt Hpt)=>[].
- move=>[nd][[sent]|[recvd]][];
  move /(cn_state_functional V CS)=>[]; discriminate.
- move=>[nd][[sent]|[sent]|[recvd]|[recvd]][];
  move /(cn_state_functional V CS)=>[]; discriminate.
Qed.

(* End TwoPhaseInductiveInv. *)

(* Module Exports. *)
(* Section Exports. *)

(* Definition tpc_with_inv := tpc_with_inv. *)
(* Definition tpc_inv := Inv. *)
(* Definition tpc_ii := ii. *)

(* End Exports. *)
(* End Exports. *)

End TwoPhaseInductiveInv.

(* Export TwoPhaseInductiveInv.Exports. *)

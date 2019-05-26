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
Require Import TwoPhaseProtocol TwoPhaseInductiveInv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section TwoPhaseInductiveProof.

Variable l : Label.
Variables (cn : nid) (pts : seq nid) (others : seq nid).
Hypothesis Hnin : cn \notin pts.
Hypothesis PtsNonEmpty : pts != [::].

Definition tpc := TwoPhaseCommitProtocol others Hnin l.

(* Take the transitions *)
Notation sts := (snd_trans tpc).
Notation rts := (rcv_trans tpc).

Notation loc z d := (getLocal z d).

Notation Sinv := (@S_inv tpc (fun d _ => Inv cn pts d)).
Notation Rinv := (@R_inv tpc (fun d _ => Inv cn pts d)).
Notation coh d := (coh tpc d).
Notation PI := pf_irr.

Export TPCProtocol.

(*************************************************************)
(*                  Send-transitions                         *)
(*************************************************************)

(*** [Coordinator] Send prepare-request ***)

Program Definition s1: Sinv (cn_send_prep_trans cn pts others).
Proof.
move=>this to d msg S h/= Hi/=[]T G.
case: (S)=>[][/eqP]Z H1[C]; subst this.
case=>[[e[E1][dt]Z']|[e][dt][ps][E1]Z']; subst msg;
rewrite (PI (cn_safe_coh _) C) E1 in T.

(* We're in the global Init state *)
case: (@inv_init l cn pts others Hnin d e _ Hi E1)=>lg{Hi E1}[E1]H2.
rewrite (PI (cn_this_in _ _) (cn_in _ _ _))
        (getStL_Kc C (cn_in _ _ _) E1) in T; subst h=>/=.
exists e, lg; constructor 2; exists dt.
have Y: {subset [::to] <= pts} by move=>z; rewrite inE=>/eqP->.
case X: (pts == [::to]); [right; exists [::]|left; exists [::to]];
split=>//=; do?[by rewrite /cn_state locE'?(cohVl C)///cstep_send H1 X];
move=>pt Hp.
(* TODO: Factor this out *)
- move/eqP: X=>Z; rewrite Z inE in Hp; move/eqP: Hp=>Hp _; subst pt.
  constructor 1=>/=; simpl in G. case/H2: (H1)=>H1' H1''.
  split=>//; rewrite /pt_state//; last first.
  apply: msg_specE; rewrite ?(cohVs C)//.
  apply: no_msg_from_toE'; rewrite ?(cohVs C)//.
  + by move: (this_not_pts Hnin H1); rewrite eq_sym.
  by rewrite (G _ (this_not_pts Hnin H1)); rewrite /pt_state in H1'.
- case: ifP.
  rewrite inE=>/eqP=>Z; subst pt.
  constructor 1=>/=; simpl in G; case/H2: (H1)=>H1' H1''.
  split=>//; rewrite /pt_state//; last first.
  apply: msg_specE; rewrite ?(cohVs C)//.
  apply: no_msg_from_toE'; rewrite ?(cohVs C)//.
  + by move: (this_not_pts Hnin H1); rewrite eq_sym.
  by move:(this_not_pts Hnin H1)=>/G->; rewrite/pt_state in H1'.
- rewrite /pt_Init.
  move=>N/=;simpl in G; case/H2: (Hp)=>H1' H1''; rewrite/pt_state/=.
  move: (this_not_pts Hnin Hp)=>Hp'; rewrite (G _ Hp'); split=>//.
  - apply: no_msg_from_toE'; rewrite ?(cohVs C)//.
    by move: (this_not_pts Hnin Hp); rewrite eq_sym.
  apply: no_msg_from_toE; rewrite ?(cohVs C)//.
  by apply/negbTE/negP=>/eqP Z; subst to; rewrite inE eqxx in N.

(* Now we're in a state, when the coordinator is in the
   CSentPrep position. Repeat the same pattern. *)
case: (@inv_prep_send l cn pts others Hnin d e _ _ _ Hi E1).
move=> lg{Hi}[ps'][E1']H2 H3 H4 H5.
rewrite (PI (cn_this_in _ _) (cn_in _ _ _))
        (getStL_Kc C (cn_in _ _ _) E1') in T; subst h=>/=.
rewrite (getStC_K C E1') in E1; case: E1=>Z; subst ps'.
exists e, lg; constructor 2; simpl in G; exists dt.
case X: (perm_eq (to :: ps) pts);
  [right; exists [::]|left; exists (to::ps)]=>/=;
split; do?[by rewrite /cn_state locE'?(cohVl C)///cstep_send H1 X]=>//;
[move=>pt Hp _| move=>/=; by rewrite H5| |move=>pt Hp]; first 1 last.

- move=>z; rewrite inE=>/orP[];[by move/eqP=>->|by apply: H3].
- case: ifP; last first.
  + rewrite inE=>/Bool.orb_false_iff[Z1]Z2.
    move: (H4 _ Hp); rewrite Z2; move=>[G1 G2].
    split; first by move:(this_not_pts Hnin Hp)=>/G; rewrite /pt_state=>->.
    - apply: no_msg_from_toE'; rewrite ?(cohVs C)//.
      by move: (this_not_pts Hnin Hp); rewrite eq_sym.
  by apply: no_msg_from_toE; rewrite ?(cohVs C)//.

- rewrite inE=>/orP[].
  move/eqP=>Z;subst to.
  move: (H4 _ Hp); move/negbTE: H5->; case=>G1 G2 G3.
  constructor 1=>/=; split=>//; last 2 first.
  + apply:no_msg_from_toE'=>//;
  rewrite ?(cohVs C)//; move:(this_not_pts Hnin Hp).
  by rewrite eq_sym.
- by apply:msg_specE;rewrite ?(cohVs C)//.
  move:(this_not_pts Hnin Hp)=>/G; rewrite /pt_state=>->.
  by rewrite /pt_state.

- move=>Z; move: (H4 _ Hp); rewrite Z.
  have Z1: pt == to = false.
  + by apply/negbTE/negP=>/eqP=>Z1; subst to; rewrite Z in H5.
  by apply:(@pt_PhaseOneE l cn pts others Hnin d e dt lg pt to _ _ C Hp Z1 G).

case Z1: (pt == to); last first.
- move/perm_eq_mem: X=>/(_ pt); rewrite inE Z1/= Hp=>Z.
  move: (H4 _ Hp); rewrite Z.
  by apply:(@pt_PhaseOneE l cn pts others Hnin d e dt lg pt to _ _ C Hp Z1 G).
move/eqP:Z1=>Z1; subst to.
move: (H4 _ H1); rewrite (negbTE H5); case=>G1 G2.
constructor 1=>/=; split=>//; last 2 first.
- apply:no_msg_from_toE'=>//;
  rewrite ?(cohVs C)//; move: (this_not_pts Hnin Hp).
  by rewrite eq_sym.
- by apply:msg_specE;rewrite ?(cohVs C)//.
move:(this_not_pts Hnin Hp)=>/G; rewrite /pt_state=>->.
by rewrite /pt_state.
Qed.

(*** [Coordinator] Send commit-request ***)

Program Definition s2: Sinv (cn_send_commit_trans cn pts others).
Proof.
move=>this to d msg S h/= Hi/=[]T G.
case: (S)=>[][/eqP]Z Hto[C]; subst this.

move=>[[round][next_data][recvd]|[round][next_data][sent]].
- move=>[St M P A]. subst msg.
  rewrite (PI (cn_safe_coh _) C) St in T.
  case: (@inv_waitprep l cn pts others Hnin _ round C next_data recvd Hi St) =>lg.
  move=>[] Hst Huniq Hsub Hrecvd1 Hrecvd2.
  exists round, lg. constructor 3.
  exists next_data.
  rewrite (getStL_Kc C _ Hst) /cstep_send Hto P A in T.
  case X: (pts == [::to]);
    [constructor 3; exists [::]|constructor 1; exists [:: to]];
    rewrite X in T; subst h; split=>//;
    do?[by rewrite /cn_state locE' ?(cohVl C)//]; first 1 last.
  + by move=>x; rewrite inE => /eqP->.
  + move=>pt Hpt.
    case: ifP; rewrite inE.
    * move=>/eqP ?; subst pt.
      have Htorecv: (to, true) \in recvd by apply (has_all_true P A).
      case: (Hrecvd1 _ _ Hpt Htorecv) => M1 M2 PS.
      constructor 1; split.
      by move: PS; rewrite /pt_state (G _ (this_not_pts Hnin Hpt)).
      by apply: msg_specE; rewrite ?(cohVs C).
      by apply: (no_msg_from_toE' (cohVs C))=>//;
         rewrite eq_sym (this_not_pts Hnin Hto).
    * move=> Npt.
      have Hptrecvd: (pt, true) \in recvd by apply (has_all_true P A).
      move: (Hrecvd1 _ _ Hpt Hptrecvd).
      by apply: (@pt_PhaseOneRespondedE l cn pts others Hnin).
  + move=>pt Hpt.
    rewrite in_nil.
    move/eqP in X.
    rewrite X inE in Hpt.
    move /eqP in Hpt. subst pt.
    have Htorecv: (to, true) \in recvd by apply (has_all_true P A).
    case: (Hrecvd1 _ _ Hto Htorecv) => M1 M2 PS.
    constructor 1; split.
    by move: PS; rewrite /pt_state (G _ (this_not_pts Hnin Hto)).
    by apply: msg_specE; rewrite ?(cohVs C).
    by apply: (no_msg_from_toE' (cohVs C))=>//;
         rewrite eq_sym (this_not_pts Hnin Hto).
- move=>[St ? HtoNsent]. subst msg.
  rewrite (PI (cn_safe_coh _) C) St in T.
  case: (@inv_sentcommit l cn pts others Hnin _ round C next_data sent Hi St) =>lg.
  case => Hst Huniq Hsub Hsent.
  exists round, lg. constructor 3.
  exists next_data.
  rewrite (getStL_Kc C _ Hst) /cstep_send Hto in T.
  case X: (perm_eq (to :: sent) pts); subst h; rewrite X; rewrite X in G.
  + constructor 3. exists [::].
    split=>//.
    by rewrite /cn_state locE' ?(cohVl C).
    move=>pt Hpt.
    rewrite in_nil.
    move/perm_eq_mem: X=>/(_ pt); rewrite inE Hpt.
    case/orP.
    * move/eqP=>?; subst pt.
      move: (Hsent to Hto).
      move: HtoNsent => /negbTE->.
      case=> M1 M2 PS.
      constructor 1; split.
      by move: PS; rewrite /pt_state (G _ (this_not_pts Hnin Hto)).
      by apply: msg_specE; rewrite ?(cohVs C).
      by apply: (no_msg_from_toE' (cohVs C))=>//;
         rewrite eq_sym (this_not_pts Hnin Hto).
    * move=> Hptsent.
      move: (Hsent _ Hpt).
      rewrite Hptsent.
      apply: (@pt_PhaseTwoCommitE l cn pts others Hnin)=>//.
      apply/negP. move=>/eqP ?; subst pt.
      move/negbTE in HtoNsent.
      congruence.
  + constructor 1. exists (to :: sent).
    split.
    * by rewrite /cn_state locE' ?(cohVl C).
    * by rewrite cons_uniq Huniq andbT.
    * by rewrite /sub_mem => x; rewrite in_cons => /orP[/eqP->|/Hsub].
    * move=>pt Hpt.
      rewrite in_cons.
      case: ifP.
      case/orP.
      -- move/eqP=>?; subst pt.
         move: (Hsent to Hto).
         move: HtoNsent => /negbTE->.
         case=> M1 M2 PS.
         constructor 1; split.
         by move: PS; rewrite /pt_state (G _ (this_not_pts Hnin Hto)).
         by apply: msg_specE; rewrite ?(cohVs C).
         by apply: (no_msg_from_toE' (cohVs C))=>//;
                   rewrite eq_sym (this_not_pts Hnin Hto).
      -- move=> Hptsent.
         move: (Hsent _ Hpt).
         rewrite Hptsent.
         apply: (@pt_PhaseTwoCommitE l cn pts others Hnin)=>//.
         apply/negP. move=>/eqP ?. subst pt.
         move/negbTE in HtoNsent.
         congruence.
      -- move/Bool.orb_false_elim=>[N] HptNsent.
         move: (Hsent pt Hpt).
         rewrite HptNsent.
         by apply: (@pt_PhaseOneRespondedE l cn pts others Hnin).
Qed.

(*** [Coordinator] Send abort-request ***)

Program Definition s3: Sinv (cn_send_abort_trans cn pts others).
Proof.
move=>this to d msg S h/= Hi/=[]T G.
case: (S)=>[][/eqP]Z Hto[C]; subst this.

move=>[[round][next_data][recvd]|[round][next_data][sent]].

- move=>[St M P A]. subst msg.
  rewrite has_predC in A; move/negbTE: A=>A.
  rewrite (PI (cn_safe_coh _) C) St in T.
  case: (@inv_waitprep l cn pts others Hnin _ round C next_data recvd Hi St) =>lg.
  move=>[] Hst Huniq Hsub Hrecvd1 Hrecvd2.
  exists round, lg; constructor 3.
  exists next_data.
  rewrite (getStL_Kc C _ Hst) /cstep_send Hto P A in T.
  case X: (pts == [::to]);
    [constructor 4; exists [::]|constructor 2; exists [:: to]];
    rewrite X in T; subst h; split=>//;
    do?[by rewrite /cn_state locE' ?(cohVl C)//]; first 1 last.
  + by move=>x; rewrite inE => /eqP->.
  + move=>pt Hpt.
    case: ifP; rewrite inE.
    * move=>/eqP ?; subst pt.
      have Htorecv: exists b, (to, b) \in recvd
           by apply: (has_some_false P Hpt).
      case: Htorecv=>b Htorecv.
      case: (Hrecvd1 _ _ Hpt Htorecv) => M1 M2 PS.
      constructor 1; split=>/={Htorecv}.
      by case: b PS; rewrite /pt_state (G _ (this_not_pts Hnin Hpt));
         [left | right].
      by apply: msg_specE; rewrite ?(cohVs C).
      by apply: (no_msg_from_toE' (cohVs C))=>//;
         rewrite eq_sym (this_not_pts Hnin Hto).
    * move=> Npt.
      have Htorecv: exists b, (pt, b) \in recvd
          by apply: (has_some_false P Hpt).
      case: Htorecv=>b Htorecv/=; exists b.
      apply: (@pt_PhaseOneRespondedE l cn pts others Hnin)=>//.
      by apply: (Hrecvd1 pt _ _ Htorecv).
  + move=>pt Hpt.
    rewrite in_nil.
    move/eqP in X.
    rewrite X inE in Hpt.
    move /eqP in Hpt. subst pt.
    have Htorecv: exists b, (to, b) \in recvd
        by apply: (has_some_false P Hto).
    case: Htorecv=>b Htorecv.
    case: (Hrecvd1 _ _ Hto Htorecv) => M1 M2 PS {Htorecv}.
    constructor 1; split.
    by case: b PS; rewrite /pt_state (G _ (this_not_pts Hnin Hto));
       [left | right].
    by apply: msg_specE; rewrite ?(cohVs C).
    by apply: (no_msg_from_toE' (cohVs C))=>//;
         rewrite eq_sym (this_not_pts Hnin Hto).
- move=>[St ? HtoNsent]. subst msg.
  rewrite (PI (cn_safe_coh _) C) St in T.
  case: (@inv_sentabort l cn pts others Hnin _ round C next_data sent Hi St) =>lg.
  case => Hst Huniq Hsub Hsent.
  exists round, lg. constructor 3.
  exists next_data.
  rewrite (getStL_Kc C _ Hst) /cstep_send Hto in T.
  case X: (perm_eq (to :: sent) pts); subst h; rewrite X; rewrite X in G.
  + constructor 4; exists [::].
    split=>//.
    by rewrite /cn_state locE' ?(cohVl C).
    move=>pt Hpt.
    rewrite in_nil.
    move/perm_eq_mem: X=>/(_ pt); rewrite inE Hpt.
    case/orP.
    * move/eqP=>?; subst pt.
      move: (Hsent to Hto).
      move: HtoNsent => /negbTE->.
      case=>b [M1] M2 PS.
      constructor 1; split.
      by case: b PS; rewrite /pt_state (G _ (this_not_pts Hnin Hto)); [left|right].
      by apply: msg_specE; rewrite ?(cohVs C).
      by apply: (no_msg_from_toE' (cohVs C))=>//;
         rewrite eq_sym (this_not_pts Hnin Hto).
    * move=> Hptsent.
      move: (Hsent _ Hpt).
      rewrite Hptsent.
      apply: (@pt_PhaseTwoAbortE l cn pts others Hnin)=>//.
      apply/negP. move=>/eqP ?. subst pt.
      move/negbTE in HtoNsent.
      congruence.
  + constructor 2. exists (to :: sent).
    split.
    * by rewrite /cn_state locE' ?(cohVl C).
    * by rewrite cons_uniq Huniq andbT.
    * by rewrite /sub_mem => x; rewrite in_cons => /orP[/eqP->|/Hsub].
    * move=>pt Hpt.
      rewrite in_cons.
      case: ifP.
      case/orP.
      -- move/eqP=>?; subst pt.
         move: (Hsent to Hto).
         move: HtoNsent => /negbTE->.
         case=>b[M1] M2 PS.
         constructor 1; split.
         by case: b PS; rewrite /pt_state (G _ (this_not_pts Hnin Hto));
            [left|right].
         by apply: msg_specE; rewrite ?(cohVs C).
         by apply: (no_msg_from_toE' (cohVs C))=>//;
                   rewrite eq_sym (this_not_pts Hnin Hto).
      -- move=> Hptsent.
         move: (Hsent _ Hpt).
         rewrite Hptsent.
         apply: (@pt_PhaseTwoAbortE l cn pts others Hnin)=>//.
         apply/negP. move=>/eqP ?. subst pt.
         move/negbTE in HtoNsent.
         congruence.
      -- move/Bool.orb_false_elim=>[N] HptNsent.
         move: (Hsent pt Hpt).
         rewrite HptNsent; case=>b H; exists b.
         by apply: (@pt_PhaseOneRespondedE l cn pts others Hnin).
Qed.

(*** [Pariticpant] Send yes ***)

Program Definition s4: Sinv (pn_send_yes_trans others Hnin).
Proof.
move=>this to d m S h I [] T G.
case: (S)=>[][] Hthis /eqP ? [H][C] [r][nd][PS] ?. subst to m.
have Vl := cohVl C.
have Vs := cohVs C.
move: (inv_gotrequest(l:=l) Hthis PS I)=> [lg]PO.
move: (PhaseOne_round_pt Hthis PO) => [ps] PS'.
move: PS.
rewrite (getStP_K Hnin C _ Hthis PS').
case=>?. subst ps.
move: PS'=>PS.
exists r, lg.
constructor 2.
exists nd.
move: (PhaseOne_PGotRequest_next_data_pt(l:=l)(Hnin:=Hnin) C Hthis PS PO) =>[]_ NM1 NM2.
case: PO=>[[sent]|[recvd]].
- case=>CS' U Sub Pts.
  left. exists sent.
  split=>//.
  + apply /(cn_state_soupE(Hnin := Hnin) _ _ C)=>//.
    by apply: (pt_not_cn Hnin).
  + move=>pt Hpt.
    move: (Pts _ Hpt).
    case E: (this == pt).
    + move/eqP in E. subst pt.
      case: ifP.
      * move=>_ _.
        constructor 3.
        split.
        -- rewrite /pt_state locE'//. subst.
           by rewrite (getStP_K Hnin _ _ Hthis PS)
                      (getStL_Kp _ _ PS).
        -- apply /no_msg_from_toE'=>//.
           by apply/negbTE/(pt_not_cn Hnin).
        -- by apply /msg_specE.
      * move=>_ [] PS'.
        move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
        move: (pt_state_functional V PS PS')=>[]; discriminate.
    + move/negbT in E.
      case: ifP.
      * move=>_.
        apply: (pt_PhaseOneE' _ _ _ C)=>//.
        by apply/(pt_not_cn Hnin).
      * move=>_.
        apply: (pt_InitE _ _ _ C)=>//.
        by apply/(pt_not_cn Hnin).
- case=>CS' U Sub Hrecvd1 Hrecvd2.
  right. exists recvd.
  split=>//.
  + apply /(cn_state_soupE _ _ C)=>//.
    by apply: (pt_not_cn Hnin).
  + move=>pt b Hpt Hr.
    case E: (this == pt).
    * move/eqP in E. subst pt.
      exfalso.
      case: (Hrecvd1 _ _ Hpt Hr)=> _ _.
      case: ifP=>_ PS';
        move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
        move: (pt_state_functional V PS PS')=>[]; discriminate.
    * move: (Hrecvd1 pt b Hpt Hr).
      apply: (pt_PhaseOneRespondedE' _ _ _ C)=>//.
      by apply /negbT.
      by apply: (pt_not_cn Hnin).
  + move=>pt Hpt Hr.
    case E: (this == pt).
    * move/eqP in E. subst pt.
      constructor 3.
      split.
      -- rewrite /pt_state locE'//. subst.
           by rewrite (getStP_K Hnin _ _ Hthis PS)
                      (getStL_Kp _ _ PS).
      -- apply /no_msg_from_toE'=>//.
         by apply /negbTE/(pt_not_cn Hnin).
      -- by apply msg_specE=>//.
    * move: (Hrecvd2 pt Hpt Hr).
      apply: (pt_PhaseOneE' _ _ _ C)=>//.
      by apply /negbT.
      by apply: (pt_not_cn Hnin).
Qed.

(*** [Pariticpant] Send no ***)

Program Definition s5: Sinv (pn_send_no_trans others Hnin).
Proof.
move=>this to d m S h I [] T G.
case: (S)=>[][] Hthis /eqP ? [H][C] [r][nd][PS] ?. subst to m.
have Vl := cohVl C.
have Vs := cohVs C.
move: (inv_gotrequest(l := l) Hthis PS I)=> [lg]PO.
move: (PhaseOne_round_pt Hthis PO) => [ps] PS'.
move: PS.
rewrite (getStP_K Hnin C _ Hthis PS').
case=>?. subst ps.
move: PS'=>PS.
exists r, lg.
constructor 2.
exists nd.
move: (PhaseOne_PGotRequest_next_data_pt(l:=l)(Hnin:=Hnin) C Hthis PS PO) =>[]_ NM1 NM2.
case: PO=>[[sent]|[recvd]].
- case=>CS' U Sub Pts.
  left. exists sent.
  split=>//.
  + apply /(cn_state_soupE _ _ C)=>//.
    by apply: (pt_not_cn Hnin).
  + move=>pt Hpt.
    move: (Pts _ Hpt).
    case E: (this == pt).
    + move/eqP in E. subst pt.
      case: ifP.
      * move=>_ _.
        constructor 4.
        split.
        -- rewrite /pt_state locE'//. subst.
           by rewrite (getStP_K Hnin _ _ Hthis PS)
                      (getStL_Kp _ _ PS).
        -- apply /no_msg_from_toE'=>//.
           by apply/negbTE/(pt_not_cn Hnin).
        -- by apply /msg_specE.
      * move=>_ [] PS'.
        move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
        move: (pt_state_functional V PS PS')=>[]; discriminate.
    + move/negbT in E.
      case: ifP.
      * move=>_.
        apply: (pt_PhaseOneE' _ _ _ C)=>//.
        by apply/(pt_not_cn Hnin).
      * move=>_.
        apply: (pt_InitE _ _ _ C)=>//.
        by apply/(pt_not_cn Hnin).
- case=>CS' U Sub Hrecvd1 Hrecvd2.
  right. exists recvd.
  split=>//.
  + apply /(cn_state_soupE _ _ C)=>//.
    by apply: (pt_not_cn Hnin).
  + move=>pt b Hpt Hr.
    case E: (this == pt).
    * move/eqP in E. subst pt.
      exfalso.
      case: (Hrecvd1 _ _ Hpt Hr)=> _ _.
      case: ifP=>_ PS';
        move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
        move: (pt_state_functional V PS PS')=>[]; discriminate.
    * move: (Hrecvd1 pt b Hpt Hr).
      apply: (pt_PhaseOneRespondedE' _ _ _ C)=>//.
      by apply /negbT.
      by apply: (pt_not_cn Hnin).
  + move=>pt Hpt Hr.
    case E: (this == pt).
    * move/eqP in E. subst pt.
      constructor 4.
      split.
      -- rewrite /pt_state locE'//. subst.
           by rewrite (getStP_K Hnin _ _ Hthis PS)
                      (getStL_Kp _ _ PS).
      -- apply /no_msg_from_toE'=>//.
         by apply /negbTE/(pt_not_cn Hnin).
      -- by apply msg_specE=>//.
    * move: (Hrecvd2 pt Hpt Hr).
      apply: (pt_PhaseOneE' _ _ _ C)=>//.
      by apply /negbT.
      by apply: (pt_not_cn Hnin).
Qed.

(*** [Pariticpant] Send commit-ack ***)

Program Definition s6: Sinv (pn_commit_ack_trans others Hnin).
Proof.
move=>this to d m S h I [] T G.
case: (S)=>[][] Hthis /eqP ? [H][C] [r][nd][PS] ?. subst to m.
have Vl := cohVl C.
have Vs := cohVs C.

move: (inv_committed(l:=l) Hthis PS I)=> [lg] PT.
case: (PhaseTwo_PCommitted_pt(l := l)(Hnin := Hnin) Hthis PS PT)=>{PS}PS NM1 NM2.
exists r, lg.
constructor 3.
exists nd.
have: this != cn by apply: (pt_not_cn Hnin).
case: PT=>[[sent]|[sent]|[recvd]|[recvd]] {I}I;
  [constructor 1; exists sent|constructor 2; exists sent|
   constructor 3; exists recvd|constructor 4; exists recvd];
case: I=> CS U S' Pts; split=>//;
do?[by apply /(cn_state_soupE _ _ C)=>//];
move=> pt Hpt; move: (Pts pt Hpt); case: ifP=>_.
- case E: (this == pt).
  + move/eqP in E. subst pt.
    move=>_.
    constructor 3.
    split.
    * by rewrite /pt_state locE'// T
              (getStP_K _ _ _ _ PS)//
              (getStL_Kp _ _ PS).
    * apply /no_msg_from_toE'=>//.
      by apply: negbTE.
    * by apply: msg_specE=>//.
  + move/negbT in E.
    by apply: (pt_PhaseTwoCommitE' _ _ _ C)=>//.
- move=>H1.
  apply: (pt_PhaseOneRespondedE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1 => _ _ PS'.
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- move=>H1.
  apply: (pt_PhaseTwoAbortE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1 => [][][]PS' _ _;
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- move=>[b] H1.
  exists b.
  apply: (pt_PhaseOneRespondedE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1 => _ _; case: ifP=>_ PS';
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- move=>H1.
  apply: (pt_PhaseTwoRespondedE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1=> PS' _ _;
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- case E: (this == pt).
  + move/eqP in E. subst pt.
    move=>_.
    constructor 3.
    split.
    * by rewrite /pt_state locE'// T
              (getStP_K _ _ _ _ PS)//
              (getStL_Kp _ _ PS).
    * apply /no_msg_from_toE'=>//.
      by apply: negbTE.
    * by apply: msg_specE=>//.
  + move/negbT in E.
    by apply: (pt_PhaseTwoCommitE' _ _ _ C)=>//.
- move=>H1.
  apply: (pt_PhaseTwoRespondedE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1=> PS' _ _;
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- move=>H1.
  apply: (pt_PhaseTwoAbortE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1 => [][][]PS' _ _;
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
Qed.

(*** [Pariticpant] Send abort-ack ***)

Program Definition s7: Sinv (pn_abort_ack_trans others Hnin).
Proof.
move=>this to d m S h I [] T G.
case: (S)=>[][] Hthis /eqP ? [H][C] [r][nd][PS] ?. subst to m.
have Vl := cohVl C.
have Vs := cohVs C.

move: (inv_aborted(l:=l) Hthis PS I)=> [lg] PT.
case: (PhaseTwo_PAborted_pt(l:=l)(Hnin:=Hnin) Hthis PS PT)=>{PS}PS NM1 NM2.
exists r, lg.
constructor 3.
exists nd.
have: this != cn by apply: (pt_not_cn Hnin).
case: PT=>[[sent]|[sent]|[recvd]|[recvd]] {I}I;
  [constructor 1; exists sent|constructor 2; exists sent|
   constructor 3; exists recvd|constructor 4; exists recvd];
case: I=> CS U S' Pts; split=>//;
do?[by apply /(cn_state_soupE _ _ C)=>//];
move=> pt Hpt; move: (Pts pt Hpt); case: ifP=>_.
- move=>H1.
  apply: (pt_PhaseTwoCommitE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1 => [][][]PS' _ _;
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- move=>H1.
  apply: (pt_PhaseOneRespondedE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1 => _ _ PS'.
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- case E: (this == pt).
  + move/eqP in E. subst pt.
    move=>_.
    constructor 3.
    split.
    * by rewrite /pt_state locE'// T
              (getStP_K _ _ _ _ PS)//
              (getStL_Kp _ _ PS).
    * apply /no_msg_from_toE'=>//.
      by apply: negbTE.
    * by apply: msg_specE=>//.
  + move/negbT in E.
    by apply: (pt_PhaseTwoAbortE' _ _ _ C)=>//.
- move=>[b] H1.
  exists b.
  apply: (pt_PhaseOneRespondedE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1 => _ _; case: ifP=>_ PS';
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- move=>H1.
  apply: (pt_PhaseTwoRespondedE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1=> PS' _ _;
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- move=>H1.
  apply: (pt_PhaseTwoCommitE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1 => [][][]PS' _ _;
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- move=>H1.
  apply: (pt_PhaseTwoRespondedE' _ _ _ C)=>//.
  case E: (this == pt)=>//.
  move/eqP in E. subst pt.
  case: H1=> PS' _ _;
  move: C=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _;
  move: (pt_state_functional V PS PS')=>[]; discriminate.
- case E: (this == pt).
  + move/eqP in E. subst pt.
    move=>_.
    constructor 3.
    split.
    * by rewrite /pt_state locE'// T
              (getStP_K _ _ _ _ PS)//
              (getStL_Kp _ _ PS).
    * apply /no_msg_from_toE'=>//.
      by apply: negbTE.
    * by apply: msg_specE=>//.
  + move/negbT in E.
    by apply: (pt_PhaseTwoAbortE' _ _ _ C)=>//.
Qed.


(*************************************************************)
(*                  Receive-transitions                      *)
(*************************************************************)

(*** [Coordinator] Receive "yes" ***)

Program Definition r1: Rinv (cn_receive_prep_yes_trans cn pts others).
Proof.
move=>d from this i C [tag m] H1 I F D/= Hmatch Et G.
subst tag.

case Hinternal: (internal_msg cn pts prep_yes from this); first last.
- move /negbT in Hinternal.
  rewrite (rc_step_external _ _ _ F)//.
  by apply /(invE_consume_external C F)=>//.

rewrite /rc_step/cstep_recv.
case CS: (getStC (cn:=cn) (pts:=pts) (others:=others) (d:=d) C) => [round cs].
have Hthis := (internal_msg_tagFromParticipant_to_cn Hinternal erefl).
rewrite Hthis. move/eqP in Hthis. subst this.
have Hfrom := (internal_msg_tagFromParticipant_from_pts Hinternal erefl).
rewrite Hfrom/=.
have Hround := (inv_msg_round F Hinternal I CS).
rewrite Hround/=.

move: Hmatch.
rewrite CS/=.
move=>/c_matches_tag_prep_yes_inv [next_data] [recvd] ?.
subst cs.
move: (CS)=>/inv_waitprep.
move => /(_ I){I} [lg] I.
case: (I) => []Hst U Hsub Hrecvd1 Hrecvd2.
exists round, lg. constructor 2.
exists next_data. right.
case: ifP.
- move => Hignore.
  exists recvd.
  rewrite (getStL_Kc C _ Hst).
  by apply: (@cn_PhaseOneReceive_consume l cn pts others _ _ _ _ _ _ _ _ from); try exact: F.
move /negbT=>Hnew.
exists ((from, true) :: recvd).
split.
- rewrite /cn_state locE'; last by exact: (cohVl C).
  by rewrite (getStL_Kc C _ Hst) eqxx.
- by rewrite cons_uniq /= Hnew.
- by move => x; rewrite inE /=; move=> /orP[/eqP->|]//; exact: Hsub.
- move => pt b Hpt.
  rewrite inE => /orP[].
  + move=>/eqP[] ? ?. subst pt b.
    move: Hnew.
    move /(Hrecvd2 _ Hpt)/(@prep_yes_pt_inv cn _ _ _ _ _ _ _ _ F).
    move /(_ erefl).
    case=>[]PS NM M.
    split=>/=.
    by apply /no_msg_from_to_consume=>//; rewrite (cohVs C).
    clear G.
    by apply: (msg_spec_consume (cohVs C) F M).
    rewrite /pt_state.
    have HfromN: from != cn.
    * apply /negbT.
      case H: (from == cn)=>//.
      move/eqP in H. subst from.
      by move: (Hnin); rewrite Hpt.
    by rewrite locU// (cohVl C).
  move=>Hr; apply /(@pt_PhaseOneRespondedE_consume l cn pts others _)=>//.
  by apply: (pt_not_cn Hnin).
  by apply Hrecvd1; auto.
- move=>pt Hpt.
  rewrite inE.
  move=>/norP/=[] N Hr.
  apply /(@pt_PhaseOneE_consume l cn pts others _ _ _ _ _ _ _ _ from _)=>//; try exact: F.
  by apply /(pt_not_cn _ Hpt).
  apply /Hrecvd2=>//.
Qed.

(*** [Coordinator] Receive "no" ***)

Program Definition r2: Rinv (cn_receive_prep_no_trans cn pts others).
Proof.
move=>d from this i C [tag m] H1 I F D/= Hmatch Et G.
subst tag.

case Hinternal: (internal_msg cn pts prep_yes from this); first last.
- move /negbT in Hinternal.
  rewrite (rc_step_external _ _ _ F)//.
  by apply /(invE_consume_external C F)=>//.

rewrite /rc_step/cstep_recv.
case CS: (getStC (cn:=cn) (pts:=pts) (others:=others) (d:=d) C) => [round cs].
have Hthis := (internal_msg_tagFromParticipant_to_cn Hinternal erefl).
rewrite Hthis. move/eqP in Hthis. subst this.
have Hfrom := (internal_msg_tagFromParticipant_from_pts Hinternal erefl).
rewrite Hfrom/=.
have Hround := (inv_msg_round F Hinternal I CS).
rewrite Hround/=.

move: Hmatch.
rewrite CS/=.
move=>/c_matches_tag_prep_yes_inv [next_data] [recvd] ?.
subst cs.
move: (CS)=>/inv_waitprep.
move => /(_ I){I} [lg] I.
case: (I) => []Hst U Hsub Hrecvd1 Hrecvd2.
exists round, lg. constructor 2.
exists next_data. right.
case: ifP.
- move => Hignore.
  exists recvd.
  rewrite (getStL_Kc C _ Hst).
  by apply: (@cn_PhaseOneReceive_consume l cn pts others _ _ _ _ _ _ _ _ from _ F).
move /negbT=>Hnew.
exists ((from, false) :: recvd).
split.
- rewrite /cn_state locE'; last by exact: (cohVl C).
  by rewrite (getStL_Kc C _ Hst).
- by rewrite cons_uniq /= Hnew.
- by move => x; rewrite inE /=; move=> /orP[/eqP->|]//; exact: Hsub.
- move => pt b Hpt.
  rewrite inE => /orP[].
  + move=>/eqP[] ? ?. subst pt b.
    move: Hnew.
    move /(Hrecvd2 _ Hpt)/(@prep_no_pt_inv cn _ _ _ _ _ _ _ _ F).
    move /(_ erefl).
    case=>[]PS NM M.
    split=>/=.
    by apply /no_msg_from_to_consume=>//; rewrite (cohVs C).
    clear G.
    by apply: (msg_spec_consume (cohVs C) F M).
    rewrite /pt_state.
    have HfromN: from != cn.
    * apply /negbT.
      case H: (from == cn)=>//.
      move/eqP in H. subst from.
      by move: (Hnin); rewrite Hpt.
    by rewrite locU// (cohVl C).
  move=>Hr; apply /(@pt_PhaseOneRespondedE_consume l cn pts others _)=>//.
  by apply: (pt_not_cn Hnin).
  by apply Hrecvd1; auto.
- move=>pt Hpt.
  rewrite inE.
  move=>/norP/=[] N Hr.
  apply /(pt_PhaseOneE_consume _ C _ _ _ F)=>//.
  by apply /(pt_not_cn Hnin).
  apply /Hrecvd2=>//.
Qed.


(*** [Coordinator] Receive commit-ack ***)

Program Definition r3: Rinv (cn_receive_commit_ack_trans cn pts others).
Proof.
move=>d from this i C [tag m] H1 I F D/= Hmatch Et G.
subst tag.
have Vl := cohVl C.
have Vs := cohVs C.

case Hinternal: (internal_msg cn pts prep_yes from this); first last.
- move /negbT in Hinternal.
  rewrite (rc_step_external _ _ _ F)//.
  by apply /(invE_consume_external C F)=>//.

rewrite /rc_step/cstep_recv.
case CS: (getStC (cn:=cn) (pts:=pts) (others:=others) (d:=d) C) => [round cs].
have Hthis := (internal_msg_tagFromParticipant_to_cn Hinternal erefl).
rewrite Hthis. move/eqP in Hthis. subst this.
have Hfrom := (internal_msg_tagFromParticipant_from_pts Hinternal erefl).
rewrite Hfrom/=.
have Hround := (inv_msg_round F Hinternal I CS).
rewrite Hround/=.

move: Hmatch.
rewrite CS/=.
move=>/c_matches_tag_commit_ack_inv [next_data] [recvd] ?.
subst cs.
move: (CS)=>/inv_waitcommit.
move => /(_ I){I} [lg] I.
case: (I) => [] Hst U Hsub Pts.
case: ifP.
- move => Hignore.
  exfalso.
  move: (Pts _ Hfrom). rewrite Hignore.
  by move=>[] _ _ /(_ _ _ _ F).
move=>/negbT Hr.
case: ifP.
- move=>P.
  exists round.+1, (rcons lg (true, next_data)).
  constructor 1.
  split.
  + rewrite /cn_state locE'//.
    by rewrite (getStL_Kc C _ Hst).
  + move=>pt Hpt.
    move/Pts: (Hpt).
    move: (perm_eq_mem P) => {P}P.
    move: (Hpt).
    rewrite -P inE.
    case/orP.
    * move/eqP=>?. subst pt.
      rewrite (negbTE Hr).
      move/(commit_ack_pt_inv _ F)=>/(_ erefl)[] PS NM M.
      split.
      -- rewrite /pt_state locU//.
         by apply /(@pt_not_cn cn pts Hnin from)=>//.
      -- by apply /(msg_spec_consume _ F M).
      -- by apply /no_msg_from_to_consume=>//.
    * move=>->[] PS NM1 NM2.
      split.
      -- apply /(pt_state_consume _ _ _ C)=>//.
         by apply /(@pt_not_cn cn pts Hnin pt)=>//.
      -- by apply /no_msg_from_to_consume=>//.
      -- by apply /no_msg_from_to_consume=>//.
- move=>P.
  exists round, lg.
  constructor 3.
  exists next_data.
  constructor 3.
  exists (from :: recvd).
  split.
  + rewrite /cn_state locE'//.
    by rewrite (getStL_Kc C _ Hst).
  + by rewrite cons_uniq /= Hr.
  + by move => x; rewrite inE /=; move=> /orP[/eqP->|]//; exact: Hsub.
  + move=> pt Hpt.
    rewrite inE.
    move: (Pts pt Hpt).
    case: ifP.
    * rewrite orbT=>Hr'.
       apply: (pt_PhaseTwoRespondedE_consume(pts:=pts) _ _ C)=>//.
       by apply: (pt_not_cn Hnin).
    * rewrite orbF.
      case: ifP.
      -- move/eqP => ? _. subst pt.
         move/(commit_ack_pt_inv _ F)=>/(_ erefl)[] PS NM M.
         split.
         ++ rewrite /pt_state locU//.
            by apply /(@pt_not_cn cn pts Hnin from)=>//.
         ++ by apply /no_msg_from_to_consume=>//.
         ++ by apply /(msg_spec_consume _ F M).
      -- move=>/negbT N /negbT H.
         apply: (pt_PhaseTwoCommitE_consume _ C _ _ F)=>//.
         by apply: (pt_not_cn Hnin).
Qed.



(*** [Coordinator] Receive abort-ack ***)

Program Definition r4: Rinv (cn_receive_abort_ack_trans cn pts others).
Proof.
move=>d from this i C [tag m] H1 I F D/= Hmatch Et G.
subst tag.
have Vl := cohVl C.
have Vs := cohVs C.

case Hinternal: (internal_msg cn pts prep_yes from this); first last.
- move /negbT in Hinternal.
  rewrite (rc_step_external _ _ _ F)//.
  by apply /(invE_consume_external C F)=>//.

rewrite /rc_step/cstep_recv.
case CS: (getStC (cn:=cn) (pts:=pts) (others:=others) (d:=d) C) => [round cs].
have Hthis := (internal_msg_tagFromParticipant_to_cn Hinternal erefl).
rewrite Hthis. move/eqP in Hthis. subst this.
have Hfrom := (internal_msg_tagFromParticipant_from_pts Hinternal erefl).
rewrite Hfrom/=.
have Hround := (inv_msg_round F Hinternal I CS).
rewrite Hround/=.

move: Hmatch.
rewrite CS/=.
move=>/c_matches_tag_abort_ack_inv [next_data] [recvd] ?.
subst cs.
move: (CS)=>/inv_waitabort.
move => /(_ I){I} [lg] I.
case: (I) => [] Hst U Hsub Pts.
case: ifP.
- move => Hignore.
  exfalso.
  move: (Pts _ Hfrom). rewrite Hignore.
  by move=>[] _ _ /(_ _ _ _ F).
move=>/negbT Hr.
case: ifP.
- move=>P.
  exists round.+1, (rcons lg (false, next_data)).
  constructor 1.
  split.
  + rewrite /cn_state locE'//.
    by rewrite (getStL_Kc C _ Hst).
  + move=>pt Hpt.
    move/Pts: (Hpt).
    move: (perm_eq_mem P) => {P}P.
    move: (Hpt).
    rewrite -P inE.
    case/orP.
    * move/eqP=>?. subst pt.
      rewrite (negbTE Hr).
      move/(abort_ack_pt_inv _ F)=>/(_ erefl)[] PS NM M.
      split.
      -- rewrite /pt_state locU//.
         by apply /(@pt_not_cn cn pts Hnin from)=>//.
      -- by apply /(msg_spec_consume _ F M).
      -- by apply /no_msg_from_to_consume=>//.
    * move=>->[] PS NM1 NM2.
      split.
      -- apply /(pt_state_consume _ _ _ C)=>//.
         by apply /(@pt_not_cn cn pts Hnin pt)=>//.
      -- by apply /no_msg_from_to_consume=>//.
      -- by apply /no_msg_from_to_consume=>//.
- move=>P.
  exists round, lg.
  constructor 3.
  exists next_data.
  constructor 4.
  exists (from :: recvd).
  split.
  + rewrite /cn_state locE'//.
    by rewrite (getStL_Kc C _ Hst).
  + by rewrite cons_uniq /= Hr.
  + by move => x; rewrite inE /=; move=> /orP[/eqP->|]//; exact: Hsub.
  + move=> pt Hpt.
    rewrite inE.
    move: (Pts pt Hpt).
    case: ifP.
    * rewrite orbT=>Hr'.
      apply: (pt_PhaseTwoRespondedE_consume(pts:=pts) _ _ C)=>//.
      by apply: (pt_not_cn Hnin).
    * rewrite orbF.
      case: ifP.
      -- move/eqP => ? _. subst pt.
         move/(abort_ack_pt_inv _ F)=>/(_ erefl)[] PS NM M.
         split.
         ++ rewrite /pt_state locU//.
            by apply /(@pt_not_cn cn pts Hnin from)=>//.
         ++ by apply /no_msg_from_to_consume=>//.
         ++ by apply /(msg_spec_consume _ F M).
      -- move=>/negbT N /negbT H.
         apply: (pt_PhaseTwoAbortE_consume _ C _ _ F)=>//.
         by apply: (pt_not_cn Hnin).
Qed.

(*** [Pariticpant] Receive prep-request ***)

Program Definition r5: Rinv (pn_receive_got_prep_trans others Hnin).
Proof.
move=>d from this i C [tag m] H1 I F D/= _ Et G.
subst tag.
have Vl := cohVl C.
have Vs := cohVs C.

case Hinternal: (internal_msg cn pts prep_req from this); first last.
- move /negbT in Hinternal.
  rewrite (rp_step_external _ _ _ F)//.
  by apply /(invE_consume_external C F)=>//.

rewrite /rp_step/pstep_recv.
case PS: (getStP Hnin C H1) => [round ps].
have Hthis := (internal_msg_tagFromCoordinator_to_pts Hinternal erefl).
rewrite Hthis.
have Hfrom := (internal_msg_tagFromCoordinator_from_cn Hinternal erefl).
rewrite Hfrom/=. move/eqP in Hfrom. subst from.

move: (fun H => prep_req_cn_inv H Hthis F I) => /(_ erefl) [r][lg][nd] PO.
move: (PhaseOne_round_pt Hthis PO)=>[ps'] PS'.
move: PS.
rewrite (getStP_K Hnin C H1 Hthis PS').
case=> ? ?. subst.
move: (PhaseOne_round_cn PO)=>[cs] CS.
move /(getStC_K C) in CS.
have Hround := (inv_msg_round F Hinternal I CS).
rewrite Hround/= !orbF.

have Hmatch := (p_matches_tag_internal_inv C Hthis F Hinternal PS' I).
rewrite Hmatch /=.

move: Hmatch. rewrite /p_matches_tag.
destruct ps=>// _.
exists round, lg.
constructor 2.
exists nd.
move: (PhaseOne_msg_next_data C F Hinternal PO) => /eqP Hnd. subst.
move: PO=>[].
- move=>[sent][] CS' U S Pts.
  left. exists sent. split=>//.
  + apply/(cn_state_consume _ _ _ C)=>//.
    by apply /eqP/nesym/eqP/(pt_not_cn Hnin).
  + move=>pt Hpt.
    move: (Pts _ Hpt).
    case: ifP => _ H.
    * case E: (pt == this).
      -- move /eqP in E. subst pt.
         case/(prep_req_pt_inv F): H=>_ NM M.
         constructor 2.
         split.
         ++ by rewrite/ pt_state locE'// (getStL_Kp C H1 PS').
         ++ by apply /no_msg_from_to_consume.
         ++ by apply /(msg_spec_consume _ F M).
      -- move /negbT in E.
         apply /(pt_PhaseOneE_consume _ C _ _ _ F)=>//.
         by apply: (pt_not_cn Hnin).
    * case E: (pt == this).
      -- move/eqP in E. subst pt.
         case: H => PS NM1 NM2.
         by move: (NM2 _ _ _ F).
      -- move/negbT in E.
         apply /(pt_InitE_consume _ C _ _ _ F)=>//.
         by apply /(pt_not_cn Hnin).
- move=>[recvd][] CS' U S Hrecvd1 Hrecvd2.
  right. exists recvd. split=>//.
  + apply/(cn_state_consume _ _ _ C)=>//.
    by apply /eqP/nesym/eqP/(pt_not_cn Hnin).
  + move=>pt b Hpt Hr.
    case E: (pt == this).
    * move/eqP in E. subst pt.
      case: (Hrecvd1 _ _ Hpt Hr).
      by move=>/(_ _ _ _ F).
    * move/negbT in E.
      apply /(pt_PhaseOneRespondedE_consume _ _ C)=>//.
      by apply: Hrecvd1.
  + move=>pt Hpt Hr.
    move: (Hrecvd2 _ Hpt Hr).
    case E: (pt == this).
    * move/eqP in E. subst pt.
      case/(prep_req_pt_inv F)=>_ NM1 M.
      constructor 2. split.
      ++ by rewrite/ pt_state locE'// (getStL_Kp C H1 PS').
      ++ by apply /no_msg_from_to_consume.
      ++ by apply /(msg_spec_consume _ F M).
    * move/negbT in E.
      apply /(pt_PhaseOneE_consume _ C _ _ _ F)=>//.
      by apply: (pt_not_cn Hnin).
Qed.

(*** [Pariticpant] Receive commit-request ***)

Program Definition r6: Rinv (pn_receive_commit_ack_trans others Hnin).
Proof.
move=>d from this i C [tag m] H1 I F D/= _ Et G.
subst tag.
have Vl := cohVl C.
have Vs := cohVs C.

case Hinternal: (internal_msg cn pts prep_req from this); first last.
- move /negbT in Hinternal.
  rewrite (rp_step_external _ _ _ F)//.
  by apply /(invE_consume_external C F)=>//.

rewrite /rp_step/pstep_recv.
case PS: (getStP Hnin C H1) => [round ps].
have Hthis := (internal_msg_tagFromCoordinator_to_pts Hinternal erefl).
rewrite Hthis.
have Hfrom := (internal_msg_tagFromCoordinator_from_cn Hinternal erefl).
rewrite Hfrom/=. move/eqP in Hfrom. subst from.

move: (fun H => commit_req_cn_inv H Hthis F I) => /(_ erefl) [r][lg][nd] PT.
move: (fun H => PhaseTwoCommit_req_round H Hthis F PT) => /(_ erefl) [ps'] PS'.
move: PS.
rewrite (getStP_K Hnin C H1 Hthis PS').
case=> ? ?. subst.
move: (PhaseTwoCommit_round_cn PT)=>[cs] CS.
move /(getStC_K C) in CS.
have Hround := (inv_msg_round F Hinternal I CS).
rewrite Hround/= !orbF.

have Hmatch := (p_matches_tag_internal_inv C Hthis F Hinternal PS' I).
rewrite Hmatch /=.

move: Hmatch. rewrite /p_matches_tag.
destruct ps=>// _.
exists round, lg.
constructor 3.
exists nd.
move: PT=>[].
- move=>[sent][] CS' U S Pts.
  constructor 1. exists sent.
  split=>//.
  + apply/(cn_state_consume _ _ _ C)=>//.
    by apply /eqP/nesym/eqP/(pt_not_cn Hnin).
  + move=>pt Hpt.
    move: (Pts _ Hpt).
    case: ifP => _ H.
    * case E: (pt == this).
      -- move /eqP in E. subst pt.
         case/(commit_req_pt_inv F): H=>PS'' M NM.
         pose proof C as C'.
         move: C'=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
         move: (pt_state_functional V PS' PS'')=>[][]? ?. subst.
         constructor 2.
         split.
         ++ by rewrite/ pt_state locE'// (getStL_Kp C H1 PS').
         ++ by apply /(msg_spec_consume _ F M).
         ++ by apply /no_msg_from_to_consume.
      -- move /negbT in E.
         apply /(pt_PhaseTwoCommitE_consume _ C _ _ F)=>//.
         by apply: (pt_not_cn Hnin).
    * case E: (pt == this).
      -- move/eqP in E. subst pt.
         case: H => NM1 NM2 PS.
         by move: (NM1 _ _ _ F).
      -- move/negbT in E.
         by apply /(pt_PhaseOneRespondedE_consume _ _ C)=>//.
- move=>[recvd][] CS' U S Pts.
  constructor 3. exists recvd.
  split=>//.
  + apply/(cn_state_consume _ _ _ C)=>//.
    by apply /eqP/nesym/eqP/(pt_not_cn Hnin).
  + move=>pt Hpt.
    move: (Pts _ Hpt).
    case: ifP => _ H.
    * case E: (pt == this).
      -- move/eqP in E. subst pt.
         case: H => PS NM1 NM2.
         by move: (NM1 _ _ _ F).
      -- move/negbT in E.
         by apply /(pt_PhaseTwoRespondedE_consume _ _ C).
    * case E: (pt == this).
      -- move /eqP in E. subst pt.
         case/(commit_req_pt_inv F): H=>PS'' M NM.
         pose proof C as C'.
         move: C'=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
         move: (pt_state_functional V PS' PS'')=>[][]? ?. subst.
         constructor 2.
         split.
         ++ by rewrite/ pt_state locE'// (getStL_Kp C H1 PS').
         ++ by apply /(msg_spec_consume _ F M).
         ++ by apply /no_msg_from_to_consume.
      -- move /negbT in E.
         apply /(pt_PhaseTwoCommitE_consume _ C _ _ F)=>//.
         by apply: (pt_not_cn Hnin).
Qed.


(*** [Pariticpant] Receive abort-request ***)

Program Definition r7: Rinv (pn_receive_abort_ack_trans others Hnin).
Proof.
move=>d from this i C [tag m] H1 I F D/= _ Et G.
subst tag.
have Vl := cohVl C.
have Vs := cohVs C.

case Hinternal: (internal_msg cn pts prep_req from this); first last.
- move /negbT in Hinternal.
  rewrite (rp_step_external _ _ _ F)//.
  by apply /(invE_consume_external C F)=>//.

rewrite /rp_step/pstep_recv.
case PS: (getStP Hnin C H1) => [round ps].
have Hthis := (internal_msg_tagFromCoordinator_to_pts Hinternal erefl).
rewrite Hthis.
have Hfrom := (internal_msg_tagFromCoordinator_from_cn Hinternal erefl).
rewrite Hfrom/=. move/eqP in Hfrom. subst from.

move: (fun H => abort_req_cn_inv H Hthis F I) => /(_ erefl) [r][lg][nd] PT.
move: (fun H => PhaseTwoAbort_req_round H Hthis F PT) => /(_ erefl) [ps'] PS'.
move: PS.
rewrite (getStP_K Hnin C H1 Hthis PS').
case=> ? ?. subst.
move: (PhaseTwoAbort_round_cn PT)=>[cs] CS.
move /(getStC_K C) in CS.
have Hround := (inv_msg_round F Hinternal I CS).
rewrite Hround/= !orbF.

have Hmatch := (p_matches_tag_internal_inv C Hthis F Hinternal PS' I).
rewrite Hmatch /=.

move: Hmatch. rewrite /p_matches_tag.
exists round, lg.
constructor 3.
exists nd.
move: PT=>[].
- move=>[sent][] CS' U S Pts.
  constructor 2. exists sent.
  split=>//.
  + apply/(cn_state_consume _ _ _ C)=>//.
    by apply /eqP/nesym/eqP/(pt_not_cn Hnin).
  + move=>pt Hpt.
    move: (Pts _ Hpt).
    case: ifP => _ H.
    * case E: (pt == this).
      -- move /eqP in E. subst pt.
         case/(abort_req_pt_inv F): H=>PS'' M NM.
         pose proof C as C'.
         move: C'=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
         constructor 2.
         split.
         ++ rewrite/ pt_state locE'// (getStL_Kp C H1 PS').
            move: Hmatch. destruct ps=>//;
            (case: PS''=>PS'';
            move: (pt_state_functional V PS' PS'')=>[]); try discriminate;
            by move => [] ? ?; subst.
         ++ by apply /(msg_spec_consume _ F M).
         ++ by apply /no_msg_from_to_consume.
      -- move /negbT in E.
         apply /(pt_PhaseTwoAbortE_consume _ C _ _ F)=>//.
         by apply: (pt_not_cn Hnin).
    * move: H => [b] H.
      exists b.
      case E: (pt == this).
      -- move/eqP in E. subst pt.
         case: H => NM1 NM2 PS.
         by move: (NM1 _ _ _ F).
      -- move/negbT in E.
         by apply /(pt_PhaseOneRespondedE_consume _ _ C)=>//.

- move=>[recvd][] CS' U S Pts.
  constructor 4. exists recvd.
  split=>//.
  + apply/(cn_state_consume _ _ _ C)=>//.
    by apply /eqP/nesym/eqP/(pt_not_cn Hnin).
  + move=>pt Hpt.
    move: (Pts _ Hpt).
    case: ifP => _ H.
    * case E: (pt == this).
      -- move/eqP in E. subst pt.
         case: H => PS NM1 NM2.
         by move: (NM1 _ _ _ F).
      -- move/negbT in E.
         by apply /(pt_PhaseTwoRespondedE_consume _ _ C).
    * case E: (pt == this).
      -- move /eqP in E. subst pt.
         case/(abort_req_pt_inv F): H=>PS'' M NM.
         pose proof C as C'.
         move: C'=>[] _ _ _ /(_ _ (pts_in cn others Hpt)) [] V _.
         constructor 2.
         split.
         ++ rewrite/ pt_state locE'// (getStL_Kp C H1 PS').
            move: Hmatch. destruct ps=>//;
            (case: PS''=>PS'';
            move: (pt_state_functional V PS' PS'')=>[]); try discriminate;
            by move => [] ? ?; subst.
         ++ by apply /(msg_spec_consume _ F M).
         ++ by apply /no_msg_from_to_consume.
      -- move /negbT in E.
         apply /(pt_PhaseTwoAbortE_consume _ C _ _ F)=>//.
         by apply: (pt_not_cn Hnin).
Qed.

Definition sts' := [:: SI s1; SI s2; SI s3; SI s4; SI s5; SI s6; SI s7].
Definition rts' := [:: RI r1; RI r2; RI r3; RI r4; RI r5; RI r6; RI r7].

Program Definition ii := @ProtocolWithInvariant.II _ _ sts' rts' _ _.

Definition tpc_with_inv := ProtocolWithIndInv ii.

End TwoPhaseInductiveProof.

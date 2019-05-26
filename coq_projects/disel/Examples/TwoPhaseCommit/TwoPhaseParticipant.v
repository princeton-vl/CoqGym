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
Require Import InductiveInv While.
From DiSeL
Require Import TwoPhaseProtocol.

Module TwoPhaseParticipant.
Section TwoPhaseParticipant.

Variable l : Label.
Variables (cn : nid) (pts : seq nid) (others : seq nid).
Hypothesis Hnin : cn \notin pts.
Hypothesis PtsNonEmpty : pts != [::].

Definition tpc := TwoPhaseCommitProtocol others Hnin l.
Notation W := (mkWorld tpc).

Variable p : nid.
Hypothesis Hpin : p \in pts.

Section ParticipantImplementation.

(************** Atomic actions **************)

(* Three receive-actions *)

(* This action actually encompasses two receive-transitions *)
Program Definition tryrecv_prep_req := act (@tryrecv_action_wrapper W p
      (fun k _ t b => (k == l) && (t == prep_req)) _).
(* TODO: automate these kinds of proofs *)
Next Obligation. by case/andP: H=>/eqP->_; rewrite /ddom domPt inE/=. Qed.

(*

[Overly cautious filtering]

This action uses different filter for the tags of incoming messages
depending on what was this participant's answer to the initial prepare
request. If the answer what "yes", then the expected incomming
messages can be of the type "commit" and "abort" (as some other
participant may decide to abort). However, if this participant said
"no", the only expected message is "abort".

This filter can be removed if the inductive invariant is established
upfront, hence we can formally _prove_ that any incoming message will
be of this shape. However, we decided to postpone this proof and do it separately, therefore, making the implementation "overly cautious".

*)

Program Definition tryrecv_commabrt_req c :=
  act (@tryrecv_action_wrapper W p
  (fun k _ t b => (k == l) &&
  (if c then (t == commit_req) || (t == abort_req) else (t == abort_req))) _).
Next Obligation. by case/andP: H=>/eqP->_; rewrite /ddom domPt inE/=. Qed.

(* Four send-actions, e -- id of the current era *)

Program Definition send_yes e to :=
  act (@send_action_wrapper W tpc p l (prEq tpc) (pn_send_yes_trans others Hnin) _ [:: e] to).
Next Obligation. by rewrite !InE; right; right; right; left. Qed.

Program Definition send_no e to :=
  act (@send_action_wrapper W tpc p l (prEq tpc) (pn_send_no_trans others Hnin) _ [:: e] to).
Next Obligation. by rewrite !InE; right; right; right; right; left. Qed.

Program Definition send_commit_ack e to :=
  act (@send_action_wrapper W tpc p l (prEq tpc) (pn_commit_ack_trans others Hnin) _ [:: e] to).
Next Obligation. by rewrite !InE; right; right; right; right; right; left. Qed.

Program Definition send_abort_ack e to :=
  act (@send_action_wrapper W tpc p l (prEq tpc) (pn_abort_ack_trans others Hnin) _ [:: e] to).
Next Obligation. by rewrite !InE; do![right]. Qed.


(************** Participant code **************)

Arguments TPCProtocol.TPCCoh [cn pts others].
Notation coh := (@TPCProtocol.TPCCoh cn pts others).
Notation getS s := (getStatelet s l).
Notation loc i := (getLocal p (getStatelet i l)).

(* Read current round *)

Notation Pin := (TPCProtocol.pts_in cn others Hpin).

Program Definition read_round_p :
  {(ecl : (nat * PState) * Log)}, DHT [p, W]
  (fun i => loc i = st :-> ecl.1 \+ log :-> ecl.2, 
   fun r m => loc m = st :-> ecl.1 \+ log :-> ecl.2 /\
              exists (pf : coh (getS m)), r = (getStP Hnin pf Pin).1) :=
  Do (act (@skip_action_wrapper W p l tpc (prEq tpc) _
                                (fun s pf => (getStP Hnin pf Pin).1))).
Next Obligation.  
apply: ghC=>i [[e c]lg]/= E _.
apply: act_rule=>j R; split=>[|r k m]; first by case: (rely_coh R).
case=>/=H1[Cj]Z; subst j=>->R'.
split; first by rewrite (rely_loc' l R') (rely_loc' _ R).
case: (rely_coh R')=>_; case=>_ _ _ _/(_ l)=>/= pf; rewrite prEq in pf.
exists pf; move: (rely_loc' l R').
move => E'.
apply sym_eq in E'.
suff X: getStP Hnin (Actions.safe_local (prEq tpc) H1) Pin = getStP Hnin pf Pin by rewrite X.
by apply: (TPCProtocol.getStPE Hnin pf _ Pin Hpin E').
Qed.

(* Step 1 receive perp-messages *)

Export TPCProtocol.

(* Ending condition *)
Definition rp_prep_req_cond (res : option data) := res == None.

(* Invariant relates the argument and the shape of the state *)
Definition rp_prep_req_inv (e : nat) (lg : Log) : cont (option data) :=
  fun res i =>
    if res is Some d
    then loc i = st :-> (e, PGotRequest d) \+ log :-> lg
    else loc i = st :-> (e, PInit) \+ log :-> lg.

Program Definition receive_prep_req_loop (e : nat):
  {(lg : Log)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PInit) \+ log :-> lg,
   fun res m => exists d, res = Some d /\
       loc m = st :-> (e, PGotRequest d) \+ log :-> lg)
  :=
  Do _ (@while p W _ _ rp_prep_req_cond (rp_prep_req_inv e) _
        (fun _ => Do _ (
           r <-- tryrecv_prep_req;
           match r with
           | Some (from, tg, body) =>
             if (from == cn) && (head 0 body == e)
             then ret _ _ (Some (behead body))
             else ret _ _ None
           | None => ret _ _ None
           end              
        )) None).

Next Obligation. by apply: with_spec x. Defined.
Next Obligation. by move:H; rewrite /rp_prep_req_inv (rely_loc' _ H0). Qed.
Next Obligation.
apply:ghC=>i1 lg[/eqP->{H}/=E1]C1; apply: step.
apply: act_rule=>i2/=R1; split; first by case: (rely_coh R1).
case=>[[[from e']d i3 i4]|i3 i4]; last first.
- case=>S/=[]?; case; last by case=>?[?][?][?][?][?][].
  case=>_ _ Z; subst i3=>R2; apply: ret_rule=>i5 R4/=.
  by rewrite (rely_loc' _ R4) (rely_loc' _ R2)(rely_loc' _ R1).
case=>Sf[]C2[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E2 Hw/=]; first by case.
case/andP=>/eqP Z G->[]Z1 Z2 Z3 R2; subst l' from' e' d.
move: rt pf (coh_s (w:=W) l (s:=i2) C2) Hin R2 E2 Hw G E; rewrite prEq/=.
move=>rt pf Cj' Hin R E2 Hw G E.
have D: rt = pn_receive_got_prep_trans _ Hnin.
- move: Hin G; by do! [case=>/=; first by move=>->].  
subst rt=>{G}.
have P1: valid (dstate (getS i2))
  by apply: (@cohVl _ coh); case: (Cj')=>P1 P2 P3 P4; split=>//=; done.
have P2: valid i2 by apply: (cohS (proj2 (rely_coh R1))).
have P3: l \in dom i2 by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
case: ifP=>G1; apply: ret_rule=>//i5 R4.
- rewrite /rp_prep_req_inv; rewrite (rely_loc' _ R4) (rely_loc' _ R) locE//=.
  rewrite /TPCProtocol.rp_step Hpin/=. case/andP:G1=>/eqP=>Z1/eqP H2; subst from.
  rewrite -(rely_loc' _ R1) in E1; rewrite (getStL_Kp _ pf E1)(getStP_K Hnin _ pf Hpin E1).
  by rewrite/pstep_recv/= H2 !eqxx/= .
rewrite /rp_prep_req_inv; rewrite (rely_loc' _ R4) (rely_loc' _ R) locE//=.
rewrite /TPCProtocol.rp_step Hpin/=.
rewrite -(rely_loc' _ R1) in E1; rewrite (getStL_Kp _ pf E1)(getStP_K Hnin _ pf Hpin E1).
rewrite/pstep_recv/=.
by move/negbT: G1; rewrite Bool.negb_andb; case/orP=>->//=; rewrite orbC. 
Qed.

Next Obligation.
apply: ghC=>i1 lg E1 C1/=.
apply: (gh_ex (g:=lg)); apply: call_rule=>//r i2 [H1]H2 C2.
rewrite /rp_prep_req_cond/rp_prep_req_inv in H1 H2.
by case: r H1 H2=>//d _->; exists d.
Qed.

(* Step 2: Respond yes or no to the coordinator *)

Program Definition resp_to_req (e : nat) (doCommit : bool) :
  {(dl : (data * Log))}, DHT [p, W]
  (fun i => loc i = st :-> (e, PGotRequest dl.1) \+ log :-> dl.2,
   fun (_ : seq nat) m => 
     let:  (d, lg) := dl in
     if doCommit
     then loc m = st :-> (e, PRespondedYes d) \+ log :-> lg
     else loc m = st :-> (e, PRespondedNo d) \+ log :-> lg)
  := Do (if doCommit then send_yes e cn else send_no e cn).
Next Obligation.
apply:ghC=>i [d lg]E1 C1.
have Pre: forall i2, network_rely W p i i2 ->
          Actions.send_act_safe W (p:=tpc) p l
          (if doCommit
           then (pn_send_yes_trans (cn:=cn) (pts:=pts) others Hnin)
           else (pn_send_no_trans (cn:=cn) (pts:=pts) others Hnin)) [:: e] cn i2.
- move=>i2 R1.
  split; first by case: (rely_coh R1).
  + have X: HPn cn pts p cn by [].
    case: (proj2 (rely_coh R1))=>_ _ _ _/(_ l); rewrite (prEq tpc)=>C.
    case: doCommit; split=>//; exists X, C, e, d;
    by rewrite -(rely_loc' _ R1) in E1; rewrite (getStP_K _ _ _ _ E1).
  + rewrite /Actions.can_send /nodes inE/= mem_cat Hpin orbC.
    by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/= eqxx.
  rewrite /Actions.filter_hooks umfilt0=>???.
  move => F.
  apply sym_eq in F.
  move: F.
  by move/find_some; rewrite dom0.

case: doCommit Pre=>Pre; apply: act_rule=>i2 R1/=; move:(Pre i2 R1)=>{Pre}Pre.

(* Send yes-answer *)
split=>//; move=>b i3 i4[Sf]St R3.
case: {-1}(Sf)=>_/=[]_[H][]C'//; rewrite -(rely_loc' _ R1) in E1.
rewrite (getStP_K Hnin C' (pn_this_in _ H) Hpin E1)/=.
case=>e'[d'][][]Z1 Z2 _ G; subst d' e'.
move: St; rewrite/Actions.send_act_step/==>[][_][h][].
rewrite /pn_step -!(pf_irr C' (pn_safe_coh _))
        -!(pf_irr (pn_this_in _ H) (pn_this_in _ _)).
rewrite (getStP_K Hnin C' (pn_this_in _ H) Hpin E1)(getStL_Kp _ (pn_this_in _ H) E1)/=. 
case=>Z Z';subst h i3; rewrite (rely_loc' _ R3) locE//; last by apply: (cohVl C').
+ by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
by apply: (cohS (proj2 (rely_coh R1))).

(* Send no-answer *)
(* TODO: Remove proof duplication!!! *)  
split=>//; move=>b i3 i4[Sf]St R3.
case: {-1}(Sf)=>_/=[]_[H][]C'//; rewrite -(rely_loc' _ R1) in E1.
rewrite (getStP_K Hnin C' (pn_this_in _ H) Hpin E1)/=.
case=>e'[d'][][]Z1 Z2 _ G; subst d' e'.
move: St; rewrite/Actions.send_act_step/==>[][_][h][].
rewrite /pn_step -!(pf_irr C' (pn_safe_coh _))
        -!(pf_irr (pn_this_in _ H) (pn_this_in _ _)).
rewrite (getStP_K Hnin C' (pn_this_in _ H) Hpin E1)(getStL_Kp _ (pn_this_in _ H) E1)/=. 
case=>Z Z';subst h i3; rewrite (rely_loc' _ R3) locE//; last by apply: (cohVl C').
+ by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
by apply: (cohS (proj2 (rely_coh R1))).
Qed.

(* Step 3 Receive commit/abort msg *)

Definition rp_commabrt_cond (res : option bool) := res == None.

(* Invariant relates the argument and the shape of the state *)
Definition rp_commabrt_inv (e : nat) (c: bool) (ld : (Log * data)) :
  cont (option bool) :=
  fun res i =>
    let: (lg, d) := ld in
    if res is Some b
    then if b
         then loc i = st :-> (e, PCommitted d) \+ log :-> (rcons lg (b, d))
         else loc i = st :-> (e, PAborted d) \+ log :-> (rcons lg (b, d))
    else loc i = st :-> (e, if c then PRespondedYes d else PRespondedNo d) \+ log :-> lg.

Program Definition receive_commabrt_loop (e : nat) (c : bool):
  {(ld : (Log * data))}, DHT [p, W]
   (fun i => let: (lg, d) := ld in
    loc i = st :-> (e, if c then PRespondedYes d else PRespondedNo d) \+ log :->lg,
    fun (res : option bool) m => let: (lg, d) := ld in
    exists b, res = Some b /\
    if b 
    then loc m = st :-> (e, PCommitted d) \+ log :-> (rcons lg (b, d))
    else loc m = st :-> (e, PAborted d) \+ log :-> (rcons lg (b, d)))
  :=
  Do _ (@while p W _ _ rp_commabrt_cond (rp_commabrt_inv e c) _
        (fun _ => Do _ (
           r <-- tryrecv_commabrt_req c;
           match r with
           | Some (from, tg, body) =>
             if (from == cn) && (head 0 body == e)
             then ret _ _ (Some (tg == commit_req))
             else ret _ _ None
           | None => ret _ _ None
           end              
        )) None).
Next Obligation. by apply: (with_spec x). Defined.
Next Obligation. by move:H; rewrite /rp_commabrt_inv (rely_loc' _ H0). Qed.
Next Obligation.
apply:ghC=>i1 [lg d][/eqP->{H}/=E1]C1; apply: step.
apply: act_rule=>i2/=R1; split; first by case: (rely_coh R1).
case=>[[[from e']v i3 i4]|i3 i4]; last first.
- case=>S/=[]?; case; last by case=>?[?][?][?][?][?][].
  case=>_ _ Z; subst i3=>R2; apply: ret_rule=>i5 R4/=.
  rewrite /rp_commabrt_inv/= in E1 *.
  by rewrite (rely_loc' _ R4) (rely_loc' _ R2) (rely_loc' _ R1).
case=>Sf[]C2[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E2 Hw/=]; first by case.
case/andP=>/eqP Z G->[]Z1 Z2 Z3 R2; subst l' from' e' v.
move: rt pf (coh_s (w:=W) l (s:=i2) C2) Hin R2 E2 Hw G E; rewrite prEq/=.
move=>rt pf Cj' Hin R E2 Hw G E.
have P1: valid (dstate (getS i2))
  by apply: (@cohVl _ coh); case: (Cj')=>P1 P2 P3 P4; split=>//=; done.
have P2: valid i2 by apply: (cohS (proj2 (rely_coh R1))).
have P3: l \in dom i2 by rewrite-(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
(* See the remark [Overly cautious filtering] *)
have D: if c
        then rt = pn_receive_commit_ack_trans _ Hnin \/
             rt = pn_receive_abort_ack_trans _ Hnin
        else rt = pn_receive_abort_ack_trans _ Hnin.
-  move: Hin G; clear E1; do![case=>/=; first by move=>->; case: c].
   by case;[|case=>//];move=>->; case:c=>//=; [left | right].
case: ifP=>G1; apply: ret_rule=>//i5 R4.
- rewrite /rp_commabrt_inv (rely_loc' _ R4) (rely_loc' _ R) locE//=.
  case/andP:G1=>/eqP=>Z1/eqP H2; subst from.
  rewrite -(rely_loc' _ R1) in E1.
  case: (c) E1 E2 D G=>/=E1 E2; case=>Z; subst rt; rewrite E2{E2}//==>_;
  rewrite/rp_step (getStL_Kp _ pf E1)(getStP_K Hnin _ pf Hpin E1) Hpin;
  by rewrite/pstep_recv/= H2 !eqxx/=. 
rewrite /rp_commabrt_inv; rewrite (rely_loc' _ R4) (rely_loc' _ R) locE//=.
rewrite -(rely_loc' _ R1) in E1.
case: (c) E1 E2 D G=>/=E1 E2; case=>Z {E2}; subst rt=>//= _;
rewrite/rp_step (getStL_Kp _ pf E1)(getStP_K Hnin _ pf Hpin E1) Hpin;
by rewrite/pstep_recv/=; move/negbT: G1; rewrite Bool.negb_andb; case/orP=>->//=; rewrite orbC.
Qed.

Next Obligation.
apply: ghC=>i1 [lg d] E1 C1/=.
apply: (gh_ex (g:=(lg, d))); apply: call_rule=>//r i2 [H1]H2 C2. 
rewrite /rp_commabrt_cond/rp_commabrt_inv in H1 H2; case: r H1 H2=>//b _.
by exists b.
Qed.

(* Step 4 Send ack wrt commit/abort *)
 
Program Definition send_ack (e : nat) (hasCommitted : bool) :
  {(dl : (data * Log))}, DHT [p, W]
  (fun i =>  let:  (d, lg) := dl in
     if hasCommitted
     then loc i = st :-> (e, PCommitted d) \+ log :-> lg
     else loc i = st :-> (e, PAborted d) \+ log :-> lg,
   fun (_ : seq nat) m => 
     let:  (d, lg) := dl in
     if hasCommitted
     then loc m = st :-> (e.+1, PInit) \+ log :-> lg
     else loc m = st :-> (e.+1, PInit) \+ log :-> lg)
  := Do (if hasCommitted then send_commit_ack e cn else send_abort_ack e cn).

(* TODO: automate this proof, as it's exactly the same as for the previous send-transition! *)
Next Obligation.
apply:ghC=>i [d lg]E1 C1.
have Pre: forall i2, network_rely W p i i2 ->
          Actions.send_act_safe W (p:=tpc) p l
          (if hasCommitted
           then (pn_commit_ack_trans (cn:=cn) (pts:=pts) others Hnin)
           else (pn_abort_ack_trans (cn:=cn) (pts:=pts) others Hnin)) [:: e] cn i2.
- move=>i2 R1.
  split; first by case: (rely_coh R1).
  + have X: HPn cn pts p cn by [].
    case: (proj2 (rely_coh R1))=>_ _ _ _/(_ l); rewrite (prEq tpc)=>C.
    case: hasCommitted E1; split=>//; exists X, C, e, d;
    by rewrite -(rely_loc' _ R1) in E1; rewrite (getStP_K _ _ _ _ E1).
  + rewrite /Actions.can_send /nodes inE/= mem_cat Hpin orbC.
    by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/= eqxx.
  rewrite /Actions.filter_hooks umfilt0=>???.
  move => F.
  apply sym_eq in F.
  move: F.
  by move/find_some; rewrite dom0.

case: hasCommitted E1 Pre=>E1 Pre; apply: act_rule=>i2 R1/=; move:(Pre i2 R1)=>{Pre}Pre.
(* Send commit-ack *)
split=>//; move=>b i3 i4[Sf]St R3.
case: {-1}(Sf)=>_/=[]_[H][]C'//; rewrite -(rely_loc' _ R1) in E1.
rewrite (getStP_K Hnin C' (pn_this_in _ H) Hpin E1)/=.
case=>e'[d'][][]Z1 Z2 _ G; subst d' e'.
move: St; rewrite/Actions.send_act_step/==>[][_][h][].
rewrite /pn_step -!(pf_irr C' (pn_safe_coh _))
        -!(pf_irr (pn_this_in _ H) (pn_this_in _ _)).
rewrite (getStP_K Hnin C' (pn_this_in _ H) Hpin E1)(getStL_Kp _ (pn_this_in _ H) E1)/=. 
case=>Z Z';subst h i3; rewrite (rely_loc' _ R3) locE//; last by apply: (cohVl C').
+ by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
by apply: (cohS (proj2 (rely_coh R1))).
(* Send abort-ack *)
(* TODO: Remove proof duplication!!! *)  
split=>//; move=>b i3 i4[Sf]St R3.
case: {-1}(Sf)=>_/=[]_[H][]C'//; rewrite -(rely_loc' _ R1) in E1.
rewrite (getStP_K Hnin C' (pn_this_in _ H) Hpin E1)/=.
case=>e'[d'][][]Z1 Z2 _ G; subst d' e'.
move: St; rewrite/Actions.send_act_step/==>[][_][h][].
rewrite /pn_step -!(pf_irr C' (pn_safe_coh _))
        -!(pf_irr (pn_this_in _ H) (pn_this_in _ _)).
rewrite (getStP_K Hnin C' (pn_this_in _ H) Hpin E1)(getStL_Kp _ (pn_this_in _ H) E1)/=. 
case=>Z Z';subst h i3; rewrite (rely_loc' _ R3) locE//; last by apply: (cohVl C').
+ by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
by apply: (cohS (proj2 (rely_coh R1))).
Qed.


(*****************************************************)
(*      Full participant implementation              *)
(*****************************************************)

Definition get (r : option bool) : bool :=
  if r is Some b then b else false.

(* Just one round *)
Program Definition participant_round (doCommit : bool) :
  {(el : nat * Log)}, DHT [p, W] 
  (fun i =>  loc i = st :-> (el.1, PInit) \+ log :-> el.2,
   fun (_ : unit) m => exists (b : bool)(d: data),
     loc m = st :-> (el.1.+1, PInit) \+ log :-> (rcons el.2 (b, d)))
  := 
  Do _ (e <-- read_round_p;
      receive_prep_req_loop e;;
      resp_to_req e doCommit;;
      r <-- receive_commabrt_loop e doCommit;                     
      send_ack e (get r);;
      ret _ _ tt).
Next Obligation.
apply:ghC=>i1[e lg]/=E1 C1; apply: step.
apply: (gh_ex (g:=(e, PInit, lg))); apply: call_rule=>//e' i2 [E2][pf]->C2.
have X: (getStP (cn:=cn) (others:=others) Hnin  pf Pin).1 = e
  by move: (getStP_K Hnin pf Pin Hpin E2)=>->.
rewrite X; apply: step; apply: (gh_ex (g:=lg));
apply: call_rule=>//_ i3[d][_]E3 _.
apply: step; apply: (gh_ex (g:=(d, lg))).
apply: call_rule=>//_ i4 E4 _.
apply: step; apply: (gh_ex (g:=(lg, d))).
apply: call_rule=>[|r i5 [b [Z E5]] _]; first by case: doCommit E4. 
subst r; apply: step; apply: (gh_ex (g:=(d, rcons lg (b, d)))).
apply: call_rule=>//= _ i6 E6 _{E4}.
apply: ret_rule=>i7 R6 {E5}; exists b, d; rewrite (rely_loc' _ R6).
by case: b E6.
Qed.

(**************************************************)
(*
Overall Implementation effort:

4 person-hours

*)
(**************************************************)

(*****************************************************)
(*    Waiting for a list of incoming transactions    *)
(*****************************************************)

Definition part_with_choices_loop_spec := forall (chs : seq bool),
  {(el : nat * Log)}, DHT [p, W] 
  (fun i =>  loc i = st :-> (el.1, PInit) \+ log :-> el.2,
   fun (_ : unit) m => exists (bs : seq bool)(ds : seq data),
     loc m = st :-> (el.1 + (size chs), PInit) \+ log :-> (el.2 ++ (seq.zip bs ds))).
                                               

Program Definition participant_with_choices_loop : part_with_choices_loop_spec :=
  fun choices  =>
    Do (fix rec choices :=
          (match choices with
           | c :: chs => participant_round c ;; rec chs
           | [::] => ret _ _ tt
           end)) choices.
Next Obligation.
apply:ghC=>i; elim: choices i=>//=[|c cs/= Hi]i1 [e lg] E1 C1. 
- by apply: ret_rule=>i2 R1; exists [::], [::];
                        rewrite cats0 addn0 (rely_loc' _ R1).
apply: step; apply: (gh_ex (g:=(e, lg))).
apply: call_rule=>//_ i2[b][d]/=E2 C2/=.
move:(Hi i2 (e.+1, rcons lg (b, d)) E2 C2)=>/=.
apply: vrf_mono=>_ i3[bs][ds]->.
rewrite -[e.+1]addn1 -[(size cs).+1]addn1 addnAC addnA.
exists (b:: bs), (d :: ds)=>/=.
by rewrite -cats1 -!catA/=.
Qed.

(* Take a list of choices and loop until they run out *)
Program Definition participant_with_choices choices:
  DHT [p, W] 
  (fun i =>  loc i = st :-> (0, PInit) \+ log :-> ([::] : seq (bool * data)),
   fun (_ : unit) m => exists (bs : seq bool) (ds : seq data),
       loc m = st :-> (size choices, PInit) \+ log :-> (seq.zip bs ds))
  := Do (participant_with_choices_loop choices).
Next Obligation.
by move=>i/=E; apply: (gh_ex (g:=(0, [::]))); apply: call_rule.
Qed.    

End ParticipantImplementation.
End TwoPhaseParticipant.

Module Exports.
Section Exports.

Definition participant_round := participant_round.
Definition participant_with_choices_loop := participant_with_choices_loop.
Definition participant_with_choices := participant_with_choices.

End Exports.
End Exports.

End TwoPhaseParticipant.


Export TwoPhaseParticipant.Exports.

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

Module TwoPhaseCoordinator.
Section TwoPhaseCoordinator.

Variable l : Label.
Variables (cn : nid) (pts : seq nid) (others : seq nid).
Hypothesis Hnin : cn \notin pts.
Hypothesis Puniq : uniq pts.
Hypothesis PtsNonEmpty : pts != [::].

Definition tpc := TwoPhaseCommitProtocol others Hnin l.
Notation W := (mkWorld tpc).

Section CoordinatorImplementation.

(************** Atomic actions **************)

(* Three send-actions, e -- id of the current era *)

(* TODO: automate the proofs of obligations *)
Program Definition send_prep e data to :=
  act (@send_action_wrapper W tpc cn l (prEq tpc) (cn_send_prep_trans cn pts others) _ (e :: data) to).
Next Obligation. by rewrite InE; do![left|right]. Qed.

Program Definition send_commit e to :=
  act (@send_action_wrapper W tpc cn l (prEq tpc) (cn_send_commit_trans cn pts others) _ [:: e] to).
Next Obligation. by rewrite !InE; right; left. Qed.

Program Definition send_abort e to :=
  act (@send_action_wrapper W tpc cn l (prEq tpc) (cn_send_abort_trans cn pts others) _ [:: e] to).
Next Obligation. by rewrite !InE; right; right; left. Qed.

(* Three receive-actions *)

(* This action actually encompasses two receive-transitions *)
Program Definition tryrecv_prep_resp := act (@tryrecv_action_wrapper W cn
      (* filter *)
      (fun k _ t b => (k == l) && ((t == prep_yes) || (t == prep_no))) _).
(* TODO: automate these kinds of proofs *)
Next Obligation. by case/andP: H=>/eqP->_; rewrite /ddom domPt inE/=. Qed.

Program Definition tryrecv_commit_ack :=
  act (@tryrecv_action_wrapper W cn (fun k _ t b => (k == l) && (t == commit_ack)) _).
Next Obligation. by case/andP: H=>/eqP->_; rewrite /ddom domPt inE/=. Qed.

Program Definition tryrecv_abort_ack :=
  act (@tryrecv_action_wrapper W cn (fun k _ t b => (k == l) && (t == abort_ack)) _).
Next Obligation. by case/andP: H=>/eqP->_; rewrite /ddom domPt inE/=. Qed.


(************** Coordinator code **************)

(*** Reading internal state ***)
Arguments TPCProtocol.TPCCoh [cn pts others].
Notation coh := (@TPCProtocol.TPCCoh cn pts others).
Notation getS s := (getStatelet s l).
Notation loc i := (getLocal cn (getStatelet i l)).

Export TPCProtocol.

(*************************************)
(* Reading current state - with spec *)
(*************************************)

Program Definition read_round :
  {(ecl : (nat * CState) * Log)}, DHT [cn, W]
  (fun i => loc i = st :-> ecl.1 \+ log :-> ecl.2, 
   fun r m => loc m = st :-> ecl.1 \+ log :-> ecl.2 /\
              exists (pf : coh (getS m)), r = (getStC pf).1) :=
  Do (act (@skip_action_wrapper W cn l tpc (prEq tpc) _
                                (fun s pf => (getStC pf).1))).
Next Obligation.
apply: ghC=>i [[e c]lg]/= E _. 
apply: act_rule=>j R; split=>[|r k m]; first by case: (rely_coh R).
case=>/=H1[Cj]Z; subst j=>->R'.
split; first by rewrite (rely_loc' l R') (rely_loc' _ R).
case: (rely_coh R')=>_; case=>_ _ _ _/(_ l)=>/= pf; rewrite prEq in pf.
exists pf; move: (rely_loc' l R').
move => E'.
apply sym_eq in E'.
suff X: getStC (Actions.safe_local (prEq tpc) H1) = getStC pf by rewrite X.
by apply: (getStCE pf _ E').
Qed.

(*******************************************)
(***   Sending out proposals in a loop   ***)
(*******************************************)

Definition send_prep_loop_spec (e : nat) d := forall to_send,
  {l : Log}, DHT [cn, W] 
  (fun i =>
     loc i = st :-> (e, CInit) \+ log :-> l /\ perm_eq pts to_send \/
     if to_send == [::]
     then loc i = st :-> (e, CWaitPrepResponse d [::]) \+ log :-> l 
     else exists (ps : seq nid),
         loc i = st :-> (e, CSentPrep d ps) \+ log :-> l /\
         perm_eq pts (ps ++ to_send),
   fun r m => r = tt /\ loc m = st :-> (e, CWaitPrepResponse d [::]) \+ log :-> l).

Program Definition send_prep_loop e d :
  {l : Log}, DHT [cn, W] 
  (fun i => loc i = st :-> (e, CInit) \+ log :-> l,
   fun r m => r = tt /\
              loc m = st :-> (e, CWaitPrepResponse d [::]) \+ log :-> l) :=
  Do (ffix (fun (rec : send_prep_loop_spec e d) to_send => 
              Do (match to_send with
                  | to :: tos => send_prep e d to ;; rec tos
                  | [::] => ret _ _ tt
                  end)) pts).

(* Verifying the loop invariant *)
Next Obligation. 
apply: ghC=>i1 lg.
(*********************************)
(* two cases of the precondition *)
(*********************************)
case=>[[E1 P1 C1]|].

(*--------------------------------------*)
(* Case 1: We are in the initial state  *)
(*--------------------------------------*)

- case: to_send P1=>[|to tos Hp].
  + by move/perm_eq_size=>/=/size0nil=>Z; rewrite Z in (PtsNonEmpty). 
- apply: step; apply:act_rule=>j1 R1/=; split=>[|r k m[Sf]St R2]. 
  split=>//=; first by case: (rely_coh R1).
  + split; first by split=>//; move/perm_eq_mem: Hp->; rewrite inE eqxx.
    case: (proj2 (rely_coh R1))=>_ _ _ _/(_ l); rewrite (prEq tpc)=>C; exists C.
    left; exists e; split; last by exists d.
    by rewrite -(rely_loc' _ R1) in E1; rewrite (getStC_K _ E1).
  + rewrite /Actions.can_send /nodes inE eqxx andbC/=.
    by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
  + rewrite /Actions.filter_hooks umfilt0=>???.
    move => F.
    apply sym_eq in F.
    move: F.
    by move/find_some; rewrite dom0.
case: {-1}(Sf)=>_/=[]Hc[C][]; last first.
- move=>[n][d'][ps][E1'][]Z1 Z2 _; subst n d'.
  rewrite -(rely_loc' _ R1) in E1.
  by rewrite (getStC_K C E1) in E1'; discriminate E1'.
case=>b[E1'][d'][Z1 Z2]_ _; subst b d'.
move: St=>[Z][h][[]Z' G]; subst r h.
apply: (gh_ex (g := lg)).

(* Verifying precondition of the recursive call *)
have Pre:
  (if tos == [::]
   then loc m = st :-> (e, CWaitPrepResponse d [::]) \+ log :-> lg
   else exists ps : seq nid, loc m = st :-> (e, CSentPrep d ps) \+ log :-> lg /\ perm_eq pts (ps ++ tos)).
- case X: ([::] == tos);[move/eqP: X=>X; subst tos; rewrite eqxx|
                         rewrite eq_sym X].
  have Y: pts == [:: to] by rewrite (perm_eq_small _ Hp).
  rewrite /cstep_send/= Y in G. 
  move: (proj2 Hc)=>Y'; rewrite Y' in G=>{Y'}.
  rewrite [cn_safe_coh _ ](pf_irr _ C) E1' in G. (* TADA! *)
  rewrite (rely_loc' l R2); subst k; rewrite -(rely_loc' _ R1) in E1.
  rewrite locE; last apply: (cohVl C).
  + by rewrite -(pf_irr (cn_in cn pts others) (cn_this_in _ _))
                  (getStL_Kc _ (cn_in cn pts others) E1). 
  + by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
  by apply: (cohS (proj2 (rely_coh R1))).
- exists [:: to]; split; last by rewrite cat_cons/=.
  have Y: pts == [:: to] = false.
  + apply/negP=>/eqP Z; rewrite Z in Hp.
    move/perm_eq_size: (Hp).
    move => F.
    apply sym_eq in F.
    move: F.
    by case=>/size0nil=>Z'; rewrite Z' eqxx in X.
    (* This part is similar to the previous step *)
  rewrite /cstep_send/= Y in G. 
  move: (proj2 Hc)=>Y'; rewrite Y' in G=>{Y'}.
  rewrite [cn_safe_coh _ ](pf_irr _ C) E1' in G. (* TADA! *)
  rewrite (rely_loc' l R2); subst k; rewrite -(rely_loc' _ R1) in E1.
  rewrite locE; last apply: (cohVl C).
  + by rewrite -(pf_irr (cn_in cn pts others) (cn_this_in _ _))
                  (getStL_Kc _ (cn_in cn pts others) E1). 
  + by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
  by apply: (cohS (proj2 (rely_coh R1))).

apply: call_rule'=>/=[Cm|r2 m2]; first by right.
by case=>//; right. 

(*------------------------------------------*)
(* Case 2: We are in the intermediate state *)
(*------------------------------------------*)

(*** Subcase 2.1 : The last step of the loop ***)
case X: (to_send == [::]).
- move=>E1 C1; move/eqP: X=>Z; subst to_send.
  by apply: ret_rule=>m R; split=>//; rewrite (rely_loc' _ R).

(*** Subcase 2.2 : The proper intermediate step ***)
case=>ps[E1]Hp C1.
have Y: exists to tos, to_send = to :: tos.
- case: to_send X Hp; first by rewrite eqxx.
  by move=>to tos _ _; exists to, tos.
case: Y=>to[tos] Z; subst to_send=>{X}.
- apply: step; apply:act_rule=>j1 R1/=; split=>[|r k m[Sf]St R2]. 
  split=>//=; first by case: (rely_coh R1).
  + split; first by split=>//; move/perm_eq_mem: Hp->;
                    rewrite mem_cat orbC inE eqxx.
    case: (proj2 (rely_coh R1))=>_ _ _ _/(_ l); rewrite prEq=>C; exists C.
    right; exists e, d, ps; split=>//.
      by rewrite -(rely_loc' _ R1) in E1; rewrite (getStC_K _ E1).
  + move/perm_eq_uniq: Hp; rewrite Puniq.
    move => F.
    apply sym_eq in F.
    move: F.
    rewrite -cat_rcons cat_uniq -cats1 cat_uniq=>/andP[]/andP[_]/andP[].
    by rewrite /= orbC/=.
  + rewrite /Actions.can_send /nodes inE eqxx andbC.
    by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
  rewrite /Actions.filter_hooks umfilt0=>???.
  move => F.
  apply sym_eq in F.
  move: F.
  by move/find_some; rewrite dom0.
(* dismiss the bogus branch *)    
case: {-1}(Sf)=>_/=[]Hc[C][]. 
- case=>b[E1'][d'][Z1 Z2]_; subst b d'.
  rewrite -(rely_loc' _ R1) in E1.
  by rewrite (getStC_K C E1) in E1'; discriminate E1'.
move=>[n][d'][ps'][E1'][]Z1 Z2 N _ _; subst n d'. 
rewrite -(rely_loc' _ R1) in E1.
move: (E1'); rewrite (getStC_K C E1); case=>Z; subst ps'.
move: St=>[Z][h][[]Z' G]; subst r h.
apply: (gh_ex (g := lg)).

(* the same precondition, but different state *)
suff Pre:
  (if tos == [::]
   then loc m = st :-> (e, CWaitPrepResponse d [::]) \+ log :-> lg
   else exists ps : seq nid,
   loc m = st :-> (e, CSentPrep d ps) \+ log :-> lg /\ perm_eq pts (ps ++ tos)).
- apply: call_rule'=>/=[Cm|r2 m2]; first by right.
  by case=>//; right.
- case X: ([::] == tos);
    [move/eqP: X=>X; subst tos; rewrite eqxx| rewrite eq_sym X].
    rewrite /cstep_send/= (proj2 Hc)/= in G.
    rewrite [cn_safe_coh _ ](pf_irr _ C) E1' in G.
  have Y: perm_eq (to :: ps) pts.
    rewrite (perm_eq_sym pts) in Hp.
    by apply/perm_eqlE; rewrite -cat1s perm_catC; apply/perm_eqlP. 
  rewrite Y/= in G.     
  rewrite (rely_loc' l R2); subst k; rewrite locE; last apply: (cohVl C).
  + by rewrite -(pf_irr (cn_in cn pts others) (cn_this_in _ _))
               (getStL_Kc _ (cn_in cn pts others) E1). 
  + by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
  by apply: (cohS (proj2 (rely_coh R1))).   

rewrite /cstep_send/= (proj2 Hc)/= in G.
rewrite [cn_safe_coh _ ](pf_irr _ C) E1' in G.
have Y : perm_eq (to :: ps) pts = false.
- apply/negP=>Hp'; move: (perm_eq_trans Hp' Hp).
  rewrite -[to::ps]cat1s -[to::tos]cat1s.
  move/perm_eqlE: (perm_catC ps [::to])=>Hs.
  move/(perm_eq_trans Hs); rewrite -[_++[::_]]cats0 catA perm_cat2l.
  move/perm_eq_size.
  move => F.
  apply sym_eq in F.
  move: F.
  by move/size0nil=>Z; subst tos.
rewrite Y/= in G.     
rewrite (rely_loc' l R2); subst k; rewrite locE; last apply: (cohVl C).
  + rewrite -(pf_irr (cn_in cn pts others) (cn_this_in _ _))
               (getStL_Kc _ (cn_in cn pts others) E1); exists (to::ps).
    split=>//; move: Hp.
    by rewrite -cat_rcons -cat1s -!catA !(perm_eq_sym pts) -perm_catCA catA cats1. 
  + by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
  by apply: (cohS (proj2 (rely_coh R1))).   
Qed.

(* Verifying the top-level call of ffix *)
Next Obligation.
apply:ghC=>i lg E1 _; apply: (gh_ex (g:=lg)).
by apply: call_rule=>C1; first by left.
Qed.


(*******************************************)
(*** Receiving responses to the proposal ***)
(*******************************************)

(* Ending condition *)
Definition rc_prep_cond (acc : seq (nid * bool)) := ~~ perm_eq (map fst acc) pts.

(* Invariant relates the argument and the shape of the state *)
Definition rc_prep_inv (e : nat) (dl : data * Log) : cont (seq (nid * bool)) :=
  fun acc i => loc i = st :-> (e, CWaitPrepResponse dl.1 acc) \+ log :-> dl.2.

Program Definition receive_prep_loop (e : nat):
  {(dl : data * Log)}, DHT [cn, W]
  (fun i => loc i = st :-> (e, CWaitPrepResponse dl.1 [::]) \+ log :-> dl.2,
   fun res m => 
       loc m = st :-> (e, CWaitPrepResponse dl.1 res) \+ log :-> dl.2 /\
       (perm_eq (map fst res) pts))
  :=
  Do _ (@while cn W _ _ rc_prep_cond (rc_prep_inv e) _
        (fun acc => Do _ (
           r <-- tryrecv_prep_resp;
           match r with
           | Some (from, tg, body) =>
               if [&& from \in pts, head 0 body == e & from \notin (map fst acc)]
               then ret _ _ ((from, tg == prep_yes) :: acc)
               else ret _ _ acc
           | None => ret _ _ acc
           end              
        )) [::]).

(* TODO: Get rid of this bogus obligation! *)
Next Obligation. by apply: with_spec x. Defined.
Next Obligation. by move:H; rewrite /rc_prep_inv (rely_loc' _ H0). Qed.

Next Obligation.
move=>i[[d lg]]/=[H1 I1]; apply: step.
apply: act_rule=>j R1/=; split; first by case: (rely_coh R1).
case=>[[[from tg] body] k m|k m]; last first.
- case=>Sf []Cj[]H; last by case: H=>[?][?][?][?][?][?][].
  have E: k = j by case: H. 
  move: H; subst k=>_ R2; apply: ret_rule=>m' R3 {d lg I1}[d lg][H2].
  by rewrite /rc_prep_inv; rewrite -(rely_loc' _ R1)-(rely_loc' _ R2)-(rely_loc' _ R3).
case=>Sf []Cj[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E1 Hw/=]; first by case.
case/andP=>/eqP Z G->{k}[]Z1 Z2 Z3 R2; subst l' from' tg body.
move: rt pf (coh_s (w:=W) l (s:=j) Cj) Hin R2 E1 Hw G E; rewrite prEq/=. 
move=>rt pf Cj' Hin R E1 Hw G E.
have D: rt = cn_receive_prep_yes_trans _ _ _ \/ rt = cn_receive_prep_no_trans _ _ _.
- case: Hin G=>/=; first by intuition.
  case; first by intuition.
  by do! [case; first by move=>->]. 
(* Some forward facts: *)
have P1: valid (dstate (getS j))
  by apply: (@cohVl _ TPCCoh); case: (Cj')=>P1 P2 P3 P4; split=>//=; done. 
have P2: valid j by apply: (cohS (proj2 (rely_coh R1))).
have P3: l \in dom j by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
(* Two cases: received yes or no from a participant *)
case: D=>{Hin G Hw}Z; subst rt; rewrite/= in E1 R; case:ifP=>G1;
apply: ret_rule=>m' R'=>{d lg I1}[[d lg][I1]]; rewrite /rc_prep_inv ?E1 ?eqxx/=;
rewrite -(rely_loc' _ R1)(rely_loc' _ R')(rely_loc' _ R)=>Ej; rewrite locE//;
rewrite /rc_step eqxx/cstep_recv/= (getStC_K Cj' Ej) (getStL_Kc _ _ Ej) ?eqxx/=;
do? [by move: G1; case: (from \in pts)=>//=;
        case: (head 0 tms == e)=>//=/negbFE->/=];
do ? by case/andP:G1=>->/andP[]/eqP->G1; rewrite negbF ?eqxx//=;
     by move/negbTE: G1=>->.
Qed.

Next Obligation.
apply: ghC=>i[d lg]E1 C1.
have Pre: rc_prep_inv e (d, lg) [::] i by rewrite /rc_prep_inv/= E1.
apply: call_rule'=>[|acc m]; first by exists (d, lg).
case/(_ (d, lg) Pre)=>/=H1 H2 Cm; split=>//;  by move/negbNE: H1.
Qed.

Definition read_res (st : CStateT) :=
  let: (_, s) := st in
  match s with
  | CWaitPrepResponse _ res => res
  | _ => [::]
  end.

(* Reading the accumulated responses from the state *)
Program Definition read_resp_result :
  {(e : nat) (d : data) (lg : Log) res}, DHT [cn, W]
  (fun i => loc i = st :-> (e, CWaitPrepResponse d res) \+ log :-> lg,
   fun r m => loc m = st :-> (e, CWaitPrepResponse d res) \+ log :-> lg /\
              r = all (fun i => i) (map snd res)) :=                        
  Do (act (@skip_action_wrapper W cn l tpc (prEq tpc) _
          (fun s pf => all (fun i => i) (map snd (read_res (getStC pf)))))).
Next Obligation.
move=>/=i[e][d][lg][res] E/=. 
apply: act_rule=>j R; split=>/=[|r k m]; first by case: (rely_coh R).
case=>/=H1[Cj]Z; subst j=>->R'.
split; first by rewrite (rely_loc' l R') (rely_loc' _ R).
by rewrite -(rely_loc' _ R) in H; rewrite (getStC_K _ H)/=.
Qed.

(*************************)
(* Coordinator's prelude *)
(*************************)

Program Definition coordinator_prelude (d : data) :
  {(lg : Log)}, DHT [cn, W] 
  (fun i => exists (e : nat), loc i = st :-> (e, CInit) \+ log :-> lg,
   fun r m => let: (res, b) := r in
       exists (e : nat),
       [/\ loc m = st :-> (e, CWaitPrepResponse d res) \+ log :-> lg,
           perm_eq (map fst res) pts &
           b = all id (map snd res)]) :=
  Do (e <-- read_round;
      send_prep_loop e d;;
      res <-- receive_prep_loop e;                     
      b <-- read_resp_result;
      ret _ _ (res, b)).
Next Obligation.
move=>s0/=[lg][e]E0; apply: step.
apply: (gh_ex (g := (e, CInit, lg))).
apply: call_rule=>//=e' s1 [E1][pf]->C1.
rewrite !(getStC_K _ E1)=>{e'}.
apply: step; apply: (gh_ex (g:=lg)).
apply: call_rule=>//_ s2[_]/=E2 C2.
apply: step; apply: (gh_ex (g:=(d, lg))).
apply: call_rule=>//res s3/= [E3 H3] C3.
apply: step; apply: (gh_ex (g:=e)); apply: (gh_ex (g:=d));
  apply: (gh_ex (g:=lg)); apply: (gh_ex (g:=res)).
apply: call_rule=>// b s4 [E4]->{b}C4/=.
apply: ret_rule=>i5 R5 lg'[e'] E0'; exists e.
rewrite E0 in E0'; case: (hcancelV _ E0'); first by rewrite validPtUn.
case=>Z1 _; subst e'; move/(hcancelPtV _)=>/=.
by rewrite validPt (rely_loc' _ R5)=>/(_ is_true_true)=><-.
Qed.                                                     

(*******************************************)
(***    Sending commits/aborts           ***)
(*******************************************)

(* Commit *)

Definition send_commit_loop_spec (e : nat) d := forall to_send,
  {lg : Log}, DHT [cn, W]
  (fun i =>
     (exists res,
         [/\ loc i = st :-> (e, CWaitPrepResponse d res) \+ log :-> lg,
          to_send = pts, perm_eq (map fst res) pts &
          all id (map snd res)]) \/
     if to_send == [::]
     then loc i = st :-> (e, CWaitAckCommit d [::]) \+ log :-> lg
     else exists (ps : seq nid),
         loc i = st :-> (e, CSentCommit d ps) \+ log :-> lg /\
         perm_eq pts (ps ++ to_send),
   fun (r : unit) m => loc m = st :-> (e, CWaitAckCommit d [::]) \+ log :-> lg).

Program Definition send_commit_loop e d : send_commit_loop_spec e d :=
  fun to_send  =>
    Do (fix rec to_send :=
          (match to_send with
           | to :: tos => send_commit e to ;; rec tos
           | [::] => ret _ _ tt
           end)) to_send.

Next Obligation.
apply: ghC=>s1 lg E1 C1; elim: to_send s1 E1 C1=>//=.
- move=>s1; case; first by case=>?[]_ Z; rewrite -Z in (PtsNonEmpty). 
  by move=>E1 _; apply: ret_rule=>i2 R; rewrite (rely_loc' _ R).
move=>to tos Hi s1 H C1.
apply: step; apply: act_rule=>s2 R2/=.
have Pre: Actions.send_act_safe W (p:=tpc) cn l
          (cn_send_commit_trans cn pts others) [:: e] to s2.
- split; [by case: (rely_coh R2) | | |]; last first.
  + rewrite /Actions.filter_hooks umfilt0=>???.
    move => F.
    apply sym_eq in F.
    move: F.
    by move/find_some; rewrite dom0.
  + rewrite /Actions.can_send /nodes inE eqxx andbC/=.
    by rewrite -(cohD (proj2 (rely_coh R2)))/ddom domPt inE/=.
  case: (proj2 (rely_coh R2))=>_ _ _ _/(_ l); rewrite prEq=>C; split.
  + split=>//; case: H; first by case=>?[_]<-; rewrite inE eqxx.
    by case=>ps[_]/perm_eq_mem->; rewrite mem_cat orbC inE eqxx.
  exists C; case:H=>[[res][P1]P2 P3|[ps][P1 P2]];[left|right];  
  rewrite -(rely_loc' _ R2) in P1; rewrite (getStC_K _ P1);
  first by exists e, d, res=>//.
  exists e, d, ps; split=>//.
  move/perm_eq_uniq: P2; rewrite Puniq.
  move => F.
  apply sym_eq in F.
  move: F.
  rewrite -cat_rcons cat_uniq -cats1 cat_uniq=>/andP[]/andP[_]/andP[].
  by rewrite /= orbC.                                                          
  
(* Using the postcondition *)  
split=>// body i3 i4[Sf]/=St R3.
apply: Hi; last by case: (rely_coh R3).  
right; rewrite (rely_loc' _ R3).
case: (Sf)=>C2/=[][]_ Tp [C2']/=; case; move=>[e'][d']. 
- move=>[res][E'][]Z P1 P2/andP[P3] _; subst e'. 
  case: H=>[[res'][E1]Te _ _|[ps]]; last first.
  + by rewrite -(rely_loc' _ R2)=>[][E1]; rewrite (getStC_K _ E1) in E'.
  rewrite -(rely_loc' _ R2) in E1; rewrite (getStC_K _ E1) in E'.
  case: E'=>Z Z'; subst res' d'.
  case: St=>Z1[h][];case=>->{h}; subst body=>G.
  rewrite (getStC_K _ E1) (getStL_Kc _ _ E1) 
          /cstep_send -{1}Te inE eqxx/= P1 P2 in G.
  have X: (pts == [:: to]) = (tos == [::]).
  + rewrite -Te; apply/Bool.eq_iff_eq_true.
    by split; [move=>/eqP[]->|move/eqP->;rewrite eqxx].
    rewrite X in G; subst i3.
    rewrite locE//; [|by apply: (cohS C2)|by apply: (cohVl C2')].
  by case: ifP=>X'; rewrite X'//; exists [::to]; split=>//; rewrite -Te. 
case=>ps[E'][]Z N/andP[P1]_; subst e'.   
case: H=>[[res'][E1]Te _ _|[ps']].
- by rewrite -(rely_loc' _ R2) in E1; rewrite (getStC_K _ E1) in E'.
rewrite -(rely_loc' _ R2)=>[][E1] P2; rewrite (getStC_K _ E1) in E'.
case: E'=>Z1 Z2; subst d' ps'; case: St=>Z1[h][];case=>->{h}; subst body=>G.
rewrite (getStC_K _ E1) (getStL_Kc _ _ E1) 
        /cstep_send Tp in G.
have X: perm_eq (to :: ps) pts = (tos == [::]).
- apply/Bool.eq_iff_eq_true; split.
  + move=>Hp'; move: (perm_eq_trans Hp' P2).
    rewrite -[to::ps]cat1s -[to::tos]cat1s.
    move/perm_eqlE: (perm_catC ps [::to])=>Hs.
    move/(perm_eq_trans Hs); rewrite -[_++[::_]]cats0 catA perm_cat2l.
    move/perm_eq_size.
    move => F.
    apply sym_eq in F.
    move: F.
    by move/size0nil=>Z; subst tos. 
  move/eqP=>Z; subst tos; rewrite perm_eq_sym; apply: (perm_eq_trans P2).
  by apply/perm_eqlE; move: (perm_catC ps [:: to]).
rewrite X in G=>{X}; subst i3.
rewrite locE//; [|by apply: (cohS C2)|by apply: (cohVl C2')].
case:ifP=>->//; exists (to :: ps);split=>//.
apply: (perm_eq_trans P2); apply/perm_eqlE.
by rewrite -[to::ps]cat1s -[to::tos]cat1s -!catA perm_catCA.
Qed.

Program Definition send_commits e d :
  {lg : Log}, DHT [cn, W]
  (fun i => exists res,
         [/\ loc i = st :-> (e, CWaitPrepResponse d res) \+ log :-> lg,
          perm_eq (map fst res) pts &
          all id (map snd res)],
   fun (r : unit) m => loc m = st :-> (e, CWaitAckCommit d [::]) \+ log :-> lg)
  := Do (send_commit_loop e d pts).
Next Obligation.
apply: ghC=>i lg[res][H1]H2 H3 C; apply: (gh_ex (g:=lg)).
apply: call_rule=>//; first by move=>_; left; exists res. 
Qed.

(* Abort *)

Definition send_abort_loop_spec (e : nat) d := forall to_send,
  {lg : Log}, DHT [cn, W]
  (fun i =>
     (exists res,
         [/\ loc i = st :-> (e, CWaitPrepResponse d res) \+ log :-> lg,
          to_send = pts, perm_eq (map fst res) pts &
          has (fun r => negb r) (map snd res)]) \/
     if to_send == [::]
     then loc i = st :-> (e, CWaitAckAbort d [::]) \+ log :-> lg
     else exists (ps : seq nid),
         loc i = st :-> (e, CSentAbort d ps) \+ log :-> lg /\
         perm_eq pts (ps ++ to_send),
   fun (r : unit) m => loc m = st :-> (e, CWaitAckAbort d [::]) \+ log :-> lg).

Program Definition send_abort_loop e d : send_abort_loop_spec e d :=
  fun to_send  =>
    Do (fix rec to_send :=
          (match to_send with
           | to :: tos => send_abort e to ;; rec tos
           | [::] => ret _ _ tt
           end)) to_send.

Next Obligation.
apply: ghC=>s1 lg E1 C1; elim: to_send s1 E1 C1=>//=.
- move=>s1; case; first by case=>?[]_ Z; rewrite -Z in (PtsNonEmpty). 
  by move=>E1 _; apply: ret_rule=>i2 R; rewrite (rely_loc' _ R).
move=>to tos Hi s1 H C1.
apply: step; apply: act_rule=>s2 R2/=.
have Pre: Actions.send_act_safe W (p:=tpc) cn l
          (cn_send_abort_trans cn pts others) [:: e] to s2.
- split; [by case: (rely_coh R2) | | |]; last first.
  + rewrite /Actions.filter_hooks umfilt0=>???.
    move => F.
    apply sym_eq in F.
    move: F.
    by move/find_some; rewrite dom0.
  + rewrite /Actions.can_send /nodes inE eqxx andbC/=.
    by rewrite -(cohD (proj2 (rely_coh R2)))/ddom domPt inE/=.
  case: (proj2 (rely_coh R2))=>_ _ _ _/(_ l); rewrite prEq=>C; split.
  + split=>//; case: H; first by case=>?[_]<-; rewrite inE eqxx.
    by case=>ps[_]/perm_eq_mem->; rewrite mem_cat orbC inE eqxx.
  exists C; case:H=>[[res][P1]P2 P3|[ps][P1 P2]];[left|right];
  rewrite -(rely_loc' _ R2) in P1; rewrite (getStC_K _ P1);
  first by exists e, d, res=>//.
  exists e, d, ps; split=>//.
  move/perm_eq_uniq: P2; rewrite Puniq.
  move => F.
  apply sym_eq in F.
  move: F.
  rewrite -cat_rcons cat_uniq -cats1 cat_uniq=>/andP[]/andP[_]/andP[].
  by rewrite /= orbC.                                                          

(* Using the postcondition *)  
split=>// body i3 i4[Sf]/=St R3.
apply: Hi; last by case: (rely_coh R3).  
right; rewrite (rely_loc' _ R3).
case: (Sf)=>C2/=[][]_ Tp [C2']/=; case; move=>[e'][d']. 
- move=>[res][E'][]Z P1 P2/andP[P3] _; subst e'. 
  case: H=>[[res'][E1]Te _ _|[ps]]; last first.
  + by rewrite -(rely_loc' _ R2)=>[][E1]; rewrite (getStC_K _ E1) in E'.
  rewrite -(rely_loc' _ R2) in E1; rewrite (getStC_K _ E1) in E'.
  case: E'=>Z Z'; subst res' d'.
  case: St=>Z1[h][];case=>->{h}; subst body=>G.
  have P2' : all id [seq i.2 | i <- res] = false
    by rewrite has_predC in P2; apply/negbTE.
  rewrite (getStC_K _ E1) (getStL_Kc _ _ E1) 
          /cstep_send -{1}Te inE eqxx/= P1 P2' in G.
  have X: (pts == [:: to]) = (tos == [::]).
  + rewrite -Te; apply/Bool.eq_iff_eq_true.
    by split; [move=>/eqP[]->|move/eqP->;rewrite eqxx].
    rewrite X in G; subst i3.
    rewrite locE//; [|by apply: (cohS C2)|by apply: (cohVl C2')].
  by case: ifP=>X'; rewrite X'//; exists [::to]; split=>//; rewrite -Te. 
case=>ps[E'][]Z N/andP[P1]_; subst e'.   
case: H=>[[res'][E1]Te _ _|[ps']].
- by rewrite -(rely_loc' _ R2) in E1; rewrite (getStC_K _ E1) in E'.
rewrite -(rely_loc' _ R2)=>[][E1] P2; rewrite (getStC_K _ E1) in E'.
case: E'=>Z1 Z2; subst d' ps'; case: St=>Z1[h][];case=>->{h}; subst body=>G.
rewrite (getStC_K _ E1) (getStL_Kc _ _ E1) 
        /cstep_send Tp in G.
have X: perm_eq (to :: ps) pts = (tos == [::]).
- apply/Bool.eq_iff_eq_true; split.
  + move=>Hp'; move: (perm_eq_trans Hp' P2).
    rewrite -[to::ps]cat1s -[to::tos]cat1s.
    move/perm_eqlE: (perm_catC ps [::to])=>Hs.
    move/(perm_eq_trans Hs); rewrite -[_++[::_]]cats0 catA perm_cat2l.
    move/perm_eq_size.
    move => F.
    apply sym_eq in F.
    move: F.
    by move/size0nil=>Z; subst tos. 
  move/eqP=>Z; subst tos; rewrite perm_eq_sym; apply: (perm_eq_trans P2).
  by apply/perm_eqlE; move: (perm_catC ps [:: to]).
rewrite X in G=>{X}; subst i3.
rewrite locE//; [|by apply: (cohS C2)|by apply: (cohVl C2')].
case:ifP=>->//; exists (to :: ps);split=>//.
apply: (perm_eq_trans P2); apply/perm_eqlE.
by rewrite -[to::ps]cat1s -[to::tos]cat1s -!catA perm_catCA.
Qed.

Program Definition send_aborts e d :
  {lg : Log}, DHT [cn, W]
  (fun i => exists res,
         [/\ loc i = st :-> (e, CWaitPrepResponse d res) \+ log :-> lg,
          perm_eq (map fst res) pts &
          has (fun r => negb r) (map snd res)],
   fun (r : unit) m => loc m = st :-> (e, CWaitAckAbort d [::]) \+ log :-> lg)
  := Do (send_abort_loop e d pts).
Next Obligation.
apply: ghC=>i lg[res][H1]H2 H3 C; apply: (gh_ex (g:=lg)).
apply: call_rule=>//; first by move=>_; left; exists res. 
Qed.


(*******************************************)
(*** Receiving acks on commit/abort    ***)
(*******************************************)

(* Acks on Commit *)

(* Ending condition *)
Definition rc_commit_cond (acc : seq nid) := ~~ perm_eq acc pts.

(* Invariant relates the argument and the shape of the state *)
Definition rc_commit_inv (e : nat) (dl : data * Log) : cont (seq nid) :=
  fun acc i =>
    if perm_eq acc pts
    then loc i = st :-> (e.+1, CInit) \+ log :-> rcons dl.2 (true, dl.1)
    else loc i = st :-> (e, CWaitAckCommit dl.1 acc) \+ log :-> dl.2.

Program Definition receive_commit_loop (e : nat):
  {(dl : data * Log)}, DHT [cn, W]
  (fun i => loc i = st :-> (e, CWaitAckCommit dl.1 [::]) \+ log :-> dl.2,
   fun (res : seq nat) m => 
       loc m = st :-> (e.+1, CInit) \+ log :-> rcons dl.2 (true, dl.1))
  :=
  Do _ (@while cn W _ _ rc_commit_cond (rc_commit_inv e) _
        (fun acc => Do _ (
           r <-- tryrecv_commit_ack;
           match r with
           | Some (from, tg, body) =>
               if [&& from \in pts, head 0 body == e & from \notin acc]
               then ret _ _ (from :: acc)
               else ret _ _ acc
           | None => ret _ _ acc
           end              
        )) [::]).

Next Obligation. by apply: with_spec x. Defined.
Next Obligation. by move:H; rewrite /rc_commit_inv (rely_loc' _ H0). Qed.

Next Obligation.
move=>i[[d lg]]/=[H1 I1]; apply: step.
apply: act_rule=>j R1/=; split; first by case: (rely_coh R1).
case=>[[[from tg] body] k m|k m]; last first.
- case=>Sf []Cj[]H; last by case: H=>[?][?][?][?][?][?][].
  have E: k = j by case: H.
  move: H; subst k=>_ R2; apply: ret_rule=>m' R3 {d lg I1}[d lg][H2].
  by rewrite /rc_commit_inv;
     rewrite -(rely_loc' _ R1)-(rely_loc' _ R2)-(rely_loc' _ R3).
case=>Sf []Cj[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E1 Hw/=]; first by case.
case/andP=>/eqP Z G->{k}[]Z1 Z2 Z3 R2; subst l' from' tg body.
move: rt pf (coh_s (w:=W) l (s:=j) Cj) Hin R2 E1 Hw G E; rewrite prEq/=.
move=>rt pf Cj' Hin R E1 Hw G E.
have D: rt = cn_receive_commit_ack_trans _ _ _.
- by move: Hin G; do! [case ;first by move=>->].
(* Some forward facts: *)
have P1: valid (dstate (getS j))
  by apply: (@cohVl _ TPCCoh); case: (Cj')=>P1 P2 P3 P4; split=>//=; done.
have P2: valid j by apply: (cohS (proj2 (rely_coh R1))).
have P3: l \in dom j by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
(* The final blow *)
by subst rt; rewrite/= in E1 R; case:ifP=>G1;
apply: ret_rule=>m' R'; rewrite /rc_commit_cond=>{d lg I1}[[d lg][I1]];
rewrite /rc_commit_inv ?E1 ?eqxx/=;
rewrite -(rely_loc' _ R1)(rely_loc' _ R')(rely_loc' _ R)=>Ej; rewrite locE//;
rewrite /rc_step eqxx/cstep_recv/=;
move/negbTE: I1=>I1; rewrite I1 in Ej *;
rewrite (getStC_K Cj' Ej) (getStL_Kc _ _ Ej) ?eqxx/=;
move: G1; case: (from \in pts)=>//=;case: (head 0 tms == e)=>//=;
case: (from \in acc)=>//=_; case:ifP=>X; rewrite X//=. 
Qed.

Next Obligation.
apply: ghC=>i[d lg]E1 C1.
have Pre: rc_commit_inv e (d, lg) [::] i.
- rewrite /rc_commit_inv/= E1/=.
  have X: perm_eq [::] pts = false.
  - apply/negP. 
    move/perm_eq_size.
    move => F.
    apply sym_eq in F.
    move: F.
    move/size0nil=>Z.
    by move: (PtsNonEmpty); rewrite Z.
  by rewrite X.
apply: call_rule'=>[|acc m]; first by exists (d, lg).
case/(_ (d, lg) Pre)=>/=H1 H2 Cm.
by move/negbNE: H1=>H1; rewrite /rc_commit_inv H1 in H2.
Qed.

(* Acks on Abort *)

(* Ending condition *)
Definition rc_abort_cond (acc : seq nid) := ~~ perm_eq acc pts.

(* Invariant relates the argument and the shape of the state *)
Definition rc_abort_inv (e : nat) (dl : data * Log) : cont (seq nid) :=
  fun acc i =>
    if perm_eq acc pts
    then loc i = st :-> (e.+1, CInit) \+ log :-> rcons dl.2 (false, dl.1)
    else loc i = st :-> (e, CWaitAckAbort dl.1 acc) \+ log :-> dl.2.

Program Definition receive_abort_loop (e : nat):
  {(dl : data * Log)}, DHT [cn, W]
  (fun i => loc i = st :-> (e, CWaitAckAbort dl.1 [::]) \+ log :-> dl.2,
   fun (res : seq nat) m => 
       loc m = st :-> (e.+1, CInit) \+ log :-> rcons dl.2 (false, dl.1))
  :=
  Do _ (@while cn W _ _ rc_abort_cond (rc_abort_inv e) _
        (fun acc => Do _ (
           r <-- tryrecv_abort_ack;
           match r with
           | Some (from, tg, body) =>
               if [&& from \in pts, head 0 body == e & from \notin acc]
               then ret _ _ (from :: acc)
               else ret _ _ acc
           | None => ret _ _ acc
           end              
        )) [::]).

Next Obligation. by apply: with_spec x. Defined.
Next Obligation. by move:H; rewrite /rc_abort_inv (rely_loc' _ H0). Qed.

Next Obligation.
move=>i[[d lg]]/=[H1 I1]; apply: step.
apply: act_rule=>j R1/=; split; first by case: (rely_coh R1).
case=>[[[from tg] body] k m|k m]; last first.
- case=>Sf []Cj[]H; last by case: H=>[?][?][?][?][?][?][].
  have E: k = j by case: H.
  move: H; subst k=>_ R2; apply: ret_rule=>m' R3 {d lg I1}[d lg][H2].
  by rewrite /rc_abort_inv;
     rewrite -(rely_loc' _ R1)-(rely_loc' _ R2)-(rely_loc' _ R3).
case=>Sf []Cj[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E1 Hw/=]; first by case.
case/andP=>/eqP Z G->{k}[]Z1 Z2 Z3 R2; subst l' from' tg body.
move: rt pf (coh_s (w:=W) l (s:=j) Cj) Hin R2 E1 Hw G E; rewrite prEq/=.
move=>rt pf Cj' Hin R E1 Hw G E.
have D: rt = cn_receive_abort_ack_trans _ _ _.
- by move: Hin G; do! [case ;first by move=>->].
(* Some forward facts: *)
have P1: valid (dstate (getS j))
  by apply: (@cohVl _ TPCCoh); case: (Cj')=>P1 P2 P3 P4; split=>//=; done.
have P2: valid j by apply: (cohS (proj2 (rely_coh R1))).
have P3: l \in dom j by rewrite -(cohD (proj2 (rely_coh R1)))/ddom domPt inE/=.
(* The final blow *)
by subst rt; rewrite/= in E1 R; case:ifP=>G1;
apply: ret_rule=>m' R'; rewrite /rc_abort_cond=>{d lg I1}[[d lg][I1]];
rewrite /rc_abort_inv ?E1 ?eqxx/=;
rewrite -(rely_loc' _ R1)(rely_loc' _ R')(rely_loc' _ R)=>Ej; rewrite locE//;
rewrite /rc_step eqxx/cstep_recv/=;
move/negbTE: I1=>I1; rewrite I1 in Ej *;
rewrite (getStC_K Cj' Ej) (getStL_Kc _ _ Ej) ?eqxx/=;
move: G1; case: (from \in pts)=>//=;case: (head 0 tms == e)=>//=;
case: (from \in acc)=>//=_; case:ifP=>X; rewrite X//=. 
Qed.

Next Obligation.
apply: ghC=>i[d lg]E1 C1.
have Pre: rc_abort_inv e (d, lg) [::] i.
- rewrite /rc_abort_inv/= E1/=.
  have X: perm_eq [::] pts = false.
  - apply/negP. 
    move/perm_eq_size.
    move => F.
    apply sym_eq in F.
    move: F.
    move/size0nil=>Z.
    by move: (PtsNonEmpty); rewrite Z.
  by rewrite X.
apply: call_rule'=>[|acc m]; first by exists (d, lg).
case/(_ (d, lg) Pre)=>/=H1 H2 Cm.
by move/negbNE: H1=>H1; rewrite /rc_abort_inv H1 in H2.
Qed.
 
(*****************************************************)
(*      Full coordinator Implementation              *)
(*****************************************************)

Program Definition coordinator_round (d : data) :
  {(e : nat)(lg : Log)}, DHT [cn, W] 
  (fun i => loc i = st :-> (e, CInit) \+ log :-> lg,
   fun res m => loc m = st :-> (e.+1, CInit) \+ log :-> rcons lg (res, d))
  :=
  Do (e <-- read_round;
      send_prep_loop e d;;
      res <-- receive_prep_loop e;                     
      b <-- read_resp_result;
      (if b
       then send_commits e d;;
            receive_commit_loop e                
       else send_aborts e d;;
            receive_abort_loop e);; 
      ret _ _ b).
Next Obligation.
move=>s0/=[e][lg]E0; apply: step.
apply: (gh_ex (g := (e, CInit, lg))).
apply: call_rule=>//e' s1 [E1][pf]->C1.
rewrite !(getStC_K _ E1)=>{e'}.
apply: step; apply: (gh_ex (g:=lg)).
apply: call_rule=>//_ s2[_]/=E2 C2.
apply: step; apply: (gh_ex (g:=(d, lg))).
apply: call_rule=>//res s3/= [E3 H3] C3.
apply: step; apply: (gh_ex (g:=e)); apply: (gh_ex (g:=d));
  apply: (gh_ex (g:=lg)); apply: (gh_ex (g:=res)).
apply: call_rule=>// b s4 [E4]->{b}C4/=.
case:ifP=>A.
- do![apply: step]; apply: (gh_ex (g:=lg)).
  apply: call_rule=>_; first by exists res.
  move=>s5 E5 C5; apply: (gh_ex (g:=(d, lg))).
  apply: call_rule=>//_ s6 E6 C6.
  apply: ret_rule=>i6 R6 e' lg' E0'.
  rewrite E0 in E0'; case: (hcancelV _ E0'); first by rewrite validPtUn.
  + case=>Z1 _; subst e'; move/(hcancelPtV _)=>/=.
  by rewrite validPt (rely_loc' _ R6)=>/(_ is_true_true)=><-.
do![apply: step]; apply: (gh_ex (g:=lg)).
apply: call_rule=>_; first by exists res; rewrite has_predC A.
move=>s5 E5 C5; apply: (gh_ex (g:=(d, lg))).
apply: call_rule=>//_ s6 E6 C6.
apply: ret_rule=>i6 R6 e' lg' E0'.
rewrite E0 in E0'; case: (hcancelV _ E0'); first by rewrite validPtUn.
- case=>Z1 _; subst e'; move/(hcancelPtV _)=>/=.
by rewrite validPt (rely_loc' _ R6)=>/(_ is_true_true)=><-.
Qed.                                                     

(**************************************************)
(*
Overall Implementation effort:

2 full person-days

TODO: Do something about severe proof duplication!

*)
(**************************************************)


(*****************************************************)
(*    Announcing a list of data transactions         *)
(*****************************************************)

Definition coord_loop_spec := forall dts,
  {(el : nat * Log)}, DHT [cn, W] 
  (fun i =>  loc i = st :-> (el.1, CInit) \+ log :-> el.2,
   fun (_ : unit) m => exists (chs : seq bool),
     loc m = st :-> (el.1 + (size dts), CInit) \+ log :-> (el.2 ++ (seq.zip chs dts))).
                                               

Program Definition coord_loop : coord_loop_spec :=
  fun dts  =>
    Do (fix rec dts :=
          (match dts with
           | d :: dts => coordinator_round d ;; rec dts
           | [::] => ret _ _ tt
           end)) dts.
Next Obligation.
apply:ghC=>i; elim: dts i=>//=[|d ds/= Hi]i1 [e lg] E1 C1. 
- by apply: ret_rule=>i2 R1; exists [::]; rewrite cats0 addn0 (rely_loc' _ R1).
apply: step; apply: (gh_ex (g:=e)); apply: (gh_ex (g:=lg)).
apply: call_rule=>//b i2/=E2 C2/=.
move:(Hi i2 (e.+1, rcons lg (b, d)) E2 C2)=>/=; apply: vrf_mono=>_ i3 [chs]->.
rewrite -[e.+1]addn1 -[(size ds).+1]addn1 addnAC addnA; exists (b :: chs)=>/=.
by rewrite -cats1 -!catA/=.
Qed.

Program Definition coordinator_loop_zero (ds : seq data) : 
  DHT [cn, W] 
  (fun i =>  loc i = st :-> (0, CInit) \+ log :-> ([::] : seq (bool * data)),
   fun (_ : unit) m => exists (chs : seq bool),
       loc m = st :-> (size ds, CInit) \+ log :-> (seq.zip chs ds))
  := Do (coord_loop ds).
Next Obligation.
by move=>i/=E; apply: (gh_ex (g:=(0, [::]))); apply: call_rule.
Qed.

(*****************************************************)
(*          Checking the invariant rule              *)
(*****************************************************)

(* Section CheckingDummyInv. *)

(* Require Import TwoPhaseInductiveInv. *)
(* Definition tpc' := tpc_with_inv l cn pts others Hnin PtsNonEmpty. *)

(* Definition W' := mkWorld tpc'. *)
(* Notation ii := (tpc_ii l cn pts others Hnin PtsNonEmpty). *)

(* (* Check with_inv ii. *) *)

(* Program Definition coordinator_inv (d : data) : *)
(*   {(e : nat)(lg : Log)}, DHT [cn, W']  *)
(*   (fun i => loc i = st :-> (e, CInit) \+ log :-> lg, *)
(*    fun r m => 1 == 1 /\ *)
(*        loc m = st :-> (e.+1, CInit) \+ log :-> rcons lg (r, d)) *)
(*   := Do (with_inv ii (coordinator_round d)). *)
(* Next Obligation. *)
(* move=>i1/=[e][lg]E1; apply with_inv_rule'. *)
(* apply: (gh_ex (g:=e)); apply: (gh_ex (g:=lg)). *)
(* apply: call_rule=>//r m H/=C' I e' lg' E'. *)
(* have X: e' = e /\ lg' = lg. *)
(* rewrite E1 in E'; case: (hcancelV _ E'); first by rewrite hvalidPtUn. *)
(* - case=>Z1 _; subst e'; move/(hcancelPtV _)=>/=. *)
(*   by rewrite hvalidPt/=/(_ is_true_true)=><-. *)
(* case: X=>Z1 Z2; subst e' lg'; split; last by []. *)
(* move: I; rewrite/TwoPhaseInductiveInv.Inv. *)
(* done. *)
(* Qed. *)

(* End CheckingDummyInv. *)

End CoordinatorImplementation.
End TwoPhaseCoordinator.

Module Exports.
Section Exports.

Definition coordinator_loop_zero := coordinator_loop_zero.
Definition coordinator_loop := coord_loop.
Definition coordinator_round := coordinator_round.

End Exports.
End Exports.

End TwoPhaseCoordinator.

Export TwoPhaseCoordinator.Exports.

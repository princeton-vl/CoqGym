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
From DiSeL
Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL
Require Import InductiveInv While.
From DiSeL
Require Import CalculatorProtocol CalculatorInvariant.
From DiSeL
Require Import CalculatorClientLib.
From DiSeL
Require Import SeqLib.

Section CalculatorServerLib.

Variable l : Label.
Variable f : input -> option nat.
Variable prec : input -> bool.
Variables (cs cls : seq nid).
Notation nodes := (cs ++ cls).
Hypothesis Huniq : uniq nodes.

Notation cal := (CalculatorProtocol f prec cs cls l).
Notation sts := (snd_trans cal).
Notation rts := (rcv_trans cal).
Notation W := (mkWorld cal).

(* A server node *)
Variable sv : nid.
Hypothesis  Hs : sv \in cs.
Notation loc i := (getLocal sv (getStatelet i l)).

(***********************)
(* Server receive loop *)
(***********************)

Export CalculatorProtocol.

Program Definition tryrecv_req_act := act (@tryrecv_action_wrapper W sv
      (fun k _ t b => (k == l) && (t == req)) _).
Next Obligation. by case/andP:H=>/eqP->; rewrite domPt inE/=. Qed.

(* Receive-transition for the calculator *)
Program Definition tryrecv_req :
  {ps : reqs}, DHT [sv, W]
  (fun i => loc i = st :-> ps,
   fun (r : option perm) m =>
     match r with
     | Some (from, t, args) =>
       [/\ loc m = st :-> ((from, sv, args) :: ps),
        prec args & from \in cls]
     | None => loc m = st :-> ps
     end) 
  := Do tryrecv_req_act.    
Next Obligation.
apply: ghC=>i1 ps E1 C1.
apply: act_rule=>i2 R1; split=>//=; first by apply: (proj2 (rely_coh R1)).
move=>r i3 i4[_]/=St R3.
case: St=>C2; case.
- by move=>[]?->Z; subst i3;rewrite (rely_loc' _ R3) (rely_loc' _ R1).
case=>k[m][tms][from][rt][pf'][[F]]H1 H2 H3/andP[/eqP Z]H4/= Z'->; subst k i3. 
move: rt  pf' (coh_s l C2) H1 H2 H3 H4 R3.
rewrite prEq=>rt  pf' cohs H1 H2 H3 H4 R3.
case: H1 H4; last by case=>//=->. 
move=>Z _; subst rt; move: H3; rewrite /msg_wf/=/sr_wf=>->; split=>//.
set d := (getStatelet i2 l).
have P1: valid (dstate d) by apply: (cohVl cohs).
have P2: valid i2 by apply: (cohS (proj2 (rely_coh R1))).
have P3: l \in dom i2 by rewrite -(cohD(proj2(rely_coh R1)))domPt inE/=.
rewrite -(rely_loc' _ R1) in E1.
- by rewrite (rely_loc' _ R3)/= locE//=/sr_step Hs/= (getStK cohs E1).
case: (cohs)=>Cs _ _ _. move/esym: F=> F.
by case: Cs=>_/(_ _ _ F); rewrite /cohMsg/= H2/=; case.
Qed.

Definition receive_req_loop_cond (res : option (nid * input)) := res == None.

Definition receive_req_loop_inv (ps : reqs) :=
  fun (r : option (nid * input)) i =>
    match r with
     | Some (from, args) =>
       [/\ loc i = st :-> ((from, sv, args) :: ps),
        prec args & from \in cls]
     | None => loc i = st :-> ps
    end.

Program Definition receive_req_loop :
  {ps : reqs}, DHT [sv, W]
  (fun i => loc i = st :-> ps,
   fun (r : option (nid * input)) m =>
     exists from args,
     [/\ r = Some (from, args),
      loc m = st :-> ((from, sv, args) :: ps),
      from \in cls &
      prec args]) := 
  Do _ (@while sv W _ _ receive_req_loop_cond receive_req_loop_inv _
        (fun r => Do _ (
           r <-- tryrecv_req;
           match r with
           | Some (from, _, args) => ret _ _ (Some (from, args))
           | None => ret _ _ None
           end)) None).

Next Obligation. by apply: with_spec x. Defined.
Next Obligation.
by move:H; rewrite /receive_req_loop_inv (rely_loc' _ H0).
Qed.
Next Obligation.
apply:ghC=>i1 ps/=[/eqP H1]L1 C1; subst r.
apply: step; apply: (gh_ex (g:=ps)).
apply: call_rule=>//r i2/=; case: r; last first.
- by move=>L2 C2; apply: ret_rule=>i3 R2; rewrite -(rely_loc' _ R2) in L2.
case=>[[from to] args]E2 C2; apply: ret_rule=>i3 R2/=.
by rewrite (rely_loc' _ R2). 
Qed.
Next Obligation.
apply: ghC=>i ps E1 C1; apply: (gh_ex (g:=ps)).
apply: call_rule=>//res m[].
rewrite /receive_req_loop_cond; case: res=>//=[[from args]]_ [H1 H2]C2.
by exists from, args. 
Qed.

Program Definition blocking_receive_req :
  {ps : reqs}, DHT [sv, W]
  (fun i => loc i = st :-> ps,
   fun (r : nid * input) m =>
     [/\ loc m = st :-> ((r.1, sv, r.2) :: ps),
      r.1 \in cls &
      prec r.2]) :=
  Do _ (r <-- receive_req_loop;
        match r with
        | Some res => ret _ _ res
        | None => ret _ _ (0, [::])
        end).
Next Obligation.
apply: ghC=>i ps E1 C1; apply: step; apply: (gh_ex (g:=ps)).
apply: call_rule=>//res i2[from][args][Z]E2 H1 H2 C2.
by subst res; apply: ret_rule=>i3 R2/=; rewrite (rely_loc' _ R2).
Qed.


(***************************)
(* Server sending messages *)
(***************************)


(* Generic server' send that assumes a permission to respond *)

Program Definition send_ans_act to msg :=
  act (@send_action_wrapper W cal sv l (prEq cal)
        (server_send_trans f prec cs cls) _ msg to).
Next Obligation. by rewrite /cal_sends /InMem/=; left. Qed.

Program Definition send_answer (to : nid) (args : seq nat) (ans : nat) :
  {ps : reqs}, DHT [sv, W]
  (fun i => [/\ loc i = st :-> ps, to \in cls,
             (to, sv, args) \in ps &
             f args = Some ans],                    
   fun (r : seq nat) m =>
       [/\ loc m = st :-> (remove_elem ps (to, sv, args)) &
       r = ans :: args]) 
  := Do send_ans_act to (ans :: args).    
Next Obligation.
apply: ghC=>i1 ps [L1]H1 H2 H3 C1.
apply: act_rule=>i2 R1.
move: (proj2 (rely_coh R1))=>C2.
case: (C2)=>_ _ _ _/(_ l); rewrite prEq=>C.
set d := (getStatelet i2 l).
split=>//[|r i3 i4[Sf]St R3].
- split=>//; first 1 last.
  + by rewrite/Actions.can_send mem_cat Hs/=
       -(cohD C2)/= domPt/= inE eqxx.
  + rewrite/Actions.filter_hooks umfilt0=>???.
    move => F.
    apply sym_eq in F.
    move: F.
    move/find_some.
    by rewrite dom0.
  split=>//; split=>//.
  exists C; rewrite -(rely_loc' _ R1) in L1; rewrite (getStK C L1).
  by apply/hasP; exists (to, sv, args)=>//=; rewrite H3 !eqxx.
rewrite (rely_loc' _ R3)=>{R3}.
case: St=>->[b]/=[][]->->/=; split=>//.
have P1: valid (dstate (getStatelet i2 l)). by apply: (cohVl C).
have P2: valid i2 by apply: (cohS (proj2 (rely_coh R1))).
have P3: l \in dom i2 by rewrite -(cohD(proj2(rely_coh R1))) domPt inE/=. 
rewrite -(rely_loc' _ R1) in L1.
by rewrite (pf_irr (ss_safe_coh _ ) C) locE// (getStK C L1).
Qed.

(**************************************************)
(*
Overall Implementation effort:

2 person-hours

*)
(**************************************************)


End CalculatorServerLib.

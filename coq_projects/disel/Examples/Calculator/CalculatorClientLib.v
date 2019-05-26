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
Require Import SeqLib.

Section CalculatorRecieve.

Variable l : Label.

Variable f : input -> option nat.
Variable prec : input -> bool.

Variable cs: seq nid.
Variable cls : seq nid.
(* All nodes *)
Notation nodes := (cs ++ cls).
(* All nodes are unique *)
Hypothesis Huniq : uniq nodes.

(* Protocol and its transitions *)

Notation cal := (cal_with_inv l f prec cs cls).
Notation sts := (snd_trans cal).
Notation rts := (rcv_trans cal).

Notation W := (mkWorld cal).

(* Variable d : dstatelet. *)
(* Hypothesis C : coh cal d. *)
(* Check proj2 C. *)
(* Check cal_inv_resp _ _ _ _ _ _ _ _ _ _ _ _ (proj1 C)(proj2 C). *)

Variable cl : nid.
Hypothesis  Hc : cl \in cls.

Program Definition tryrecv_resp_act := act (@tryrecv_action_wrapper W cl
      (fun k _ t b => (k == l) && (t == resp)) _).
Next Obligation. by case/andP:H=>/eqP->; rewrite domPt inE/=. Qed.

Notation loc i := (getLocal cl (getStatelet i l)).
Notation st := (ptr_nat 1).

Export CalculatorProtocol.

(* The following spec relates outstanding requests in
   pre/postconditions and also ensures that we've got the right
   answer. *)
Program Definition tryrecv_resp :
  {rs : reqs}, DHT [cl, W]
  (fun i => loc i = st :-> rs,
   fun (r : option perm) m =>
     match r with
     | Some (from, _, ms) =>
       let v := head 0 ms in
       let args := behead ms in
       exists rs' : reqs,
       [/\ loc m = st :-> rs',
        perm_eq rs ((cl, from, args) :: rs') &
        f args = Some v]
     | None => loc m = st :-> rs
     end) 
  := Do tryrecv_resp_act.    
Next Obligation.
apply: ghC=>i1 rs L1 C.
apply: act_rule=>i2 R1/=; split; first by case: (rely_coh R1).
move=>r i3 i4[Sf]S R3/=; rewrite -(rely_loc' l R1) in L1.
case: Sf=>_ _ _ _ /(_ l); clear C=>C.
case: S=>C2[|[l'][mid][tms][from][rt][pf][][E]Hin E1 Hw/=].
- by case=>?->Z; subst i3; rewrite (rely_loc' _ R3).
case/andP=>/eqP Z G; subst l'; set d := (getStatelet i2 l) in C E pf Hw *.
move=>Z->{r}; subst i3.
move: rt pf (coh_s l C2) Hin E1 Hw R3 C G.
rewrite prEq=>rt pf cohs Hin E1 Hw R3 C G.
case: Hin=>/=Z; do?[subst rt|case: Z]=>//Z; subst rt.
simpl in E1, Hw, R3; clear G.
rewrite /cr_wf/= in Hw.
case: tms E E1 R3 Hw=>t tms/= E E1 R3 Hw; subst t.
have A1: exists s', dsoup d = mid \\-> (Msg (TMsg resp tms) from cl true) \+ s'.
+ by move/esym/um_eta2: E=>->; exists (free mid (dsoup d)). 
case: A1=>s' Es.

(* Some auxiliary facts *)
have Y : tms = head 0 tms :: behead tms.
- suff M: exists x xs, tms = x::xs by case:M=>x [xs]E'; subst tms. 
  by case/andP: Hw=>_; case: (tms)=>//x xs _; exists x, xs.
have Y' : from \in cs.
- case: (proj1 C)=>Cs _ _ _. case: Cs=>Vs/(_ mid)Cs.
  rewrite Es in Vs Cs; move: (findPtUn Vs)=>Ez.
  by move: (Cs _ Ez)=>/=; rewrite/cohMsg/==>H; case: H.

(* Using the invariant *)
move: ((proj2 C) (proj1 C) cl from (head 0 tms) (behead tms) mid s' Hc Y')=>//=.
rewrite -!Y; move/(_ Es)=>F.
rewrite Y in Hw.

(* Proving the change in permissions *)
have X: (cl, from, (behead tms)) \in rs.
- by case/andP: Hw; rewrite (getStK (proj1 cohs) L1). 
have P1: valid (dstate d) by apply: (cohVl C).
have P2: valid i2 by apply: (cohS (proj2 (rely_coh R1))).
have P3: l \in dom i2 by rewrite -(cohD(proj2(rely_coh R1)))domPt inE/=. 
rewrite (rely_loc' _ R3)/= locE// /cr_step (getStK (proj1 cohs) L1)/=.
clear R3 Hw P1 P2 P3; exists (remove_elem rs (cl, from, (behead tms))). 
move: (remove_elem_in rs (cl, from, (behead tms))); rewrite X.
by rewrite perm_eq_sym=>H.
Qed.


Definition receive_loop_cond (res : option nat) := res == None .

Definition receive_loop_inv (rs : reqs) :=
  fun r i =>
    match r with
     | Some v =>
       exists (rs' : reqs) from args ,
       [/\ loc i = st :-> rs',
        perm_eq rs ((cl, from, args) :: rs') &
        f args = r]
     | None => loc i = st :-> rs
    end.

Program Definition receive_loop' :
  {(rs : reqs)}, DHT [cl, W]
  (fun i => loc i = st :-> rs,
   fun (res : option nat) m => 
     exists (rs' : reqs) v from args ,
       [/\ res = Some v, loc m = st :-> rs',
        perm_eq rs ((cl, from, args) :: rs') &
        f args = res]) :=
  Do _ (@while cl W _ _ receive_loop_cond receive_loop_inv _
        (fun r => Do _ (
           r <-- tryrecv_resp;
           match r with
           | Some (_, _, msg) => ret _ _ (Some (head 0 msg))
           | None => ret _ _ None
           end)) None).

Next Obligation. by apply: with_spec x. Defined.
Next Obligation.
by move:H; rewrite /receive_loop_inv (rely_loc' _ H0).
Qed.
Next Obligation.
apply:ghC=>i1 rs[];rewrite /receive_loop_cond.
move/eqP=>->/=E1 C1; apply: step; apply: (gh_ex (g:=rs)).
apply: call_rule=>//={r}res i2; case: res; last first.
- move=>E2 C; apply:ret_rule=>i3 R2.
  by rewrite /receive_loop_inv (rely_loc' _ R2).
case; case=>from v msg[rs'][E2]P F C2.
apply:ret_rule=>i3 R2; rewrite /receive_loop_inv (rely_loc' _ R2).
by exists rs', from, (behead msg).
Qed.

Next Obligation.
apply: ghC=>i rs E1 C1; apply: (gh_ex (g:=rs)).
apply: call_rule=>//res m[].
rewrite /receive_loop_cond; case: res=>//=v _.
move=>[rs'][from][args][E2]Hp F C2.
by exists rs', v, from, args. 
Qed.

(* Blocking receive-loop that always returns a result (but may not
   terminate) *)
Program Definition blocking_receive_resp :
  {(rs : reqs)}, DHT [cl, W]
  (fun i => loc i = st :-> rs,
   fun (res :  nat) m => 
     exists (rs': reqs) from args ,
       [/\ loc m = st :-> rs',
        perm_eq rs ((cl, from, args) :: rs') &
        f args = Some res]) :=
  Do _ (r <-- receive_loop';
        match r with
        | Some res => ret _ _ res
        | None => ret _ _ 0
        end).
Next Obligation.
apply: ghC=>i rs E1 C1; apply: step; apply: (gh_ex (g:=rs)).
apply: call_rule=>//res i2[rs'][v][from][args][Z]E2 H1 H2.
subst res=>C2; apply: ret_rule=>i3 R2.
by exists rs', from, args; rewrite (rely_loc' _ R2).
Qed.

(* Simple send_transition *)

Definition client_send_trans :=
  ProtocolWithInvariant.snd_transI (s2 l f prec cs cls).

Program Definition send_request server args :=
  act (@send_action_wrapper W cal cl l (prEq cal) client_send_trans _
                            args server).
Next Obligation. by rewrite InE; right; rewrite InE. Qed.


Program Definition compute_f (server : nid) (args: seq nat) : 
  DHT [cl, W]
  (fun i =>
     [/\ loc i = st :-> ([::] : reqs),
      prec args & server \in cs],
   fun (res : nat) m => loc m = st :-> ([::] : reqs) /\
                        f args = Some res) :=
  Do _ (send_request server args;;
        blocking_receive_resp).
Next Obligation.
move=>i1/=[E1 H2 H3]. 
apply: step; apply: act_rule=>i2 R1.
case: (rely_coh R1)=>_ C2.
have C': coh cal (getStatelet i2 l) by case: C2=>_ _ _ _/(_ l);rewrite prEq.
split=>//=.
- split=>//=.
  + by split=>//; case: C'. 
  + rewrite/Actions.can_send -(cohD C2)/=domPt inE/= eqxx.
    by rewrite mem_cat Hc orbC.
  + rewrite/Actions.filter_hooks umfilt0=>???.
    move => F.
    apply sym_eq in F.
    move: F.
    by move/find_some; rewrite dom0.
move=>y i3 i4[S]/=;case=>Z[b]/=[F]E3 R3; subst y.
case: F=>/=F; subst b i3=>/=.
rewrite -(rely_loc' _ R1) in E1.
rewrite (getStK _ E1) in R3.
apply: (gh_ex (g:=[:: (cl, server, args)])).
apply: call_rule=>//.
- move=>C4; rewrite (rely_loc' _ R3) locE//; last by apply: (cohVl C').
  + by rewrite -(cohD C2) domPt inE/=.
  by apply: (cohS C2).
clear R3=>v i5[rs'][from][args'][E5]P5 R C.  
suff X: args = args' /\ rs' = [::] by case: X=>Z X; subst args' rs'.  
suff X': rs' = [::].
- subst rs'; split=>//; move/perm_eq_mem: P5=>P5. 
  move/P5: (cl, server, args).
  by rewrite inE eqxx inE/==>/esym/eqP; case=>_->.
by case/perm_eq_size: P5=>/esym/size0nil. 
Qed.

(**************************************************)
(*
Overall Implementation effort:

5 person-hours

*)
(**************************************************)


(* More elaborated client program, compting a list of values *)

Definition compute_list_spec server ys :=
  forall (xs_acc : (seq input) * (seq (input * nat))),
  DHT [cl, W]
   (fun i =>
     let: (xs, acc) := xs_acc in         
     [/\ loc i = st :-> ([::] : reqs),
      all prec xs,
      all (fun e => f e.1 == Some e.2) acc,
      ys = map fst acc ++ xs &
      server \in cs],
   fun (res : seq (input * nat)) m =>
     [/\ loc m = st :-> ([::] : reqs),
      all (fun e => f e.1 == Some e.2) res &
      ys = map fst res]).

Program Definition compute_list_f server (xs : seq input) :
  DHT [cl, W]
   (fun i =>
     [/\ loc i = st :-> ([::] : reqs),
      all prec xs &
      server \in cs],
   fun (res : seq (input * nat)) m =>
     [/\ loc m = st :-> ([::] : reqs),
      all (fun e => f e.1 == Some e.2) res &
      xs = map fst res])
  :=
  Do (ffix (fun (rec : compute_list_spec server xs) xsa =>
    Do _ (let: (xs, acc) := xsa in         
          if xs is x :: xs' 
          then r <-- compute_f server x;
               let: acc' := rcons acc (x, r) in
               rec (xs', acc') 
          else ret _ _ acc)) (xs, [::])). 

Next Obligation.
move=>i1/=[L1]; move:l0 l4=>zs acc H1 H2 H3 H4.
case: zs H1 H3=>//=[_|z zs/andP[H1]H5] H3. 
- by rewrite cats0 in H3;
  apply: ret_rule=>i2 R1; split=>//; rewrite ?(rely_loc' _ R1)//.
apply: step; apply: call_rule=>//r i2[L2]F C2.
apply: call_rule=>//_; split=>//; first by rewrite all_rcons/= F eqxx.
by rewrite map_rcons/= -cats1 -catA cat_cons/=.
Qed.

Next Obligation.
by move=>i1/=[L1]??; apply: call_rule=>//; rewrite cats0.
Qed.

End CalculatorRecieve.

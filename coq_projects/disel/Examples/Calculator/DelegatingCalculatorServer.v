From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
From DiSeL
Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL
Require Import InductiveInv While.
From DiSeL
Require Import CalculatorProtocol CalculatorInvariant.
From DiSeL
Require Import CalculatorClientLib CalculatorServerLib.

Export CalculatorProtocol.

Section DelegatingCalculator.

Variables (l1 l2 : Label).
Hypothesis (lab_disj : l2 != l1).

Variable f : input -> option nat.
Variable prec : input -> bool.
Variables (cs1 cls1 : seq nid).
Variables (cs2 cls2 : seq nid).
Notation nodes1 := (cs1 ++ cls1).
Notation nodes2 := (cs2 ++ cls2).
Hypothesis Huniq1 : uniq nodes1.
Hypothesis Huniq2 : uniq nodes2.

(* Protocol I'm a server in *)
Notation cal1 := (cal_with_inv l1 f prec cs1 cls1).
Notation cal2 := (cal_with_inv l2 f prec cs2 cls2).

Notation W1 := (mkWorld cal1).
Notation W2 := (mkWorld cal2).

(* Composite world *)
Definition V := W1 \+ W2.
Lemma validV : valid V.
Proof.
rewrite /V; apply/andP=>/=.
split; first by rewrite validPtUn/= validPt/= domPt inE/=.
by rewrite unitR valid_unit.
Qed.

(* This server node *)
Variable sv : nid.
(* It's a server in protocol cal1 *)
Hypothesis  Hs1 : sv \in cs1.
(* It's a client in protocol cal2 *)
Hypothesis  Hc2 : sv \in cls2.
(* Delegate server *)
Variable sd : nid.
Hypothesis  Hs2 : sd \in cs2.

Notation loc i k := (getLocal sv (getStatelet i k)).
Notation loc1 i := (loc i l1).
Notation loc2 i := (loc i l2).

(* Delegate computation to someone else *)
Definition delegate_f := compute_f l2 f prec cs2 cls2 _ Hc2 sd.

Notation cal_ii := (ii l1 f prec cs1 cls1).

Definition receive_msg :=
  with_inv cal_ii (blocking_receive_req l1 f prec cs1 cls1 _ Hs1).
Definition send_ans to args ans :=
  with_inv cal_ii (send_answer l1 f prec cs1 cls1 _ Hs1 to args ans).

Definition delegating_body_spec :=
  forall _ : unit,
      DHT [sv, V]
  (fun i =>
     loc1 i = st :-> ([::]:reqs) /\
     loc2 i = st :-> ([::]:reqs),                    
   fun (r : unit) m =>
     loc1 m = st :-> ([::]:reqs) /\
     loc2 m = st :-> ([::]:reqs)).

Program Definition delegating_body :
  delegating_body_spec := fun (_ : unit) =>
  Do _ (
    r <-- uinject (receive_msg);
    let: (from, args) := r in
    (* Delegate computations *)
    ans <-- uinject (delegate_f args);
    uinject (send_ans from args ans);;
    ret sv V tt).

Lemma hook_complete_unit (c : context) : hook_complete (c, Unit).
Proof. by move=>????; rewrite dom0. Qed.

Lemma hooks_consistent_unit (c : context) : hooks_consistent c Unit.
Proof. by move=>????; rewrite dom0. Qed.

Next Obligation.
rewrite -(unitR V)/V.
have V: valid (W1 \+ W2 \+ Unit) by rewrite unitR validV.
apply: (injectL V); do?[apply: hook_complete_unit | apply: hooks_consistent_unit].
by move=>??????; rewrite dom0.
Defined.

Next Obligation.
rewrite -(unitR V)/V.
have V: valid (W1 \+ W2 \+ Unit) by rewrite unitR validV.
apply: (injectR V); do?[apply: hook_complete_unit | apply: hooks_consistent_unit].
by move=>??????; rewrite dom0.
Qed.

Next Obligation.
rewrite -(unitR V)/V.
have V: valid (W1 \+ W2 \+ Unit) by rewrite unitR validV.
apply: (injectL V); do?[apply: hook_complete_unit | apply: hooks_consistent_unit].
by move=>??????; rewrite dom0.
Defined.

Lemma hcomp l : hook_complete (mkWorld l).
Proof. by move=>????; rewrite dom0. Qed.

Next Obligation.
move=>i/=[K1 L1]; apply: vrf_coh=>CD1; apply: step.
move: (coh_split CD1 (hcomp cal1) (hcomp cal2))=>[i1[j1]][C1 D1 Z]; subst i.
apply: inject_rule=>//.
have E1 : loc (i1 \+ j1) l1 = loc i1 l1
  by rewrite (locProjL CD1 _ C1)// domPt inE/=.
rewrite E1 in K1.
apply: with_inv_rule=>//.
apply: (gh_ex (g:=[::])).
apply: call_rule=>//[[from args]] i2/=[K2]H1 H2 _ j2 CD2 R1.
have E2 : loc (i1 \+ j1) l2 = loc j1 l2.
  by rewrite (locProjR CD1 _ D1)// domPt inE/=.
(* Adapt the second protocol's view *)
rewrite E2 -(rely_loc' l2 R1) in L1.
apply: step; clear C1 D1.
have D2: j2 \In Coh W2 by case: (rely_coh R1)=>/= _; rewrite injExtL//(cohW CD1). 
clear R1; rewrite joinC; apply: inject_rule=>//.
apply: call_rule=>//ans j3[L3]F D3 i3 CD3/= R2.
have C3: i3 \In Coh W1 by case: (rely_coh R2)=>/= _; rewrite injExtR//(cohW CD3). 
apply: step; rewrite joinC. 
rewrite -(rely_loc' _ R2) in K2; move:K2=>K3; clear R2.
apply: inject_rule=>//; apply: with_inv_rule=>//.
apply: (gh_ex (g:=[:: (from, sv, args)])).
apply: call_rule; first by rewrite inE eqxx.
move=>_ i4 [K4 _] _ j4 CD4 R3.
rewrite -(rely_loc' _ R3) in L3; move: L3=>L4.
apply: ret_rule=>m R _; rewrite (rely_loc' _ R).
move/rely_coh: (R3)=>[]; rewrite injExtL ?(cohW CD2)//.
move=>_ D4; clear R3; rewrite !(rely_loc' _ R); clear R.
have X: l2 \in dom W2.1 by rewrite domPt inE eqxx.
rewrite (@locProjR _ _ _ _ _ CD4 X D4); split=>//.
have X': l1 \in dom W1.1 by rewrite domPt inE eqxx.
rewrite /= eqxx in K4; rewrite (@locProjL _ _ _ _ _ CD4 X' _)//.
by apply: (cohUnKL CD4 D4); apply: hook_complete_unit.
Qed.

Definition delegating_server_loop_cond (res : unit) := true.

Definition delegating_server_loop_inv :=
  fun (_ r : unit) i =>
    loc1 i = st :-> ([::]:reqs) /\
    loc2 i = st :-> ([::]:reqs).

Program Definition delegating_server_loop :
  DHT [sv, V]
  (fun i => loc1 i = st :-> ([::]:reqs) /\
            loc2 i = st :-> ([::]:reqs),
   fun (r : unit) m => False) :=
  Do _ (@while sv V _ _ delegating_server_loop_cond delegating_server_loop_inv _
        (fun r => Do _ (delegating_body r))) tt.

Next Obligation. by apply: with_spec (x x0). Defined.
Next Obligation.
by move:H; rewrite /delegating_server_loop_inv !(rely_loc' _ H0).
Qed.
Next Obligation. by apply: with_spec x. Defined.
Next Obligation.
by apply: ghC=>i1 s[H1 H2] C1/=; apply: call_rule.
Qed.
Next Obligation.
move=>i/=E1; apply: call_rule'=>//.
- by move=>C1; exists tt=>//. 
by move=>s' m/(_ s')/=; case.
Qed.    

End DelegatingCalculator.

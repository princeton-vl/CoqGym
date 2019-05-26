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
Require Import SeqLib.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module CalculatorProtocol.
Section CalculatorProtocol.

Definition input := seq nat.

(* Partially defined function, e.g., 
   addition or multiplication require precisely two arguments *)

Variable f : input -> option nat.
Variable prec : input -> bool.
Hypothesis prec_valid :
  forall i, prec i -> exists v, f i = Some v.

(* Calculator nodes *)
Variable cs: seq nid.
Variable cls : seq nid.
(* All nodes *)
Notation nodes := (cs ++ cls).
(* All nodes are unique *)
Hypothesis Huniq : uniq nodes.

(* Protocol:

- "Clients" can send messages with requests as long as the request
  satisfies the precondition prec.

- "Clients" can receive messages from "servers" (i.e., calculators).

- "Servers" can receive messages as long as they satisfy the
  precondition and record the sender and the arguments in the
  permission list.

- "Servers" can respond to clients accordingly, given that the result
  satisfies the arguments.

*)


(* Defining state-space *)

(* Calculator server state *)
Definition st := ptr_nat 1.
(* 
Calculator state: 
  - client node id
  - server node id
  - client-provided id (e.g., hash of the input)
  - client input
*)

Definition perm := (nid * nat * (seq nat))%type.
Definition cstate := seq perm.

Definition all_valid (s : cstate) := all (fun e => prec e.2) s.

(* Local state coherence *)
Definition localCoh (n : nid) : Pred heap :=
  [Pred h | exists (s : cstate), h = st :-> s /\ all_valid s].


(* Tags *)
Definition req : nat := 0.
Definition resp : nat := 1.

Definition tags := [:: req; resp].

(* Coherent messages *)
Definition cohMsg (ms: msg TaggedMessage) : Prop :=
  let body := content ms in
  if tag body == resp then
    [/\ from ms \in cs, to ms \in cls &
        exists v args, tms_cont body = [:: v] ++ args]
  else [/\ tag body == req,
        from ms \in cls, to ms \in cs &
        exists args,
          tms_cont body = args /\
          prec args].

Definition soupCoh : Pred soup :=
  [Pred s | valid s /\ forall m ms, find m s = Some ms -> cohMsg ms].

Definition calcoh d : Prop :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soupCoh ds, dom dl =i nodes,
   valid dl &
   forall n, n \in nodes -> localCoh n (getLocal n d)].

(* Axioms of the coherence predicate *)
Lemma l1 d: calcoh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d: calcoh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d: calcoh d -> dom (dstate d) =i nodes.
Proof. by case. Qed.

(* Wrapping up the coherence predicate *)
Definition CalCoh := CohPred (CohPredMixin l1 l2 l3).

(* TODO: This lemma seems very generic, it is exactly the same in TPC.
   Refactor it! *)
Lemma consume_coh d m : CalCoh d -> soupCoh (consume_msg (dsoup d) m).
Proof.
move=>C; split=>[|m' msg]; first by apply: consume_valid; rewrite (cohVs C).
case X: (m == m');[move/eqP: X=><-{m'}|].
- case/(find_mark (cohVs C))=>tms[E]->{msg}.
  by case:(C); case=>_/(_ m tms E).
rewrite eq_sym in X.
rewrite (mark_other (cohVs C) X)=>E.
by case:(C); case=>_; move/(_ m' msg E).
Qed.

Lemma trans_updDom this d s :
  this \in nodes -> CalCoh d -> dom (upd this s (dstate d)) =i nodes.
Proof.
move=>D C z; rewrite -(cohDom C) domU inE/=.
by case: ifP=>///eqP->{z}; rewrite (cohDom C) D; apply: cohVl C.
Qed.

(****************************************************)
(********* Getter lemmas for local state ************)
(****************************************************)

Lemma cs_in_nodes n : n \in cs -> n \in nodes.
Proof. by rewrite mem_cat=>->. Qed.

Lemma cohSt n d (C : CalCoh d) s:
  find st (getLocal n d) = Some s ->
  dyn_tp s = cstate.
Proof.
case: (C)=>_ _ _ G; case H: (n \in nodes).
- by move:(G _ H); case=>s'[]->_; rewrite findPt//=; case=><-.
rewrite /getLocal; rewrite -(cohDom C) in H.
by case: dom_find H=>//->; rewrite find0E.
Qed.

Definition getSt n d (C : CalCoh d) : cstate :=
  match find st (getLocal n d) as f return _ = f -> _ with
    Some v => fun epf => icast (sym_eq (cohSt C epf)) (dyn_val v) 
  | _ => fun epf => [::]
  end (erefl _).

Lemma getStK n d (C : CalCoh d)  s :
  getLocal n d = st :-> s -> getSt n C = s.
Proof.
move=>E; rewrite /getSt/=.
move: (cohSt C); rewrite !E/==>H. 
by apply: eqc.
Qed.

Lemma getStE n i j C C' (pf : n \in nodes) :
  getLocal n j = getLocal n i ->
  @getSt n j C' = @getSt n i C.
Proof.
case: {-1}(C)=>_ _ _/(_ _ pf).
by move=>[s][E]_; rewrite (getStK C E) E; move/(getStK C' )->.
Qed.

Lemma getStE' n i j C C' (pf : n \in nodes) :
  @getSt n j C' = @getSt n i C ->
  getLocal n j = getLocal n i.
Proof.
case: {-1}(C)=>_ _ _/(_ _ pf).
move=>[s][E]_; rewrite (getStK C E) E=>H.
case: {-1}(C')=>_ _ _/(_ _ pf)=>[][s'][E']_.
by rewrite (getStK C' E') in H; subst s'. 
Qed.

(****************************************************)

Notation coh := CalCoh.

(*** Server Transitions ***)

Section ServerReceiveTransition.

Definition sr_wf d (_ : coh d) (this from : nid) msg :=
  prec msg.

Definition sr_step : receive_step_t coh :=
  fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) =>
    if this \in cs
    then let s := getSt this pf in
         st :-> ((from, this, m) :: s)
    else getLocal this d.

(* This looks extremely similar to TPC, so, perhaps this should be
   refactored as well. *)
Lemma sr_step_coh : r_step_coh_t sr_wf req sr_step.
Proof.
move=>d from this m C pf tms D F Wf T/=.
rewrite /sr_step; case X: (this \in cs); last first.
- split=>/=; first by apply: consume_coh.
  + by apply: trans_updDom.
  + by rewrite validU; apply: cohVl C.
  by move=>n Ni/=; case: (C)=>_ _ _/(_ n Ni)=>L; rewrite -(getLocalU)// (cohVl C).
split=>/=; first by apply: consume_coh.
- by apply: trans_updDom.  
- by rewrite validU; apply: cohVl C.
move=>n Ni/=; rewrite /localCoh/=.
rewrite /getLocal/=findU; case: ifP=>B/=; last by case: (C)=>_ _ _/(_ n Ni). 
move/eqP: B X=>Z/eqP X; subst n; rewrite (cohVl C)/=.
have Y: all_valid (getSt this C).
by case: {-1}(C)=>_ _ _/(_ _ pf)[]s[]/(getStK C)->.
exists ((from, this, tms_cont tms) :: (getSt this C)); split=>//. 
rewrite /all_valid/= in Y *; rewrite Y.
by rewrite /sr_wf in Wf; rewrite Wf.
Qed.

Definition server_recv_trans := ReceiveTrans sr_step_coh.

End ServerReceiveTransition.

Section ServerSendTransition.

Definition entry_finder (to : nid) msg :=
  let: ans := head 0 msg in
  fun e : perm => 
    let: (n, _, args) := e in
    [&& n == to, f args == Some ans &
        msg == ans :: args].

Definition can_send (s : cstate) to msg :=
  has (entry_finder to msg) s.

Definition ss_safe (this to : nid)
           (d : dstatelet) (msg : seq nat) :=
  to \in cls /\ this \in cs /\
  exists (C : coh d), 
  has (entry_finder to msg) (getSt this C).         

Lemma ss_safe_coh this to d m : ss_safe this to d m -> coh d.
Proof. by case=>_[]_[]. Qed.

Lemma ss_safe_in this to d m : ss_safe this to d m ->
                             this \in nodes /\ to \in nodes.
Proof.
by rewrite !mem_cat; case=>->[->]_; split=>//; rewrite orbC.
Qed.

Lemma ss_safe_this this to d m :
  ss_safe this to d m -> this \in cs.
Proof. by case=>_[?][]. Qed.

Definition ss_step (this to : nid) (d : dstatelet)
           (msg : seq nat)
           (pf : ss_safe this to d msg) :=
  let C := ss_safe_coh pf in 
  let s := getSt this C in
  Some (st :-> remove_elem s (to, this, (behead msg))).

Lemma ss_step_coh : s_step_coh_t coh resp ss_step.
Proof.
move=>this to d msg pf h[]->{h}.
have C : (coh d) by case: pf=>?[_][].
split=>/=.
- split=>[|i ms/=]; first by rewrite valid_fresh (cohVs C).
  rewrite findUnL; last by rewrite valid_fresh (cohVs C). 
  case: ifP=>E; first by case: C=>[[Vs]]H _ _ _; move/H.
  move/findPt_inv=>[Z G]; subst i ms.
  split; rewrite ?(proj2 (ss_safe_in pf))?(ss_safe_this pf)//.
  case: pf=>?[C'][tf]/hasP[]=>[[[n]]]h args
             _/andP[/eqP]Z1/andP[/eqP Z2]/eqP Z3//=.
  case: pf=>[_][_][C']/hasP[[[x1] x2]]x3 H/andP[Z1]/andP[Z2]/eqP->.
  by exists (head 0 msg), x3. 
- move=>z.
  move: (getSt this (ss_safe_coh pf) )=>G.
  rewrite -(cohDom C) domU inE/= (cohVl C).
  by case: ifP=>///eqP->{z}; rewrite (cohDom C)(proj1 (ss_safe_in pf)). 
- by rewrite validU; apply: cohVl C.
move=>n Ni. rewrite /localCoh/=.
rewrite /getLocal/=findU; case: ifP=>B/=; last by case: C=>_ _ _/(_ n Ni). 
move/eqP: B=>Z; subst n; rewrite (cohVl C).
exists (remove_elem (getSt this (ss_safe_coh pf)) (to, this, behead msg)).
split=>//; apply: remove_elem_all.
by case: {-1}(ss_safe_coh pf)=>_ _ _/(_ _ Ni)[]s[]/(getStK (ss_safe_coh pf))->.
Qed.

Lemma ss_safe_def this to d msg :
      ss_safe this to d msg <->
      exists b pf, @ss_step this to d msg pf = Some b.
Proof.
split=>[pf/=|]; last by case=>?[]. 
set b := let C := ss_safe_coh pf in 
         let s := getSt this C in
         st :-> remove_elem s (to, this, (behead msg)).
by exists b, pf. 
Qed.

Definition server_send_trans :=
  SendTrans ss_safe_coh ss_safe_in ss_safe_def ss_step_coh.

End ServerSendTransition.

(**************************)
(*** Client transitions ***)
(**************************)

Section ClientSendTransition.

Definition cs_safe (this to : nid)
           (d : dstatelet) (msg : seq nat) :=
  [/\ to \in cs, this \in cls, coh d & prec msg].         

Lemma cs_safe_coh this to d m : cs_safe this to d m -> coh d.
Proof. by case=>_[]. Qed.

Lemma cs_safe_in this to d m : cs_safe this to d m ->
                             this \in nodes /\ to \in nodes.
Proof.
by rewrite !mem_cat; case=>->->/=_ _; split=>//; rewrite orbC. 
Qed.

Definition cs_step (this to : nid) (d : dstatelet)
           (msg : seq nat)
           (pf : cs_safe this to d msg) :=
  let C := cs_safe_coh pf in 
  let s := getSt this C in
  Some (st :-> ((this, to, msg)::s)).


Lemma cs_step_coh : s_step_coh_t coh req cs_step.
Proof.
move=>this to d msg pf h[]->{h}.
have C : (coh d) by case: pf=>?[].
split=>/=.
- split=>[|i ms/=]; first by rewrite valid_fresh (cohVs C).
  rewrite findUnL; last by rewrite valid_fresh (cohVs C). 
  case: ifP=>E; first by case: C=>[[Vs]]H _ _ _; move/H.
  move/findPt_inv=>[Z G]; subst i ms.
  split=>//; rewrite ?(proj2 (cs_safe_in pf));
  rewrite ?(proj2 (cs_safe_in pf))?(cs_safe_this pf)//=;
  by case: pf=>// _ _ _; exists msg.
- move=>z; move: (getSt this (cs_safe_coh pf))=>G.
  rewrite -(cohDom C) domU inE/= (cohVl C).
  by case: ifP=>///eqP->{z}; rewrite (cohDom C)(proj1 (cs_safe_in pf)). 
- by rewrite validU; apply: cohVl C.
move=>n Ni. rewrite /localCoh/=.
rewrite /getLocal/=findU; case: ifP=>B; last by case: C=>_ _ _/(_ n Ni). 
move/eqP: B=>Z; subst n; rewrite (cohVl C)/=.
exists ((this, to, msg) :: getSt this (cs_safe_coh pf)); split=>//.
have Y: all_valid (getSt this (cs_safe_coh pf)).
by case: {-1}(cs_safe_coh pf)=>_ _ _/(_ _ Ni)[]s[]/(getStK (cs_safe_coh pf))->.
by rewrite /=Y andbC/=; case: (pf).
Qed.

Lemma cs_safe_def this to d msg :
      cs_safe this to d msg <->
      exists b pf, @cs_step this to d msg pf = Some b.
Proof.
split=>[pf/=|]; last by case=>?[]. 
set b := let C := cs_safe_coh pf in 
         let s := getSt this C in
         st :-> ((this, to, msg)::s).
by exists b, pf. 
Qed.

Definition client_send_trans :=
  SendTrans cs_safe_coh cs_safe_in cs_safe_def cs_step_coh.

End ClientSendTransition.

Section ClientReceiveTransition.

Definition cr_wf d (C : coh d) this from (msg : seq nat) :=
  let s := getSt this C in
  let: args := (behead msg) in
  [&& (this, from, args) \in s &
     size msg > 2].

Definition cr_step : receive_step_t coh := 
  fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) =>
    let s := getSt this pf : seq perm in
    st :-> remove_elem s (this, from, (behead m) : seq nat).

Lemma cr_step_coh : r_step_coh_t cr_wf resp cr_step.
Proof.
move=>d from this m C pf tms D F Wf T/=.
rewrite /sr_step; case X: (this \in cs); last first.
- split=>/=; first by apply: consume_coh.
  + by apply: trans_updDom.
  + by rewrite validU; apply: cohVl C.
  move=>n Ni/=; rewrite /localCoh/=.
  rewrite /getLocal/=findU; case: ifP=>B/=; last by case: (C)=>_ _ _/(_ n Ni). 
  move/eqP: B X=>Z/eqP X; subst n; rewrite (cohVl C)/=.
  exists (remove_elem (getSt this C) (this, from, behead tms)).  
  split=>//; apply: remove_elem_all.
  by case: {-1}(C)=>_ _ _/(_ _ Ni)[]s[]/(getStK (C))->.  
split=>/=; first by apply: consume_coh.
- by apply: trans_updDom.  
- by rewrite validU; apply: cohVl C.
move=>n Ni/=; rewrite /localCoh/=.
rewrite /getLocal/=findU; case: ifP=>B/=; last by case: (C)=>_ _ _/(_ n Ni). 
move/eqP: B X=>Z/eqP X; subst n; rewrite (cohVl C)/=.
exists (remove_elem (getSt this C) (this, from, behead tms)).  
split=>//; apply: remove_elem_all.
by case: {-1}(C)=>_ _ _/(_ _ Ni)[]s[]/(getStK (C))->.  
Qed.

Definition client_recv_trans := ReceiveTrans cr_step_coh.

End ClientReceiveTransition.


Section Protocol.

Variable l : Label.

Definition cal_sends :=    [:: server_send_trans; client_send_trans].
Definition cal_receives := [:: server_recv_trans; client_recv_trans].

Program Definition CalculatorProtocol : protocol :=
  @Protocol _ l _ cal_sends cal_receives _ _.

End Protocol.
End CalculatorProtocol.

Module Exports.

Definition CalculatorProtocol := CalculatorProtocol.

Definition CalCoh := CalCoh.

Definition server_send_trans := server_send_trans.
Definition server_recv_trans := server_recv_trans.
Definition client_send_trans := client_send_trans.
Definition client_recv_trans := client_recv_trans.

Definition req := req.
Definition resp := resp.
Notation input := (seq nat).
Definition cstate := cstate.

Definition getSt := getSt.
Definition getStK := getStK.
Definition getStE := getStE.
Definition getStE' := getStE'.

End Exports.

End CalculatorProtocol.

(**************************************************)
(*
Overall Implementation effort:

4 person-hours

*)
(**************************************************)
 
Export CalculatorProtocol.Exports.

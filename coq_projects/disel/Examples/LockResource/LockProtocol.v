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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module LockProtocol.
Section LockProtocol.

Variable server : nid.
Variable clients : seq nid.

Hypothesis Hnin : server \notin clients.
Hypothesis Huniq : uniq clients.

Lemma client_not_server n : n \in clients -> (n == server) = false.
Proof.
  move=>H.
  case E: (n == server)=>//.
  move/eqP in E. subst n.
  move: (Hnin).
  by rewrite H.
Qed.

Definition nodes := [:: server] ++ clients.

Lemma client_nodes n : n \in clients -> n \in nodes.
Proof.
  by rewrite inE orbC/= =>->.
Qed.

Notation epoch := nat (only parsing).

Record server_state :=
  ServerState {
      outstanding : seq nid;
      current_epoch : epoch;
      current_holder : option nid
    }.

Inductive client_state :=
| NotHeld
| Held of epoch.

Definition acquire_tag := 0.
Definition grant_tag := 1.
Definition release_tag := 2.

Definition msg_from_server ms e :=
  (tag ms == grant_tag) && (tms_cont ms == [:: e]).

Definition msg_from_client ms :=
  ((tag ms == acquire_tag) || (tag ms == release_tag)) &&
  (tms_cont ms == [::]).

Definition coh_msg pkt e :=
  if from pkt == server
  then to pkt \in clients /\ msg_from_server (content pkt) e
  else if from pkt \in clients
  then to pkt == server /\ msg_from_client (content pkt)
  else False.

Definition st := ptr_nat 1.

Definition client_local_coh (cs : client_state) :=
  [Pred h | h = st :-> cs].

Definition server_local_coh (ss : server_state) :=
  [Pred h | h = st :-> ss].

Definition local_coh (n : nid) :=
  [Pred h | valid h /\
   if n == server
   then exists ss, server_local_coh ss h
   else n \in clients /\
        exists cs, client_local_coh cs h].

Definition soup_coh : Pred soup :=
  [Pred s |
    valid s /\
    forall m ms, find m s = Some ms -> active ms -> exists e, coh_msg ms e].

Lemma soup_coh_post_msg d m:
    soup_coh (dsoup d) -> (exists e, coh_msg m e) -> soup_coh (post_msg (dsoup d) m).1.
Proof.
move=>[H1 H2][y]Cm; split=>[|i ms/=]; first by rewrite valid_fresh.
rewrite findUnL; last by rewrite valid_fresh.
case: ifP=>E; first by move/H2.
by move/findPt_inv=>[Z G]; subst i m; exists y.
Qed.

Definition state_coh d :=
  forall n, n \in nodes -> local_coh n (getLocal n d).

Definition lock_coh d :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soup_coh ds
   , dom dl =i nodes
   , valid dl
   & state_coh d].

Lemma l1 d: lock_coh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d: lock_coh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d: lock_coh d -> dom (dstate d) =i nodes.
Proof. by case. Qed.

Definition LockCoh := CohPred (CohPredMixin l1 l2 l3).

Lemma consume_coh d m : LockCoh d -> soup_coh (consume_msg (dsoup d) m).
Proof.
move=>C; split=>[|m' msg]; first by apply: consume_valid; rewrite (cohVs C).
case X: (m == m');[move/eqP: X=><-{m'}|].
- case/(find_mark (cohVs C))=>tms[E]->{msg}.
  by case:(C); case=>_/(_ m tms E).
rewrite eq_sym in X.
rewrite (mark_other (cohVs C) X)=>E.
by case:(C); case=>_; move/(_ m' msg E).
Qed.

Lemma coh_dom_upd this d s :
  this \in nodes -> LockCoh d -> dom (upd this s (dstate d)) =i nodes.
Proof.
move=>D C z; rewrite -(cohDom C) domU inE/=.
by case: ifP=>///eqP->{z}; rewrite (cohDom C) D; apply: cohVl C.
Qed.

Definition server_send_step (ss : server_state) (to : nid) : server_state :=
  if to \in clients
  then if outstanding ss is _ :: out'
       then ServerState out' (S (current_epoch ss)) (Some to)
       else ss
  else ss.

Definition client_send_step (cs : client_state) : client_state :=
  NotHeld. (* ! *)



Definition server_recv_step (ss : server_state) (from : nid)
           (mtag : nat) (mbody : seq nat) : server_state :=
  if mtag == acquire_tag
  then
    ServerState (rcons (outstanding ss) from) (current_epoch ss) (current_holder ss)
  else (* mtag == release_tag *)
    ServerState (outstanding ss) (current_epoch ss) None.


Definition client_recv_step (cs : client_state) (from : nid)
           (mtag : nat) (mbody : seq nat) : client_state :=
  if mbody is [:: e]
  then Held e
  else NotHeld.

Section GetterLemmas.

Lemma getLocal_coh n d (C : LockCoh d):
  n \in nodes ->
  valid (getLocal n d) /\
  if n == server
  then exists (ss : server_state),
      getLocal n d = st :-> ss
  else (n \in clients) /\
       exists (cs : client_state),
           getLocal n d = st :-> cs.
Proof.
  by case: C=>_ _ _ /(_ n)G; rewrite /local_coh/=.
Qed.

Lemma getLocal_server_st_tp d (C : LockCoh d) s:
  find st (getLocal server d) = Some s ->
  dyn_tp s = server_state.
Proof.
have pf: server \in nodes by rewrite inE eqxx.
move: (getLocal_coh C pf); rewrite eqxx; move =>[V][s']Z; rewrite Z in V *.
rewrite findPt /=.
by case =><-.
Qed.

Lemma getLocal_client_st_tp n d (C : LockCoh d) (H : n \in clients) s:
  find st (getLocal n d) = Some s ->
  dyn_tp s = client_state.
Proof.
have pf: n \in nodes by rewrite inE/= orbC H.
move: (getLocal_coh C pf); rewrite H=>[[V]].
rewrite client_not_server//.
move=>[_][cs] L. rewrite L in V *.
rewrite findPt /=.
by case=> <-.
Qed.

Definition getSt_server d (C : LockCoh d) : server_state :=
  match find st (getLocal server d) as f return _ = f -> _ with
    Some v => fun epf => icast (sym_eq (getLocal_server_st_tp C epf)) (dyn_val v)
  | _ => fun epf => ServerState [::] 0 None
  end (erefl _).

Lemma getSt_server_K d (C : LockCoh d) m :
  getLocal server d = st :-> m -> getSt_server C = m.
Proof.
move=>E; rewrite /getSt_server/=.
have pf: server \in nodes by rewrite inE eqxx.
have V: valid (getLocal server d) by case: (getLocal_coh C pf).
move: (getLocal_server_st_tp C); rewrite !E=>/= H.
by apply: eqc.
Qed.

Program Definition getSt_client c d (C : LockCoh d) (pf : c \in nodes) : client_state.
case X: (c \in clients); last by exact: NotHeld.
exact: (match find st (getLocal c d) as f return _ = f -> _ with
    Some v => fun epf => icast (sym_eq (getLocal_client_st_tp C X epf)) (dyn_val v)
  | _ => fun epf => NotHeld
  end (erefl _)).
Defined.

Lemma getSt_client_K c d (C : LockCoh d) (pf : c \in nodes) m :
  c \in clients -> getLocal c d = st :-> m -> getSt_client C pf = m.
Proof.
move=>X E; rewrite /getSt_client/=.
have V: valid (getLocal c d) by case: (getLocal_coh C pf).
move: (getLocal_client_st_tp C); rewrite X !E=>/= H.
by apply: eqc.
Qed.

End GetterLemmas.

Section ServerGenericSendTransitions.

Definition HServ this to := (this == server /\ to \in clients).

Variable the_tag : nat.

Variable prec : server_state -> nid -> seq nid -> Prop.

Hypothesis prec_safe :
  forall this to s m,
    HServ this to ->
    prec s to m ->
    coh_msg (Msg (TMsg the_tag m) this to true) (current_epoch s).

Notation coh := LockCoh.

Definition server_send_safe (this n : nid)
           (d : dstatelet) (msg : seq nat) :=
  HServ this n /\
  exists (C : coh d), prec (getSt_server C) n msg.

Lemma server_send_safe_coh this to d m : server_send_safe this to d m -> coh d.
Proof. by case=>_[]. Qed.

Lemma server_send_this_in this to : HServ this to -> this \in nodes.
Proof. by case=>/eqP->; rewrite inE eqxx. Qed.

Lemma server_send_to_in this to : HServ this to -> to \in nodes.
Proof. by case=>_; rewrite /nodes inE/= orbC=>->. Qed.

Lemma server_send_safe_in this to d m : server_send_safe this to d m ->
                                  this \in nodes /\ to \in nodes.
Proof.
by case=>[]=>G _; move/server_send_to_in: (G)->; case: G=>/eqP-> _; rewrite inE eqxx.
Qed.


Definition server_step (this to : nid) (d : dstatelet)
           (msg : seq nat)
           (pf : server_send_safe this to d msg) :=
  let C := server_send_safe_coh pf in
  let s := getSt_server C in
  Some (st :-> server_send_step s to).

Lemma server_step_coh : s_step_coh_t coh the_tag server_step.
Proof.
move=>this to d msg pf h[]->{h}.
have C : (coh d) by case: pf=>?[].
have E: this = server by case: pf=>[][]/eqP.
split=>/=.
- apply: soup_coh_post_msg; first by case:(server_send_safe_coh pf).
  case: (pf)=>H[C']P/=.
  eexists.
  by apply: (prec_safe _ P).
- by apply: coh_dom_upd=>//; case: (server_send_safe_in pf).
- by rewrite validU; apply: cohVl C.
move=>n Ni. rewrite /local_coh/=.
rewrite /getLocal/=findU; case: ifP=>B; last by case: C=>_ _ _/(_ n Ni).
move/eqP: B=>Z; subst n this; rewrite eqxx (cohVl C)/=.
split.
by rewrite validPt.
by eexists.
Qed.

Lemma server_step_def this to d msg :
      server_send_safe this to d msg <->
      exists b pf, @server_step this to d msg pf = Some b.
Proof.
split=>[pf/=|]; last by case=>?[].
set b := let C := server_send_safe_coh pf in
         let s := getSt_server C in
         st :-> (server_send_step s to).
by exists b, pf.
Qed.

Definition server_send_trans :=
  SendTrans server_send_safe_coh server_send_safe_in server_step_def server_step_coh.

End ServerGenericSendTransitions.

Section ServerSendTransitions.

Definition server_send_grant_prec (ss : server_state) to m :=
  exists rest e,
    ss = ServerState (to :: rest) e None /\
    m = [:: e].

Program Definition server_send_grant_trans : send_trans LockCoh :=
  @server_send_trans grant_tag server_send_grant_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /coh_msg eqxx; split=>//=.
case: H0=>[rest] [e] []-> ->/=. by rewrite /msg_from_server /= eqxx.
Qed.

End ServerSendTransitions.

Section ServerGenericReceiveTransitions.

Notation coh := LockCoh.

Variable the_tag : nat.
Variable server_recv_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool.

Definition rs_step : receive_step_t coh :=
  fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) =>
    if (this == server)
    then let s := getSt_server pf in
         st :-> server_recv_step s from the_tag m
    else getLocal this d.

Lemma rs_step_coh : r_step_coh_t server_recv_wf the_tag rs_step.
Proof.
move=>d from this m C pf tms D F Wf T/=.
rewrite /rs_step; case X: (this == server); last first.
- split=>/=; first by apply: consume_coh.
  + by apply: coh_dom_upd.
  + by rewrite validU; apply: cohVl C.
  by move=>n Ni/=; case: (C)=>_ _ _/(_ n Ni)=>L; rewrite -(getLocalU)// (cohVl C).
split=>/=; first by apply: consume_coh.
- by apply: coh_dom_upd.
- by rewrite validU; apply: cohVl C.
move=>n Ni/=; rewrite /local_coh/=.
rewrite /getLocal/=findU; case: ifP=>B/=; last by case: (C)=>_ _ _/(_ n Ni).
move/eqP: B X=>Z/eqP X; subst n this; rewrite eqxx (cohVl C)/=.
split; first by rewrite validPt.
by eexists.
Qed.

Definition rs_recv_trans := ReceiveTrans rs_step_coh.

End ServerGenericReceiveTransitions.

Section ServerReceiveTransitions.

Definition s_matches_tag (ss : server_state) from t :=
  (t == acquire_tag) ||
  ((t == release_tag) && (current_holder ss == Some from)).

Definition server_msg_wf d (C : LockCoh d) (this from : nid) :=
  [pred m : TaggedMessage | s_matches_tag (getSt_server C) from (tag m)].

Definition server_recv_acquire_trans := rs_recv_trans acquire_tag server_msg_wf.

Definition server_recv_release_trans := rs_recv_trans release_tag server_msg_wf.

End ServerReceiveTransitions.


Section ClientGenericSendTransitions.

Definition HClient this to := (this \in clients /\ to == server).

Variable the_tag : nat.

Variable prec : client_state -> nid -> seq nat -> Prop.

Hypothesis prec_safe :
  forall this to s m,
    HClient this to ->
    prec s to m ->
    msg_from_client (TMsg the_tag m).

Notation coh := LockCoh.

Lemma client_send_this_in this to : HClient this to -> this \in nodes.
Proof. case=>H _. by apply /client_nodes. Qed.

Definition client_send_safe (this n : nid)
           (d : dstatelet) (msg : seq nat) :=
  HClient this n /\
  exists (HC : HClient this n) (C : coh d), prec (getSt_client C (client_send_this_in HC)) n msg.

Lemma client_send_safe_coh this to d m : client_send_safe this to d m -> coh d.
Proof. by case => _[?][C]. Qed.

Lemma client_send_to_in this to : HClient this to -> to \in nodes.
Proof. by case=>_ /eqP->; rewrite /nodes inE/= eqxx. Qed.

Lemma client_send_safe_in this to d m : client_send_safe this to d m ->
                                  this \in nodes /\ to \in nodes.
Proof.
case=>_[HC][C]_.
split.
- exact: (client_send_this_in HC).
exact: (client_send_to_in HC).
Qed.

Definition client_step (this to : nid) (d : dstatelet)
           (msg : seq nat)
           (pf : client_send_safe this to d msg) :=
  let C := client_send_safe_coh pf in
  let s := getSt_client C (client_send_this_in (proj1 pf)) in
  Some (st :-> client_send_step s).

Lemma client_step_coh : s_step_coh_t coh the_tag client_step.
Proof.
move=>this to d msg pf h[]->{h}.
have C : (coh d) by exact: (client_send_safe_coh pf).
have E: this \in clients by case: pf=>_[][].
split=>/=.
- apply: soup_coh_post_msg; first by case:(client_send_safe_coh pf).
  case: (pf)=>_[H][C']P/=.
  exists 0.
  rewrite/coh_msg/= client_not_server// E.
  split; first by case: (H).
  by apply: (prec_safe H P).
- by apply: coh_dom_upd=>//; case: (client_send_safe_in pf).
- by rewrite validU; apply: cohVl C.
move=>n Ni. rewrite /local_coh/=.
rewrite /getLocal/=findU; case: ifP=>B; last by case: C=>_ _ _/(_ n Ni).
move/eqP: B=>Z; subst n.
rewrite client_not_server// (cohVl C)/=.
split.
- by rewrite validPt.
split=>//.
by eexists.
Qed.

Lemma client_step_def this to d msg :
      client_send_safe this to d msg <->
      exists b pf, @client_step this to d msg pf = Some b.
Proof.
split=>[pf/=|]; last by case=>?[].
set b := let C := client_send_safe_coh pf in
         let s := getSt_client C (client_send_this_in (proj1 pf)) in
         st :-> (client_send_step s).
by exists b, pf.
Qed.

Definition client_send_trans :=
  SendTrans client_send_safe_coh client_send_safe_in client_step_def client_step_coh.

End ClientGenericSendTransitions.

Section ClientSendTransitions.

Definition client_send_acquire_prec (cs : client_state) (to : nid) (m : seq nat) :=
  cs = NotHeld /\
  m = [::].

Program Definition client_send_acquire_trans : send_trans LockCoh :=
  @client_send_trans acquire_tag client_send_acquire_prec _.
Next Obligation.
apply/andP=>/=.
split=>//.
by case: H0=>_/eqP.
Qed.

Definition client_send_release_prec (cs : client_state) (to : nid) (m : seq nat) :=
  (exists e, cs = Held e) /\
  m = [::].

Program Definition client_send_release_trans : send_trans LockCoh :=
  @client_send_trans release_tag client_send_release_prec _.
Next Obligation.
apply/andP=>/=.
split=>//.
by case: H0=>_/eqP.
Qed.

End ClientSendTransitions.

Section ClientGenericReceiveTransitions.

Notation coh := LockCoh.

Variable the_tag : nat.
Variable client_recv_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool.

Definition rc_step : receive_step_t coh :=
  fun this (from : nid) (m : seq nat) d (pf : coh d) (pt : this \in nodes) =>
    if (this \in clients)
    then let s := getSt_client pf pt in
         st :-> client_recv_step s from the_tag m
    else getLocal this d.

Lemma rc_step_coh : r_step_coh_t client_recv_wf the_tag rc_step.
Proof.
move=>d from this m C pf tms D F Wf T/=.
rewrite /rc_step; case X: (this \in clients); last first.
- split=>/=; first by apply: consume_coh.
  + by apply: coh_dom_upd.
  + by rewrite validU; apply: cohVl C.
  have Y: forall z : nat_eqType, z \in nodes -> local_coh z (getLocal z d)
      by case: (C).
  by move=>n Ni/=; move: (Y n Ni)=>L; rewrite -(getLocalU)// (cohVl C).
split=>/=; first by apply: consume_coh.
- by apply: coh_dom_upd.
- by rewrite validU; apply: cohVl C.
move=>n Ni/=; rewrite /local_coh/=.
rewrite /getLocal/=findU; case: ifP=>B/=; last by case: (C)=>_ _ _/(_ n Ni).
move/eqP: B X=>Z/eqP X/= ;rewrite !(cohVl C); subst n.
split; first done.
move/eqP: X => X.
rewrite client_not_server X//.
split=>//.
by eexists _.
Qed.

Definition rc_recv_trans := ReceiveTrans rc_step_coh.

End ClientGenericReceiveTransitions.

Section ClientReceiveTransitions.

Definition client_msg_wf d (_ : LockCoh d) (this from : nid) :=
  [pred m : TaggedMessage | true].

Definition client_receive_grant_trans := rc_recv_trans grant_tag client_msg_wf.

End ClientReceiveTransitions.

Section Protocol.

Variable l : Label.

(* All send-transitions *)
Definition lock_sends :=
  [::
     server_send_grant_trans;
     client_send_acquire_trans;
     client_send_release_trans
  ].

(* All receive-transitions *)
Definition lock_receives :=
  [::
     server_recv_acquire_trans;
     server_recv_release_trans;
     client_receive_grant_trans
  ].

Program Definition LockProtocol : protocol :=
  @Protocol _ l _ lock_sends lock_receives _ _.

End Protocol.
End LockProtocol.

Module Exports.
Section Exports.

Definition LockProtocol := LockProtocol.

End Exports.
End Exports.

End LockProtocol.

Export LockProtocol.Exports.

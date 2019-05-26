From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem.
Require Classical_Prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* "Atomic" send/receive actions, coherent with the network semantics *)

Module Actions.

Section Actions.

Variable W : world.
Notation getS s l := (getStatelet s l).

(*

Action is defined with respect to the world (i.e., a number of
protocols) and label.

It changes the state as a whole, but, in fact, affects only a specific
statelet in it, associated with a specific label.


*)


Structure action (V : Type) (this : nid)
  := Action
       {
         (* a_lab : Label; *)
         (* a_lab_dom : a_lab \in ddom W; *)

         a_safe : state -> Prop;

         a_safe_coh : forall s, a_safe s -> s \In Coh W;


         (* safe_coh : forall s, a_safe s -> coh (getP a_lab) (getS s a_lab); *)

         a_step : forall s1, (a_safe s1) -> state -> V -> Prop;

         step_total : forall s (pf : a_safe s), exists s' r, a_step pf s' r;

         (* step_coh  : forall s1 s2 r, Coh W s1 -> *)
         (*     a_safe s1 -> a_step s1 s2 r -> coh (getP a_lab) (getS s2 a_lab); *)

         (* step_frame : forall s1 s2 r z, *)
         (*     a_lab != z -> Coh W s1 -> *)
         (*     a_safe s1 -> a_step s1 s2 r -> getS s1 z  = getS s2 z; *)
         
         (* Action step semantics respects the overall network semantics *)
         step_sem  : forall s1 (pf : a_safe s1) s2 r,
             a_step pf s2 r -> network_step W this s1 s2

       }.


(* Framing follows from the network semantics *)
Lemma step_other this V (a : action V this) l s1 s2 r n (pf : a_safe a s1):
  this != n -> a_step pf s2 r ->
  getLocal n (getS s1 l) = getLocal n (getS s2 l).
Proof.
move=>N S2; move: (step_sem S2)=>H.
by rewrite eq_sym in N; rewrite /getLocal !(step_is_local l H N).
Qed.

End Actions.

Section SkipActionWrapper.

Variable W : world.
Notation getP l := (getProtocol W l).
Notation getS s l := (getStatelet s l).
Variable this : nid.
Variable l : Label.
Variable p : protocol.
Variable pf : getP l = p.

Definition skip_safe s := Coh W s.

Variable V : Type.

(* Skip-like actions allow for reading from the state *)
Variable f : forall s, coh p (getS s l) -> V.

Lemma safe_local s : skip_safe s -> coh p (getS s l).
Proof. by rewrite -pf=>/(coh_s l). Qed.

Definition skip_step s1 (pf : skip_safe s1) (s2 : state) r :=
  [/\ s1 \In Coh W, s1 = s2 & r = f (safe_local pf)].

(* Lemma skip_step_safe s1 s2 r: skip_step s1 s2 r -> skip_safe s1. *)
(* Proof. by case. Qed. *)

Lemma skip_step_total s (S : skip_safe s) : exists s' r, skip_step S s' r.
Proof. by exists s, (f (safe_local S)). Qed.

Lemma skip_safe_coh s1 : skip_safe s1 -> Coh W s1.
Proof. by []. Qed.

Lemma skip_step_sem s1 (S : skip_safe s1) s2 r:
  skip_step S s2 r -> network_step W this s1 s2.
Proof. by move=>H; apply: Idle; case: H. Qed.

Definition skip_action_wrapper :=
  Action skip_safe_coh skip_step_total skip_step_sem.

End SkipActionWrapper.


Section TryReceiveActionWrapper.

Variable W : world.
Notation getP l := (getProtocol W l).
Notation getS s l := (getStatelet s l).
Variable this : nid.

(* 

Filter for specific 
 - protocol labels
 - message tags
 - message bodies
 *)
Variable filter : Label -> nid -> nat -> pred (seq nat).

(* Necessary validity lemmas *)
Variable f_valid_label : forall l n t m ,
    filter l n t m -> l \in dom (getc W).

(* Variable f_valid_tags : forall l t m , *)
(*     filter l t m -> t \in rcv_tags (getP l). *)

Definition tryrecv_act_safe (s : state) := s \In Coh W.

Lemma tryrecv_act_safe_coh s : tryrecv_act_safe s -> Coh W s.
Proof. by []. Qed.

(* Can we make it decidable rather than classic? *)
Definition tryrecv_act_step s1 s2 (r : option (nid * nat * seq nat)) :=
  exists (pf : s1 \In Coh W),
  (* No message to receive -- all relevant messages are marked *)
    ([/\ (forall l m tms from rt b,
          this \in nodes (getP l) (getS s1 l) -> 
          Some (Msg tms from this b) = find m (dsoup (getS s1 l)) ->
          rt \In (rcv_trans (getP l)) ->
          tag tms = (t_rcv rt) ->
          (* This is required for safety *)
          msg_wf rt (coh_s l pf) this from tms ->
          (* The filter applies *)   
          filter l from (t_rcv rt) (tms_cont tms) ->
          ~~b),
    r = None & s2 = s1] \/
   (* There is a message to receive and the transition can be executed *)
   exists l m tms from rt (pf' : this \in nodes (getP l) (getS s1 l)),
     let: d :=  getS s1 l in
     [/\ [/\ Some (Msg tms from this true) = find m (dsoup (getS s1 l)),
          rt \In (rcv_trans (getP l)),
          tag tms = (t_rcv rt),
          (* This is required for safety *)
          msg_wf rt (coh_s l pf) this from tms &
          (* The filter applies *)   
          filter l from (t_rcv rt) (tms_cont tms)],
      let loc' := receive_step rt from tms (coh_s l pf) pf' in
      let: f' := upd this loc' (dstate d) in
      let: s' := consume_msg (dsoup d) m in
      s2 = upd l (DStatelet f' s') s1 &
      r = Some (from, tag tms, tms_cont tms)]).

Import Classical_Prop.

Lemma tryrecv_act_step_total s:
  tryrecv_act_safe s -> exists s' r , tryrecv_act_step s s' r.
Proof.
move=>C; rewrite /tryrecv_act_step.
case: (classic (exists l m tms from rt (pf' : this \in nodes (getP l) (getS s l)),
                   let: d :=  getS s l in
                   [/\ Some (Msg tms from this true) = find m (dsoup (getS s l)),
                    rt \In (rcv_trans (getP l)),
                    tag tms = (t_rcv rt),
                    msg_wf rt (coh_s l C) this from tms &
                    filter l from (t_rcv rt) (tms_cont tms)])); last first.
- move=>H; exists s, None, C; left; split=>//l m tms from rt b T E1 E2 E3 E M.
  apply/negP=>Z; rewrite Z in E1; clear Z b; apply: H.
  by exists l, m, tms, from, rt.
case=>[l][m][tms][from][rt][T][E1 E2 E3 E M].
exists (let: d :=  getS s l in
        let loc' := receive_step rt from tms (coh_s l C) T in
        let: f' := upd this loc' (dstate d) in
        let: s' := consume_msg (dsoup d) m in
        upd l (DStatelet f' s') s), (Some (from, tag tms, tms_cont tms)).
by exists C; right; exists l, m, tms, from, rt, T. 
Qed.

Lemma tryrecv_act_step_safe s1 s2 r:
  tryrecv_act_step s1 s2 r -> tryrecv_act_safe s1.
Proof. by case. Qed.

Lemma tryrecv_act_step_sem s1 (S : tryrecv_act_safe s1) s2 r:
  tryrecv_act_step s1 s2 r -> network_step W this s1 s2.
Proof.
case=>C; rewrite /tryrecv_act_step; case; first by case=>_ _ ->; apply: Idle.
case=>[l][m][tms][from][rt][Y][[E R E1 M]]F/=Z _.
have X1: l \in dom s1 by move: (f_valid_label F); rewrite (cohD C).
by apply: (ReceiveMsg R X1 E1 (i := m) (from := from)).
Qed.

Definition tryrecv_action_wrapper :=
  Action tryrecv_act_safe_coh tryrecv_act_step_total tryrecv_act_step_sem.

End TryReceiveActionWrapper.

(* A wrapper for the send-action *)
Section SendActionWrapper.

Variable W : world.
Variable p : protocol.
Notation getP l := (getProtocol W l).
Notation getS s l := (getStatelet s l).
Variable this : nid.

Variable l : Label.

Variable pf : (getProtocol W l) = p.

(* A dedicated send-transition *)
Variable st: send_trans (coh p).
(* The transition is present *)
Variable pf' : st \In (snd_trans p).

(* The message and the recipient *)
Variable msg : seq nat.
Variable to  : nid.

(* This check is implicit in the action semantics *)
Definition can_send (s : state) := (l \in dom s) && (this \in nodes p (getS s l)).


(* Take only the hooks that affect the transition with a tag st of *)
(* protocol l *)
Definition filter_hooks (h : hooks) :=
  um_filter (fun e => e.2 == (l, t_snd st)) h.

Definition send_act_safe s :=
  [/\ Coh W s, send_safe st this to (getS s l) msg, can_send s &
      (* All hooks from a "reduced footprint" are applicable *)         
      all_hooks_fire (filter_hooks (geth W)) l (t_snd st) s this msg to].

Lemma send_act_safe_coh s : send_act_safe s -> Coh W s.
Proof. by case. Qed.

Lemma safe_safe s : send_act_safe s -> send_safe st this to (getS s l) msg.
Proof. by case. Qed.

Definition send_act_step s1 (S: send_act_safe s1) s2 r :=
   r = msg /\
   exists b,
     Some b = send_step (safe_safe S) /\
     let: d :=  getS s1 l in
     let: f' := upd this b (dstate d) in
     let: s' := (post_msg (dsoup d) (Msg (TMsg (t_snd st) msg)
                                         this to true)).1 in
     s2 = upd l (DStatelet f' s') s1.

Lemma send_act_step_total s (S: send_act_safe s): exists s' r , send_act_step S s' r.
Proof.
rewrite /send_act_step/send_act_safe.
case: S=>C S J K.
move/(s_safe_def): (S)=>[b][S']E.
set s2 := let: d :=  getS s l in
          let: f' := upd this b (dstate d) in
          let: s' := (post_msg (dsoup d) (Msg (TMsg (t_snd st) msg)
                                                this to true)).1 in
          upd l (DStatelet f' s') s.
exists s2, msg; split=>//; exists b; split=>//.
move: (safe_safe (And4 C S J K))=> S''.
by rewrite -E (pf_irr S'' S') .
Qed.

Lemma send_act_step_sem s1 (S : send_act_safe s1) s2 r:
  send_act_step S s2 r -> network_step W this s1 s2.
Proof.
case=>_[b][E Z]; case: (S)=>C S' /andP[D1] D2 K; subst s2=>/=.
rewrite (pf_irr (safe_safe S) S') in E; clear S.
rewrite /all_hooks_fire/filter_hooks in K.
move: st S' E K pf'; clear pf' st; subst p=>st S' E K' pf'.
apply: (@SendMsg W this s1 _ l st pf' to msg)=>////.
move=>z lc hk E'; apply: (K' z); rewrite E'.
by rewrite find_umfilt/= eqxx.
Qed.

Definition send_action_wrapper :=
  Action send_act_safe_coh send_act_step_total send_act_step_sem.

End SendActionWrapper.

End Actions.

Module ActionExports.

Definition action := Actions.action.
Definition a_safe := Actions.a_safe.
Definition a_step := Actions.a_step.

Definition a_safe_coh := Actions.a_safe_coh.
Definition a_step_total := Actions.step_total.
Definition a_step_sem := Actions.step_sem.
Definition a_step_other := Actions.step_other.

Definition skip_action_wrapper := Actions.skip_action_wrapper.
Definition send_action_wrapper := Actions.send_action_wrapper.
Definition tryrecv_action_wrapper := Actions.tryrecv_action_wrapper.

End ActionExports.

Export ActionExports.


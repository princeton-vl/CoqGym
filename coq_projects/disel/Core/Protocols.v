From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Definition of the protocols, including coherence predicate, tags,
   messages and transitions.  *)

Definition getLocal (n : nid) (d : dstatelet) : heap :=
  match find n (dstate d) with
  | Some h => h
  | None => Unit
  end.

Lemma getLocalU n m d s :
  valid (dstate d) -> m \in dom (dstate d) ->
  getLocal n d = (getLocal n {| dstate := upd m (getLocal m d) (dstate d); dsoup := s |}).
Proof.
move=>V H2; move/um_eta: (H2)=>[v2][F2 _].
rewrite /getLocal F2/=; case X: (n == m); last by rewrite findU X/=.
by move/eqP: X=>X; subst m; rewrite findU eqxx/=V F2.
Qed.
        
(* Definition castEqX T (t t' : eqTypeX) (r : t = t') (e : T t) := *)
(*   match r in (_ = t') return T t' with erefl => e end. *)

(* Definition eqcEqX X m' (r : m' = m') (e : X m') : castEqX r e = e. *)
(* Proof. by move: r; apply: Streicher_K. Qed. *)

Module Coherence.

Section CohDef.

(* Represent nodes as a decidable predicate, 
   which depends on the state *)
Variable nodes: dstatelet -> pred nid.

Notation protocol_soup  := (soup (TaggedMessage)).

Structure mixin_of (coh : Pred dstatelet) := Mixin {
    _   : forall d, coh d -> valid (dstate d);
    _   : forall d, coh d -> valid (dsoup d);
    _   : forall d, coh d -> dom (dstate d) =i nodes d;
}.

End CohDef.

Section ClassDef.

Variable nodes: dstatelet -> pred nid.

Notation class_of := mixin_of (only parsing).

Structure cohpred : Type := Pack {sort : dstatelet -> Prop;
                                  _ : class_of nodes sort}.
Local Coercion sort : cohpred >-> Funclass.

Variables (T : dstatelet -> Prop) (cT : cohpred).

Definition class := let: Pack _ c as cT' := cT
                    return class_of nodes cT' in c.

Definition pack c := @Pack T c.
Definition clone := fun c & T = cT & phant_id (pack c) cT => pack c. 

End ClassDef.

Module Exports.
Section Exports.

Variable Lstate : Type.
Variable nodes: dstatelet -> pred nid.

Coercion sort : cohpred >-> Funclass.
Definition cohpred := cohpred.
Definition CohPredMixin := Mixin.
Definition CohPred T m := (@pack T m).

Notation "[ 'cohPredMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'cohPredMixin'  'of'  T ]") : form_scope.
Notation "[ 'cohpred' 'of' T 'for' C ]" := (@clone T C _ (erefl _) id)
  (at level 0, format "[ 'cohpred'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'cohpred' 'of' T ]" := (@clone T _ _ (erefl _) id)
  (at level 0, format "[ 'cohpred'  'of'  T ]") : form_scope.

Canonical cohpred_PredType := mkPredType (@sort nodes).

Variable coh : cohpred nodes.

Lemma cohVl d : d \In coh -> valid (dstate d).
Proof. by case: coh=>p [H1 H2 H3]; apply: H1. Qed.

Lemma cohVs d : d \In coh -> valid (dsoup d).
Proof. by case: coh=>p [H1 H2 H3]; apply: H2. Qed.

Lemma cohDom d : d \In coh -> dom (dstate d) =i nodes d.
Proof. by case: coh=>p [H1 H2 H3]; apply: H3. Qed.

End Exports.
End Exports.
End Coherence.

Export Coherence.Exports.

Module Transitions.
Section Transitions.

Variable nodes: dstatelet -> pred nid.

Variable coh : cohpred nodes.

Notation lstate := heap%type.

Definition send_step_t (send_safe : nid -> nid -> dstatelet -> seq nat -> Prop) :=
  forall (this to : nid) (d : dstatelet)
         (msg : seq nat) (pf : send_safe this to d msg),
    option lstate.

Definition s_step_coh_t t_snd
           (send_safe : nid -> nid -> dstatelet -> seq nat -> Prop)
           (send_step : send_step_t send_safe) :=
  forall this to d msg (pf : send_safe this to d msg) b,
    let: f := dstate d in
    let: s := dsoup d  in
    Some b = @send_step this to d msg pf ->         
    let: f' := upd this b f in
    let: tms := TMsg t_snd msg in 
    let: s' := (post_msg s (Msg tms this to true)).1 in 
    coh (DStatelet f' s').

Structure send_trans := SendTrans
    {
      t_snd : nat;

      send_safe : nid -> nid -> dstatelet -> seq nat -> Prop;
      s_safe_coh : forall this to d m, send_safe this to d m -> coh d;
      s_safe_in  : forall this to d m, send_safe this to d m ->
                                       this \in nodes d /\ to \in nodes d;  

      (* Send is a partially defined function, initially it is allowed
         to observe the entire statelet d to avoif a complex
         precondition *)
      send_step : send_step_t send_safe;

      s_safe_def : forall this to d msg,
          send_safe this to d msg <->
          exists b pf, @send_step this to d msg pf = Some b;

      (* Sending preserves coherence *)
      s_step_coh : s_step_coh_t t_snd send_step 
    }.


Definition receive_step_t :=
  forall (this from: nid) (m : seq nat)
         (d : dstatelet) (pf : coh d)
         (pf' : this \in nodes d), lstate.

Definition r_step_coh_t (msg_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool)
           t_rcv (receive_step : receive_step_t) :=
  forall (d : dstatelet) from this i (C : coh d) (pf' : this \in nodes d)
         (m : TaggedMessage),
    let: f := dstate d in
    let: s := dsoup d  in
    this \in dom f ->
    find i s = Some (Msg m from this true) ->
    msg_wf d C this from m -> tag m = t_rcv ->
    let: loc' := receive_step this from m d C pf' in
    let: s'' := consume_msg s i in
    let: f' := upd this loc' f in
    coh (DStatelet f' s'').


Structure receive_trans := ReceiveTrans
    {
      t_rcv : nat;

      msg_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool;

      (* The semantics ensures the "well-formedness" of a message
         being reveived. The following transition, defined as a total
         function, is only executed if m satisfies the msg_wf
         check. However, we still need the coherence passed in order
         to provide facilities for dependently-typed programming.  *)
      receive_step : receive_step_t;

      (* Receiving preserves coherence *)
      r_step_coh : r_step_coh_t msg_wf t_rcv receive_step
    }.

End Transitions.

Module Exports.

Definition SendTrans := SendTrans.
Definition send_trans := send_trans.
Definition ReceiveTrans := ReceiveTrans.
Definition receive_trans := receive_trans.

Definition t_snd := t_snd.
Definition send_safe := send_safe.
Definition send_step := send_step.
Definition send_step_t := send_step_t.

Definition s_safe_coh := s_safe_coh.
Definition s_safe_in := s_safe_in.
Definition s_safe_def := s_safe_def.
Definition s_step_coh := s_step_coh.
Definition s_step_coh_t := s_step_coh_t.

Definition t_rcv := t_rcv.
Definition msg_wf := msg_wf.

Definition receive_step := receive_step.
Definition receive_step_t := receive_step_t.
Definition r_step_coh := r_step_coh.
Definition r_step_coh_t := r_step_coh_t.

End Exports.

End Transitions.

Export Transitions.Exports.

Module Protocols.
Section Protocols.

Definition snd_tags {nodes} {coh : cohpred nodes}
           (sts : seq (send_trans coh)) := 
  map (@t_snd nodes _) sts.

Definition rcv_tags {nodes} {coh : cohpred nodes} (sts : seq (receive_trans coh)) :=
  map (@t_rcv nodes _) sts.

Structure protocol := Protocol {
  nodes: dstatelet -> pred nid;
  plab : Label;                        
  coh : cohpred nodes ;
  snd_trans : seq (send_trans coh);
  rcv_trans : seq (receive_trans coh);

  (* All transition tags are unique *)
  snd_uniq : uniq (snd_tags snd_trans);
  rcv_uniq : uniq (rcv_tags rcv_trans);
}.

End Protocols.

Module Exports.
Section Exports.

Definition protocol := protocol.
Definition Protocol := Protocol.
Definition plab := plab.
Definition nodes := nodes.
Definition coh := coh.
Definition snd_trans := snd_trans.
Definition rcv_trans := rcv_trans.

(* Tags for transitions *)
Definition snd_tags p := snd_tags (snd_trans p).
Definition rcv_tags p := rcv_tags (rcv_trans p).

Definition snd_uniq := snd_uniq.
Definition rcv_uniq := rcv_uniq.

Definition cohMT d := d = empty_dstatelet.

Lemma pred0v1 d: cohMT d -> valid (dstate d).
Proof.
by rewrite /cohMT=>->; apply: valid_mt_state.
Qed.

Lemma pred0v2 d: cohMT d -> valid (dsoup d).
Proof.
by rewrite /cohMT=>->; apply: valid_mt_soup.
Qed.

Lemma pred0v3 d: cohMT d -> dom (dstate d) =i [::].
Proof. by rewrite /cohMT=>->; apply: mt_nodes. Qed.

Definition EmptyProtMixin := CohPredMixin pred0v1 pred0v2 pred0v3.
Definition empty_coh := CohPred EmptyProtMixin.

Lemma snd_uniq0 {nodes} {coh : cohpred nodes} :
  uniq (@Protocols.snd_tags _ coh ([::] : seq (send_trans coh))).
Proof. by []. Qed.

Lemma rcv_uniq0 {nodes} {coh : cohpred nodes} :
  uniq (@Protocols.rcv_tags nodes _ ([::] : seq (receive_trans coh))).
Proof. by []. Qed.

Definition EmptyProt i : protocol :=
  @Protocol (fun _ => pred0) i empty_coh [::] [::] snd_uniq0 rcv_uniq0.

End Exports.
End Exports.

End Protocols.

Export Protocols.Exports.

(* TODO: switch to dynamic values to avoid constant casts *)

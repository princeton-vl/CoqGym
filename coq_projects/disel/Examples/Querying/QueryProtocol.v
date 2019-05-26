From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
From fcsl
Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely Actions.
From DiSeL
Require Import SeqLib.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition left_inverse {A B : Type} (op: A -> B) (inv : B -> A) :=
  forall x, inv (op x) = x.

Definition fresh_id (xs : seq (nid * nat)) : nat :=
   (last 0 (sort oleq (unzip2 xs))).+1.      

Lemma zip_in2 (A B : eqType) (a : A) (b : B) xs:
  (a, b) \in xs -> b \in unzip2 xs.
Proof.
elim:xs=>//x xs Hi; rewrite inE.
case/orP; last by move/Hi=>/=; rewrite inE=>->; rewrite orbC. 
by case: x=>x y/=/eqP[]Z1 Z2; subst x y; rewrite inE eqxx.
Qed.

Lemma fresh_not_in z xs : (z, fresh_id xs) \notin xs.
Proof.
suff X: ~((z, fresh_id xs) \in xs) by apply/negP.
rewrite /fresh_id=>H.
move: (zip_in2 H)=>{H}X; set ls := (unzip2 xs) in X.
have G: sorted oleq (sort oleq ls).
- apply: (@sort_sorted [eqType of nat] oleq _).
  by rewrite /oleq/=/ord/=; move=>a b; case: ltngtP.
rewrite -(mem_sort oleq) in X.
move: (sorted_last_key_max 0 G X).
move: (last 0 (sort oleq ls))=>n.
by rewrite /oleq/=/ord orbC -leq_eqVlt ltnn. 
Qed.

(* Simple protocol for querying a state *)

Module QueryProtocol.
Section  QueryProtocol.

(* Arbitrary data type *)
Variable Data : Type.
Variable nodes : seq nat.

(* Serialize/decerialize functions *)
Variable serialize : Data -> seq nat.
Variable deserialize : seq nat -> Data.
Hypothesis ds_inverse : left_inverse serialize deserialize.

(* Protocol state *)
Definition st := ptr_nat 1.

(* Pending requests (client-side): node, request id *)
(* Pending responses (server-side): node, response id *)
Definition reqs := seq (nid * nat)%type.
Definition resp := seq (nid * nat)%type.

Definition qstate := (reqs * resp)%type.

(* All responses and requests are unique per-node *)
Definition localCoh (n : nid) : Pred heap :=
  [Pred h | exists (s : qstate), h = st :-> s /\ (uniq s.1 && uniq s.2)].

(* Tags *)
Definition treq : nat := 0.
Definition tresp : nat := 1.
Definition tags := [:: treq; tresp].

Definition cohMsg (ms: msg TaggedMessage) : Prop :=
  let body := content ms in
  (* If a message is a request, it carries a request number *)                                                           
  if tag body == treq then exists req_num, tms_cont body = [:: req_num]
  (* Otherwise it's a response and serialized data *)                                                           
  else exists resp_num sdata, tms_cont body = resp_num :: sdata.

Definition soupCoh : Pred soup :=
  [Pred s | valid s /\ forall m ms, find m s = Some ms -> cohMsg ms].

Definition qcoh d : Prop :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soupCoh ds, valid dl, dom dl =i nodes &
      forall n, n \in dom dl -> localCoh n (getLocal n d)].

(* Axioms of the coherence predicate *)
Lemma l1 d: qcoh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d: qcoh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d: qcoh d -> dom (dstate d) =i nodes.
Proof. by case. Qed.

(* Wrapping up the coherence predicate *)
Definition QCoh := CohPred (CohPredMixin l1 l2 l3).

(*********************************************************************)
(**********                Coherence lemmas                  *********)
(*********************************************************************)

Lemma send_soupCoh d m : 
    soupCoh (dsoup d) -> cohMsg m -> soupCoh (post_msg (dsoup d) m).1.
Proof.
move=>[H1 H2]Cm; split=>[|i ms/=]; first by rewrite valid_fresh.
rewrite findUnL; last by rewrite valid_fresh.
case: ifP=>E; [by move/H2|by move/findPt_inv=>[Z G]; subst i m].
Qed.

Lemma consume_coh d m : QCoh d -> soupCoh (consume_msg (dsoup d) m).
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
  this \in nodes -> QCoh d -> dom (upd this s (dstate d)) =i nodes.
Proof.
move=>D C z; rewrite -(cohDom C) domU inE/=.
by case: ifP=>///eqP->{z}; rewrite (cohDom C) D; apply: cohVl C.
Qed.

(****************************************************)
(********* Getter lemmas for local state ************)
(****************************************************)

(************** TODO: Refactor this!!! **************)
Lemma cohSt n d (C : QCoh d) s:
  find st (getLocal n d) = Some s ->
  dyn_tp s = qstate.
Proof.
case: (C)=>_ _ D G; case H: (n \in nodes); rewrite -D in H.
- by move:(G _ H); case=>s'[]->_; rewrite findPt//=; case=><-.
by rewrite /getLocal; case: dom_find H=>//->; rewrite find0E.
Qed.

Definition getSt n d (C : QCoh d) : qstate :=
  match find st (getLocal n d) as f return _ = f -> _ with
    Some v => fun epf => icast (sym_eq (cohSt C epf)) (dyn_val v)
  | _ => fun epf => ([::], [::])
  end (erefl _).

Lemma getStK n d (C : QCoh d)  s :
  getLocal n d = st :-> s -> getSt n C = s.
Proof.
by move=>E; rewrite /getSt/=; move: (cohSt C); rewrite !E/==>H; apply: eqc.
Qed.

Lemma getStE n i j C C' (pf : n \in nodes) :
  getLocal n j = getLocal n i ->
  @getSt n j C' = @getSt n i C.
Proof.
case: {-1}(C)=>_ _ D G; rewrite -D in pf; move:(G _ pf).
by move=>[s][E]_; rewrite (getStK C E) E; move/(getStK C' )->.
Qed.

Lemma getStE' n i j C C' (pf : n \in nodes) :
  @getSt n j C' = @getSt n i C ->
  getLocal n j = getLocal n i.
Proof.
case: {-1}(C)=>_ _ D G; rewrite -D in pf; move:(G _ pf).
move=>[s][E]_; rewrite (getStK C E) E=>H.
case: {-1}(C')=>_ _ D'/(_ n)=>G'; rewrite D' in G'; rewrite D in pf.
by move/G': pf=>[s'][E']_; rewrite (getStK C' E') in H; subst s'. 
Qed.

(****************************************************)

Notation coh := QCoh.

(*********************
Takes:
- initial state q
- a recipient node to
- a transition tag tag
- a request id to be spent (in the case of response)

Returns 
- a new local state 
**********************)
Definition send_step_fun (q : qstate) (to : nid) (tag : nat) (rid: nat) : qstate :=
  let: (xs, ys) := q in
  if tag == treq then ((to, fresh_id xs) :: xs, ys)
  else if (tag == tresp) && ((to, rid) \in ys)
       then (xs, seq.rem (to, rid) ys)
       else q.

Lemma send_step_uniq q to tag rid:
  uniq q.1 -> uniq q.2 ->
  uniq (send_step_fun q to tag rid).1  /\ uniq (send_step_fun q to tag rid).2.
Proof.
case: q=>xs ys/= U1 U2; rewrite /send_step_fun; case: ifP=>_/=.
- by rewrite U1 U2; rewrite fresh_not_in.
by case: ifP=>_//=; rewrite U1 rem_uniq //.
Qed.


(*********************
Takes:
- initial state q
- a sender node from
- a transition tag tag
- a request id to be processed (added or removed)

Returns 
- a new local state 
**********************)
Definition receive_step_fun (q : qstate) (from : nid) (tag : nat) (rid : nat) :=
  let: (xs, ys) := q in
  if (tag == treq) && ((from, rid) \notin ys)
  then (xs, (from, rid) :: ys)
  else if (tag == tresp) && ((from, rid) \in xs)
       then (seq.rem (from, rid) xs, ys)
       else q.

Lemma receive_step_uniq q from tag rid:
  uniq q.1 -> uniq q.2 ->
  uniq (receive_step_fun q from tag rid).1  /\
  uniq (receive_step_fun q from tag rid).2.
Proof.
case: q=>xs ys/= U1 U2; rewrite /receive_step_fun; case: ifP=>B/=.
- by rewrite U1 U2 andbC/=; case/andP:B=>_->.
by case:ifP=>///andP[_ B']/=; rewrite U2 rem_uniq.
Qed.

Section GenericQuerySendTransitions.

Definition Hn this to := this \in nodes /\ to \in nodes.
Definition mkLocal (q : qstate) := st :-> q.

(* Send tag *)
Variable stag : nat.

(* Generic precondition *)

Variable prec : qstate -> nid -> seq nat -> Prop.

(* Making sure that the precondition is legit *)
Definition prec_safe :=
    forall this to q m, Hn this to -> prec q to m ->
                      cohMsg (Msg (TMsg stag m) this to true).

Hypothesis psafe : prec_safe.

(* Generic send-safety *)
Definition send_safe (this n : nid)
           (d : dstatelet) (msg : seq nat) :=
  Hn this n /\ exists (C : coh d), prec (getSt this C) n msg.

Lemma send_safe_coh this to d m : send_safe this to d m -> coh d.
Proof. by case=>_[]. Qed.

Lemma send_this_in this to : Hn this to -> this \in nodes.
Proof. by case. Qed.

Lemma send_safe_in this to d m : send_safe this to d m ->
                                 this \in nodes /\ to \in nodes.
Proof. by case. Qed.

Definition send_step (this to : nid) (d : dstatelet)
           (msg : seq nat)
           (pf : send_safe this to d msg) :=
  let C := send_safe_coh pf in 
  let q := getSt this C in
  Some (mkLocal (send_step_fun q to stag (head 0 msg))). 

Lemma send_step_coh : s_step_coh_t coh stag send_step.
Proof.
move=>this to d msg pf h[]->{h}.
have C : (coh d) by case: pf=>?[].
split=>/=.
- apply: send_soupCoh; first by case:(send_safe_coh pf).
  by case: (pf)=>H[C']P/=;move: (psafe H P).
- by rewrite validU; apply: cohVl C.    
- by apply: trans_updDom=>//; case: (send_safe_in pf).
move=>n Ni. rewrite /localCoh/=.
rewrite /getLocal/=findU; case: ifP=>B; rewrite domU inE B/= in Ni; last first.
- by case: C=>_ _ _/(_ n Ni).  
move/eqP: B=>Z; subst n; rewrite/= (cohVl C)/=.
case: (send_safe_in pf); rewrite -(cohDom C)=>D _.
case: C=>_ _ _/(_ this D); case=>q[H/andP[U1 U2]].
exists (send_step_fun (getSt this (send_safe_coh pf)) to stag (head 0 msg)). 
by split=>//; apply/andP; rewrite (getStK _ H); apply: send_step_uniq.
Qed.

Lemma send_safe_def this to d msg :
      send_safe this to d msg <->
      exists b pf, @send_step this to d msg pf = Some b.
Proof.
split=>[pf/=|]; last by case=>?[]. 
set b := let C := send_safe_coh pf in 
         let q := getSt this C in
         mkLocal (send_step_fun q to stag (head 0 msg)). 
by exists b, pf. 
Qed.

Definition qsend_trans :=
  SendTrans send_safe_coh send_safe_in send_safe_def send_step_coh.

End GenericQuerySendTransitions.

Definition send_req_prec (q : qstate) (to : nid) (payload : seq nat) :=
  payload = [::(fresh_id q.1)].

(* Making sure that the precondition is legit *)
Lemma send_req_prec_safe : prec_safe treq send_req_prec.
Proof.
by move=>this to q m Hn Hp; rewrite /cohMsg; exists (fresh_id q.1). 
Qed.

Definition send_resp_prec (q : qstate) (to : nid) (payload : seq nat) :=
  exists rid d, payload = rid :: (serialize d) /\
                (to, rid) \in q.2.

Lemma send_resp_prec_safe : prec_safe tresp send_resp_prec.
Proof.
move=>this from q m Hn Hp; rewrite /cohMsg/=.
by case: Hp=>rid[d][H1]H2; exists rid, (serialize d).
Qed.


(* Concrete send-transitions *)
Definition qsend_req  := qsend_trans send_req_prec_safe.
Definition qsend_resp := qsend_trans send_resp_prec_safe.

Section GenericQueryReceiveTransitions.

(* Send-prepare *)
Variable rtag : nat.
Variable rc_wf : forall d, coh d -> nid -> nid -> TaggedMessage -> bool.

Definition receive_step : receive_step_t coh :=
  fun this (from : nid) (msg : seq nat) d (pf : coh d) (pt : this \in nodes) =>
    let q := getSt this pf in
    mkLocal (receive_step_fun q from rtag (head 0 msg)).

Lemma receive_step_coh : r_step_coh_t rc_wf rtag receive_step.
Proof.
move=>d from this m C pf tms D F Wf T/=.
rewrite /receive_step.
- split=>/=; first by apply: consume_coh.
  + by rewrite validU; apply: cohVl C.
  + by apply: trans_updDom.
move=>n Ni; rewrite /localCoh/=.
rewrite /getLocal/=findU; case: ifP=>/=B; rewrite domU inE B/= in Ni; last first.
- by case: (C)=>_ _ _/(_ n Ni).  
rewrite Ni; exists (receive_step_fun (getSt this C) from rtag (head 0 tms)).
split=>//; clear Wf.
have X: forall n, n \in dom (dstate d) -> localCoh n (getLocal n d) by case: C.
case:(X this D)=>q[H/andP[U1 U2]]; rewrite (getStK _ H).
by apply/andP; apply: receive_step_uniq.  
Qed.

Definition qrecv_trans := ReceiveTrans receive_step_coh.

End GenericQueryReceiveTransitions.

Definition query_msg_wf d (C : coh d) (this from : nid) :=
  [pred m : TaggedMessage | (tag m == treq) || (tag m == tresp)].

(* Concrete receive-transitions *)
Definition qrecv_req  := qrecv_trans treq query_msg_wf.
Definition qrecv_resp := qrecv_trans tresp query_msg_wf.

Section Protocol.

(* All send-transitions *)
Definition query_sends := [:: qsend_req; qsend_resp ].

(* All receive-transitions *)
Definition query_receives := [:: qrecv_req; qrecv_resp ].

(* Definint quety protocol *)
Program Definition QueryProtocol l : protocol :=
  @Protocol _ l _ query_sends query_receives _ _.

End Protocol.
End QueryProtocol.

Module Exports.
Section Exports.

(*  Tags *)
Definition treq := treq.
Definition tresp := tresp.

Definition getSt := getSt.
Definition getStK := getStK.
Definition getStE := getStE.
Definition getStE' := getStE'.

Definition qsend_req := qsend_req.
Definition qsend_resp := qsend_resp.
Definition qrecv_req := qrecv_req.
Definition qrecv_resp := qrecv_resp.

Definition query_msg_wf := query_msg_wf.
Definition qst := st.

Definition QueryProtocol := QueryProtocol.

End Exports.
End Exports.

End QueryProtocol.

Export QueryProtocol.Exports.

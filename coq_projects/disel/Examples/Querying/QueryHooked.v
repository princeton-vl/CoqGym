From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Require Import Eqdep.
From fcsl
Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely Actions.
From DiSeL
Require Import SeqLib QueryProtocol NewStatePredicates Actions.
From DiSeL
Require Import Injection Process Always HoareTriples InferenceRules While.

Section QueryHooked.

(* Constructing the composite world *)

Variables (lq : Label) (pc : protocol).
Variable Data : Type.
Variable qnodes : seq nat.
Variable serialize : Data -> seq nat.
Variable deserialize : seq nat -> Data.
Hypothesis ds_inverse : left_inverse serialize deserialize.
Definition pq := QueryProtocol qnodes serialize lq.

Variable core_state_to_data : nid -> heap -> Data -> Prop.

Hypothesis core_state_to_data_inj :
  forall n h d d', core_state_to_data n h d -> core_state_to_data n h d' -> d = d'.

(* The query hook extracts certain data from the the core protocol *)
(* local state if it's present there. *)
Definition query_hook : hook_type :=
  fun hc hq ms to => 
    forall n rid d, ms = rid :: serialize d -> core_state_to_data n hc d.

Definition query_hookz := (1, (plab pc), (plab pq, tresp)) \\-> query_hook.

Definition W : world := ((plab pc \\-> pc) \+ (plab pq \\-> pq), query_hookz).

Hypothesis Lab_neq: lq != (plab pc).
(* Hypothesis Nodes_eq: forall d, nodes pc d =i qnodes. *)

Lemma W_valid : valid W.
Proof.
apply/andP; split=>/=; last by rewrite validPt.
case: validUn=>//; rewrite ?validPt// =>l.
rewrite !domPt !inE=>/eqP=>Z; subst l=>/eqP=>Z.
by subst lq; move/negbTE: Lab_neq; rewrite eqxx.
Qed.

Lemma W_complete : hook_complete W.
Proof.
move=>z lc ls t/=; rewrite domPt inE=>/eqP[]_<-<-_.
rewrite !domUn !inE/= !domPt !inE !eqxx/= orbC.
case/andP:W_valid=>->_.
rewrite 3!andTb.
rewrite inE.
by apply/orP; left.
Qed.

Lemma W_dom : dom W.1 =i [:: plab pc; lq].
Proof.
move=>z/=; rewrite domUn !inE/=; case/andP: W_valid=>->/=_. 
rewrite !domPt !inE; rewrite -!(eq_sym z).
rewrite /cond /= inE orbC.
apply sym_eq.
by rewrite orbC eq_sym.
Qed.

Lemma eqW : 
  W = (plab pc \\-> pc, Unit) \+ (plab pq \\-> pq, Unit) \+ (Unit, query_hookz).
Proof. by rewrite /PCM.join/=/W !unitL !unitR. Qed.

Lemma eqW' : 
  W = (plab pc \\-> pc, Unit) \+ ((plab pq \\-> pq, Unit) \+ (Unit, query_hookz)).
Proof. by rewrite eqW joinA. Qed.

Lemma injW : injects (plab pc \\-> pc, Unit) W query_hookz.
Proof.
rewrite eqW; apply:injectL=>//; try by move=>????/=; rewrite dom0 inE.
- by rewrite -eqW W_valid.
- move=>z lc ls t; rewrite domPt inE.
  by rewrite /cond /= dom0.
- move=>z lc ls t; rewrite domPt inE.
  by rewrite /cond /= dom0.
- move=>z lc ls t; rewrite domPt inE.
  case/eqP=>Z1 Z2 Z3 Z4; subst ls z lc t.
  rewrite !domUn !inE !domPt !inE !eqxx/=.
  case/andP:W_valid=>/=->_/=; rewrite orbC inE.
  by apply/orP; left.
move=>l; rewrite domPt inE=>/eqP=><-.
move=>z lc ls t; rewrite domPt inE=>/eqP[]_ _<-_.  
apply/negbT; apply/eqP=>Z; subst lq; move/negbTE: Lab_neq.
by rewrite eqxx.
Qed.

Lemma labC : plab pc \in dom W.1.
Proof.
case/andP: W_valid=>V1 V2.
by rewrite domUn !inE V1/= domPt inE eqxx.
Qed.

Lemma labQ : lq \in dom W.1.
Proof.
case/andP: W_valid=>V1 V2.
rewrite domUn !inE V1/= !domPt !inE /cond /= inE.
by apply/orP; right.
Qed.

Lemma injWQ : inj_ext injW = (lq \\-> pq, Unit).
Proof.
move: (W_valid)=>V; move: (cohK injW).
rewrite {1}eqW/mkWorld/= -!joinA /PCM.join/= in V.
case/andP: V=>/=V V'.
rewrite {1}eqW/mkWorld/= -!joinA /PCM.join/=; case=>H K.
case: (cancel V H)=>_; rewrite !unitR=>_{H}H1.
rewrite [inj_ext _]surjective_pairing -H1{H1}; congr (_, _).
rewrite !unitL joinC/=/query_hookz/= in V' K.
rewrite -[_ \\-> _]unitR in V'.
have Z:  (1, plab pc, (lq, tresp)) \\-> query_hook \+ Unit =
         (1, plab pc, (lq, tresp)) \\-> query_hook \+ (inj_ext injW).2
  by rewrite unitR.
by case: (cancel V' Z).
Qed.

Lemma prEqC : getProtocol W (plab pc) = pc.
rewrite /getProtocol/W/= findUnL; last by case/andP: W_valid.
by rewrite domPt inE eqxx findPt.
Qed.

Lemma prEqQ : getProtocol W lq = pq.
Proof.
rewrite /getProtocol/W/= findUnR; last by case/andP: W_valid.
by rewrite domPt inE eqxx findPt.
Qed.

Lemma prEqQ' : getProtocol (lq \\-> pq, Unit) lq = pq.
Proof. by rewrite /getProtocol findPt. Qed.

(* Finished constructing the composite world *)

Variable this : nid.
Hypothesis this_in_qnodes: this \in qnodes.

(* Now playing with the stability of the desired invariant *)

(* Core getters *)
Notation getSc s := (getStatelet s (plab pc)).
Notation getLc s := (getLocal this (getSc s)).
Notation getLc' s n := (getLocal n (getSc s)).

(* Query getters *)
Notation getSq s := (getStatelet s (plab pq)).
Notation getLq s := (getLocal this (getSq s)).

(* Describing the response-permissions of our recipient *)
Definition holds_res_perms d n (pp : nat -> Prop) :=
  exists (reqs resp : seq (nid * nat)),
    getLocal n d = qst :-> (reqs, resp) /\
    forall rn, (this, rn) \in resp -> pp rn.

(* TODO: define the channel criterion *)
Definition request_msg (t: nat) (_ : seq nat) :=  t == treq.
Definition response_msg (t: nat) (_ : seq nat) := t == tresp.

(************************************************)
(*        Predicate for initial state           *)
(************************************************)

Definition query_init_state (to : nid) s :=
  [/\ to \in qnodes,
      holds_res_perms (getSq s) to (fun _ : nat => false),
      no_msg_from_to' this to request_msg (dsoup (getSq s)) &
      no_msg_from_to' to this response_msg (dsoup (getSq s))].    

(* This is the first serious one. *)
Lemma query_init_step' z to s s' :
  this != z -> query_init_state to s ->
  network_step (lq \\-> pq, Unit) z s s' -> query_init_state to s'.
Proof.
move=> N H S; case: (step_coh S)=>C1 _.
case: S; [by case=>_<- |
  move=>l st H1 to'/= msg n H2 H3 C H4 H5 H6->{s'}|
  move=>l rt H1 i from pf H3 C msg H2/=[H4]_->{s'}];
rewrite -(cohD C) domPt inE in H3; move/eqP: H3=>H3; subst l;
(* TODO: Get rid of irrelevant cases: by means of a tactic *)
rewrite /query_init_state/getStatelet !findU !eqxx (cohS C1)/=;
have Cq: coh pq (getStatelet s lq) by move: (coh_coh lq C1); rewrite /getProtocol findPt.
(* Send-transitions. *)
- case:H=>G1 G2 G3 G4.
  move: st H1 H4 H5 H6; rewrite /get_st prEqQ'=>st H1 H4 H5 H6.
  case B: (to == z); rewrite /holds_res_perms/getLocal findU B/=; last first.
  + split=>//.
    move=>m t c; rewrite findUnR ?valid_fresh ?(cohVs Cq)//; case: ifP; last by move=>_/G3.
    rewrite domPt inE=>/eqP<-{m}; rewrite findPt; case=>_ _ Z; subst z.
    by move/negbTE: N; rewrite eqxx.
  + move=>m t c; rewrite findUnR ?valid_fresh ?(cohVs Cq)//; case: ifP; last by move=>_/G4.
    rewrite domPt inE=>/eqP<-{m}; rewrite findPt; case=>_ _ Z; subst z.
    by rewrite eqxx in B.
  move/eqP: B=>B; subst z; split=>//; first 1 last.
  + move=>m t c; rewrite findUnR ?valid_fresh ?(cohVs Cq)//; case: ifP; last by move=>_/G3.  
    rewrite domPt inE=>/eqP<-{m}; rewrite findPt; case=>_ _ Z; subst to.
    by move/negbTE: N; rewrite eqxx.
  (* Now two interesting assertions. *)  
  + move=>m t c; rewrite findUnR ?valid_fresh ?(cohVs Cq)//; case: ifP; last by move=>_/G4.
    rewrite domPt inE=>/eqP<-{m}; rewrite findPt; case=>Z' Z2 Z; subst to' t c.
    (* Consider two possible send-transitions. *)
    case: H1;[|case=>//]; move=>Z; subst st=>//. 
    case: (H4)=>_[C']/=[rid][d][_]; case: G2=>rq[rs][E]H.
    by rewrite (getStK _ E)/==>/H.
  rewrite (cohVl Cq); case: G2=>rq[rs][E]H.  
  case: H1;[|case=>//]; move=>Z; subst st=>//; last first.
  + case: (H4)=>_[C']/=[rid][d][H']; subst msg.
    rewrite (getStK _ E)/==>G.
    rewrite /=/QueryProtocol.send_step/=!(getStK _ E)/= G/= in H6; case: H6=>Z.
    subst n; eexists rq, (seq.rem (to', rid) rs); split=>//.
    by move=>rn; move/mem_rem; apply/H.
  case: (H4)=>_[C']/==>Z.
  rewrite/QueryProtocol.send_req_prec (getStK _ E) in Z; subst msg. 
  rewrite /=/QueryProtocol.send_step/=!(getStK _ E)/= in H6; case: H6=>Z; subst n.
  by exists ((to', fresh_id rq) :: rq), rs.
(* Receive-transitions *)
case:H=>G1 G2 G3 G4.
move: (coh_s _ _) rt pf H1 H2.
rewrite /get_rt prEqQ'/==>Cq'; rewrite !(pf_irr Cq' Cq)=>{Cq'}.
move=>rt pf H1 H2.
case B: (to == z); rewrite /holds_res_perms/getLocal findU B/=; last first.
- by split=>//; apply: no_msg_from_to_consume'=>//; rewrite ?(cohVs Cq).
rewrite !(cohVl Cq); move/eqP:B=>B; subst z. 
split=>//; try by apply: no_msg_from_to_consume'=>//; rewrite ?(cohVs Cq).
case: G2=>rq[rs][E]H.
case: H1;[|case=>//]; move=>Z; subst rt=>//=; simpl in H2;
rewrite /QueryProtocol.receive_step (getStK _ E)/=; last first.
- case: ifP=>_; last by eexists _, _.
  by exists (seq.rem (from, head 0 msg) rq), rs. 
case: ifP=>_; last by eexists _, _.
exists rq, ((from, head 0 msg) :: rs); split=>//.
move=>rn; rewrite inE; case/orP; last by apply: H.
case/eqP=>Z1 Z2; subst rn from.
case: msg H2 H4=>t c/=Z H4; subst t.
by move: (G3 _ _ _ H4).
Qed.

Lemma query_init_rely' to s s' :
  query_init_state to s ->
  network_rely (lq \\-> pq, Unit) this s s' -> query_init_state to s'.
Proof.
move=>H1 [n]H2; elim: n s H2 H1=>/=[s | n Hi s]; first by case=>Z _; subst s'.
case=>z[s1][N]H1 H2 H3; apply: (Hi s1 H2).
by apply: (query_init_step' _ _ _ _ N H3 H1).
Qed.

(* TODO: this is a good candidate for a general lemma in the
framework. *)

(* Proving a large-footprint predicate out of a small-footprint
predicate, spanning only the query world. *)
Lemma query_init_rely to s s2 :
  query_init_state to s ->
  network_rely W this s s2 -> query_init_state to s2.
Proof.
move=>Q R; case:(rely_coh R)=>CD CD'.
rewrite eqW in CD; move: (coh_hooks CD)=>{CD}CD.
rewrite eqW in CD'; move: (coh_hooks CD')=>{CD'}CD'.
case: (coh_split CD _ _); try apply: hook_complete0.
move=>i1[j1][C1 D1 Z]; subst s.
case: (coh_split CD' _ _); try apply: hook_complete0.
move=>i2[j2][C2 D2 Z]; subst s2.
rewrite /query_init_state in Q *.
rewrite (locProjR CD _ D1) in Q; last by rewrite domPt inE andbC eqxx.
rewrite (locProjR CD' _ D2); last by rewrite domPt inE andbC eqxx.
case: (rely_split injW C1 C2 R)=>Rc Rq; rewrite injWQ in Rq.
by apply: (query_init_rely' _ _ _ Q Rq).
Qed.

(***************************************************)
(*  Query-specific intermediate predicate          *)
(***************************************************)

(* 1. We've just sent our stuff. *)
Definition msg_just_sent d (reqs resp : seq (nid * nat)) req_num to :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   no_msg_from_to' to this response_msg (dsoup d), 
   (to, req_num) \in reqs, 
   msg_spec' this to treq ([:: req_num]) (dsoup d) &
   holds_res_perms d to (fun _ => false)].

(* 2. Our request is received but not yet responded. *)
Definition msg_received d (reqs resp : seq (nid * nat)) req_num to :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   (to, req_num) \in reqs,
   no_msg_from_to' this to request_msg (dsoup d),
   no_msg_from_to' to this response_msg (dsoup d) &
   holds_res_perms d to (fun rn => rn == req_num)].

(* 3. Our request is responded. *)
Definition msg_responded d (reqs resp : seq (nid * nat)) req_num to data :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   (to, req_num) \in reqs,
   no_msg_from_to' this to request_msg (dsoup d),
   msg_spec' to this tresp (req_num :: serialize data) (dsoup d) &
   holds_res_perms d to (fun _ => false)].

(* 4. Stability of the local state of a core protocol, 
      to be proved separately *)

(* A local assertion ensuring stability of the core_state_to_data *)
Variable local_indicator : Data -> Pred heap.

Hypothesis core_state_stable_step : forall z s data s' n,
  this != z -> network_step (plab pc \\-> pc, Unit) z s s' ->
  n \in qnodes ->
  local_indicator data (getLc s) ->
  core_state_to_data n (getLc' s n) data  -> 
  core_state_to_data n (getLc' s' n) data.

Lemma prEqC' : (getProtocol (plab pc \\-> pc, Unit) (plab pc)) = pc.
Proof. by rewrite /getProtocol findPt/=. Qed.
  
(* Showing that the core assertion is stable *)
Lemma core_state_stable_step_W s data s' z :
  this != z ->
  network_step W z s s' ->
  z \in qnodes ->
  local_indicator data (getLc s) ->
  core_state_to_data z (getLc' s z) data -> 
  core_state_to_data z (getLc' s' z) data.
Proof.
move=>N H2 G L H1; move:(step_coh H2)=>[C1 C2].
rewrite eqW' in C1 C2.
move: (projectSE C1)(projectSE C2)=>E1 E2.
set s1 := projectS (plab pc \\-> pc, Unit) s in E1.
set s2 := projectS ((plab pq \\-> pq, Unit) \+ (Unit, query_hookz)) s in E1.
set s1' := projectS (plab pc \\-> pc, Unit) s' in E2.
set s2' := projectS ((plab pq \\-> pq, Unit) \+ (Unit, query_hookz)) s' in E2.
move: (C1) (C2) =>C1' C2'.
rewrite E1 E2 in H2 C1' C2'.
have [X X'] : (forall z, getLc' s z  = getLc' s1 z) /\
              (forall z, getLc' s' z = getLc' s1' z).
- by split; move=>z'; rewrite /getStatelet find_umfilt domPt inE eqxx.
case: (sem_split injW _ _ H2).
- apply: (@projectS_cohL (plab pc \\-> pc, Unit)
                         ((plab pq \\-> pq, Unit) \+ (Unit, query_hookz)))=>//.
  by move=>????; rewrite dom0.
- suff H : hook_complete (plab pc \\-> pc, Unit).
  apply: (@projectS_cohL _ ((plab pq \\-> pq, Unit)\+(Unit, query_hookz)))=>//.
  by move=>????; rewrite dom0.
- case=>H _; rewrite X'; rewrite !X in L H1.
  by apply: (core_state_stable_step _ _ _ _ _ N H _ L H1).
by case=>_ E; rewrite X'; rewrite !X in L H1; rewrite -E.
Qed.

Lemma core_state_stable s data s' z :
  network_rely W this s s' ->
  z \in qnodes ->
  local_indicator data (getLc s) ->
  core_state_to_data z (getLc' s z) data -> 
  core_state_to_data z (getLc' s' z) data.
Proof.
move=> R Z L. move: (L); rewrite -(@rely_loc' _ _ (plab pc) s s' R)=>L'.
move: R Z L.
case B: (this == z); [move/eqP: B=>B|move/negbT: B=>B].
- by subst z=>R; rewrite (@rely_loc' _ _ (plab pc) s s' R).
move=>[n]H2 H1; elim: n s H2=>/=[s | n Hi s]; first by case=>Z _; subst s'.
case=>y[s1][N]G1 G2 G3 G4; apply: (Hi s1 G2).
- by rewrite /getLocal -(step_is_local (plab pc) G1 N). 
case B' : (z == y); [move/eqP: B'=>B' | move/negbT: B'=>B'].
- by subst y; apply: (core_state_stable_step_W _ _ _ _ B G1 _ G3).
by rewrite /getLocal -(step_is_local (plab pc) G1 B').
Qed.

(************************************************************************)
(******       Auxiliary lemmas for establishing stability          ******)
(************************************************************************)

Lemma cohQ s : Coh W s -> (QueryProtocol.QCoh qnodes) (getSq s).
Proof. by move/(coh_coh lq); rewrite prEqQ. Qed.

Lemma send_lq_case1 req_num reqs resp to s
  (N : this != to) (Qn : to \in qnodes) 
  (M : msg_just_sent (getSq s) reqs resp req_num to)
  to' msg (n : heap) (C : Coh W s) (st : send_trans (Protocols.coh pq))
  (H1 : st \In snd_trans pq)
  (H2 : to \in qnodes)
  (H4 : send_safe st to to' (getSq s) msg) : 
  all_hooks_fire query_hookz (plab pq) (t_snd st) s to msg to' -> Some n = send_step H4 ->
  let: d := getStatelet (upd (plab pq) 
              (DStatelet (upd to n (dstate (getSq s)))
               (dsoup (getSq s) \+ fresh (dsoup (getSq s)) \\->
                      Msg (TMsg (t_snd st) msg) to to' true)) s) lq in
  msg_just_sent d reqs resp req_num to.
Proof.
move=>H5 H6; case: M=>G1 G2 G3 G4[rq][rs][E]Np; split=>//.
- by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *.
- rewrite /getStatelet findU  eqxx(cohS C)/==>z t c.
  rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
  case: ifP; [|by move=>_; apply: G2].
  rewrite domPt inE=>/eqP<-; rewrite findPt; case=>???; subst t c to'.
  case: H1;[|case=>//]; move=>Z; subst st=>//; simpl in H5, H6;
  rewrite/QueryProtocol.send_step (getStK _ E)/= in H6; case: H6=>H6/=; subst n.                                  
  by case:H4=>_[C'][rid][_][_]; rewrite (getStK _ E); move/Np. 
- rewrite /getStatelet findU  eqxx(cohS C)/=.
  case:G4; case=>i[[c']Q1 Q3] Q2; split; last first.
  + move=>j c; rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
    case:ifP; last by move=>_; apply Q2. 
    rewrite domPt inE=>/eqP<-; rewrite findPt.
    by case=>???; subst to; rewrite eqxx in N.
  exists i; split=>[|j[c1]];rewrite findUnL ?(valid_fresh) ?(cohVs (cohQ s C))//.   
  + by exists c'; rewrite (find_some Q1). 
  case: ifP=>_; first by move=> T; apply: Q3; exists c1. 
  by case/findPt_inv=>_[]_ _?; subst to; rewrite eqxx in N. 
rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).  
case: H1;[|case=>//]; move=>Z; subst st=>//; simpl in H5, H6;
rewrite/QueryProtocol.send_step (getStK _ E)/= in H6; case: H6=>H6; subst n.
- by exists ((to', fresh_id rq) :: rq), rs.
case: ifP=>_; last by exists rq, rs.                 
by exists rq, (seq.rem (to', head 0 msg) rs); split=>//rn/mem_rem/Np.
Qed.

Lemma send_lq_case3 req_num data reqs resp to s
  (N : this != to) (Qn : to \in qnodes) (H : core_state_to_data to (getLc' s to) data)
  (L : local_indicator data (getLc' s this))
  (M : msg_responded (getSq s) reqs resp req_num to data)
  to' msg (n : heap) (C : Coh W s) (st : send_trans (Protocols.coh pq))
  (H1 : st \In snd_trans pq)
  (H2 : to \in qnodes)
  (H4 : send_safe st to to' (getSq s) msg) : 
  all_hooks_fire query_hookz (plab pq) (t_snd st) s to msg to' -> Some n = send_step H4 ->
  let: d := getStatelet (upd (plab pq) 
              (DStatelet (upd to n (dstate (getSq s)))
               (dsoup (getSq s) \+ fresh (dsoup (getSq s)) \\->
                      Msg (TMsg (t_snd st) msg) to to' true)) s) lq in
  msg_responded d reqs resp req_num to data.  
Proof.
move=>H5 H6.
case: M=>G1 G2 G3 G4[rq][rs][E]Np; split=>//.
- by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *.
- rewrite /getStatelet findU  eqxx(cohS C)/==>z t c.
  rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
  case: ifP; [|by move=>_; apply: G3].
  rewrite domPt inE=>/eqP<-; rewrite findPt; case=>????; subst t c to to'.
  by rewrite eqxx in N.
- rewrite /getStatelet findU  eqxx(cohS C)/=.
  case:G4; case=>i[[c']Q1 Q3] Q2; split; last first.
  + move=>j c; rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
    case:ifP; last by move=>_; apply Q2. 
    rewrite domPt inE=>/eqP<-; rewrite findPt.
    case=>???; subst to' c.
    case: H1;[|case=>//]; move=>Z; subst st=>//; simpl in H5, H6;
    rewrite/QueryProtocol.send_step (getStK _ E)/= in H6; case: H6=>H6/=; subst n.
    by case:H4=>_[C']; rewrite (getStK _ E); case=>rid[d][->]/=/Np. 
  exists i; split=>[|j[c1]];rewrite findUnL ?(valid_fresh) ?(cohVs (cohQ s C))//.   
  + by exists c'; rewrite (find_some Q1). 
  case: ifP=>_; first by move=> T; apply: Q3; exists c1. 
  case/findPt_inv=>_[]???; subst to'.
  case: H1;[|case=>//]; move=>Z; subst st=>//; simpl in H5, H6;
  rewrite/QueryProtocol.send_step (getStK _ E)/= in H6; case: H6=>H6/=; subst n.
  by case:H4=>_[C']; rewrite (getStK _ E); case=>rid[d][_]/=/Np. 
rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).  
case: H1;[|case=>//]; move=>Z; subst st=>//; simpl in H5, H6;
rewrite/QueryProtocol.send_step (getStK _ E)/= in H6; case: H6=>H6; subst n.
- by exists ((to', fresh_id rq) :: rq), rs.
case: ifP=>_; last by exists rq, rs.                 
by exists rq, (seq.rem (to', head 0 msg) rs); split=>//rn/mem_rem/Np.
Qed.

Lemma send_lq_all_cases req_num data reqs resp to s
  (N : this != to) (Qn : to \in qnodes) (H : core_state_to_data to (getLc' s to) data)
  (L : local_indicator data (getLc' s this))
  (M : [\/ msg_just_sent (getSq s) reqs resp req_num to, msg_received (getSq s) reqs resp req_num to
        | msg_responded (getSq s) reqs resp req_num to data])
  to' msg (n : heap) (C : Coh W s) (st : send_trans (Protocols.coh (getProtocol W (plab pq))))
  (H1 : st \In get_st W (plab pq))
  (H2 : to \in nodes (getProtocol W (plab pq)) (getSq s))
  (H4 : send_safe st to to' (getSq s) msg) : 
  all_hooks_fire query_hookz (plab pq) (t_snd st) s to msg to' -> Some n = send_step H4 ->
  let: d := getStatelet (upd (plab pq) 
              (DStatelet (upd to n (dstate (getSq s)))
               (dsoup (getSq s) \+ fresh (dsoup (getSq s)) \\->
                      Msg (TMsg (t_snd st) msg) to to' true)) s) lq in
  [\/ msg_just_sent d reqs resp req_num to,
      msg_received  d reqs resp req_num to
    | msg_responded d reqs resp req_num to data].  
Proof.
move=>H5 H6.
move: st H1 H4 H5 H6; rewrite /get_st prEqQ=>st H1 H4 H5 H6.
case: M; last 1 first.
+ (* already responded to our request, should be boring *)
  constructor 3.
  by apply: (send_lq_case3 req_num data  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4). 
+ (* just sent the request *)
  by constructor 1; apply: (send_lq_case1 req_num _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4). 

Ltac kill_g3 s C G3 to N :=
  rewrite /getStatelet findU  eqxx(cohS C)/==>z t c;
  rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//;
  case: ifP; [|by move=>_; apply: G3]; 
  rewrite domPt inE=>/eqP<-; rewrite findPt;
  by case=>_ _ Z _; subst to; rewrite eqxx in N.

Ltac kill_g4 s C G4 to' t B:=
  rewrite /getStatelet findU  eqxx(cohS C)/==>z t c;
  rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//;
  case: ifP; [|by move=>_; apply: G4]; 
  rewrite domPt inE=>/eqP<-; rewrite findPt;
  by case=>??; try move=>?; try subst t; try subst to'; try rewrite ?eqxx in B.

(* now he can send us the message, this is the crucial step. *)
case=>G1 G2 G3 G4 [rq][rs][E]Np.
case B : (to' == this); [move/eqP:B=>B; subst to'|]; last first.
- constructor 2. (* boring case : sending to someone else*)
  split=>//.
  + by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *. 
  + kill_g3 s C G3 to N.
  + kill_g4 s C G4 to' t B.
  rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
  rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).  
  case: H1;[|case=>//]; move=>Z; subst st=>//; simpl in H5, H6;
  rewrite/QueryProtocol.send_step (getStK _ E)/= in H6; case: H6=>H6; subst n.
  - by exists ((to', fresh_id rq) :: rq), rs. 
  case:ifP=>_; last by exists rq, rs.   
  by exists rq, (seq.rem (to', head 0 msg) rs); split=>//rn/mem_rem/Np.
(* Actually sending to us. *)  
case: H1;[|case=>//]; move=>Z; subst st=>//; simpl in H5, H6;
rewrite/QueryProtocol.send_step (getStK _ E)/= in H6; case: H6=>H6; subst n.                                  
- constructor 2; split=>//. (* sending request (not response) -- this is boring *)
  + by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *. 
  + kill_g3 s C G3 to N.
  + kill_g4 s C G4 to' t B.
  rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
  rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).
  by exists ((this, fresh_id rq) :: rq), rs.    
(* Sending response to us!!! *)                                          
case: (H4)=>_[C']/=[rid][d][Zm]Tr; subst msg.
rewrite  (getStK _ E)/= in Tr.
rewrite Tr; constructor 3.
(* Now exploit the hook! *)
move: (H5 1 (plab pc) query_hook); rewrite findPt -!(cohD C).
move/(_ (erefl _) labC labQ to rid d (erefl _))=>D.
move: (core_state_to_data_inj _ _ _ _ D H)=>Z; subst d.
split=>//; first 3 last.
+ rewrite /getStatelet findU eqxx(cohS C)/=.
  exists (rq), (seq.rem (this, rid) rs).
  rewrite /getLocal findU eqxx/= (cohVl C'); split=>// rn R.
  move/Np/eqP: (mem_rem R)=>Zr; subst rn.
  move/Np:Tr=>/eqP=>Zr; subst rid.
  case: (C')=>_ _ _/(_ to); rewrite E (cohDom C')=>/(_ Qn). 
  case=>[[x1 x2]][]/(hcancelPtV _); rewrite validPt/==>/(_ is_true_true).
  case=>Z1 Z2; subst x1 x2=>/andP[_]G.
  by rewrite (rem_filter (this, req_num) G) mem_filter/= eqxx/= in R.
+ by rewrite /getStatelet findU eqxx(cohS C)/getLocal findU (negbTE N). 
+ rewrite /getStatelet findU eqxx (cohS C)/==>z t c.
  rewrite findUnR ?(valid_fresh) ?(cohVs C')//.
  case: ifP=>[|_]; last by apply: G3.
  by rewrite domPt inE=>/eqP<-{z}; rewrite findPt; case=><-.
(* Here's the big hooking moment *)  
split=>[|i m]; 
  rewrite /getStatelet findU eqxx/= (cohS C)/=; last first.
+ rewrite findUnR ?(valid_fresh) ?(cohVs C')//; case: ifP=>[|_]; last by move/G4. 
  rewrite domPt inE=>/eqP<-; rewrite findPt; case=><-.
  by move/Np/eqP: Tr=>->; rewrite eqxx.
exists (fresh (dsoup (getStatelet s lq))); split.
+ exists (rid :: serialize data).
  by rewrite findUnR ?(valid_fresh)?(cohVs C')// domPt inE eqxx findPt.
move=>i[c]; rewrite findUnR ?(valid_fresh)?(cohVs C')//.
case: ifP=>[|_]; last by move/G4. 
by rewrite domPt inE=>/eqP<-; rewrite findPt. 
Qed.

(*  A lemma covering send-cases in the lc-part of the world  *)
Lemma send_lc_all_cases req_num data reqs resp to s
  (N : this != to) (Qn : to \in qnodes) (H : core_state_to_data to (getLc' s to) data)
  (L : local_indicator data (getLc' s this))
  (M : [\/ msg_just_sent (getSq s) reqs resp req_num to, msg_received (getSq s) reqs resp req_num to
        | msg_responded (getSq s) reqs resp req_num to data])
  to' msg (n : heap) (C : Coh W s) (st : send_trans (Protocols.coh (getProtocol W (plab pc))))
  (H1 : st \In get_st W (plab pc))
  (H2 : to \in nodes (getProtocol W (plab pc)) (getSq s))
  (H4 : send_safe st to to' (getSq s) msg) : 
  all_hooks_fire query_hookz (plab pc) (t_snd st) s to msg to' -> Some n = send_step H4 ->
  let: d := getStatelet (upd (plab pc) 
              (DStatelet (upd to n (dstate (getSq s)))
               (dsoup (getSq s) \+ fresh (dsoup (getSq s)) \\->
                      Msg (TMsg (t_snd st) msg) to to' true)) s) lq in
  [\/ msg_just_sent d reqs resp req_num to,
      msg_received  d reqs resp req_num to
    | msg_responded d reqs resp req_num to data].  
Proof.
move=>H5 H6.
move: st H1 H4 H5 H6; rewrite /get_st prEqC=>st H1 H4 H5 H6.
by case: M; [constructor 1|constructor 2|constructor 3];
   rewrite /getStatelet findU (negbTE Lab_neq)/=. 
Qed.

Lemma recv_lq_case1 req_num reqs resp to s
  (N : this != to) (Qn : to \in qnodes)
  (M : msg_just_sent (getSq s) reqs resp req_num to)
  i from msg (C : Coh W s) (C' : (coh pq) (getSq s))
  (pf : to \in nodes pq (getSq s))
  (rt : receive_trans (Protocols.coh pq)) : 
  rt \In rcv_trans pq -> tag msg = t_rcv rt ->
  find i (dsoup (getSq s)) = Some (Msg msg from to true) ->
  let: d := getStatelet (upd (plab pq) 
              (DStatelet (upd to (receive_step rt from msg C' pf) (dstate (getSq s)))
               (consume_msg (dsoup (getSq s)) i)) s) lq in
  msg_just_sent d reqs resp req_num to \/
  msg_received d reqs resp req_num to. 
Proof.
move=>H1 H2 H4; case: M=>G1 G2 G3 G4[rq][rs][Tr]Np.
case X: (this == from); [move/eqP:X=>X; subst from|constructor 1];
last first.
- split=>//.
  + by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *. 
  + rewrite /getStatelet findU eqxx(cohS C)/=.
    by apply: no_msg_from_to_consume'=>//; rewrite (cohVs C').
  + rewrite /getStatelet findU eqxx(cohS C)/=.
    case: msg H2 H4=>t c H2 H4.
    by apply: (msg_spec_consumeE (cohVs C') H4 G4); rewrite (negbT X).   
  rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
  rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).  
  case: H1;[|case=>//]; move=>Z; subst rt=>//=; simpl in H2, H4;
  rewrite/QueryProtocol.receive_step (getStK _ Tr)/=.
  + case:ifP=>_; last by exists rq, rs. 
    exists rq, ((from, head 0 msg) :: rs); split=>//rn.
    by rewrite inE; case/orP; [case/eqP=>Z; subst; rewrite eqxx in X|move/Np].
  case:ifP=>_; last by exists rq, rs. 
  by exists (seq.rem (from, head 0 msg) rq), rs. 
case: msg H2 H4=>t c H2 H4.
case: H1;[|case=>//]; move=>Z; subst rt=>//=; simpl in H2, H4; subst t; last first.
- constructor 1; split=>//.
  + by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *. 
  + rewrite /getStatelet findU eqxx(cohS C)/=.
    by apply: no_msg_from_to_consume'=>//; rewrite (cohVs C').
  + rewrite /getStatelet findU eqxx(cohS C)/=.
    by apply: (msg_spec_consumeE (cohVs C') H4 G4)=>/=; rewrite -(orbC true)/= orbC.
  rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
  rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).  
  rewrite/QueryProtocol.receive_step (getStK _ Tr)/=.
  case:ifP=>_; last by exists rq, rs. 
  by exists (seq.rem (this, head 0 c) rq), rs.  
(* Finally, the only interesting case here *)
constructor 2; split=>//.  
+ by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *.     
+ rewrite /getStatelet findU eqxx(cohS C)/=.
  by apply: (no_msg_spec_consume (cohVs C') H4 G4).
+ rewrite /getStatelet findU eqxx(cohS C)/=.
  by apply: no_msg_from_to_consume'=>//; rewrite (cohVs C').
rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).  
rewrite/QueryProtocol.receive_step (getStK _ Tr)/=.
case:ifP=>X; last by move/negbT/negbNE/Np: X.
exists rq, ((this, head 0 c) :: rs); split=>//rn.
rewrite inE=>/orP[]; last by move/Np.
by case/eqP=>Z; subst rn; case:G4=>_/(_ _ _ H4)/eqP->.
Qed.

Lemma recv_lq_case2 req_num reqs resp to s
  (N : this != to) (Qn : to \in qnodes)
  (M : msg_received (getSq s) reqs resp req_num to)
  i from msg (C : Coh W s) (C' : (coh pq) (getSq s))
  (pf : to \in nodes pq (getSq s))
  (rt : receive_trans (Protocols.coh pq)) : 
  rt \In rcv_trans pq -> tag msg = t_rcv rt ->
  find i (dsoup (getSq s)) = Some (Msg msg from to true) ->
  let: d := getStatelet (upd (plab pq) 
              (DStatelet (upd to (receive_step rt from msg C' pf) (dstate (getSq s)))
               (consume_msg (dsoup (getSq s)) i)) s) lq in
  msg_received d reqs resp req_num to.  
Proof.
move=>H1 H2 H4; case: M=>G1 G2 G3 G4[rq][rs][Tr]Np.
split=>//.
- by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *. 
- rewrite /getStatelet findU eqxx(cohS C)/=.
  by apply: no_msg_from_to_consume'=>//; rewrite (cohVs C').
- rewrite /getStatelet findU eqxx(cohS C)/=.  
  by apply: no_msg_from_to_consume'=>//; rewrite (cohVs C').
rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).  
case: H1;[|case=>//]; move=>Z; subst rt=>//=; simpl in H2, H4;
rewrite/QueryProtocol.receive_step (getStK _ Tr)/=.
- case:ifP=>_; last by exists rq, rs. 
  exists rq, ((from, head 0 msg) :: rs); split=>//rn.
  case X: (this == from); last first.
  + by rewrite inE; case/orP; [case/eqP=>Z; subst; rewrite eqxx in X|move/Np].
  move/eqP:X=>X; subst from.
  by case: msg H2 H4=>t c/= H2 H4; move: (G3 _ _ _ H4); subst t.  
case:ifP=>_; last by exists rq, rs. 
by exists (seq.rem (from, head 0 msg) rq), rs. 
Qed.

Lemma recv_lq_case3 req_num reqs resp to s data
  (N : this != to) (Qn : to \in qnodes)
  (M : msg_responded (getSq s) reqs resp req_num to data)
  (H : core_state_to_data to (getLc' s to) data)
  (L : local_indicator data (getLc' s this))
  i from msg (C : Coh W s) (C' : (coh pq) (getSq s))
  (pf : to \in nodes pq (getSq s))
  (rt : receive_trans (Protocols.coh pq)) : 
  rt \In rcv_trans pq -> tag msg = t_rcv rt ->
  find i (dsoup (getSq s)) = Some (Msg msg from to true) ->
  let: d := getStatelet (upd (plab pq) 
              (DStatelet (upd to (receive_step rt from msg C' pf) (dstate (getSq s)))
               (consume_msg (dsoup (getSq s)) i)) s) lq in
  msg_responded d reqs resp req_num to data.  
Proof.
move=>H1 H2 H4; case: M=>G1 G2 G3 G4[rq][rs][Tr]Np.
split=>//.
- by rewrite /getStatelet findU eqxx(cohS C)/=/getLocal/= findU (negbTE N) in G1 *. 
- rewrite /getStatelet findU eqxx(cohS C)/=.
  by apply: no_msg_from_to_consume'=>//; rewrite (cohVs C').
- rewrite /getStatelet findU eqxx(cohS C)/=.
  case: msg H2 H4=>t c H2 H4.
  by apply: (msg_spec_consumeE (cohVs C') H4 G4); rewrite N orbC.
rewrite /getStatelet findU eqxx (cohS C)/=/holds_res_perms.
rewrite /getLocal/=findU eqxx/= (cohVl (cohQ s C)).  
case: H1;[|case=>//]; move=>Z; subst rt=>//=; simpl in H2, H4;
rewrite/QueryProtocol.receive_step (getStK _ Tr)/=.
- case:ifP=>_; last by exists rq, rs. 
  exists rq, ((from, head 0 msg) :: rs); split=>//rn.
  case X: (this == from); last first.
  + by rewrite inE; case/orP; [case/eqP=>Z; subst; rewrite eqxx in X|move/Np].
  move/eqP:X=>X; subst from.
  by case: msg H2 H4=>t c/= H2 H4; move: (G3 _ _ _ H4); subst t.  
case:ifP=>_; last by exists rq, rs. 
by exists (seq.rem (from, head 0 msg) rq), rs. 
Qed.

(***********************************************************)
(* A rely-inductive predicate describing the message story *)
(***********************************************************)

Definition msg_story s req_num to data reqs resp :=
  [/\ to \in qnodes,
     core_state_to_data to (getLc' s to) data,
     local_indicator data (getLc s) & 
     let: d := getSq s in
     [\/ msg_just_sent d reqs resp req_num to,
      msg_received d reqs resp req_num to |
      msg_responded d reqs resp req_num to data]].

(* This lemma employs hooking -= it's better hold!.. :-s *)
Lemma msg_story_step' req_num data reqs resp to s s' :
  this != to ->
  msg_story s req_num to data reqs resp ->
  network_step W to s s' ->
  msg_story s' req_num to data reqs resp.
Proof.
move=> N H S; case: H=> Qn H L M; split=>//.
- apply: (core_state_stable s data s')=>//.
  by exists 1, to, s'; split=>//=; split=>//; case/step_coh: S.
- suff R : (network_rely W this s s') by rewrite -(rely_loc' _ R) in L.
  by exists 1, to, s'; split=>//=; split=>//; case/step_coh: S.
case: S; [by case=>_<- |
  move=>l st H1 to'/= msg n H2 H3 C H4 H5 H6->{s'}|
  move=>l rt H1 i from pf H3 C msg H2/=[H4]_->{s'}];
  rewrite -(cohD C) domUn !inE !domPt !inE in H3;
  case/andP:H3=>_ H3; case/orP: H3=>/eqP H3; subst l.

(* Something sending in lc, should be irrelevant for us. *)
- move: st H1 H4 H5 H6; rewrite /get_st prEqC=>st H1 H4 H5 H6.
  by case: M; [constructor 1|constructor 2|constructor 3];
     rewrite /getStatelet findU (negbTE Lab_neq). 

(* Something sending in lq, this is where the interesting stuff happens! *)
- by apply: send_lq_all_cases.

(* Something is receiving in lc, should be irrelevant for us. *)
- move: (coh_s _ _) rt pf H1 H2 H4; rewrite /get_rt prEqC=>C' rt pf H1 H2 H4.
  by case: M; [constructor 1|constructor 2|constructor 3];
     rewrite /getStatelet findU (negbTE Lab_neq). 

(* Something receiving in lq, requires honest proving. *)  
move: (coh_s _ _) rt pf H1 H2 H4; rewrite /get_rt prEqQ=>C' rt pf H1 H2 H4.
case: M=>M;[|constructor 2|constructor 3]; last first.
- by apply: recv_lq_case3.
- by apply: recv_lq_case2.
by case:(recv_lq_case1 req_num _ _ to s N Qn M i from msg C C' pf _ H1 H2 H4);
  [constructor 1|constructor 2].
Qed.

Lemma msg_story_step req_num to data reqs resp z s s' :
  this != z ->
  msg_story s req_num to data reqs resp ->
  network_step W z s s' ->
  msg_story s' req_num to data reqs resp.
Proof.
case A: (to == z); first by move/eqP: A=>A; subst to; apply: msg_story_step'.
move=> N H S; case: H=> Qn H L M; split=>//.
- apply: (core_state_stable s data s')=>//.
  by exists 1, z, s'; split=>//=; split=>//; case/step_coh: S.
- suff R : (network_rely W this s s') by rewrite -(rely_loc' _ R) in L.
  by exists 1, z, s'; split=>//=; split=>//; case/step_coh: S.

case: S; [by case=>_<- |
  move=>l st H1 to'/= msg n H2 H3 C H4 H5 H6->{s'}|
  move=>l rt H1 i from pf H3 C msg H2/=[H4]_->{s'}];
  rewrite -(cohD C) domUn !inE !domPt !inE in H3;
  case/andP:H3=>_ H3; case/orP: H3=>/eqP H3; subst l;
  do? [by rewrite /getStatelet findU (negbTE Lab_neq)];
  rewrite /getStatelet findU eqxx(cohS C)/=.                

(* Now only consider send-receive transitions within pq protocol *)

(** Send-transitions **)
case:M; case=>G1 G2 G3 G4 G5; [constructor 1|constructor 2|constructor 3].

(* Send-transition, case 1 *)
- split=>//=; first by rewrite /getLocal/= findU (negbTE N) in G1 *. 
  + move=>i t c; rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
    case:ifP; last by move=>_; apply G2. 
    rewrite domPt inE=>/eqP<-; rewrite findPt.
    by case=>???; subst to; rewrite eqxx in A.
  + case: G4; case=>i[[c']Q1 Q3] Q2; split; last first.
    - move=>j c; rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
      case:ifP; last by move=>_; apply Q2.
      rewrite domPt inE=>/eqP<-; rewrite findPt.
      by case=>????; subst z to' c; rewrite eqxx in N.
    exists i; split=>[|j[c1]];rewrite findUnL ?(valid_fresh) ?(cohVs (cohQ s C))//.   
    - by exists c'; rewrite (find_some Q1). 
    case: ifP=>_; first by move=> T; apply: Q3; exists c1. 
    by case/findPt_inv=>_[]????; subst to' z; rewrite eqxx in N.
  by case:G5=>rq[rs][Tr]Np; exists rq, rs; rewrite /getLocal/=findU A/=. 
    
(* Send-transition, case 2 *)
- split=>//=; first by rewrite /getLocal/= findU (negbTE N) in G1 *. 
  + move=>i t c; rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
    case:ifP; last by move=>_; apply G3. 
    rewrite domPt inE=>/eqP<-; rewrite findPt.
    by case=>????; subst z to'; rewrite eqxx in N.
  + move=>i t c; rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
    case:ifP; last by move=>_; apply G4. 
    rewrite domPt inE=>/eqP<-; rewrite findPt.
    by case=>????; subst z to'; rewrite eqxx in A.
  by case:G5=>rq[rs][Tr]Np; exists rq, rs; rewrite /getLocal/=findU A/=. 

(* Send-transition, case 3 *)
- split=>//=; first by rewrite /getLocal/= findU (negbTE N) in G1 *. 
  + move=>i t c; rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
    case:ifP; last by move=>_; apply G3. 
    rewrite domPt inE=>/eqP<-; rewrite findPt.
    by case=>????; subst to' z; rewrite eqxx in N.
  + case: G4; case=>i[[c']Q1 Q3] Q2; split; last first.
    - move=>j c; rewrite findUnR ?(valid_fresh) ?(cohVs (cohQ s C))//.
      case:ifP; last by move=>_; apply Q2.
      rewrite domPt inE=>/eqP<-; rewrite findPt.
      by case=>????; subst z to' c; rewrite eqxx in A.
    exists i; split=>[|j[c1]];rewrite findUnL ?(valid_fresh) ?(cohVs (cohQ s C))//.   
    - by exists c'; rewrite (find_some Q1). 
    case: ifP=>_; first by move=> T; apply: Q3; exists c1. 
    by case/findPt_inv=>_[]????; subst to' z; rewrite eqxx in A.
  by case:G5=>rq[rs][Tr]Np; exists rq, rs; rewrite /getLocal/=findU A/=. 

(** Receive-transitions **)
case:M; case=>G1 G2 G3 G4 G5; [constructor 1|constructor 2|constructor 3].

(* Receive-transition, case 1 *)
- split=>//=; first by rewrite /getLocal/= findU (negbTE N) in G1 *. 
  + by apply: no_msg_from_to_consume'=>//; rewrite (cohVs (cohQ s C)).
  + case: msg H2 H4=>t c H2 H4.
    apply: (msg_spec_consumeE (cohVs (cohQ s C)) H4 G4).
    by rewrite (negbT A) orbC.
  by case:G5=>rq[rs][Tr]Np; exists rq, rs; rewrite /getLocal/=findU A/=. 

(* Receive-transition, case 2 *)
- split=>//=; first by rewrite /getLocal/= findU (negbTE N) in G1 *. 
  + by apply: no_msg_from_to_consume'=>//; rewrite (cohVs (cohQ s C)).
  + by apply: no_msg_from_to_consume'=>//; rewrite (cohVs (cohQ s C)).
  by case:G5=>rq[rs][Tr]Np; exists rq, rs; rewrite /getLocal/=findU A/=. 

(* Receive-transition, case 3 *)
- split=>//=; first by rewrite /getLocal/= findU (negbTE N) in G1 *. 
  + by apply: no_msg_from_to_consume'=>//; rewrite (cohVs (cohQ s C)).
  + case: msg H2 H4=>t c H2 H4.
    apply: (msg_spec_consumeE (cohVs (cohQ s C)) H4 G4).
    by rewrite (negbTE N) orbC.
  by case:G5=>rq[rs][Tr]Np; exists rq, rs; rewrite /getLocal/=findU A/=.
Qed.


Lemma msg_story_rely req_num to data reqs resp s s2 :
  msg_story s req_num to data reqs resp ->
  network_rely W this s s2 ->
  msg_story s2 req_num to data reqs resp.
Proof.
move=>H1 [n]H2; elim: n s H2 H1=>/=[s | n Hi s]; first by case=>Z _; subst s2.
case=>z[s1][N]H1 H2 H3; apply: (Hi s1 H2).
by apply: (msg_story_step _ _ _ _ _ _ _ _ N H3 H1).
Qed.  


(**************************************************************)
(*********************  Query Programs ************************)
(**************************************************************)

(****************** Reading a request number *******************)

Program Definition read_request_id to :
  {rrd : seq (nid * nat) * seq (nid * nat) * Data}, DHT [this, W]
   (fun i =>
      let: (reqs, resp, data) := rrd in 
      [/\ getLq i = qst :-> (reqs, resp),
       local_indicator data (getLc i),
       query_init_state to i &
       core_state_to_data to (getLc' i to) data],
   fun (r : nat) m => 
     let: (reqs, resp, data) := rrd in 
     [/\ getLq m = qst :-> (reqs, resp),
       local_indicator data (getLc m),
       query_init_state to m,
       core_state_to_data to (getLc' m to) data &                                              
       r = fresh_id reqs]) :=
  Do _ (act (@skip_action_wrapper W this lq pq prEqQ _
                                (fun s pf => fresh_id (getSt this pf).1))).
Next Obligation.
apply: ghC=>i0 [[rq rs] d][P1] P2 P3 P4 C1.
apply: act_rule=>i1 R1; split=>[|r i2 i3]; first by case: (rely_coh R1).
case=>/=H1[Cj]Z; subst i1=>->R2.
rewrite !(rely_loc' _ R2) !(rely_loc' _ R1); split=>//.
- by apply: (query_init_rely _ _ _ _ R2); apply: (query_init_rely _ _ _ _ R1).
- apply: (core_state_stable _ _ _ _ R2); [by case: P3|by rewrite !(rely_loc' _ R1)|].
  by apply: (core_state_stable _ _ _ _ R1)=>//; case: P3.
rewrite -(rely_loc' _ R1) in P1.
suff X: getSt this (Actions.safe_local prEqQ H1) = (rq, rs) by rewrite X. 
by move: (getStK (Actions.safe_local prEqQ H1) P1)=>/=.
Qed.
    
(********************** Sending request ***********************)

Program Definition send_req rid to :=
  act (@send_action_wrapper W pq this (plab pq) prEqQ
                            (qsend_req qnodes) _ [:: rid] to).
Next Obligation. by rewrite !InE; left. Qed.

Program Definition send_req_act (rid : nat) (to : nid) :
  {rrd : seq (nid * nat) * seq (nid * nat) * Data}, DHT [this, W]
   (fun i =>
      let: (reqs, resp, data) := rrd in 
      [/\ getLq i = qst :-> (reqs, resp),
       local_indicator data (getLc i),
       rid = fresh_id reqs,
       query_init_state to i &
       core_state_to_data to (getLc' i to) data],
   fun (r : seq nat) m => 
     let: (reqs, resp, data) := rrd in 
     [/\ getLq m = qst :-> ((to, rid) :: reqs, resp),
      local_indicator data (getLc m),
      r = [:: rid],
      msg_story m rid to data ((to, rid) :: reqs) resp &
      core_state_to_data to (getLc' m to) data])
  := Do (send_req rid to).

Next Obligation.
apply: ghC=>s0[[reqs resp] d]/=[P1] Pi P2 Q P3 C0.
apply: act_rule=>i1 R0; split=>//=[|r i2 i3[Hs]St R2].
(* Precondition *)
- rewrite /Actions.send_act_safe/=.
  move/rely_coh: (R0)=>[_ C1]; rewrite -(rely_loc' _ R0) in P1.
  move: (coh_coh lq C1); rewrite prEqQ=>Cq1; 
  split=>//; [split=>//; try by case:Q| | ].
  + by exists Cq1; rewrite /QueryProtocol.send_req_prec (getStK _ P1)/= P2.
  + by apply/andP; split=>//; rewrite -(cohD C1) W_dom !inE eqxx orbC.
  move=>z lc hk; rewrite find_umfilt eqxx /query_hookz.
  move => F.
  apply sym_eq in F.
  move: F.
  by move/find_some; rewrite domPt !inE=>/eqP.
(* Postcondition *)
have N: network_step W this i1 i2.
- apply: (Actions.send_act_step_sem _ _ St)=>//; first by rewrite prEqQ.
  by rewrite !InE; left.
rewrite (rely_loc' _ R2).
rewrite -(rely_loc' _ R0) in P1.
move/rely_coh: (R0)=>[_]C1; move: (coh_coh lq C1);rewrite prEqQ=>Cq1.
case: St=>->[h]/=[].
rewrite/QueryProtocol.send_step/QueryProtocol.send_step_fun/=.
rewrite (pf_irr (QueryProtocol.send_safe_coh _) Cq1).
rewrite (getStK _ P1); case=>Z Z'; subst h rid.
rewrite Z' locE; last first;
[by apply: cohVl Cq1| by apply: cohS C1|
   by rewrite -(cohD C1) W_dom !inE eqxx orbC|].
have X : getLc i3 = getLc s0.
- rewrite (rely_loc' _ R2) -(rely_loc' _ R0) Z'.
  by rewrite /getStatelet findU; move/negbTE: Lab_neq; rewrite eq_sym=>->.
(* Massaging the hypotheses. *)
split=>//; try by rewrite X//.
apply: (msg_story_rely _ _ _ _ _ i2)=>//.
have E: core_state_to_data to (getLc' i1 to) = core_state_to_data to (getLc' i2 to).
- case B: (to == this); [move/eqP:B=>Z; subst to | ]; last first.
  + by rewrite /getLocal (step_is_local _ N)=>//; move/negbT: B.
  subst i2; rewrite ![getLc' _ _]/getLocal /getStatelet/=.
  by rewrite findU; move/negbTE: Lab_neq; rewrite eq_sym=>->.
move: (query_init_rely _ s0 i1 Q R0)=>{Q}Q; subst i2.
move: (Q)=>[Q1 Q2 Q3 Q4].
move: (core_state_stable _ _ _ _ R0 Q1 Pi P3); rewrite E=>{E}E.
clear N R2 Q C0 X i3 P3.
split=>//.
- rewrite /getStatelet findU; move/negbTE: Lab_neq; rewrite eq_sym=>->//=.
  by rewrite (rely_loc' _ R0).
constructor 1. 
split=>//; rewrite ?inE ?eqxx=>//=.
- rewrite locE=>//; 
  [by rewrite -(cohD C1) W_dom !inE eqxx orbC|
   apply: cohS C1|by apply: cohVl Cq1].
(* Prove the interesting transition *)
- move=>m t c; rewrite /getStatelet findU eqxx (cohS C1)/=.
  set ds := (dsoup _); rewrite findUnR; last first.
  by rewrite valid_fresh; apply: cohVs Cq1.
  rewrite domPt !inE/=; case:ifP=>[/eqP<-|_]; last by apply: Q4.
  by rewrite findPt; case=><-. 
(* TODO: refactor this into a separate lemma about those state predicates *)
- rewrite /getStatelet findU eqxx (cohS C1)/=.
  set ds := (dsoup _); split=>//.
  exists (fresh ds); split=>//.
  + exists [:: fresh_id reqs].
    rewrite findUnR; last by rewrite valid_fresh; apply: cohVs Cq1.
    by rewrite domPt inE eqxx findPt. 
  + move=>x[c]; rewrite findUnR; last by rewrite valid_fresh; apply: cohVs Cq1.
    case:ifP=>[|_[]]; first by rewrite domPt inE=>/eqP->.
    by move/(Q3 x treq c).
  move=>x c ; rewrite findUnR; last by rewrite valid_fresh; apply: cohVs Cq1.
  case:ifP=>[|_[]]; last by move/(Q3 x treq c).
  by rewrite domPt inE=>/eqP->; rewrite findPt;case=>->.
set ds := (dsoup _).
case: Q2=>reqs'[resp'][G1 G2].
case X: (to == this).
- exists ((this, fresh_id reqs) :: reqs), resp; move/eqP:X=>X; subst to.
  rewrite P1 in G1; have V: valid (qst :-> (reqs, resp)) by [].
  case: (hcancelPtV V G1)=>Z1 Z2; subst reqs' resp'=>{G1}.
  split=>//; rewrite locE//; last first;
    [by apply: cohVl Cq1| by apply: cohS C1|
       by rewrite -(cohD C1) W_dom !inE eqxx orbC].
- exists reqs', resp'; split=>//.
  rewrite /getStatelet findU eqxx (cohS C1)/=.
  by rewrite /getLocal findU X. 
case: (Q)=>Nq _ _ _.
move: (core_state_stable _ _ _ _ R0 Nq Pi P3)=>H1.
rewrite -(rely_loc' _ R0) in Pi.
have Pi': local_indicator d (getLc' i2 this).
- by rewrite Z'/getStatelet findU/= eq_sym; move/negbTE:Lab_neq->. 
apply: (core_state_stable _ _ _ _ R2 Nq Pi').
by rewrite Z'/getStatelet findU/= eq_sym; move/negbTE:Lab_neq->. 
Qed.

(***************** Receiving request in a loop ******************)

Program Definition tryrecv_resp (rid : nat) (to : nid) :=
  act (@tryrecv_action_wrapper W this
      (fun k n t (b : seq nat) => [&& k == lq, n == to, t == tresp,
                                   head 0 b == rid & to \in qnodes]) _).
Next Obligation.
case/andP:H=>/eqP=>->_; rewrite joinC domUn inE domPt inE eqxx andbC/=.
case: validUn=>//=; rewrite ?validPt//.
move=>k; rewrite !domPt !inE=>/eqP<-/eqP Z; subst lq.
by move/negbTE: Lab_neq; rewrite eqxx.
Qed.

(* Ending condition *)
Definition recv_resp_cond (res : option Data): bool :=
  if res is Some v then false else true.

(* Invariant relates the argument and the shape of the state *)
Definition recv_resp_inv (rid : nat) to
           (rrd : (seq (nid * nat) * seq (nid * nat) * Data)) :
  cont (option Data) :=
  fun res i =>
    let: (reqs, resp, data) := rrd in
    if res is Some d
    then [/\ getLq i = qst :-> (reqs, resp),
          local_indicator data (getLc i),
          query_init_state to i,
          core_state_to_data to (getLc' i to) data &
          d = data]
    else [/\ getLq i = qst :-> ((to, rid) :: reqs, resp),
          local_indicator data (getLc i) &
          msg_story i rid to data ((to, rid) :: reqs) resp].

Program Definition receive_resp_loop (rid : nat) to :
  {(rrd : (seq (nid * nat) * seq (nid * nat) * Data))}, DHT [this, W]
  (fun i => let: (reqs, resp, data) := rrd in
    [/\ getLq i = qst :-> ((to, rid) :: reqs, resp),
     local_indicator data (getLc i),
     msg_story i rid to data ((to, rid) :: reqs) resp &
     core_state_to_data to (getLc' i to) data],
  fun res m =>
    let: (reqs, resp, data) := rrd in
    exists d, res = Some d /\
     [/\ getLq m = qst :-> (reqs, resp),
      local_indicator data (getLc m),
      query_init_state to m,
      core_state_to_data to (getLc' m to) data &
      d = data]) := 
  Do _ (@while this W _ _ recv_resp_cond (recv_resp_inv rid to) _
         (fun _ => Do _ (
           r <-- tryrecv_resp rid to;
             match r with
             | Some (from, tg, body) =>
               ret _ _ (Some (deserialize (behead body)))             
             | None => ret _ _ None
             end              
         )) None).

Next Obligation. by apply: with_spec x. Defined.
Next Obligation.
case: b H=>[b|]; rewrite /recv_resp_inv !(rely_loc' _ H0); case=>H1 H2 H3.
- move=>H4 ->; split=>//; try by apply: (query_init_rely _ _ _ H3 H0).
- by apply: (core_state_stable _ _ _ _ H0 _ H2)=>//; case: H3. 
split=>//; try apply: (msg_story_rely _ _ _ _ _ _ _ H3 H0).
Defined.
  
Next Obligation.
rename H into d.
apply: ghC=>i0 [[reqs resp] data][G0 H0] C0; apply: step.
apply: act_rule=>i1 R1/=; split; first by case: (rely_coh R1).
case=>[[[from tg] body] i2 i3|i2 i3]; last first.
- case=>S/=[]C1; case; last by case=>?[?][?][?][?][?][].
  case=>_ _ Z; subst i2=>R3; apply: ret_rule=>i4 R4/=.
  case: d G0 H0=>//=_[H1 H2 H3].
  rewrite !(rely_loc' _ R4)!(rely_loc' _ R3)!(rely_loc' _ R1); split=>//.
  by apply: (msg_story_rely _ _ _ _ _ _ _ _ R4);
    apply: (msg_story_rely _ _ _ _ _ _ _ _ R3);
    apply: (msg_story_rely _ _ _ _ _ _ _ _ R1).
case=>Sf[]C1[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E2 Hw/=]; first by case. 
case/andP=>/eqP Z1/andP[/eqP Z2]/andP[/eqP Z3]/andP[/eqP Z4]Qn->{i2}[Z5] Z6 Z7 R3.
subst l' from' from tg body rid.
move: rt pf (coh_s (w:=W) lq (s:=i1) C1) Hin R3 E2 Hw Z3 E; rewrite !prEqQ.
move=>/=rt pf C1' Hin R E2 Hw G E.
have D: rt = qrecv_resp _ by move: Hin G; do![case=>/=; first by move=>->].  
subst rt=>{G}; simpl in E2.
set i2 := (upd _ _ _) in R.
apply: ret_rule=>i4 R3/=; rewrite !(rely_loc' _ R3)!(rely_loc' _ R).
suff X : [/\ getLocal this (getStatelet i2 lq) = qst :-> (reqs, resp),
          local_indicator data (getLc' i2 this),
          query_init_state to i2 &
          deserialize (behead tms) = data].
- case: X=>X1 X2 X3 X4; split=>//.
  by apply: (query_init_rely _ _ _ _ R3); apply: (query_init_rely _ _ _ _ R).
- case: d G0 H0=>//=_[_ H2][_] H3 _ _; case: X3=>Nq _ _ _.
  move: (X2); rewrite -(rely_loc' _ R)=>X3.
  apply: (core_state_stable _ _ _ _ R3 Nq X3).  
  apply: (core_state_stable _ _ _ _ R Nq X2).  
  move: (core_state_stable _ _ _ _ R1 Nq H2 H3)=>{H2 H3 X3 X4}Y.
  by subst i2; rewrite /getStatelet findU eq_sym; move/negbTE:Lab_neq=>->.  
clear R i4 R3.  
case: d G0 H0=>//=_[Q1 Q2 Q3]; rewrite -!(rely_loc' _ R1) in Q1 Q2.
move: (msg_story_rely _ _ _ _ _ _ _ Q3 R1)=>{Q3}Q3.
have P1: valid (dstate (getSq i1)) by case: (C1')=>P1 P2 P3 P4.
have P2: valid i1 by apply: (cohS C1).
have P3: lq \in dom i1.
  rewrite -(cohD C1) domUn inE !domPt !inE/= inE eqxx orbC andbC/=.
  by case/andP: W_valid.
clear Hin R1 C0 i0 i3 Hw. 
(* Consider different cases for msg_story. *)
case: Q3=>_ Q3 Q4 [].
(* Now dismiss two first disjuncts. *)
- case=>_/(_ mid (tag tms) (tms_cont tms)); rewrite -E.
  by case: (tms)E2=>t c/=E2=>/(_ (erefl _))/=; subst t. 
- case=>_ _ _/(_ mid (tag tms) (tms_cont tms)); rewrite -E.
  by case: (tms)E2=>t c/=E2=>/(_ (erefl _))/=; subst t. 
(* The interesting part *)
case=>X1 _ X2 X3 X4; rewrite /query_init_state.
subst i2.
rewrite /receive_step/=/QueryProtocol.receive_step !(getStK C1' X1)/=!inE!eqxx/=.
rewrite !locE ?Qn/=;[|by case: C1'|by apply: cohS C1|by case: C1'].
apply sym_eq in E.
split=>//; last 1 first.
- case:X3; case=>m'[[c]]E'/(_ mid) H.
  have Z: m' = mid by apply: H; exists (tms_cont tms);
    rewrite E; case: (tms) E2=>/=t c'->.
  subst m'; clear H; rewrite E in E'.
  case: (tms) E' E=>t c'[]Z1 Z2; subst c' t=>E.
  by move/(_ _ _ E)=>/eqP->/=; apply: ds_inverse.
- by rewrite /getStatelet findU eq_sym; move/negbTE:Lab_neq=>->.
split=>//.
- case B: (to == this); last first. 
  + rewrite /getStatelet findU eqxx/= (cohS C1)/=.
    rewrite /holds_res_perms in X4.
    case: X4=> rq[rs][G1 G2]; exists rq, rs; split=>//.
    by rewrite /getLocal/= findU; case:ifP=>//=/eqP Z; subst to; rewrite eqxx in B.
  move/eqP:B=>B; subst to; case: X4=> rq[rs][G1 G2].
  rewrite G1 in X1.
  have V: valid (qst :-> (rq, rs)) by apply: validPt.
  case: (hcancelPtV V X1)=>Z1 Z2; subst rq rs; exists reqs, resp; split=>//.
  rewrite /getStatelet/= findU eqxx (cohS C1)/=/getLocal/=findU eqxx/=. 
  by case: C1'=>_->. 
- rewrite /getStatelet/= findU eqxx/= (cohS C1)/=.
  by apply: (no_msg_from_to_consume' _ X2); case: C1'; case.
rewrite /getStatelet/= findU eqxx/= (cohS C1)/=.
case: (tms) E2 E=>t c/=-> E;apply: (no_msg_spec_consume _ E X3).
by case: C1'; case.
Qed.

Next Obligation.
apply:ghC=>i1[[reqs resp] d][L1 I1 M1 S1] C1.
apply: (gh_ex (g:=(reqs, resp, d))); apply: call_rule=>// res i2[Q1 Q2] C2.
by case: res Q1 Q2=>//=data _ [Q1 Q2 Z]; exists data.
Qed.

(*****************************************************************)
(*********           Full request program            *************)
(*****************************************************************)

Variable default_data : Data.

Program Definition request_data_program to :
  {rrd : seq (nid * nat) * seq (nid * nat) * Data}, DHT [this, W]
   (fun i =>
      let: (reqs, resp, data) := rrd in 
      [/\ getLq i = qst :-> (reqs, resp),
       local_indicator data (getLc i),
       query_init_state to i &
       core_state_to_data to (getLc' i to) data],
    fun res m =>
      let: (reqs, resp, data) := rrd in
      [/\ getLq m = qst :-> (reqs, resp),
       local_indicator data (getLc m),
       query_init_state to m,
       core_state_to_data to (getLc' m to) data &
       res = data]) :=
  Do _ (
     rid <-- read_request_id to;
     send_req_act rid to;;
     r <-- receive_resp_loop rid to;
     ret _ _ (if r is Some d then d else default_data) 
     ).
Next Obligation.
apply:ghC=>i1[[reqs resp] d][L1 I1 M1 S1] C1.
apply: step; apply: (gh_ex (g:=(reqs, resp, d))).
apply: call_rule=>//r i2[P1 P2 P3 P4->{r}] C2.
apply: step; apply: (gh_ex (g:=(reqs, resp, d))).
apply: call_rule=>//_ i3[Q1 Q2 _ Q3 Q4]C3.
apply: step; apply: (gh_ex (g:=(reqs, resp, d))).
apply: call_rule=>//? i4[d'][->][T1] T2 T3 T4->{d'}C4.
apply: ret_rule=>i5 R; rewrite !(rely_loc' _ R); split=>//.
- by apply: (query_init_rely _ _ _ _ R).
by apply: (core_state_stable _ _ _ _ R _ T2 T4); case: T3.  
Qed.

End QueryHooked.

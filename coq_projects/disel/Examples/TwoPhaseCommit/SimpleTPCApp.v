From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import State Protocols Worlds NetworkSem Rely.
From DiSeL
Require Import HoareTriples InferenceRules While.
From DiSeL
Require Import TwoPhaseProtocol TwoPhaseCoordinator TwoPhaseParticipant.
From DiSeL
Require TwoPhaseInductiveProof.

Section SimpleTpcApp.

(*

A simple application to run on the shim implementation.

Check for [Run] tags to find the initial state and the code for the
coordinator and the participants.

*)

Definition l := 0.
(* Coordinator node *)
Definition cn := 0.

(* Participant node *)
Definition p1 := 1.
Definition p2 := 2.
Definition p3 := 3.
Definition pts := [::p1; p2; p3].
Definition others : seq nid := [::].

(* Necessary coherence facts *)
Fact Hnin : cn \notin pts. Proof. by []. Qed.
Fact PtsNonEmpty : pts != [::]. Proof. by []. Qed.
Fact Puniq : uniq pts. Proof. by []. Qed.

(* Coordinator *)
Variable data_stream : seq data.
Definition coordinator :=
  coordinator_loop_zero l cn pts others Hnin Puniq PtsNonEmpty data_stream.

(* Participants *)
Program Definition participant p (pf : p \in pts) choices :=
  participant_with_choices l cn pts others Hnin p pf choices. 

Variables (choices1 choices2 choices3 : seq bool).

(* Initial distributed state *)
Definition st_ptr := TPCProtocol.States.st.
Definition log_ptr := TPCProtocol.States.log. 

Definition init_heap_c := st_ptr :-> (0, CInit) \+ log_ptr :-> ([::] : seq (bool * data)).
Definition init_heap_p := st_ptr :-> (0, PInit) \+ log_ptr :-> ([::] : seq (bool * data)).

Definition init_dstate :=
  cn \\-> init_heap_c \+
  p1 \\-> init_heap_p \+
  p2 \\-> init_heap_p \+
  p3 \\-> init_heap_p.

Lemma valid_init_dstate : valid init_dstate.
Proof.
case: validUn=>//=;
do?[case: validUn=>//; do?[rewrite ?validPt/=//]|by rewrite validPt/=].
- by move=>k; rewrite !domPt !inE/==>/eqP<-/eqP.
- by move=>k; rewrite domUn!inE/==>/andP[_]/orP[]; rewrite !domPt!inE/==>/eqP=><-.
move=>k; rewrite domUn!inE/==>/andP[_]/orP[]; last by rewrite !domPt!inE/==>/eqP=><-.
by rewrite domUn!inE/==>/andP[_]/orP[]; rewrite !domPt!inE/==>/eqP=><-.
Qed.

Notation init_dstatelet := (DStatelet init_dstate Unit).

(* [Run] Initial state to run *)
Definition init_state : state := l \\-> init_dstatelet.

Lemma getCnLoc : getLocal cn init_dstatelet = init_heap_c.
Proof.
rewrite /getLocal/init_dstate -!joinA findPtUn//.
by rewrite !joinA valid_init_dstate.
Qed.

Lemma getPLoc p : p \in pts -> getLocal p init_dstatelet = init_heap_p.
Proof.
rewrite /pts !inE=>/orP[];[|move=>/orP[]]=>/eqP->{p};
  move: valid_init_dstate; rewrite /getLocal/init_dstate.
- by rewrite -!joinA joinCA=>V; rewrite findPtUn//.
- by rewrite -joinA joinCA=>V; rewrite findPtUn//.
by rewrite joinC=>V; rewrite findPtUn//.
Qed.


(* Final Safety Facts *)
Notation W := (mkWorld (TwoPhaseCoordinator.tpc l cn pts others Hnin)).

Lemma hook_complete_unit (c : context) : hook_complete (c, Unit).
Proof. by move=>????; rewrite dom0. Qed.

Lemma hooks_consistent_unit (c : context) : hooks_consistent c Unit.
Proof. by move=>????; rewrite dom0. Qed.

Lemma init_coh : init_state \In Coh W.
Proof.
split.
- apply/andP; split; last by rewrite valid_unit.
  by rewrite validPt.
- by rewrite/init_state validPt.
- by apply: hook_complete_unit.  
- by move=>z; rewrite /init_state !domPt inE/=.
move=>k; case B: (l==k); last first.
- have X: (k \notin dom init_state) /\ (k \notin dom W.1).
    by rewrite /init_state/W/=!domPt !inE/=; move/negbT: B. 
  rewrite /getProtocol /getStatelet/=.
  case: dom_find X=>//; last by move=>? _ _[].
  by move=>->[_]; case: dom_find=>//->.
move/eqP:B=>B; subst k; rewrite prEq/getStatelet/init_state findPt/=.
split=>//=; do?[by apply: valid_init_dstate]; first by split=>//m ms; rewrite find0E.
- move=>z; rewrite /init_dstate/TPCProtocol.nodes/=/others.
  rewrite !domUn !inE valid_init_dstate/=.
  rewrite !domUn !inE (validL valid_init_dstate)/=.
  rewrite !domUn !inE (validL (validL valid_init_dstate))/=.
  rewrite !domPt!inE/= !(eq_sym z).
  rewrite 3!inE.
  by case:(cn==z)(p1==z)(p2==z)(p3==z);case;case;case.
move=>z/=; rewrite !inE=>/orP [].
- move/eqP=>Z; subst z; rewrite getCnLoc; split=>//=.
  by exists (0, CInit), [::].
move=>H; have P : z \in pts by case/orP: H;[|case/orP]=>/eqP->.
rewrite (getPLoc _ P); split=>//; case: ifP; first by move/eqP=>Z; subst z. 
by move=>_; rewrite P; exists (0, PInit), [::].
Qed.


(* [Run] Runnable coordinator code *)
Program Definition run_coordinator :
  DHT [cn, _] (
  fun i => network_rely W cn init_state i,
  fun _ m => exists (chs : seq bool),
  let: r := size data_stream in
  let: lg := seq.zip chs data_stream in
  getLocal cn (getStatelet m l) =
    st :-> (r, CInit) \+ log :-> lg /\
  forall pt, pt \in pts ->
    getLocal pt (getStatelet m l) =
      st :-> (r, PInit) \+ log :-> lg)
  := Do (with_inv (TwoPhaseInductiveProof.ii _ _ _) coordinator).
Next Obligation.
move=>i/=R.
apply: with_inv_rule'.
apply:call_rule=>//.
- by rewrite (rely_loc' _ R) /getStatelet findPt/=getCnLoc.
move=>_ m [chs] CS C I _.
exists chs.
split=>//.
move=>pt Hpt.
move /(coh_coh l) in C.
change l with (plab (TwoPhaseInductiveProof.tpc (cn :=cn) (pts := pts) l others Hnin)) in C.
rewrite prEq in C.
exact: (TwoPhaseInductiveInv.cn_log_agreement(l:=l)(others:=others)(Hnin:=Hnin) C CS I Hpt).
Qed.


Program Definition run_participant p (pf : p \in pts) choices :
  DHT [p, _] (
  fun i => network_rely W p init_state i,
  fun _ m => exists (lg : Log) (r : nat),
   getLocal p (getStatelet m l) = st :-> (r, PInit) \+ log :-> lg /\
   forall pt' (ps' : PState) lg', pt' \in pts ->
    getLocal pt' (getStatelet m l) = st :-> (r, ps') \+ log :-> lg' -> lg = lg')
  := Do (with_inv (TwoPhaseInductiveProof.ii _ _ _ ) (participant p pf choices)).
Next Obligation.
move=>i/=R.
apply: with_inv_rule'.
apply:call_rule=>//.
- by rewrite (rely_loc' _ R)/getStatelet findPt/= (getPLoc _ pf).
move=>_ m [bs][ds] PS C I _.
exists (seq.zip bs ds), (size choices).
move /(coh_coh l) in C.
change l with (plab (TwoPhaseInductiveProof.tpc (cn :=cn) (pts := pts) l others Hnin)) in C.
rewrite prEq in C.
split=>//.
move=>pt ps' lg' Hpt PS'.
apply/esym.
exact: (TwoPhaseInductiveInv.pt_log_agreement(l:=l)(others:=others)(Hnin:=Hnin) C pf PS I Hpt PS' erefl).
Qed.

(* [Run] Runnable participants *)
Program Definition run_participant1 := run_participant p1 _ choices1.
Program Definition run_participant2 := run_participant p2 _ choices2.
Program Definition run_participant3 := run_participant p3 _ choices3.

End SimpleTpcApp.


Definition data_seq :=
  [:: [::1;2];
      [::3;4];
      [::5;6];
      [::7;8];
      [::9;10]
  ].

Definition choice_seq1 := [:: true; true; true; true; true].
Definition choice_seq2 := [:: true; false; true; true; true].
Definition choice_seq3 := [:: true; false; true; false; true].

(* [Run] Final programs to run with actual arguments supplied *)

Definition c_runner (u : unit) := run_coordinator data_seq.

Definition p_runner1 (u : unit) := run_participant1 choice_seq1.
Definition p_runner2 (u : unit) := run_participant1 choice_seq2.
Definition p_runner3 (u : unit) := run_participant1 choice_seq3.

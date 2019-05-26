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

(* The Hello World example - a distributed protocol, allowing anyone send
anyone a greeting message. *)

Module GreeterProtocol.
Section GreeterProtocol.


Variable fixed_nodes : seq nid.

Section GreeterCoh.

(* All nodes are welcome to participate in the protocol *)
Definition nodes (d : dstatelet) : pred nid := mem fixed_nodes.

(* Defining coherence predicate for the greeter statelet *)

Definition hello := [:: 3; 1; 1; 0].
Definition counter := ptr_nat 1.

(* All messages have fixed shape *)
Definition soupCoh : Pred soup :=
  [Pred s | valid s /\
            forall m msg,
              find m s = Some msg ->
              let: from := from msg in
              let: tag := tag (content msg) in
              let: val := tms_cont (content msg) in
              [/\ from \in fixed_nodes, 
                  tag == 0 & behead val == hello]].

(* Coherence for the local state ensures that is has just one counter,
   which we will later use to count incoming messages  *)
Definition localCoh : Pred heap :=
  [Pred h | exists n : nat, h = counter :-> n].

(* Overall coherence *)
Definition greeter_coh d : Prop :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soupCoh ds, dom dl =i fixed_nodes,
   valid dl &
   forall n, n \in fixed_nodes -> localCoh (getLocal n d)].

(* Axioms of the coherence predicate *)
Lemma l1 d: greeter_coh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d: greeter_coh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d: greeter_coh d -> dom (dstate d) =i nodes d.
Proof. by case. Qed.

(* Wrapping up the coherence predicate *)
Definition GreeterCoh := CohPred (CohPredMixin l1 l2 l3).
End GreeterCoh.

Section GreeterSend.

Section SendBase.

Notation coh := GreeterCoh.

(* Defining send and receive transitions *)
Definition greet_safe (this n : nid) (d : dstatelet) msg :=
  [/\ this \in fixed_nodes,
      n \in fixed_nodes,
      exists m, msg == m :: hello &
      coh d].

Section GreetAux.

Variables (this : nid) (d : dstatelet)
          (C : coh d).

Lemma lcoh n : n \in fixed_nodes -> localCoh (getLocal n d).
Proof. by move=> H; case: C => _ _ _/(_ n H). Qed.

Lemma cohN n v :
  n \in fixed_nodes ->
  find counter (getLocal n d) = Some v ->
  dyn_tp v = nat.
Proof. by move=>H; case: (lcoh H)=>m->; rewrite findPt /=; case=><-. Qed.

Definition getN n (pf : n \in fixed_nodes) : nat := 
  match find counter (getLocal n d) as f return _ = f -> _ with
    Some v => fun epf => icast (sym_eq (cohN pf epf)) (dyn_val v)
  | None => fun epf => 0
  end (erefl _).

Lemma getNK n (Hn : n \in fixed_nodes) m:
  getLocal n d = counter :-> m -> getN Hn = m.
Proof.
move=>E; rewrite /getN; move: (cohN)=>H.
by move: (H n)=>{H}; rewrite E=>H/=; apply: eqc.
Qed.

End GreetAux.

Lemma this_in_pf this to d msg :
  greet_safe this to d msg -> this \in fixed_nodes.
Proof. by case. Qed.

Lemma greet_safe_coh this to d m : greet_safe this to d m -> coh d.
Proof. by case. Qed.

Definition greet_step (this to : nid) (d : dstatelet)
           (msg : seq nat)
           (pf: greet_safe this to d msg)
  : option heap :=
  if (behead msg == hello) && (to \in fixed_nodes)
  then Some (counter :-> (getN (greet_safe_coh pf) (this_in_pf pf)).+1)
  else None.
 
Lemma greet_safe_in this to d m : greet_safe this to d m ->
                                  this \in nodes d /\ to \in nodes d.
Proof. by case. Qed.

Lemma greet_safe_def this to d msg :
      greet_safe this to d msg <->
      exists b pf, @greet_step this to d msg pf = Some b.
Proof.
split=>[H|].
- exists (counter :-> (getN (greet_safe_coh H) (this_in_pf H)).+1), H.
  rewrite/greet_step; case: (H)=>H1 H2 H3 H4.
  move: (And4 H1 H2 H3 H4)=>C; rewrite H2; case: H3=>m H3.
  by move/eqP: H3=>H3; subst msg=>/=.
by case=>h[pf]; rewrite/greet_step; case:ifP=>///andP[/eqP->H]_; split.
Qed.

Definition greet_tag := 0.

(* We might need to put this statement into a separate definition *)
Lemma greet_step_coh this to d msg (pf : greet_safe this to d msg) b :
  let: f := dstate d in
  let: s := dsoup d  in
  Some b = greet_step pf ->         
  let: f' := upd this b f in
  let: tms := TMsg greet_tag msg in 
  let: s' := (post_msg s (Msg tms this to true)).1 in 
  coh (DStatelet f' s').
Proof.
rewrite/greet_step; case:ifP=>///andP[/eqP Z1 H][]Z'; subst b=>/=.
case:pf=>[F1]F2 F3 [Cs D]Cl Cn.
split=>//=; do?[by rewrite validU/=].
- split; first by rewrite valid_fresh; case: Cs.
  move=>m msg'; rewrite findUnR ?domPt ?inE ?valid_fresh; last by case: Cs.
  case: ifP=>[/eqP Z|_]; last by case: Cs=>_ Cs; move/Cs.
  case:F3=>[m']/eqP E; subst msg.
  by subst m; rewrite findPt/=; case=><-.
- move=>n; rewrite domU inE/=; case: ifP=>[/eqP Z| _]//; subst n.
  by rewrite Cl F1.
move: (And4 F1 F2 F3 (And4 Cs D Cl Cn)) => S.
move=>n Hn; exists (if n == this
                    then (getN (greet_safe_coh S) (this_in_pf S)).+1
                    else (getN (greet_safe_coh S) Hn)); rewrite /getLocal/=.
rewrite findU; case Z: (n == this)=>/=.
- by move/eqP: Z=>Z; subst n; move: (And4 Cs D Cl Cn)=>C; rewrite Cl.
case: (Cn n Hn)=>m E; move: (E); rewrite /getLocal=>->; congr (_ :-> _).
by move: (getNK (greet_safe_coh S) Hn E)=><-.
Qed.

End SendBase.

(*  Defined the send-transition of the greeter  *)
Definition greeter_send_trans :=
  SendTrans greet_safe_coh greet_safe_in greet_safe_def greet_step_coh.

End GreeterSend.

Variable l : Label.

(* Defining the protocol *)
Program Definition GreeterProt : protocol :=
  @Protocol _ l _ [:: greeter_send_trans] [::] _ _.

End GreeterProtocol.

Module Exports.
Section Exports.

Definition getN := getN.
Definition getNK := getNK.
Definition GreeterProtocol := GreeterProt.
Definition gsend := greeter_send_trans.
Definition hello := hello.
Definition counter := counter.
Definition greet_safe_coh := greet_safe_coh.

End Exports.
End Exports.

End GreeterProtocol.

Export GreeterProtocol.Exports.

Section GreeterPrograms.

Variable l : Label.
Variable nodes : seq nid.

Definition gp := GreeterProtocol nodes l.

(* Simplest world with one protocol *)
(* TODO: simplify this using canonicals *)
Definition W : world := (l \\-> gp, Unit).

Variable this : nid.

Lemma grEq : (getProtocol W l) = gp.
Proof. by rewrite /getProtocol findPt. Qed.

(* Defining an action for greeting on top of the corresponding transition *)
(* Sends and argument number and a suffix *)
Program Definition greet_act n :=
  @send_action_wrapper W gp this l grEq (gsend nodes) _ (n :: hello).
Next Obligation. by rewrite InE. Qed.

Hypothesis P1 : this \in nodes.

Program Definition read_act :=
  @skip_action_wrapper W this l gp grEq nat (fun s pf => getN pf P1).

Notation loc i := (getLocal this (getStatelet i l)).
Notation msgs i := (dsoup (getStatelet i l)).

Definition greeter_spec to :=
  {n : nat}, DHT [this, W]
  (fun i => loc i = counter :-> n /\ to \in nodes,
   fun r m => 
       [/\ loc m = counter :-> n.+1, 
        head 0 r = n &
        exists z b, find z (msgs m) = Some (Msg (TMsg 0 (n :: hello)) this to b)]).

Program Definition greet to : greeter_spec to :=
  Do (n <-- act read_act;
      act (greet_act n to)).

Next Obligation.
apply ghC=>s1 n [Hloc] Hto C1.

apply: step.
- apply: act_rule. 
  move=> s2 R1.
  split; first by move: R1=> /rely_coh[]; rewrite /read_act/=/Actions.skip_safe. 
  move=> y s2' s3 [Sf1]/=.
  rewrite /Actions.skip_step => -[] C2 ? ? R2; subst s2'; subst.

(* Applying inference rule for actions *)
apply: act_rule=>s4 R3.
(* Dealing with rely *)

(* Proving the precondition *)
split=>[|r s5 s6 [Sf2] St R4].
- split; case/rely_coh: R3=>C3 C4=>//.
  + split=>//; first by eauto.
    by case: C4=>_ _ _ _/(_ l); rewrite grEq.
  + by apply/andP; split=>//; move: (cohD C4)=><-; rewrite domPt inE; apply/eqP.
  move=>???/=.
  move => F.
  apply sym_eq in F.
  move: F.
  by move/find_some; rewrite /Actions.filter_hooks umfilt0 dom0.
(*Bookkeeping for the postconidtion *)
case: St=>Z1[h]/=[St]Z2; subst.

(* Making use of the stepping relation *)
rewrite /GreeterProtocol.greet_step/= Hto in St; case: St=>Z'; subst h.
(* Rewriting the state getter *)
erewrite !getNK in R4; first last. 
- by rewrite (rely_loc' l R3) (rely_loc' l R2) (rely_loc' l R1); exact: Hloc.
- by rewrite (rely_loc' l R1); exact: Hloc.
(* rewriting via rely *)
case/rely_coh: (R3)=>C3 C4.
erewrite getNK; last by rewrite (rely_loc' l R1); exact: Hloc.
rewrite (rely_loc' l R4); split=>//.
- rewrite /getLocal/getStatelet findU eqxx/= (cohS C4)/= findU eqxx/=.
  rewrite getsE /=; last by rewrite -(cohD C4) domPt inE; apply/eqP.
  by rewrite (cohVl (coh_coh l C4)).

(* Reasoning about message soup *)
exists (fresh (msgs s4)).
case: (rely_send_other' R4 (m := fresh (msgs s4)) (l := l)
                        (tm := {| tag := GreeterProtocol.greet_tag; tms_cont := n :: hello |})
                        (to := to) (b := true)); last by move=>b[->]/= _; exists b.
rewrite /getStatelet findU eqxx/= (cohS C4)/=.
rewrite getsE /=; last by rewrite -(cohD C4) domPt inE; apply/eqP.
rewrite joinC findPtUn // joinC valid_fresh.
by apply: (cohVs (coh_coh l C4)).
Qed.

Definition greeter_spec2 n to :=
  DHT [this, W]
  (fun i => loc i = counter :-> n /\ to \in nodes, 
   fun r m =>
     loc m = counter :-> n.+2 /\ head 0 r = n.+1).


Program Definition greet2 n to : greeter_spec2 n to :=
  Do (r <-- greet to;
      greet to).

Next Obligation.
move=>i/=[H1 H2].
(* Switch to the continuation *)
apply: step.
apply: (gh_ex (g := n)); apply: call_rule=>//.
move=>? j[Hcount Hhead _] Cj.
apply: (gh_ex (g := n.+1)); apply: call_rule=>//.
by move=>r m[X1 X2 _]. 
Qed.

End GreeterPrograms.


Section CombineGreeters.

Variables (l1 l2 : Label) (nodes : seq nid) (this : nid).
Variable (lab_disj : l2 != l1).

Definition gp1 := GreeterProtocol nodes l1.
Definition gp2 := GreeterProtocol nodes l2.


Definition V := (W l1 nodes) \+ (W l2 nodes).

Lemma validV : valid V.
Proof.
rewrite /V; apply/andP=>/=.
split; first by rewrite validPtUn/= validPt/= domPt inE/=.
by rewrite unitR valid_unit.
Qed.

Notation loc i k := (getLocal this (getStatelet i k)).
Notation msgs i k := (dsoup (getStatelet i k)).

Hypothesis T : this \in nodes.


Definition greet_prog1 := greet2 l1 T.
Definition greet_prog2 := greet2 l2 T.

Definition greeter_spec3 n1 n2 to :=
  DHT [this, V]
  (fun i =>
     [/\ loc i l1 = counter :-> n1,
      loc i l2 = counter :-> n2 &
      to \in nodes], 
   fun r m =>
     [/\ loc m l1 = counter :-> n1.+2,
      loc m l2 = counter :-> n2.+2 &
      r = n1 + n2 + 2]).

Lemma hook_complete_unit (c : context) : hook_complete (c, Unit).
Proof. by move=>????; rewrite dom0. Qed.

Lemma hooks_consistent_unit (c : context) : hooks_consistent c Unit.
Proof. by move=>????; rewrite dom0. Qed.

Program Definition greet3 n1 n2 to : greeter_spec3 n1 n2 to :=
  Do (r1 <-- iinject (greet_prog1 n1 to);
      r2 <-- iinject (greet_prog2 n2 to);
      ret _ _ (head 0 r1 + head 0 r2)).

Next Obligation. exact Unit. Defined.
Next Obligation. 
rewrite -(unitR V)/V.
have V: valid (W l1 nodes \+ W l2 nodes \+ Unit) by rewrite unitR validV.
apply: (injectL V); do?[apply: hook_complete_unit | apply: hooks_consistent_unit].
by move=>??????; rewrite dom0.
Qed.
Next Obligation. exact Unit. Defined.
Next Obligation.
rewrite -(unitR V)/V.
have V: valid (W l1 nodes \+ W l2 nodes \+ Unit) by rewrite unitR validV.
apply: (injectR V); do?[apply: hook_complete_unit | apply: hooks_consistent_unit].
by move=>??????; rewrite dom0.
Defined.

Lemma hcomp l : hook_complete (W l nodes).
Proof. by move=>????; rewrite dom0. Qed.

Next Obligation.
move=>i/=[H1]H2 N.
apply: vrf_coh=>C.
apply: step.
move: (coh_split C (@hcomp l1) (@hcomp l2))=>[i1[j1]][C1 C2 Z]; subst i.
apply: inject_rule=>//.
have E1 : loc (i1 \+ j1) l1 = loc i1 l1
  by rewrite (locProjL C _ C1)// domPt inE/=.
rewrite E1 in H1; apply: call_rule=>// r1 m1 [Q1 Z1] C1' j' C' R1.
have E2 : loc (i1 \+ j1) l2 = loc j1 l2.
  by rewrite (locProjR C _ C2)// domPt inE/=.
rewrite E2 -(rely_loc' l2 R1) in H2.
apply: step.
rewrite joinC; apply: inject_rule.
- case: (rely_coh R1)=>/= _.
  by rewrite injExtL//(cohW C). 
apply: call_rule=>//r2 m2 [E3]Z2 C3 j'' C3' R2.
apply: ret_rule=>m3 R3[G1]G2 G3; split; last first.
(* Playing with locality of transitions, propagating once obtained
   results from intermediate states to the post-state. *)
- by rewrite Z1 Z2 -[_.+1]addn1 -[n2.+1]addn1
             addnAC !addnA !addn1 -addn2.
- rewrite (rely_loc' l2 R3) joinC; rewrite joinC in C3'.
  by rewrite (locProjR C3' _ C3)// domPt inE/=.
rewrite (rely_loc' l1 R3).
move/rely_coh: (R2)=>[]; rewrite injExtR ?(cohW C)// =>_ C5.
rewrite joinC in C3' *.
rewrite (locProjL C3' _ C5)//?/ddom ?domPt ?inE//=.
by rewrite (rely_loc' l1 R2). 
Qed.

End CombineGreeters.

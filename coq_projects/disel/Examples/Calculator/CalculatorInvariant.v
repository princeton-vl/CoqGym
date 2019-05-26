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
Require Import InductiveInv StatePredicates.
From DiSeL
Require Import CalculatorProtocol.

Section CalculatorInductiveInv.

Variable l : Label.

Variable f : input -> option nat.
Variable prec : input -> bool.
Hypothesis prec_valid :
  forall i, prec i -> exists v, f i = Some v.

Variable cs: seq nid.
Variable cls : seq nid.
(* All nodes *)
Notation nodes := (cs ++ cls).
(* All nodes are unique *)
Hypothesis Huniq : uniq nodes.

(* Protocol and its transitions *)
Notation cal := (CalculatorProtocol f prec cs cls l).
Notation sts := (snd_trans cal).
Notation rts := (rcv_trans cal).

Definition reqs := cstate.
Notation coh := (coh cal).

Notation loc n d := (getLocal n d).

Lemma nodes_falso z : z \in cs -> z \in cls -> False.
Proof.
move=>H1 H2.
move: (Huniq); rewrite cat_uniq=>/andP[_]/andP[/negP H]_.
by apply: H; apply/hasP; exists z.
Qed.

Definition CalcInv d :=
  forall (C: coh d) n to v args i s',
    n \in cls -> to \in cs -> 
    dsoup d = i \\-> (Msg (TMsg resp (v::args)) to n true) \+ s' ->
    f args = Some v.

Notation cal' := (CalculatorProtocol f prec cs cls l).
Notation coh' := (coh cal).
Notation Sinv := (@S_inv cal (fun d _ => CalcInv d)).
Notation Rinv := (@R_inv cal (fun d _ => CalcInv d)).
Notation PI := pf_irr.

Program Definition s1: Sinv (server_send_trans f prec cs cls).
Proof.
move=>this to d msg S b.
move=>/= Hi E G C' n to' v' args' i s1 N1 N2/= Es.
case: (S)=>_[_][C]/hasP[[[me cc]args]]_.
case/andP=>/eqP Z1/andP[/eqP Y]/eqP Z2. 
move: (cohVs C')=>V; rewrite joinC/= in Es V.
move: (cancel2 V Es)=>/=; case: ifP.
- move=>_; case. case=>Z3 Z4 Z5 Z6; subst s1 to to' msg.
  by simpl in Y; case: Z2=>->.
move=>_[E1]/=E2 E3; subst to. clear Es V.
by apply: (Hi C n to' v' args' i _ _ _ E2).
Qed.


Program Definition s2: Sinv (client_send_trans prec cs cls).
Proof.
move=>this to d msg S b.
move=>/= Hi E G C' n to' v' args' i s1 N1 N2/= Es.
move: (cohVs C')=>V; rewrite joinC/= in Es V.
move: (cancel2 V Es)=>/=; case: ifP; last first.
- move=>_[E1]/=E2 E3; clear Es V.
  by case: (S)=>_[_]C _; apply: (Hi C n to' v' args' i _ _ _ E2).
move/eqP=>Z; subst i; by case; discriminate.
Qed.

Program Definition r1: Rinv (server_recv_trans prec cs cls).
Proof.
move=>d from this i C m pf Hi F D Hw Et _.
move=> C' n to v args i' s1 N1 N2/=Es.
suff Es' : exists s', dsoup d =
       i' \\-> {| content := {| tag := resp; tms_cont := v :: args |};
                  from := to;  to := n;
                  active := true |} \+ s'.
by case: Es'=>s' Es'; apply: (Hi C n to v args i' _ N1 N2 Es').
case B: (i \in dom (dsoup d)); last first.
by move: dom_find B Es; rewrite /consume_msg; case=>//->_->; exists s1.
move/um_eta: B=>[vm][_]S1.
move: (cohVs C)=>V; rewrite S1 in V.
rewrite S1 joinC consumeUn ?eqxx joinC// in Es. 
suff V': valid (i \\-> mark_msg vm \+
                free (cT:=union_mapUMC mid (msg TaggedMessage)) i (dsoup d)).
- move: (cancel2 V' Es); case: ifP=>B.
  - move/eqP:B=>B{S1 V V' Es}; subst i'.
    by case: vm=>????/=; rewrite /mark_msg/=; case; discriminate.
  by case=>_ X2 _; rewrite X2 joinCA in S1; rewrite S1; eexists _. 
move: (consume_valid i V).
rewrite /consume_msg/= findUnL// ?domPt inE/= eqxx findPt/=. 
by rewrite updUnL/= domPt/=!inE eqxx !updPt/=.
Qed.

Program Definition r2: Rinv (client_recv_trans prec cs cls).
Proof.
move=>d from this i C m pf Hi F D Hw Et _.
move=> C' n to v args i' s1 N1 N2/=Es.
suff Es' : exists s', dsoup d =
       i' \\-> {| content := {| tag := resp; tms_cont := v :: args |};
                  from := to;  to := n;
                  active := true |} \+ s'.
by case: Es'=>s' Es'; apply: (Hi C n to v args i' _ N1 N2 Es').
case B: (i \in dom (dsoup d)); last first.
by move: dom_find B Es; rewrite /consume_msg; case=>//->_->; exists s1.
move/um_eta: B=>[vm][_]S1.
move: (cohVs C)=>V; rewrite S1 in V.
rewrite S1 joinC consumeUn ?eqxx joinC// in Es. 
suff V': valid (i \\-> mark_msg vm \+
                free (cT:=union_mapUMC mid (msg TaggedMessage)) i (dsoup d)).
- move: (cancel2 V' Es); case: ifP=>B.
  - move/eqP:B=>B{S1 V V' Es}; subst i'.
    by case: vm=>????/=; rewrite /mark_msg/=; case; discriminate.
  by case=>_ X2 _; rewrite X2 joinCA in S1; rewrite S1; eexists _. 
move: (consume_valid i V).
rewrite /consume_msg/= findUnL// ?domPt inE/= eqxx findPt/=. 
by rewrite updUnL/= domPt/=!inE eqxx !updPt/=.
Qed.

Definition sts' := [:: SI s1; SI s2].
Definition rts' := [:: RI r1; RI r2].

Program Definition ii := @ProtocolWithInvariant.II _ _ sts' rts' _ _.

Definition cal_with_inv := ProtocolWithIndInv ii.

(**************************************************)
(*
Overall Implementation effort:

1 person-day

*)
(**************************************************)

        

End CalculatorInductiveInv.


From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Domain Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL
Require Import Actions Injection Process Always.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Program is a set of processes *)
Structure prog (W : world) A (this : nid) :=
  Prog {
      set_of : proc this W A -> Prop; 
      (* Unifinshed is a bottom element that should be present *)
      _ : set_of Unfinished
  }.

Section Programs.

Variable this : nid.
Variable W : world.
Variable A : Type.

Notation coherent := (Coh W).

Arguments Prog [W A].
Arguments Prog [W A this].


Coercion set_of : prog >-> Funclass. 
Canonical prog_PredType W A := mkPredType (fun p => @set_of W A this p). 

Lemma progE (T1 T2 : prog W A this) : 
        T1 = T2 <-> set_of T1 = set_of T2.
Proof.
split=>[->//|]; case: T1 T2=>m1 H1 [m2 H2] /= E.
by move: H2; rewrite -E => H2; rewrite (pf_irr H1 H2).
Qed.

(* Pre/poscondition and  *)
Definition pre := state -> Prop.

(* Postconditions are binary *)
Definition post A := state -> A -> state -> Prop.
Definition cont A := A -> state -> Prop.
Definition spec A := prod pre (post A).

(* What does it mean for a program to have a specification s *)

Definition has_spec (s : spec A) := 
  [Pred T : prog W A this | forall i t, 
     s.1 i -> i \In Coh W -> t \In T -> after i t (s.2 i)]. 

End Programs.

Module DTbin.
Section DTbin.

Variable this : nid.

Structure DTbin (W : world) A (s : spec A) := DTbin_make {
  prog_of : prog W A this; 
  _ : prog_of \In has_spec this W s}.

End DTbin.
End DTbin.

Notation DTbin := DTbin.DTbin.
Notation DTbin_make := DTbin.DTbin_make.

Coercion DTbin.prog_of : DTbin >-> prog.

Section Specs.

Variable this : nid.

Lemma stsepE (W : world) A (s : spec A) (e1 e2 : DTbin this W s) : 
        e1 = e2 <-> e1 = e2 :> prog W A this.
Proof.
split=>[->//|]; case: e1 e2=>T1 H1 [T2 H2] /= E.
by rewrite -{T2}E in H2 *; rewrite (pf_irr H1 H2).
Qed.

(* Unfinished satisfies any specification *)
Lemma prog_unfin (W : world) A (s : spec A) (e : DTbin this W s) : 
        Unfinished \In DTbin.prog_of e.
Proof. by case: e; case. Qed.

(* Packaging the definition into an type, _indexed_ by a specificaion s. *)
Inductive DT (W: world) A :=
  with_spec (s : spec A) of DTbin this W s.

Definition spec_of W A (e : DT W A) := let: with_spec s _ := e in s.
Definition pre_of W A := fun e : DT W A => (spec_of e).1. 
Definition post_of W A := fun e : DT W A => (spec_of e).2. 

(* Returns the actual typed from the packaged type SP *)
Definition code_of (W : world) A (e : DT W A) := 
  let: with_spec _ c := e return DTbin this W (spec_of e) in c.

Arguments pre_of [W A].
Arguments post_of [W A].
Arguments with_spec [W A].
Prenex Implicits pre_of post_of.

Coercion with_spec : DTbin >-> DT.


(*

This is the main predicate defining what the verification is:

* r is a "continuation", encoding the postcondition of type (A ->
  state -> Prop).

* Our goal is to verify that it holds by the end of executing the
  program e from the state i. The program e came with a specification
  DT W A.

* The initial state is assumed to be coherent.
*)

Definition verify (W : world) A (i : state) (e : DT W A) r := 
  i \In Coh W -> 
  forall p, p \In DTbin.prog_of (code_of e) -> after i p r. 

End Specs.


(* Straightforward lattice structure structure for typed programs *)

Module DTLattice.
Section DTLattice.

Variable this : nid.
Variable W : world.
Variables (A : Type) (s : spec A).
Notation prog A := (@prog W A this).
Notation DTbin s := (@DTbin this W A s).

Definition leq (e1 e2 : DTbin s) := 
  set_of (DTbin.prog_of e1) <== set_of (DTbin.prog_of e2).

Lemma leq_refl e : leq e e. 
Proof. by []. Qed.

Lemma leq_trans e1 e2 e3 : leq e1 e2 -> leq e2 e3 -> leq e1 e3.
Proof. by move=>H1 H2 p x; apply: H2; apply: H1. Qed.

Lemma leq_asym e1 e2 : leq e1 e2 -> leq e2 e1 -> e1 = e2.
Proof.
move: e1 e2=>[m1 N1][m2 N2]; rewrite /leq /= => H1 H2.
by apply/stsepE/progE; apply: poset_asym H1 H2.
Qed.


Definition bot_set t := t = @Unfinished this W A. 
Definition bot_prg := @Prog _ _ _ bot_set (erefl _).

(* Bottom satisfies any specification *)
Lemma bot_spec : bot_prg \In has_spec this W s.
Proof. by move=>i H C t ->; apply: alw_unfin. Qed.

(* Bottom of the latice *)
Definition bot := DTbin_make bot_spec.

Lemma bot_bot e : leq bot e.
Proof. by case: e=>[[p U] H] t ->. Qed.

Definition sup_set (es : Pred (DTbin s)) t := 
  t = Unfinished \/ exists e : DTbin s, t \In DTbin.prog_of e /\ e \In es.
Definition sup_prog es := @Prog _ _ _ (sup_set es) (or_introl (erefl _)).

Lemma sup_spec es : sup_prog es \In has_spec this W s.
Proof.
move=>i H C t [->|[e [H1 H2]]]; first by apply: alw_unfin. 
by case: e H1 H2=>p H3 /= H4 _; apply: H3 H C _ H4. 
Qed.

Definition sup es := DTbin_make (@sup_spec es).

(* sup is an upper bound *)
Lemma sup_supB es e : e \In es -> leq e (sup es).
Proof. by move=>H1 x H2; right; exists e. Qed.

(* sup is the least upper bound *)
Lemma sup_supL es e : (forall c, c \In es -> leq c e) -> leq (sup es) e.
Proof. by case: e; case=>m N H /= H1 t [->//|][T][H2]; move/H1; apply. Qed.

End DTLattice.

Module Exports.
Section Exports.
Variable this : nid.
Variable W : world.
Variables (A : Type) (s : spec A).

Definition stPosetMixin := PosetMixin (@leq_refl this W A s) 
                                      (@leq_asym this W A s) (@leq_trans this W A s).
Canonical stPoset := Eval hnf in Poset (@DTbin this W A s) stPosetMixin.

Definition stLatticeMixin := LatticeMixin (@sup_supB this W A s) (@sup_supL this W A s).
Canonical stLattice := Eval hnf in Lattice (@DTbin this W A s) stLatticeMixin.

End Exports.
End Exports.

End DTLattice.

Export DTLattice.Exports.

(* Constuctors for different programs with specifications *)

(* Recursive programs *)
Section Fix. 

Variable this : nid.
Variable W : world.
Variables (A : Type)  (B : A -> Type) (s : forall x, spec (B x)).

Notation tp := (forall x, DTbin this W (s x)).
Notation lat := (dfunLattice (fun x => [lattice of DTbin this W (s x)])).
Variable (f : tp -> tp).

(* we take a fixpoint not of f, but of its monotone completion f' *)
(* should eventually prove that f' is monotone *)

Definition f' (e : lat) := sup [Pred t : lat | exists e', e' <== e /\ t = f e'].

Definition ffix : tp := tarski_lfp f'. 

End Fix.

(* Semantics of specific well-typed programs *)

Section Return.
Variable this : nid.
Variable W : world.
Variables (A : Type)  (x : A).

(* Trees inhabiting a return statement *)
Definition ret_set t := t = Unfinished \/ t = @Ret this W A x.

(* It naturally has the unfinished statement *)
Definition ret_prog := @Prog _ _ _ ret_set (or_introl (erefl _)).

Definition ret_s : spec A := 
  (fun i => True, fun i y m => network_rely W this i m /\ y = x). 

Lemma ret_has_spec : ret_prog \In has_spec this W ret_s.
Proof. 
move=>i _ C t [->|->]; first by apply: alw_unfin.
by apply: alw_ret=>//= m E y [<-].
Qed.

(* Peiring Return with its canontics specification *)
Definition ret := with_spec (DTbin_make ret_has_spec). 

End Return.


Section Act.
Variable this : nid.
Variable W : world.
Variables (A : Type)  (x : A).
Variable a : action W A this.

Definition act_set t := t = Unfinished \/ t = @Act this W A a.
Definition act_prog := @Prog _ _ _ act_set (or_introl (erefl _)).

(* Relaxing the precondition with respect to the rely, via action's safety *)
Definition act_s : spec A := 
  (fun i => forall j, network_rely W this i j -> a_safe a j,
   fun i y m => exists j k, 
       [/\ network_rely W this i j,
        exists (S: a_safe a j), a_step S k y & network_rely W this k m]). 

Lemma act_has_spec : act_prog \In has_spec this W act_s.
Proof. 
move=>i t S C [] -> /=; first by apply: alw_unfin.
apply: alw_act C _; move=>j E1; move/S: (E1)=>pf; exists pf.
split=>// k y m St E2 v [<-]; exists j, k.
by split=>//; exists pf.
Qed.

Definition act := with_spec (DTbin_make act_has_spec).

End Act.

(* Sequential composition *)
Section Bind.

Variable this : nid.
Variable W : world.
Variables (A B : Type).

Section Prog.
Variables (T : prog W A this) (K : A -> prog W B this).

Definition bnd_set t := 
  t = Unfinished \/ exists t', t \In pcat t' K /\ t' \In T.
Definition bnd_prog := @Prog _ _ _ bnd_set (or_introl (erefl _)).

End Prog.

Variables (e1 : DT this W A) (e2 : A -> DT this W B).

(* First command spec *)
Notation s1 := (spec_of e1).

(* Continuation spec *)
Notation s2 := (fun x => spec_of (e2 x)).

Definition bind_s : spec B := 
  (fun i => s1.1 i /\ forall x s, s1.2 i x s -> (s2 x).1 s,
   fun i y m => exists x s, s1.2 i x s /\ (s2 x).2 s y m).

(*
[Ensuring effects execute exactly once]:

DiSeL code is extracted to effectful OCaml programs, which means that
evaluating an expression twice is not equivalent to evaluating it once.
Below, it is essential to write `let y := e2 x in ...` so that the effects
of e2 are executed once rather than twice. This is hard to see because it
*looks* like `y` is only used once, but, in fact, it is used another time
in an implicit argument which boils down to `spec_of y`.

Eventually, we may want to find a way to not extract the `spec_of` part of
`DT`, which is essentially a dependent pair. But for now, we will put up
with this hack.
*)
Lemma bind_has_spec : 
        bnd_prog (code_of e1) (fun x => let y := e2 x in code_of y) \In has_spec this W bind_s.
Proof.
move=>i t [S1 S2] Ci [->|[t1 [Pc P1]]] /=; first by apply: alw_unfin.  
apply: aft_bnd Pc _; case: (code_of e1) P1=>T1 H /= P1.
apply: {H P1 Ci S1 T1 t t1} aft_imp (H _ _ S1 Ci P1).
move=>x s Cs S3 t; case: (code_of (e2 x))=>T /= H P. 
by apply: aft_imp (H _ _ (S2 _ _ S3) Cs P)=>m y Cm; exists x, s.
Qed.

Definition bind := with_spec (DTbin_make bind_has_spec).

End Bind.


Section Inject.
Variables (this : nid) (V W : world) (K : hooks) (A : Type) (w : injects V W K). 
Variable (e : DT this V A).
Notation W2 := (inj_ext w). 
Notation s := (spec_of e).

Section Prog.

Variable T : prog V A this.

Definition inject_set t := 
  t = Unfinished \/ exists t', t' \In T /\ t = Inject w t'. 
Definition inject_prog := @Prog _ _ _ inject_set (or_introl (erefl _)).
End Prog.

Definition inject_s : spec A :=
  (fun i => exists i1 i2, i = i1 \+ i2 /\ i1 \In Coh V /\ s.1 i1, 
   fun i y m => forall i1 i2, i = i1 \+ i2 -> i1 \In Coh V -> 
     exists m1 m2, [/\ m = m1 \+ m2, s.2 i1 y m1 &
                       network_rely W2 this i2 m2]).

Lemma inject_has_spec : inject_prog (code_of e) \In has_spec this W inject_s.
Proof.
move=>i /= t [i1][j1][->{i}][Ci1 H1] C.
case=>[|[t' [H2 ->{t}]]]; first by move=>->; apply: alw_unfin.
have : after i1 t' (s.2 i1) by case: (code_of e) H2=>p /= /(_ _ _ H1); apply. 
move/(aft_inject w C); apply: aft_imp=>{H1 t' H2} v m _.
case=>i2 [j2][->{m} Ci2 S2 H2] i3 j3 E Ci3.
suff [E1 E2]: i3 = i1 /\ j3 = j1.
- by rewrite {i3 E Ci3}E1 {j3}E2; exists i2, j2.
move: (coh_prec (cohS C) Ci1 Ci3 E) (E)=>{Ci3 E} <-.
by move/(joinxK (cohS C)).
Qed.

Definition inject := with_spec (DTbin_make inject_has_spec).

End Inject.

From DiSeL
Require Import InductiveInv.

Section InductiveInv.
Variable pr : protocol.

(* Decompose the initial protocol *)
Notation l := (plab pr).
Notation coh := (coh pr).
Variable I : dstatelet -> pred nid -> Prop.
Variable ii : InductiveInv pr I.

(* Tailored modal always-lemma *)

Variables (A : Type) (this: nid).
Notation V := (mkWorld pr).
Notation W := (mkWorld (ProtocolWithIndInv ii)).

Variable (e : DT this V A).
Notation s := (spec_of e).

Section Prog.

Variable T : prog V A this.

Definition with_inv_set t := 
  t = Unfinished \/ exists t', t' \In T /\ t = WithInv pr I ii (erefl _) t'. 
Definition with_inv_prog := @Prog _ _ _ with_inv_set (or_introl (erefl _)).
End Prog.

Notation getS i := (getStatelet i l).

Definition with_inv_s : spec A :=
  (fun i => s.1 i, 
   fun i y m => m \In Coh W /\ s.2 i y m).

Lemma with_inv_has_spec : with_inv_prog (code_of e) \In has_spec this W with_inv_s.
Proof.
move=>i/=t H1 C1.
case=>[|[t'[H2]->{t}]]; first by move=>->; apply: alw_unfin.
apply: (aft_ind_inv C1).
by case: (code_of e) H2=>p /=/(_ _ _ H1 (with_inv_coh C1)); apply;
   move/with_inv_coh: C1.
Qed.

Definition with_inv := with_spec (DTbin_make with_inv_has_spec).

End InductiveInv.

(* Proving by the rule of consequence *)

Definition conseq (W : world) A this (e : DT this W A) (s : spec A) := 
  forall i, s.1 i -> verify i e (s.2 i). 

(* The specification implies itself *)
Lemma conseq_refl (W : world) A this (e : DT this W A) :
  conseq e (spec_of e).
Proof. by case: e; case=>p q [T H i] /= Hp C t; apply: H. Qed.

Hint Resolve conseq_refl.


(* Weakening the specifications *)
Section Do.

Variable this : nid.
Variables (W : world) (A : Type) (s2 : spec A).
Variables (e : DT this W A) (pf : conseq e s2).

Definition do_prog := DTbin.prog_of (code_of e).

Lemma do_has_spec : do_prog \In has_spec this W s2. 
Proof. 
rewrite /do_prog; case: e pf=>T Ht /=; case: s2=>p q.
by move=>H1 i t /= Hp C H; apply: H1. 
Qed.

Definition do' := DTbin_make do_has_spec.

End Do.

Notation iinject x := (@inject _ _ _ _ _ _ x).
Notation uinject x := (@inject _ _ _ Unit _ _ x).

Notation "'Do' e" := (@do' _ _ _ _ e _) (at level 80).

Notation "x '<--' c1 ';' c2" := (bind c1 (fun x => c2)) 
  (at level 81, right associativity).
Notation "c1 ';;' c2" := (bind c1 (fun _ => c2)) 
  (at level 81, right associativity).

From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem.
From DiSeL
Require Import Actions Injection InductiveInv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ProcessSyntax.

Variable this : nid.

(* Syntax for process *)
Inductive proc (W : world) A :=
  Unfinished | Ret of A | Act of action W A this |
  Seq B of proc W B & B -> proc W A |
  Inject V K of injects V W K & proc V A |
  WithInv p I (ii : InductiveInv p I) of
          W = mkWorld (ProtocolWithIndInv ii) & proc (mkWorld p) A.  

Definition pcat W A B (t : proc W A) (k : A -> Pred (proc W B)) :=
  [Pred s | exists q, s = Seq t q /\ forall x, q x \In k x].

Inductive schedule :=
  ActStep | SeqRet | SeqStep of schedule |  
  InjectStep of schedule | InjectRet |
  WithInvStep of schedule | WithInvRet.

End ProcessSyntax.

Arguments Unfinished [this W A].
Arguments Ret [this W A].
Arguments Act [this W A].
Arguments Seq [this W A B].
Arguments WithInv [this W A].

Section ProcessSemantics.

Variable this : nid.

Fixpoint step (W : world) A (s1 : state) (p1 : proc this W A)
         sc (s2 : state) (p2 : proc this W A) : Prop :=
  match sc, p1 with
  (* Action - make a step *)  
  | ActStep, Act a => exists v pf, @a_step _ _ _ a s1 pf s2 v /\ p2 = Ret v
  (* Sequencing - apply a continuation *)  
  | SeqRet, Seq _ (Ret v) k => s2 = s1 /\ p2 = k v
  | SeqStep sc', Seq _ p' k1 => 
    exists p'', step s1 p' sc' s2 p'' /\ p2 = Seq p'' k1
  (* Injection of a non-reduced term *)
  | InjectRet, Inject V K pf (Ret v) =>
     exists s1', [/\ s2 = s1, p2 = Ret v & extends pf s1 s1']
  | InjectStep sc', Inject V K pf t1' =>
    exists s1' s2' s t2', 
    [/\ p2 = Inject pf t2', s1 = s1' \+ s, s2 = s2' \+ s, 
     s1' \In Coh V & step s1' t1' sc' s2' t2']
  (* Imposing an inductive invariant on a non-reduced term *)
  | WithInvRet, WithInv p inv ii pf (Ret v) =>
     exists s1', [/\ s2 = s1, p2 = Ret v & s1 = s1']
  | WithInvStep sc', WithInv p inv ii pf t1' =>
    exists t2', p2 = WithInv p inv ii pf t2' /\  
                     step s1 t1' sc' s2 t2'   
  | _, _ => False
  end.

Fixpoint good (W : world) A (p : proc this W A) sc  : Prop :=
  match sc, p with
  | ActStep, Act _ => True
  | SeqRet, Seq _ (Ret _) _ => True
  | SeqStep sc', Seq _ p' _ => good p' sc'
  | InjectStep sc', Inject _ _ _ p' => good p' sc'
  | InjectRet, Inject _ _ _ (Ret _) => True
  | WithInvStep sc', WithInv _ _ _ _ p' => good p' sc'
  | WithInvRet, WithInv _ _ _ _ (Ret _) => True
  | _, _ => False
  end.

(*

[Safety in small-step semantics]

The safety (in order to make the following step) with respect to the
schedule is defined inductively on the shape of the program and the
schedule. Omitting the schedule is not a good idea, at it's required
in order to "sequentialize" the execution of the program
structure. Once it's dropped, this structure is lost.

 *)

Fixpoint safe (W : world) A (p : proc this W A) sc (s : state)  : Prop :=
  match sc, p with
  | ActStep, Act a => a_safe a s
  | SeqRet, Seq _ (Ret _) _ => True
  | SeqStep sc', Seq _ p' _ => safe p' sc' s
  | InjectStep sc', Inject V K pf p' =>
      exists s', extends pf s s' /\ safe p' sc' s'
  | InjectRet, Inject V K pf (Ret _) => exists s', extends pf s s'
  | WithInvStep sc', WithInv _ _ _ _ p' => safe p' sc' s
  | WithInvRet, WithInv _ _ _ _ (Ret _) => True
  | _, _ => True
  end.

Definition pstep (W : world) A s1 (p1 : proc this W A) sc s2 p2 := 
  [/\ s1 \In Coh W, safe p1 sc s1 & step s1 p1 sc s2 p2].

(* Some sanity lemmas wrt. stepping *)

Lemma pstep_safe (W : world) A s1 (t : proc this W A) sc s2 q : 
        pstep s1 t sc s2 q -> safe t sc s1.
Proof. by case. Qed.


(*

The following lemma established the operational "progress" property: a
program, which is safe and also the schedule is appropriate. Together,
this implies that we can do a step. 
 *)

Lemma proc_progress W A s (p : proc this W A) sc : 
        s \In Coh W -> safe p sc s -> good p sc ->  
        exists s' (p' : proc this W A), pstep s p sc s' p'.
Proof.
move=>C H1 H2; elim: sc W A s p H2 H1 C=>[||sc IH|sc IH||sc IH|]W A s. 
- case=>//=a _/= H; move/a_step_total: (H)=>[s'][r]H'.
  by exists s', (Ret r); split=>//=; exists r, H.  
- by case=>//; move=>B p k/=; case: p=>//b _ _; exists s, (k b). 
- case=>//B p k/=H1 H2 C.
  case: (IH W B s p H1 H2 C)=>s'[p'][G1 G2].
  by exists s', (Seq p' k); split=>//; exists p'. 
- case=>// V K pf p/=H1 [z][E]H2 C. 
  case: (E)=>s3[Z] C1 C2.
  case: (IH V A z p H1 H2 C1) =>s'[p']H3; case: H3=>S St.
  exists (s' \+ s3), (Inject pf p'); split=>//; first by exists z.  
  by subst s; exists z, s', s3, p'. 
- case=>//V K pf; case=>// v/=_[s'] E C.          
  by exists s, (Ret v); split=>//=; exists s'.
- case=>//pr I ii E p/= H1 H2 C.
  have C' : s \In Coh (mkWorld pr) by subst W; apply: (with_inv_coh C). 
  case: (IH (mkWorld pr) A s p H1 H2 C')=>s'[p']H3.
  exists s', (WithInv pr I ii E p'); split=>//=.
  by exists p'; split=>//; case: H3. 
- case=>//pr I ii E; case=>//v/=_ _ C.          
  by exists s, (Ret v); split=>//=; exists s. 
Qed.

(* Some view lemmas for processes and corresponding schedules *)

Lemma stepUnfin W A s1 sc s2 (t : proc this W A) : 
        pstep s1 Unfinished sc s2 t <-> False.
Proof. by split=>//; case; case: sc. Qed.

Lemma stepRet W A s1 sc s2 (t : proc this W A) v : 
        pstep s1 (Ret v) sc s2 t <-> False.
Proof. by split=>//; case; case: sc. Qed.

Lemma stepAct W A s1 a sc s2 (t : proc this W A) : 
        pstep s1 (Act a) sc s2 t <->
        exists v pf, [/\ sc = ActStep, t = Ret v & @a_step _ _ _ a s1 pf s2 v].
Proof.
split; first by case=>C; case: sc=>//= c [v [pf [H ->]]]; exists v, pf. 
case=>v[pf] [->-> H]; split=>//; last by exists v, pf.
by apply: (a_safe_coh pf). 
Qed.

Lemma stepSeq W A B s1 (t : proc this W B) k sc s2 (q : proc this W A) :
        pstep s1 (Seq t k) sc s2 q <->
        (exists v, [/\ sc = SeqRet, t = Ret v, q = k v, s2 = s1 &
                       s1 \In Coh W]) \/
         exists sc' p',
           [/\ sc = SeqStep sc', q = Seq p' k & pstep s1 t sc' s2 p'].
Proof.
split; last first.
- case; first by case=>v [->->->->]. 
  by case=>sc' [t'][->->][S H]; do !split=>//; exists t'. 
case; case: sc=>//[|sc] C. 
- by case: t=>//= v _ [->->]; left; exists v. 
by move=>G /= [p' [H1 ->]]; right; exists sc, p'.
Qed.

Lemma stepInject V W K A (em : injects V W K) 
                s1 (t : proc this V A) sc s2 (q : proc this W A) :
  pstep s1 (Inject em t) sc s2 q <->
  (* Case 1 : stepped to the final state s1' of the inner program*)
  (exists s1' v, [/\ sc = InjectRet, t = Ret v, q = Ret v, s2 = s1 &
                     extends em s1 s1']) \/
  (* Case 2 : stepped to the nextx state s12 of the inner program*)
  exists sc' t' s1' s2' s, 
    [/\ sc = InjectStep sc', q = Inject em t', 
     s1 = s1' \+ s, s2 = s2' \+ s, s1 \In Coh W &
              pstep s1' t sc' s2' t'].
Proof.
split; last first.
- case.
  + case=>s1' [v][->->->->] E.
    split=>//=; [by case: E=>x[] | by exists s1'|by exists s1'].
  case=>sc' [t'][s1'][s2'][s][->->->-> C][[C' S] T]. 
  split=>//=; last by exists s1', s2', s, t'. 
  by exists s1'; split=>//; exists s. 
case=>C; case: sc=>//=; last first.
- case: t=>//= v [C1 S][s1'][->->{s2 q}] X.
  by left; exists s1'; exists v. 
move=>sc /= [s'][X] S [s1'][s2'][t'][t2'][??? C1'] T; subst q s1 s2. 
right; exists sc, t2', s1', s2', t'; do !split=>//.
by case: X=>t'' [E] Cs' _; rewrite (coh_prec (cohS C)  _ Cs' E). 
Qed.

Lemma stepWithInv W A pr I (ii : InductiveInv pr I) s1 
      (t : proc this (mkWorld pr) A) sc s2 (q : proc this W A) pf :
  pstep s1 (WithInv pr I ii pf t) sc s2 q <-> 
  (exists v, [/\ sc = WithInvRet, t = Ret v, q = Ret v, s2 = s1,
                 s1 \In Coh W & W = mkWorld (ProtocolWithIndInv ii)]) \/
  exists sc' t' , [/\ sc = WithInvStep sc', q = WithInv pr I ii pf t',
                      W = mkWorld (ProtocolWithIndInv ii),
                      s1 \In Coh W & pstep s1 t sc' s2 t'].
Proof.
split; last first.
- case.
  + by case=>v[->->->->{s2}]C E; split=>//=; exists s1.
   by case=>sc' [t'][->->{sc q}]E C[C' S]T; split=>//=; exists t'.   
case=>C; case: sc=>//=; last first.
- by case: t=>//=v _[s1'][Z1]Z2 Z3; subst s2 s1' q; left; exists v. 
move=>sc /=S[t'][->{q}T]; right; exists sc, t'; split=>//.
by split=>//; subst W; apply: (with_inv_coh C).
Qed.

(*

[Stepping and network semantics]

The following lemma ensures that the operational semantics of our
programs respect the global network semantics.

 *)

Lemma pstep_network_sem (W : world) A s1 (t : proc this W A) sc s2 q :
        pstep s1 t sc s2 q -> network_step W this s1 s2.
Proof.
elim: sc W A s1 s2 t q=>/=.
- move=>W A s1 s2 p q; case: p; do?[by case|by move=>?; case].
  + by move=>a/stepAct [v][pf][Z1]Z2 H; subst q; apply: (a_step_sem H).
  + by move=>???; case. 
  + by move=>????; case.
  by move=>?????; case.   
- move=>W A s1 s2 p q; case: p; do?[by case|by move=>?; case].
  + move=>B p p0/stepSeq; case=>[[v][_]??? C|[sc'][p'][]]//.
    by subst p s2; apply: Idle. 
  by move=>????/stepInject; case=>[[?][?][?]|[?][?][?][?][?][?]]//.
  by move=>?????; case.   
- move=>sc HI W A s1 s2 p q; case: p; do?[by case|by move=>?; case].
  + move=>B p p0/stepSeq; case=>[[?][?]|[sc'][p'][][]? ?]//.
    by subst sc' q; apply: HI.
  by move=>????; case=>? _.
  by move=>?????; case.   
- move=>sc HI W A s1 s2 p q; case: p; do?[by case|by move=>?; case].
  + by move=>B p p0; case. 
  move=>V K pf p/stepInject; case=>[[?][?][?]|[sc'][t'][s1'][s2'][s][][]????]//. 
  subst sc' q s1 s2=>C; move/HI=>S; apply: (sem_extend pf)=>//.
  apply/(cohE pf); exists s2', s; case: (step_coh S)=>C1 C2; split=>//.
  move/(cohE pf): (C)=>[s1][s2][E]C' H.
  by move: (coh_prec (cohS C) C1 C' E)=>Z; subst s1'; rewrite (joinxK (cohS C) E). 
  by move=>?????; case.   
- move=>W A s1 s2 p q; case: p; do?[by case|by move=>?; case].
  + by move=>???; case.
  + move=>V K i p; case/stepInject=>[[s1'][v][_]??? X|[?][?][?][?][?][?]]//.
    by subst p q s2; apply: Idle; split=>//; case: X=>x []. 
  by move=>?????; case.

- move=>sc HI W A s1 s2 p q; case: p;
           do?[by case|by move=>?; case|by move=>???; case|by move=>????; case].
  move=>pr I ii E p; case/(stepWithInv s1); first by case=>?; case.
  case=>sc'[t'][][]Z1 Z2 _ C1; subst q sc'.
  by move/HI=>T; subst W; apply: with_inv_step. 
move=>W A s1 s2 t q; do?[by case|by move=>?; case|by move=>???; case].
case=>C; case: t=>//pr I ii E; case=>//=v _[s1'][Z1]Z2 Z3.
by subst s1' s2 q; apply: Idle. 
Qed.

(*

[Inductive invariants and stepping]

The following lemma is the crux of wrapping into inductive invariants, as 
it leverages the proof of the fact that each transition preserves the invariant.

*)

Lemma pstep_inv A pr I (ii : InductiveInv pr I) s1 s2 sc
      (t t' : proc this (mkWorld pr) A):
  s1 \In Coh (mkWorld (ProtocolWithIndInv ii)) ->
  pstep s1 t sc s2 t' -> 
  s2 \In Coh (mkWorld (ProtocolWithIndInv ii)).
Proof. by move=>C1; case/pstep_network_sem/(with_inv_step C1)/step_coh. Qed.

End ProcessSemantics.

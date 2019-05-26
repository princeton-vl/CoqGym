From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL
Require Import Actions Injection Process InductiveInv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Here we define Nanevski et al.-style modal predicates for giving
   the meaning to Hoare triples. *)

Section Always.

Variable this : nid.
Variable W : world.

Notation coherent := (Coh W).

Arguments proc [this W].

Fixpoint always_sc A (s1 : state) p scs (P : state -> proc A -> Prop) : Prop :=
  s1 \In coherent /\ 
  if scs is sc :: scs' then 
    forall s2, network_rely W this s1 s2 -> 
      [/\ safe p sc s2, P s2 p &
          forall s3 q, @pstep this W A s2 p sc s3 q -> always_sc s3 q scs' P]
  else forall s2, network_rely W this s1 s2 -> P s2 p.

Definition always A s (p : proc A) P := forall scs, always_sc s p scs P.

(* Some basic properties of the alwas predicate *)

Lemma alw_coh' A s (p : proc A) scs P : 
        always_sc s p scs P -> s \In coherent.
Proof. by case: scs=>/=[|a l]; case. Qed.

Lemma alw_coh A s (p : proc A) P : 
        always s p P -> s \In coherent.
Proof. by move/(_ [::]); move/alw_coh'. Qed.

Lemma alw_safe' A s (p : proc A) sc scs P : 
        always_sc s p (sc :: scs) P -> safe p sc s.
Proof.
by case: scs=>[|a l][]C/(_ s (rely_refl this C))[].
Qed.    

Lemma alw_safe A s (p : proc A) P :
        always s p P -> forall sc, safe p sc s.
Proof. by move=>H sc; apply: alw_safe' (H [:: sc]). Qed.

Lemma alw_refl' A s (p : proc A) sc P : always_sc s p sc P -> P s p.
Proof.
by case: sc=>[|a l][C]/(_ s (rely_refl this C))//; case.
Qed.

Lemma alw_refl A s (p : proc A) P : always s p P -> P s p.
Proof. by move/(_ [::])/alw_refl'. Qed.

Lemma alw_envs' A s1 (p : proc A) scs s2 P : 
        always_sc s1 p scs P -> network_rely W this s1 s2 -> always_sc s2 p scs P.
Proof.
by case: scs=>//[|a l][C]H R; move/rely_coh: (R)=>/=[]H1 H2;
   split=>//s3 R'; apply: H; apply: (rely_trans R).
Qed.
 
Lemma alw_envs A s1 (p : proc A) s2 P :
        always s1 p P -> network_rely W this s1 s2 -> always s2 p P.
Proof. by move=>S E scs; apply: alw_envs' (S scs) E. Qed.

(* Always is preserved by this-stepping *)

Lemma alw_step A s1 (p : proc A) sc s2 q P :
        always s1 p P -> pstep s1 p sc s2 q -> always s2 q P.
Proof.
move=>Ls Ts; move: (Ls [:: sc])=>/= [C].
case/(_ _ (rely_refl this C))=>_ _; move/(_ _ _ Ts)=>_. 
move=>scs; move: (Ls (sc :: scs))=>/= [_].
by case/(_ _ (rely_refl this C))=>_ _; move/(_ _ _ Ts). 
Qed.

(* Relaxing the predicate P wrt. rely *)
Lemma alwp_envsq A s1 (p1 : proc A) scs (P : _ -> _ -> Prop) : 
        always_sc s1 p1 scs P ->
        always_sc s1 p1 scs 
          (fun s2 p2 => forall s3, network_rely W this s2 s3 -> P s3 p2).
Proof.
elim: scs s1 p1=>[|sc scs IH] /= s1 p1 [C H]; split=>// s2 M.
- by move=>s3 /(rely_trans M); apply: H. 
split; first by case: (H _ M).
- by move=>s3 /(rely_trans M) /H; case. 
by move=>s3 q T; apply: IH; case: (H _ M)=>_ _; apply. 
Qed.

Lemma alw_envsq A s1 (p1 : proc A) (P : _ -> _ -> Prop) : 
        always s1 p1 P ->
        always s1 p1 (fun s2 p2 => forall s3, network_rely W this s2 s3 -> P s3 p2).
Proof. by move=>H scs; apply: alwp_envsq (H scs). Qed.


Lemma alw_unfin' A s1 scs (P : state -> proc A -> Prop) :
        s1 \In coherent -> 
        (forall s2, network_rely W this s1 s2 -> P s2 Unfinished) -> 
        always_sc s1 Unfinished scs P.
Proof. 
case: scs=>[|sc scs] C H; split=>// s2 E.
split=>[||s3 q/stepUnfin]//; first by case: sc=>//.
by apply: H.
Qed.

Lemma alw_unfin A s1 (P : state -> proc A -> Prop) :
        s1 \In coherent -> 
        (forall s2, network_rely W this s1 s2 -> P s2 Unfinished) ->
        always s1 Unfinished P.
Proof. by move=>C H scs; apply: alw_unfin'. Qed.

Lemma alw_ret' A s1 (v : A) scs (P : state -> proc A -> Prop) : 
        s1 \In coherent -> 
        (forall s2, network_rely W this s1 s2 -> P s2 (Ret v)) -> 
        always_sc s1 (Ret v) scs P.
Proof. 
case: scs=>[|sc scs] C H; split=>// s2 E.
split; last by [move=>s3 q; move/stepRet].
- by case: sc.
by apply: H E.
Qed.

Lemma alw_ret A s1 (v : A) (P : state -> proc A -> Prop) : 
        s1 \In coherent -> 
        (forall s2, network_rely W this s1 s2 -> P s2 (Ret v)) -> 
        always s1 (Ret v) P.
Proof. by move=>C H ps; apply: alw_ret'. Qed.

Lemma alw_act A s1 (a : action W A this) (P : state -> proc A -> Prop) :
        s1 \In coherent ->
        (forall s2, network_rely W this s1 s2 -> exists S : a_safe a s2,
        P s2 (Act a) /\
        forall s3 v s4, a_step S s3 v -> 
                        network_rely W this s3 s4 -> P s4 (Ret v)) ->
        always s1 (Act a) P. 
Proof.
move=>C H [|sc scs]; split=>// s2; case/H=>// H1[H2]H3//. 
split=>//; first by case: sc.
move=>s3 q /stepAct [v][pf][_ -> St].
rewrite (pf_irr H1 pf) in H3.
apply: alw_ret'; last by move=>s4; apply: H3 St.
by case: (step_coh (a_step_sem St)).
Qed.

(* The predicates, corresponding to weakest postconditions, necessary
   for defining safe executions of programs.  *)

Notation alwsafe_sc s p scs := (always_sc s p scs (fun _ _ => True)).
Notation alwsafe s p := (always s p (fun _ _ => True)).


Lemma alw_imp' A s (p : proc A) scs (P1 P2 : state -> proc A -> Prop) : 
         (forall s p, s \In coherent -> P1 s p -> P2 s p) -> 
         always_sc s p scs P1 -> always_sc s p scs P2.
Proof.
elim: scs s p=>[|sc scs IH] s p /= I; case=>C L; split=>// s2 E.
- by apply: I (L _ E); case/rely_coh: E.
case/L: (E)=>S H T; split=>//; first by apply: I H; case/rely_coh: E. 
by move=>s3 q; move/T; apply: IH I. 
Qed.

Lemma alw_imp A s (p : proc A) (P1 P2 : state -> proc A -> Prop) : 
        (forall s p, s \In coherent -> P1 s p -> P2 s p) -> 
        always s p P1 -> always s p P2.
Proof. by move=>I H ps; apply: alw_imp' I _. Qed.

(* always commutes with universals, so we cann pull them out *)

Lemma alwA' A B s (p : proc A) scs (P : B -> state -> proc A -> Prop) : 
        alwsafe_sc s p scs ->
        (always_sc s p scs (fun s' p' => forall x, P x s' p') <->
         forall x, always_sc s p scs (fun s' p' => P x s' p')).
Proof.
move=>Ls; split=>[{Ls}|]. 
- elim: scs s p=>[|sc scs IH] s p /= [C Et x]; split=>// s2; move/Et=>//.
  by case=>S Ha L; split=>// s3 q; move/L/IH.
elim: scs s p Ls=>[|sc scs IH] s p /= [C Et Ha]; split=>// s2 E.
- by move=>x; case: (Ha x)=>_; apply. 
case/Et: (E)=>/= S _ L; split=>//.
- by move=>x; case: (Ha x)=>_; case/(_ _ E). 
move=>s3 q T; apply: IH; first by apply: L T.
by move=>x; case: (Ha x)=>_; case/(_ _ E)=>_ _; apply. 
Qed.

Lemma alwA A B s (p : proc A) (P : B -> state -> proc A -> Prop) : 
        alwsafe s p ->
        (always s p (fun s' p' => forall x, P x s' p') <->
         forall x, always s p (fun s' p' => P x s' p')).
Proof.
move=>Ls; split.
- by move=>H x ps; move: x; apply/(alwA' _ (Ls ps)).
by move=>H ps; apply/(alwA' _ (Ls ps))=>x; apply: H.
Qed.

Arguments alwA [A B s p P].

(* always commutes with implication, so we can weaken the postconditions *)

Lemma alwI' A s (p : proc A) scs (P : Prop) (Q : state -> proc A -> Prop) : 
        alwsafe s p ->
        (always_sc s p scs (fun s' p' => P -> Q s' p') <->
         (P -> always_sc s p scs (fun s' p' => Q s' p'))).
Proof.
move=>Ls; split.
- elim: scs s p Ls=>[|sc scs IH] s p Ls /= [C Et H]; split=>// s2.
  - by move/Et; apply.
  move=>M; move: (alw_envs Ls M)=>{Ls} Ls.
  case/Et: M=>H1 /(_ H) H2 H3; split=>// s3 q T.
  by apply: IH H; [apply: alw_step T | apply: H3].
elim: scs s p Ls=>[|sc scs IH] s p /= Ls H; 
move: (alw_coh Ls)=>C; split=>// s2 M; first by case/H=>_; apply. 
move: (alw_envs Ls M)=>{Ls} Ls.
split; first by move/alw_safe: Ls.  
- by case/H=>_; case/(_ _  M). 
move=>s3 q T; move: (alw_step Ls T)=>{Ls} Ls.
by apply: IH Ls _; case/H=>_; case/(_ _ M)=>_ _; apply. 
Qed.

Lemma alwI A s (p : proc A) (P : Prop) (Q : state -> proc A -> Prop) : 
        alwsafe s p ->
         always s p (fun s' p' => P -> Q s' p') <->
         (P -> always s p (fun s' p' => Q s' p')). 
Proof.
move=>Ls; split; first by move=>H Hp scs; apply/alwI': Hp.
by move=>H scs; apply/alwI'=>//; move/H; move/(_ scs).
Qed.

Arguments alwI [A s p P Q].


Lemma alw_bnd A B (p1 : proc A) (p12 : proc B) pp2 s1 
                 (P : state -> B -> Prop) :
        p12 \In pcat p1 pp2 -> 
        always s1 p1 (fun s2 p2 =>
          (* p2 is a process resulting from executing p1 *)              
          forall p v, p2 = Ret v -> p \In pp2 v -> 
           (* Now assume p2 is a return and p is its continuation, 
              so we proceed until we reach the return *)
           always s2 p (fun s q => forall v, q = Ret v -> P s v)) ->
        always s1 p12 (fun s p => forall v, p = Ret v -> P s v).
Proof.
move=>Tc Ls scs.
elim: scs s1 p1 p12 Tc Ls=>[|sc scs IH] s1 p1 p12 Tc Ls /=.
- by split=>[|s2]; [apply: alw_coh Ls | case: Tc=>k [->]].
split=>[|s2 E]; first by apply: alw_coh Ls.
case: Tc IH=>k [->{p12}] H IH.
split=>//; last first.
- move=>s3 q T; case/stepSeq: T Ls.
  - case=>v [_ ->->-> C]; move/alw_refl/(_ _ _ (erefl _)). 
    by move/(_ _ (H v))/alw_envs; apply. 
  case=>sc' [p'][_ ->{q}] T; move/alw_envs/(_ E)/alw_step.
  by move/(_ _ _ _ T)/IH; apply; exists k.
move/(alw_envs Ls): E=>{Ls} Ls. 
have Ls': always s2 p1 (fun s2 p2 =>
  forall sc p v, p2 = Ret v -> p \In pp2 v -> safe p sc s2).
- by apply: alw_imp Ls=>s p _ I sc' q v E; move/(I _ _ E)/alw_safe. 
case: sc=>//=; first by case: p1 {Ls} Ls'.
move=>sc; case: (Ls [:: sc])=>C.
by move/(_ _ (rely_refl this C)); case.
Qed.

Lemma alwsafe_bnd A B (p1 : proc A) (p12 : proc B) s1 pp2 :
        p12 \In pcat p1 pp2 ->
        always s1 p1 (fun s2 p2 =>
          forall p v, p2 = Ret v -> p \In pp2 v -> alwsafe s2 p) ->
        alwsafe s1 p12.
Proof.
move=>T Ls.
suff H: always s1 p12 (fun s p => forall v, p = Ret v -> True).
- by apply: alw_imp H.
apply: alw_bnd T _; apply: alw_imp Ls=>s p _ I q v H.
by move/(I _ _ H); apply: alw_imp.
Qed.

(* this suggest capturing the pattern by means of a new definition *)

Definition after A s (p : proc A) (P : A -> state -> Prop) := 
  always s p (fun s2 p2 => forall v, p2 = Ret v -> P v s2).

Lemma aft_bnd A B (p1 : proc A) (p12 : proc B) pp2 s1 P :
        p12 \In pcat p1 pp2 -> 
        after s1 p1 (fun v s => 
          forall p, p \In pp2 v -> after s p P) ->
        after s1 p12 P.
Proof. 
move=>T H; apply: alw_bnd T _.
by apply: alw_imp H=>s p _ I q v E; move/(I v E).
Qed.



Lemma aftI A s (p : proc A) (P : Prop) (Q : A -> state -> Prop) : 
        alwsafe s p ->
         after s p (fun v s' => P -> Q v s') <->
         (P -> after s p (fun v s' => Q v s')).
Proof.
move=>Ls; rewrite -(alwI Ls).
split; apply: alw_imp=>t q _ I.
- by move=>Hp v; move/I; apply. 
by move=>v; move/I. 
Qed.

Lemma aft_alwsf A s (p : proc A) :
        alwsafe s p <-> after s p (fun v s => True).
Proof. by split; apply: alw_imp. Qed.

Lemma aft_imp A s (p : proc A) (P1 P2 : A -> state -> Prop) : 
        (forall v s, s \In coherent -> 
                     P1 v s -> P2 v s) -> 
        after s p P1 -> after s p P2.
Proof. by move=>I; apply: alw_imp=>s1 p1 C H v; move/H; apply: I. Qed.

Lemma aftA A B s (p : proc A) (P : B -> A -> state -> Prop) : 
        alwsafe s p ->
        (after s p (fun v s' => forall x, P x v s') <->
         forall x, after s p (fun v s' => P x v s')).
Proof.
move=>Ls; rewrite -(alwA Ls).
split; apply: alw_imp=>t q _ I.
- by move=>x v; move/I.
by move=>v; move/I.
Qed.

Arguments aftA [A B s p P].
Arguments aftI [A s p P Q].

End Always.

Section AlwaysInject.
Variables (V W : world) (K : hooks) (A : Type) (w : injects V W K) (this: nid).
Notation W2 := (inj_ext w).

Lemma rely_ext i j s : 
        i \In Coh V -> 
        network_rely W this (i \+ j) s ->  
        exists i' j', s = i' \+ j' /\ i' \In Coh V.
Proof.
move=>C M; case: (rely_coh M)=>_; rewrite (cohE w).
by case=>[s1][s2][->] Cs1 _; exists s1, s2. 
Qed.

Lemma rely_split' z s1 s1' s2 s2' : 
  s1 \In Coh V -> s2 \In Coh V ->
  network_step W z (s1 \+ s1') (s2 \+ s2') ->
  network_step V z s1 s2 /\ network_step (inj_ext w) z s1' s2'.
Proof.
move=>C1 C2 N.
case: (sem_split w C1 C2 N); case=>R E; [subst s2'|subst s2];
split=>//; apply: Idle; split=>//.
case: (step_coh N)=>C _.
case/(cohE w): (C)=>s3[s4][E]C' C''.
move: (coh_prec (cohS C) C1 C' E)=>Z; subst s3.
by rewrite (joinxK (cohS C) E).
Qed.

Lemma rely_split s1 s1' s2 s2' : 
  s1 \In Coh V -> s2 \In Coh V ->
  network_rely W this (s1 \+ s1') (s2 \+ s2') ->
  network_rely V this s1 s2 /\ network_rely (inj_ext w) this s1' s2'.
Proof.
move=>C1 C2 [n E].
elim: n s1 s1' E C1 C2=>[|n IH] /= s1 s1'; last first.
- move=>[z][s3][N]H1 H2 C1 C2.
  case: (step_coh H1)=>D1 D2; move/(cohE w): D2=>[s4][s5][Z]C3 C4.
  subst s3; case: (IH s4 s5 H2 C3 C2)=>G1 G2.
  case: (rely_split' C1 _ H1)=>//H3 H4; split=>//.
  + by case: G1=>m R; exists m.+1, z, s4. 
  by case: G2=>m R; exists m.+1, z, s5. 
move=> [E1 E2] C1 C2.
move: (coh_prec (cohS E2) C1 C2 E1)=>Z; subst s2.
rewrite (joinxK (cohS E2) E1); split; exists 0=>//. 
split=>//; rewrite -(joinxK (cohS E2) E1)=>{E1 s2' C2}.
move/(cohE w): (E2)=>[t1][t2][E]C' C''.
move: ((coh_prec (cohS E2)) C1 C' E)=>Z; subst t1.
by rewrite (joinxK (cohS E2) E).
Qed.




Lemma alw_inject (p : proc this V A)
      (P : state -> proc this V A -> Prop) i j :
        i \+ j \In Coh W ->
        always i p P ->
        always (i \+ j) (Inject w p)
          (fun m q => exists i' j', 
             [/\ m = i' \+ j', i' \In Coh V, network_rely W2 this j j' &
                 (exists q', q = Inject w q' /\ P i' q') \/
                 (exists v', q = Ret v' /\ P i' (Ret v'))]).
Proof.
move=>C Ls scs; elim: scs i j p C Ls=>[|sc scs IH] i j p C Ls /=; 
split=>// {C} s M; move: (alw_coh Ls) (proj2 (rely_coh M))=>Ci C;
case/(rely_ext Ci): M C (M)=>i1 [j1][->{s}] Ci1 C;
case/(rely_split Ci Ci1)=> /(alw_envs Ls) {Ls} Ls S1.
- by exists i1, j1; split=>//; left; exists p; move/alw_refl: Ls.
split.
- case: sc=>//; last by case: p Ls=>// v; exists i1, j1.
  by move=>sc; move: (alw_safe Ls sc)=>Sf; exists i1; split=>//; exists j1.
- by exists i1, j1; split=>//; left; exists p; move/alw_refl: Ls.
move=>s q; rewrite stepInject => H.
case: H Ls.
- case=>_ [v][_ ->->->{p q s} _] Ls;  apply: alw_ret'=>// s M.
  case/(rely_ext Ci1): M (M)=>i2 [j2][->{s}] Ci2.
  case/(rely_split Ci1 Ci2)=> /(alw_envs Ls) {Ls} Ls S2.
  exists i2, j2; split=>//; first by apply: rely_trans S1 S2.
  by right;  exists v; move/alw_refl: Ls.
case=>sc' [q'][x1][i2][y1][_ -> E -> {sc q s}] _ T Ls.

have [E1 E2] : x1 = i1 /\ y1 = j1.
- case: T=>Cx1 _.
  move: (coh_prec (cohS C) Ci1 Cx1 E) (E)=><-{E Cx1 x1}.
  by move/(joinxK (cohS C)).
rewrite {E x1}E1 {y1}E2 in T *.
have C' : i2 \+ j1 \In Coh W.
- move: (C)=>C'; rewrite (cohE w) in C *=>[[s1]][s2][E]D1 D2.
  move: (coh_prec (cohS C') Ci1 D1 E)=>Z; subst i1.
  move: (joinxK (cohS C') E)=>Z; subst s2; clear E.
  apply/(cohE w); exists i2, j1; split=>//.
  by case/step_coh: (pstep_network_sem T). 
move/(alw_step Ls): T=>{Ls} Ls.
apply: alw_imp' (IH _ _ _ C' Ls)=>{IH Ls C' C Ci Ci1 i i1 i2 p q' sc' scs}.
move=>s p _ [i2][j2][->{s}] Ci2 S2 H; exists i2, j2; split=>//.
by apply: rely_trans S1 S2.  
Qed.

Lemma aft_inject (p : proc this V A) (P : A -> state -> Prop) i j :
        i \+ j \In Coh W ->
        after i p P ->
        after (i \+ j) (Inject w p)
          (fun v m => exists i' j', 
             [/\ m = i' \+ j', i' \In Coh V, 
                 network_rely W2 this j j' & P v i']).
Proof.
move=>C /(alw_inject C); apply: alw_imp=>{p i C} s q _.
case=>i1 [j1][->{s} Ci1 S1] H v E.
move: E H=>-> [[q'][//]|[_][[<-]] H].
by exists i1, j1; split=>//; apply: H. 
Qed.


End AlwaysInject.

Notation alwsafe_sc s p scs := (always_sc s p scs (fun _ _ => True)).
Notation alwsafe s p := (always s p (fun _ _ => True)).

Module AlwaysInductiveInv.
Section AlwaysInductiveInv.
Import InductiveInv.
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

Lemma alw_ind_inv (p : proc this V A)
      (P : state -> proc this V A -> Prop) i :
        i \In Coh W ->
        always i p P ->
        always i (WithInv pr I ii (erefl _) p)
          (fun m q => m \In Coh W /\
                 ((exists q', q = WithInv pr I ii (erefl _) q' /\ P m q') \/
                  (exists v', q = Ret v' /\ P m (Ret v')))).
Proof.
move=>C Ls scs; elim: scs i p C Ls=>[|sc scs IH] i p C Ls /=;
split=>//{C}s M; move: (alw_coh Ls) (proj2 (rely_coh M))=>Ci C.
- split; first by case:(rely_coh M)=>_/with_inv_coh.
  left; exists p; split=>//; apply: alw_refl.
  by move/with_inv_rely': M; apply: (alw_envs). 
split.
- case: sc=>//; last by case: p Ls=>//.
  move=>sc; move: (alw_safe Ls sc)=>Sf.
  by move/with_inv_rely': M; move/(alw_envs Ls)=>H; apply: (alw_safe H).
- split=>//; left; exists p; split=>//.
  by move/with_inv_rely': M; move/(alw_envs Ls)=>H; apply: alw_refl.
move=>s' q/stepWithInv=>H; case: H Ls.
- case=>[v][Z1]Z2 Z3 Z4 _ _ Ls; subst s' p q sc. apply: alw_ret'=>//=s' M'.
  split; first by case/rely_coh: M'.
  right; exists v; split=>//.
  by move: (rely_trans M M')=>/with_inv_rely'/(alw_envs Ls)/alw_refl.
case=>sc'[q'][Z1]Z2 _ _ T Ls; subst q sc.
have X: s' \In Coh W by apply: (pstep_inv (proj2 (rely_coh M)) T).
move/with_inv_rely': (M)=>/(alw_envs Ls)=>Ls'.
move/(alw_step Ls'): T=>{Ls'} Ls'.
by apply: IH.
Qed.

Lemma aft_ind_inv (p : proc this V A) (P : A -> state -> Prop) i :
        i \In Coh W ->
        after i p P ->
        after i (WithInv pr I ii (erefl _) p)
          (fun v m => m \In Coh W /\ P v m).
Proof.
move=>C /(alw_ind_inv C); apply: alw_imp=>{p i C} s q _.
case=>C H; split=>//; subst q.
case:H; first by move=>[?]; case. 
by case=>v'[][]<-{v'}/(_ v (erefl _)). 
Qed.

End AlwaysInductiveInv.
End AlwaysInductiveInv.

Export AlwaysInductiveInv.

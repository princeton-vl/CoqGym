From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL
Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL
Require Import InductiveInv While.
From DiSeL
Require Import CalculatorProtocol CalculatorInvariant.
From DiSeL
Require Import CalculatorClientLib CalculatorServerLib.

Export CalculatorProtocol.

Section CalculatorServers.

Variable l : Label.
Variable f : input -> option nat.
Variable prec : input -> bool.
Variables (cs cls : seq nid).
Notation nodes := (cs ++ cls).
Hypothesis Huniq : uniq nodes.

Notation cal := (CalculatorProtocol f prec cs cls l).
Notation sts := (snd_trans cal).
Notation rts := (rcv_trans cal).
Notation W := (mkWorld cal).

(* A server node *)
Variable sv : nid.
Hypothesis  Hs : sv \in cs.
Notation loc i := (getLocal sv (getStatelet i l)).

Section CalculatorServerLoop.

(************************************************)
(******    Generic server loop combinator   *****)
(************************************************)

(*
- Actually, this is _higher-order_ programming
- The loop runs infinitely
- It takes an additional generic state argument (useful for memoization),
  which should be constrained appropriately
*)

Variable Sstate : Type.
(* Making sure that the state is okay *)
Variable state_wf : Pred Sstate.

(* Initial well-formed state, which is well-formed *)
Variable state0 : Sstate.
Hypothesis state0_wf : state_wf state0. 

(** The server body always cleans up after itself (no outstanding
requests left to be processed) and correctly handles the state, passed
between iterations. *)

Definition server_loop_body_spec (s : Sstate) :=
  DHT [sv, W]
  (fun i => loc i = st :-> ([::]:reqs) /\ state_wf s,                    
   fun (r : Sstate) m =>
     [/\ loc m = st :-> ([::]:reqs) & state_wf r]).

(* The body to be passed to the loop *)
Variable server_body : forall s, server_loop_body_spec s.

Definition server_loop_cond (res : Sstate) := true.

Definition server_loop_inv :=
  fun (_ r : Sstate) i => loc i = st :-> ([::]:reqs) /\ state_wf r.

Program Definition server_loop :
  DHT [sv, W]
  (fun i => loc i = st :-> ([::]:reqs),
   fun (r : Sstate) m => False) :=
  Do _ (@while sv W _ _ server_loop_cond server_loop_inv _
        (fun r => Do _ (server_body r))) state0.

Next Obligation. by apply: with_spec (x x0). Defined.
Next Obligation.
by move:H; rewrite /server_loop_inv (rely_loc' _ H0).
Qed.
Next Obligation. by apply: with_spec x. Defined.
Next Obligation.
by apply: ghC=>i1 s[H1 H2] C1/=; apply: call_rule.
Qed.
Next Obligation.
move=>i/=E1; apply: call_rule'=>//.
- by move=>C1; exists state0=>//. 
by move=>s' m/(_ s')/=; case.
Qed.    
    
End CalculatorServerLoop.
End CalculatorServers.


(*************************************************)
(*      Specific server implementations          *)
(*************************************************)


(***** One-shot (per iteration) server *****)

Module OneShotServer.
Section OneShotServer.

Variable l : Label.
Variable f : input -> option nat.
Variable prec : input -> bool.
Hypothesis prec_valid :
  forall i, prec i -> exists v, f i = Some v.
Variables (cs cls : seq nid).
Notation nodes := (cs ++ cls).
Hypothesis Huniq : uniq nodes.

Notation cal := (CalculatorProtocol f prec cs cls l).
Notation sts := (snd_trans cal).
Notation rts := (rcv_trans cal).
Notation W := (mkWorld cal).

(* A server node *)
Variable sv : nid.
Hypothesis  Hs : sv \in cs.
Notation loc i := (getLocal sv (getStatelet i l)).

(* Server-specific infrastructure *)
Notation Sstate := unit.
Definition state_wf := fun _ : unit => True.
Definition state0 := tt.
Lemma state0_wf : state_wf state0. Proof. done. Qed.

Program Definition one_shot_body : forall _ : unit,
  server_loop_body_spec l f prec cs cls sv _ state_wf state0 :=
  fun _ =>
  Do _ (
    r <-- blocking_receive_req l f prec cs cls _ Hs;
    let: (from, args) := r in
    (* Compute the answer function explicitly *)
    let r := if f args is Some v then v else 0 in
    send_answer l f prec cs cls _ Hs from args r;;
    ret _ _ tt).
Next Obligation.
move=>i1/=[L1]_; apply: step; apply: (gh_ex (g:=[::])).
apply: call_rule=>//[[from args]] i2/=[L2]H1 H2 C2.
case: (prec_valid _ H2)=>ans F.
move: (erefl (f args))=>e.
have X: (match f args as anonymous' return (anonymous' = f args -> nat) with
           | Some v => fun _ : Some v = f args => v
           | None => fun _ : None = f args => 0
         end e) = ans by move: e; rewrite F.
rewrite X=>{X}; apply: step; apply: (gh_ex (g:=[:: (from, sv, args)])).
apply: call_rule=>//; first by move=>_; split=>//; rewrite inE eqxx.
move=>x i3/=; rewrite eqxx=> L3 C3. 
apply: ret_rule=>i4 R3 _; split=>//.
by rewrite (rely_loc' _ R3); case: L3.
Qed.

Definition one_shot_server :=
  server_loop _ _ _ _ _ _ _ _ _ state0_wf one_shot_body.

End OneShotServer.
End OneShotServer.

(***** Batching (per iteration) server *****)

Module BatchingServer.
Section BatchingServer.

Variable l : Label.
Variable f : input -> option nat.
Variable prec : input -> bool.
Hypothesis prec_valid :
  forall i, prec i -> exists v, f i = Some v.
Variables (cs cls : seq nid).
Notation nodes := (cs ++ cls).
Hypothesis Huniq : uniq nodes.

Notation cal := (CalculatorProtocol f prec cs cls l).
Notation sts := (snd_trans cal).
Notation rts := (rcv_trans cal).
Notation W := (mkWorld cal).

(* A server node *)
Variable sv : nid.
Hypothesis  Hs : sv \in cs.
Notation loc i := (getLocal sv (getStatelet i l)).

(* Server-specific infrastructure *)
Notation Sstate := unit.
Definition state_wf := fun _ : unit => True.
Definition state0 := tt.
Lemma state0_wf : state_wf state0. Proof. done. Qed.

(* Batch size *)
Variable bsize : nat.


Definition batch_recv_loop_spec := forall (nsa : nat * Sstate * reqs),
  DHT [sv, W]
  (fun i => let: (n, s, acc) := nsa in
            [/\ loc i = st :-> acc,
             size acc + n = bsize,
             (forall e, e \in acc ->
              [/\ e.1.1 \in cls, e.1.2 = sv & prec e.2]) &
             state_wf s],
   fun (r : (reqs * Sstate)) m =>
     [/\ loc m = st :-> r.1,
      size r.1 = bsize,
      (forall e, e \in r.1 ->
              [/\ e.1.1 \in cls, e.1.2 = sv & prec e.2]) &
      state_wf r.2]).

Program Definition receive_req_loop s :
  DHT [sv, W] 
  (fun i => loc i = st :-> ([::]:reqs) /\ state_wf s,                    
   fun (r : (reqs * Sstate)) m =>
     [/\ loc m = st :-> r.1,
      size r.1 = bsize,
      (forall e, e \in r.1 -> [/\ e.1.1 \in cls, e.1.2 = sv & prec e.2]) &
      state_wf r.2]) :=
  Do (ffix (fun (rec : batch_recv_loop_spec) nsa =>
    Do _ (let: (n, s, acc) := nsa in
          if n is n'.+1
          then r <-- blocking_receive_req l f prec cs cls _ Hs;
               let: (from, args) := r in
               let: acc' := (from, sv, args) :: acc in  
               rec (n', s, acc') 
          else ret _ _ (acc, s))) (bsize, tt, [::])). 

Next Obligation.
move=>i1/=[L1]S P _; case: n S=>//[|n]S.
- by apply: ret_rule=>i2 R1/=; rewrite (rely_loc' _ R1) addn0.
apply: step; apply: (gh_ex (g:=r)).
apply: call_rule=>//[[from args]]i2/=[L2]H1 H2 C2.
apply: call_rule=>// _; split=>//; first by rewrite addSnnS.
move=>e; rewrite inE=>/orP; case; last by apply: P.
by move/eqP=>Z; subst e. 
Qed.

Next Obligation.
by move=>i1/=[L1]_; apply: call_rule.
Qed.

(* Send batch responses *)

Definition batch_send_loop_spec := forall (acc : reqs),
  DHT [sv, W]
  (fun i => [/\ loc i = st :-> acc &
             (forall e, e \in acc -> [/\ e.1.1 \in cls, e.1.2 = sv & prec e.2])],
   fun (r : Sstate) m =>
     [/\ loc m = st :-> ([::]:reqs) & state_wf r]).


Program Definition send_ans_loop (acc : reqs) :
  DHT [sv, W] 
    (fun i => loc i = st :-> acc /\
              (forall e, e \in acc -> [/\ e.1.1 \in cls, e.1.2 = sv & prec e.2]),
   fun (r : Sstate) m =>
     [/\ loc m = st :-> ([::]:reqs) & state_wf r]) :=
  ffix (fun (rec : batch_send_loop_spec) acc =>
    Do _ (if acc is (from, _, args) :: acc'
          then let r := if f args is Some v then v else 0 in
               send_answer l f prec cs cls _ Hs from args r;;
               rec acc' 
          else ret _ _ tt)) acc. 

Next Obligation.
move=>i1/=[L1]P1; case: acc L1 P1=>[|[[from b]]args acc] L1 P1.
- by apply: ret_rule=>i2 R1[H1]_; rewrite (rely_loc' _ R1).
  apply: step.
move: (P1 (from, b, args)).
rewrite inE eqxx/==>/(_ is_true_true)[X1]Z /prec_valid [v]F; subst b.
move: (erefl (f args))=>e.
have X: (match f args as anonymous' return (anonymous' = f args -> nat) with
           | Some v => fun _ : Some v = f args => v
           | None => fun _ : None = f args => 0
         end e) = v by move: e; rewrite F.
rewrite X=>{X e}.
apply: (gh_ex (g:=((from, sv, args) :: acc))).
apply: call_rule; first by move=>_; split=>//; rewrite inE eqxx.
move=>x i2/= [L2 H2] C2; apply: call_rule=>//_.
rewrite eqxx in L2; split=>//e A; apply: P1.
by rewrite inE A orbC.
Qed.

(* Main batching server *)

Program Definition batched_body : forall _ : unit,
  server_loop_body_spec l f prec cs cls sv _ state_wf state0 :=
  fun _ => Do _ (
     sr <-- receive_req_loop tt;
     send_ans_loop sr.1).
Next Obligation.
move=>i1/=[L1]_; apply: step.
apply: call_rule=>//[[acc _]]/= i2[L2 H2]P2 _ C2.
by apply: call_rule.
Qed.

Definition batched_server :=
  server_loop _ _ _ _ _ _ _ _ _ state0_wf batched_body.

End BatchingServer.
End BatchingServer.


(***** Memoizing Server *****)

Module MemoizingServer.
Section MemoizingServer.

Variable l : Label.
Variable f : input -> option nat.
Variable prec : input -> bool.
Hypothesis prec_valid :
  forall i, prec i -> exists v, f i = Some v.
Variables (cs cls : seq nid).
Notation nodes := (cs ++ cls).
Hypothesis Huniq : uniq nodes.

Notation cal := (CalculatorProtocol f prec cs cls l).
Notation sts := (snd_trans cal).
Notation rts := (rcv_trans cal).
Notation W := (mkWorld cal).
Variable sv : nid.
Hypothesis  Hs : sv \in cs.
Notation loc i := (getLocal sv (getStatelet i l)).

(* Server-specific infrastructure *)
Notation Sstate := (seq ((seq nat) * nat)).
Definition state_wf (s : Sstate) :=
  forall e, e \in s -> f e.1 = Some e.2.
Definition state0 : Sstate := [::].
Lemma state0_wf : state_wf state0. Proof. by []. Qed.

(* Lookup tables *)
Definition update_mem_table (s : Sstate) args v :=
  (args, v) :: s.

Fixpoint lookup_mem_table (s : Sstate) args : option nat :=
  match s with
  | x :: xs => if x.1 == args
               then Some x.2
               else lookup_mem_table xs args 
  | [::] => None
  end.

Lemma lookup_valid' s args :
  state_wf s ->
  forall v, lookup_mem_table s args = Some v ->
  f args = Some v.
Proof.
elim:s=>//[[args' v']]s Hi H1 v/=.
case: ifP=>X.
- move/eqP: X=>X;subst args'; case=>Z; subst v'.
  by move:(H1 (args, v)); rewrite inE eqxx/==>/(_ is_true_true).
suff Y: state_wf s by apply: Hi.
by move=>e H; move: (H1 e); rewrite inE H orbC/==>/(_ is_true_true).
Qed.

Lemma lookup_valid s args :
  state_wf s ->
  if lookup_mem_table s args is Some v
  then f args = Some v else True.
Proof.
move/(lookup_valid' s args).
by case: (lookup_mem_table s args)=>//v H; apply: (H v).
Qed.

Program Definition memoized_body : forall s : Sstate,
  server_loop_body_spec l f prec cs cls sv _ state_wf s :=
  fun s =>
  Do _ (
    r <-- blocking_receive_req l f prec cs cls _ Hs;
    let: (from, args) := r in
    (* First, try to look up the result in the memtable *)  
    if lookup_mem_table s args is Some v
    then send_answer l f prec cs cls _ Hs from args v;;
         ret _ _ s
    else (* Compute the answer function explicitly *)
      let r := if f args is Some v then v else 0 in
      let s' := update_mem_table s args r in
      send_answer l f prec cs cls _ Hs from args r;;
      ret _ _ s').
Next Obligation.
move=>i1/=[L1]Hw; apply: step; apply: (gh_ex (g:=[::])).
apply: call_rule=>//[[from args]] i2/=[L2]H1 H2 C2.
move: (lookup_valid s args Hw).
- case: (lookup_mem_table s args)=>[v F|_].
  apply: step; apply: (gh_ex (g:=[:: (from, sv, args)])).
  apply: call_rule=>//; first by move=>_; split=>//; rewrite inE eqxx.
  move=>x i3/=; rewrite eqxx=> L3 C3. 
  apply: ret_rule=>i4 R3 _; split=>//.
  by rewrite (rely_loc' _ R3); case: L3.
case: (prec_valid _ H2)=>ans F.
move: (erefl (f args))=>e.
have X: (match f args as anonymous' return (anonymous' = f args -> nat) with
           | Some v => fun _ : Some v = f args => v
           | None => fun _ : None = f args => 0
         end e) = ans by move: e; rewrite F.
rewrite X=>{X}; apply: step; apply: (gh_ex (g:=[:: (from, sv, args)])).
apply: call_rule=>//; first by move=>_; split=>//; rewrite inE eqxx.
move=>x i3/=; rewrite eqxx=> L3 C3. 
apply: ret_rule=>i4 R3 _; split; first by rewrite (rely_loc' _ R3); case: L3.
move=>z; rewrite/update_mem_table inE/==>/orP.
case; last by move/Hw.
by move/eqP=>->.
Qed.  

Definition memoizing_server :=
  server_loop _ _ _ _ _ _ _ _ _ state0_wf memoized_body.

End MemoizingServer.
End MemoizingServer.


(************************************)
(**             Exports             *)
(************************************)

Export OneShotServer.
Export BatchingServer.
Export MemoizingServer.

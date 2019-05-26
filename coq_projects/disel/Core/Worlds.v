From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX Protocols.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module WorldGetters.
Section WorldGetters.

(* It's okay to have duplicating nodes in this list *)

(* World is a dependent partial map of protocols *)

Definition context := union_map Label protocol.

(* 
The hooks are dependencies between:

1. a hook's unique id
2. a core protocol
3. a client protocol
4. a send-transition (represented by its tag) of a client protocol

*)
Definition hook_domain := [ordType of ((nat * Label) * (Label * nat))%type].

(*

A hook is a constraint from the local state wrt. core protocol (1st
heap argument), relating the local state wrt. the client protocol (2ns
heap argument), message to be sent, and the destination node id.

*)
Definition hook_type := heap -> heap -> seq nat -> nid -> Prop.

Definition hooks := union_map hook_domain hook_type.
Definition world := (context * hooks)%type.

Definition getc (w: world) : context := fst w.
Coercion getc : world >-> context.

Definition geth (w: world) : hooks := snd w.
Coercion geth : world >-> hooks.

Variable w : world.

Variables (p : protocol).

(* The function is, in fact, partially defined and returns Empty
   Protocol for a non-present label. *)
Definition getProtocol i : protocol:=
  match find i (getc w) with
  | Some p => p
  | None => EmptyProt i 
  end.

End WorldGetters.
End WorldGetters.

Export WorldGetters.

(* Defining coherence of a state with respect to the world *)

Module Worlds.

Module Core.
Section Core.

(* The following definition ties together worlds and states *)

Definition hooks_consistent (c : context) (h : hooks) : Prop :=
  forall z lc ls t, ((z, lc), (ls, t)) \in dom h ->
  (lc \in dom c) && (ls \in dom c).

Definition hook_complete w := hooks_consistent (getc w) (geth w).

Lemma hook_complete0 c : hook_complete (c, Unit).
Proof. by move=>????; rewrite dom0. Qed.

Definition Coh (w : world) : Pred state := fun s =>
  let: c := fst w in
  let: h := snd w in                                           
  [/\ valid w, valid s, hook_complete w,
      dom c =i dom s &
      forall l, coh (getProtocol w l) (getStatelet s l)].

Lemma cohW w s : Coh w s -> valid w.
Proof. by case w=>[c h]; case. Qed.

Lemma cohS w s : Coh w s -> valid s.
Proof. by case w=>[c h]; case. Qed.

Lemma cohH w s : Coh w s -> hook_complete w.
Proof. by case w=>[c h]; case. Qed.

Lemma cohD w s : Coh w s -> dom (getc w) =i dom s.
Proof. by case w=>[c h]; case. Qed.

Lemma coh_coh w s l : Coh w s -> coh (getProtocol w l) (getStatelet s l).
Proof. by case w=>[c h]; case. Qed.

(* Now we need to establish a bunch of natural properties with respect
   to coherence of worlds and states. *)

Lemma unit_coh w s :
  Coh w s -> w = Unit <-> s = Unit.
Proof.
case: (w)=>[c h].
case=>V V' Hc E H; split.
case=>Z1 Z2; subst c h; rewrite dom0 in E; last by rewrite (dom0E V').
move=>Z; subst s; move/andP: V=>/=[V1 V2].
have Z: c = Unit by apply: (dom0E V1); move=>z; rewrite E dom0.
subst c; suff Z: (h = Unit) by subst h.
simpl in Hc; clear E H V1 V'.
apply: (dom0E V2); move=> x; case X: (x \in dom h)=>//.
by move: x X=>[[z lc] [ls t]]/Hc/andP[]; rewrite !dom0. 
Qed.

Lemma Coh0 (w : world) (s : state) :
  w = Unit -> s = Unit -> Coh w s.
Proof.
move=>->->{w s}; split; rewrite ?dom0=>//=; last first.
- by move=>l; rewrite /getProtocol /getStatelet !find0E.
by move=>z lc ls t; rewrite dom0.  
Qed.

Lemma CohUn (w1 w2 : world) (s1 s2 : state) :
  Coh w1 s1 -> Coh w2 s2 ->
  valid (w1 \+ w2) -> Coh (w1 \+ w2) (s1 \+ s2).
Proof.
case: w1=>[c1 h1]; case: w2=>[c2 h2]; move=>C1 C2 V.
case: (C1)=>_ G1 K1 J1 H1; case: (C2)=>_ G2 K2 J2 H2.
case/andP: V=>V V'; simpl in V, V'.
have X: valid (s1 \+ s2).
- case: validUn=>//; [by rewrite G1|by rewrite G2|move=>l; rewrite -J1 -J2=>D1 D2].
  by case: validUn V=>//=V1 V2; move/(_ _ D1); rewrite D2.
have Y: dom (c1 \+ c2) =i dom (s1 \+ s2).
- by move=>z; rewrite !domUn !inE/=;rewrite V X/= J1 J2.
have Z1:  valid ((c1, h1) \+ (c2, h2)) by rewrite /valid/= V V'.
split=>//[|l]; last first.
- rewrite /getProtocol /getStatelet.
  case: (dom_find l (s1 \+ s2))=>[|v]Z.
  - by move/find_none: (Z); rewrite -Y; case: dom_find=>//->_; rewrite Z.
  move/find_some: (Z)=>D; rewrite Z; rewrite -Y in D=> E.
  case: dom_find D=>// p Z' _ _; rewrite Z'.
  rewrite findUnL // in Z; rewrite findUnL // J1 in Z'.
  by case: ifP Z Z'=>_ F1 F2; [move: (H1 l)|move: (H2 l)];
     rewrite /getProtocol /getStatelet F1 F2.
by move=>z lc ls t/=; rewrite domUn inE=>/andP[_]/orP[];[move/K1|move/K2];
   move/andP=>[A1 A2]; rewrite !domUn !inE A1 A2 V -?(orbC true). 
Qed.

(* Coherence is trivially precise wrt. statelets *)
Lemma coh_prec w: precise (Coh w).
Proof.
move=>s1 s2 t1 t2 V C1 C2.
case: C1 => H1 G1 K1 D1 _.
case: C2 => H2 G2 K2 D2 _ H.
by apply: (@dom_prec _ _ _  s1 s2 t1 t2)=>//z; rewrite -D1 -D2.
Qed.

Lemma locE i n k x y :
  k \in dom i -> valid i -> valid (dstate (getStatelet i k)) ->
  getLocal n (getStatelet (upd k
       {| dstate := upd n x (dstate (getStatelet i k));
          dsoup := y |} i) k) = x.
Proof.
move=>D V; rewrite /getStatelet; case:dom_find (D) =>//d->_ _.
by rewrite findU eqxx/= V /getLocal/= findU eqxx/==>->.
Qed.

Lemma locE' d n x y :
  valid (dstate d) ->
  getLocal n {| dstate := upd n x (dstate d);
                dsoup := y |} = x.
Proof. by move=>V; rewrite /getLocal findU eqxx/= V. Qed.

Lemma locU n n' x st s :
  n != n' ->
  valid st ->
  getLocal n {| dstate := upd n' x st; dsoup := s |} =
  getLocal n {| dstate := st; dsoup := s |}.
Proof.
  move=> /negbTE N V.
  by rewrite /getLocal findU/= N.
Qed.


Section MakeWorld.

Variable p : protocol.
Notation l := (plab p).

Definition mkWorld : world := (l \\-> p, Unit).

Lemma prEq : (getProtocol mkWorld l) = p.
Proof. by rewrite /getProtocol findPt. Qed.
                          
(*

Here's an incomplete list of procedures and facts, which might be
useful eventually:

- Define getters for particular transitions of worlds;

 *)

End MakeWorld.

(* TODO: try_recv should be restricted by a set of labels and a set of
   protocols *)
End Core.
End Core.

End Worlds.

Export Worlds.Core.

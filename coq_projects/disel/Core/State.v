From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness DepMaps EqTypeX.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Shared state, as implemented by the message soup.

   At this point, the implementation is based on top of standard union
   maps. This defines the procedure for allocating new messages: just
   by taking the next-to-the largest id in the corresponding
   batch. Indeed, this is not particularly nice, as it assumes the
   _global_ message soup.

   It's not clear at this moment, what will be the best representation
   of the soup so it would be in the same time _local_ and also would
   allow for th allocation. Perhaps, we should just consider local
   soups, ensuring that they all carry distinct labels, and then when
   cojoin them, make sure that for clashing message id's protocol
   labels are different.

 *)

Section TaggedMessages. 

  Structure TaggedMessage :=
    TMsg {
        tag: nat;
        (* Okay, this is a big omissin, but for now I'm sick and tired
           to deal with casts everywhere, so for the moment the
           contents of the messages are going to be just sequences of
           natural number, and it's up to the client-supplied
           coherence predicate to restrict them appropriately, relating this thing to tags *)
        tms_cont :> seq nat          
      }.

End TaggedMessages.

Section Shared.

  Definition Label := [ordType of nat].

  (* (Heterogenious) messages are parametrized by

     - lab   - protocol Label
     - ptype - protocol, defining the content type
     - content  - the contents of the message
     - from/to  - IDs of the sender.receiver node
     - active - a bit, indicating whether the message hasn't been consumed yet (i.e., read)

     I'm not sure, if we're going to need anything else. *)
  Structure msg (mtype : Type) :=
    Msg {content  : mtype;
         from     : nat;
         to       : nat;
         active   : bool }.

  (* Message IDs: pairs Label * id, where Label comes from the protocol. *)
  Definition mid := [ordType of nat].

  (* Message soup (for a specific protocol) is just a partial finite
     map from message IDs (mid) to arbitrary Messages. *)
  Definition soup : Type :=
    union_map mid (msg (TaggedMessage)).

  Variables (s: soup) (V: valid s).

  (* Allocating new message in the soup *)
  Definition post_msg m : soup * mid :=
    let: f := fresh s in (s \+ f \\-> m, f).

  Lemma post_valid m :  valid (post_msg m).1.
  Proof. by rewrite ?valid_fresh. Qed.

  Lemma post_fresh m : (post_msg m).2 \notin dom s.
  Proof. by rewrite ?dom_fresh. Qed.

  (* Marking is  *)
  Definition mark_msg T (m : msg T) : msg T :=
    Msg (content m) (from m) (to m) false.

  (* Updating the message soup, consuming the message id *)
  Definition consume_msg (s : soup) (id : mid) : soup :=
    let: mr := find id s in
    if mr is Some m then upd id (mark_msg m) s else s.

  Definition is_active (id : mid) :=
    exists m, find id s = Some m /\ active m.

  Definition is_consumed (id : mid) :=
    exists m, find id s = Some m /\ ~~ active m.

  (* TODO: consumes "truth table" -- three possible scenarios (how to express?) *)

  (* Obvious fact about marking message *)
  Lemma find_consume s' (id: mid) m:
    valid s' -> find id s' = Some m ->
    find id (consume_msg s' id) = Some (mark_msg m).
  Proof. by move=>V' E; rewrite/consume_msg E findU eqxx V'/=. Qed.

  Lemma find_mark m s' msg :
    valid s' -> find m (consume_msg s' m) = Some msg ->
    exists msg', find m s' = Some msg' /\ msg = mark_msg msg'.
  Proof.
  move=>V'; rewrite /consume_msg; case D: (m \in dom s').
  - move/um_eta: D=>[msg'][->]_; rewrite findU eqxx/= V'.
    by case=><-; eexists _.
  by case: dom_find (D)=>//->_; move/find_some=>Z; rewrite Z in D.
  Qed.   

  Lemma mark_other m m' s' :
    valid s' -> m' == m = false -> find m' (consume_msg s' m) = find m' s'.
  Proof.
  move=>V' N; rewrite /consume_msg; case D: (m \in dom s').
  by case: dom_find (D)=>//v->_ _; rewrite findU N.
  by case: dom_find (D)=>//->_.
  Qed.   

  Lemma consume_valid s' m : valid s' -> valid (consume_msg s' m).
  Proof.
  move=>V'; rewrite /consume_msg; case (find m s')=>//v.
  by rewrite /mark_msg validU.
  Qed.

  Lemma consumeUn (s': soup) (i : mid) mm
        (j : mid) : valid (s' \+ i \\-> mm) ->
    consume_msg (s' \+ i \\-> mm) j = 
    if i == j then s' \+ i \\-> mark_msg mm
    else (consume_msg s' j) \+ (i \\-> mm).
  Proof.
  rewrite ![_ \+ i \\-> _]joinC; rewrite eq_sym.
  move=>V'; case B: (j==i); rewrite /consume_msg findPtUn2// B.
  - by move/eqP: B=>?; subst j; rewrite updPtUn.
  by case X: (find j s')=>//; rewrite updUnL domPt inE eq_sym B.   
  Qed.

  Notation "'{{' m 'in' s 'at' id '}}'" := (find id s = Some m).
  Notation "'{{' m 'in' s '}}'" := (exists id, {{m in s at id}}).


  
End Shared.

(* Local per-protocol state with per-node resources *)
Section Local.

  Variable U : Type.

  Definition nid := nat.

  (* Local state of a a protocol is simply a partial map from node ids
     to their local contributions, along with the validity of the
     cumulative contribution. *)

  Definition lstate_type := union_map [ordType of nid] U.

End Local.

(*
Definition um_all {A:ordType} {B} (p : A -> B -> bool) (u : union_map A B) : bool :=
  um_recf false true (fun k v f rec Hval Hpath => p k v && rec) u.

Definition um_some {A:ordType} {B} (p : A -> B -> bool) (u : union_map A B) : bool :=
  um_recf false false (fun k v f rec Hval Hpath => p k v || rec) u.
*)

Section Statelets.

  (* A particular statelet instance.
     The Label and the PCM are the parameters and are defined by the protocol.
     The lstate and dsop are subject of the evolution.
   *)
  Structure dstatelet  :=
    DStatelet {
        (* Not sure if it's the best way to represent information
           about kinds of messages in this particular dstatelet, but
           let's think of tags as of integers for now, so dTagToCont
           will map the tags to specific types. *)

        (* Local state for each node as a pair of heaps; first heap is
           real, second heap is a ghost one. Let's deal with this
           model for now before we figure out how to discharge
           equalities in a better way *)
        dstate     : lstate_type heap;
        dsoup      : soup
    }.

  Fixpoint empty_lstate (ns : seq nid) :=
    if ns is n :: ns'
    then n \\-> Heap.empty \+ (empty_lstate ns')
    else  Unit.
    
  (* Definition empty_dstatelet ns : dstatelet := *)
  (*   @DStatelet (empty_lstate (undup ns)) Unit. *)

  (* Lemma valid_mt_soup ns : valid (dsoup (empty_dstatelet ns)). *)
  (* Proof. by rewrite /= valid_unit. Qed. *)

  (* Lemma dom_mt ns : *)
  (*   valid (empty_lstate (undup ns)) /\ dom (empty_lstate (undup ns)) =i undup ns. *)
  (* Proof. *)
  (* elim: ns=>//=[|n ns [H1 H2]]; first by rewrite dom0. *)
  (* case B: (n \in ns)=>//=; split. *)
  (* - by rewrite gen_validPtUn/= H1 H2/=; apply/negbT; rewrite mem_undup. *)
  (* move=> z; rewrite um_domPtUn inE/= gen_validPtUn/= H1 H2/=. *)
  (* rewrite -mem_undup in B; rewrite B/=. *)
  (* case C: (n == z)=>//=; first by rewrite in_cons eq_sym C. *)
  (* by rewrite H2 in_cons eq_sym C/=. *)
  (* Qed. *)

  (* Lemma valid_mt_state ns : valid (dstate (empty_dstatelet ns)). *)
  (* Proof. *)
  (* elim:ns=>//=n ns H; case I: (n \in ns)=>//=.   *)
  (* by rewrite gen_validPtUn H/=; case: (dom_mt ns)=>_->; rewrite mem_undup I. *)
  (* Qed. *)

  (* Lemma mt_nodes ns : dom (dstate (empty_dstatelet ns)) =i ns. *)
  (* Proof. *)
  (* by case: (dom_mt ns)=>_ H2 z; rewrite -mem_undup -H2. *)
  (* Qed. *)

  Definition empty_dstatelet : dstatelet :=
    @DStatelet (empty_lstate [::]) Unit.

  Lemma valid_mt_soup : valid (dsoup empty_dstatelet).
  Proof. by rewrite /= valid_unit. Qed.

  Lemma valid_mt_state  : valid (dstate empty_dstatelet).
  Proof. by rewrite valid_unit. Qed.

  Lemma mt_nodes : dom (dstate empty_dstatelet) =i [::].
  Proof. by rewrite dom0. Qed.

End Statelets.


Module StateGetters.
Section StateGetters.

Definition state := union_map Label dstatelet.

(* Retrieve statelet from the state *)
Definition getStatelet (s: state) (i : Label) : dstatelet :=
  match find i s with
  | Some d => d
  | None => empty_dstatelet
  end.

End StateGetters.
End StateGetters.


Export StateGetters.

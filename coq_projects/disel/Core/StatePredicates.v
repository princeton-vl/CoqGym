From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness State EqTypeX DepMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SoupPredicates.

(*****************************************************)
(* Message predicates

[Valid messages in soup]

The following generic definition "msg_in_souop" specifies which
messages are considered valid in the specific state and the soup. 

The derived definition come next.

 *)

Definition msg_in_soup (from to : nid) (criterion : nat -> seq nat -> bool)
           (d : soup) : Prop :=
  (exists! i, exists t c,
        find i d = Some (Msg (TMsg t c) from to true)) /\
  forall i t c,
    find i d = Some (Msg (TMsg t c) from to true) ->
    criterion t c.

(* Fix specific tag and content *)
Definition msg_spec from to tg cnt :=
  msg_in_soup from to (fun x y => (x == tg) && (y == cnt)).

Definition no_msg_from (from : nid) (d : soup) : Prop :=
  forall i to tms b, find i d = Some (Msg tms from to b) -> b = false.

Definition no_msg_to (to : nid) (d : soup) : Prop :=
  forall i from tms b, find i d = Some (Msg tms from to b) -> b = false.


Lemma no_msg_from_post (from from' to : nid) (s : soup) tms :
  valid s ->
  no_msg_from from s -> from' != from ->
  no_msg_from from (post_msg s (Msg tms from' to true)).1.
Proof.
move=>V H/negbTE N i to' tms' b/=.
rewrite findUnR ?valid_fresh?V//.
case: ifP; last by move=>_/H.
rewrite domPt inE/==>/eqP Z; subst i.
rewrite findPt/=; case=>Z1 Z2 Z3; subst to' tms' from'.
by rewrite eqxx in N.
Qed.

Lemma no_msg_from_consume from from' to s i m :
  find i s = Some {| content := m; from := from'; to := to; active := true |} ->
  valid s ->
  no_msg_from from s ->
  no_msg_from from (consume_msg s i).
Proof.
move=>F V NM j to' tms b.
case H: (j == i).
- move /eqP in H. subst j.
  rewrite (find_consume _ F) //.
  by case.
rewrite mark_other//.
exact: NM.
Qed.

Definition no_msg_from_to from to (d : soup) :=
  forall i tms b,
    find i d = Some (Msg tms from to b) -> b = false.

Lemma no_msg_from_to_consume from to s i:
  valid s ->
  no_msg_from_to from to s ->
  no_msg_from_to from to (consume_msg s i).
Proof.
move=>V H m tms b .
rewrite /consume_msg; case: (find i s); last by move=>F; apply: (H m tms b F).
move=>ms; case B: (m == i).
- by move/eqP: B=>B; subst m; rewrite findU eqxx/= V; case. 
by rewrite findU B/==>/(H m tms b).
Qed.

Lemma msg_spec_consume s from to tg cnt cnt' i :
  valid s -> 
  find i s = Some {| content := TMsg tg cnt';
                     from := from; to := to; active := true |} ->
  msg_spec from to tg cnt s ->
  no_msg_from_to from to (consume_msg s i).
Proof.
move=>V E[][j][[t][c]]F H1 H2. 
move=>m tms b; rewrite /consume_msg; move: (find_some E).
case: dom_find=>// msg->_ _; case B: (m == i).
- by move/eqP: B=>B; subst m; rewrite findU eqxx/= V; case. 
have X: j = i by  apply: (H1 i); exists tg, cnt'.
subst j; rewrite findU B/=; case: b=>// E'.
suff X: i = m by subst i; rewrite eqxx in B.
by apply: (H1 m); case: tms E'=>t' c' E'; exists t', c'. 
Qed.

Lemma msg_specE_consume s pt from to to' tg cnt i m :
  valid s ->
  find i s =
  Some {| content := m; from := from; to := to'; active := true |} ->
  (pt != from) || (to != to') ->
  msg_spec pt to tg cnt s ->
  msg_spec pt to tg cnt (consume_msg s i).
Proof.
  move=>V E N[][j][[t][c]]F H1 H2.
  have Nij: i != j.
  - case H: (i == j)=>//.
    move/eqP in H. subst i.
    move: E. rewrite F. case. intros. subst.
    move: N=>/orP[]/eqP; congruence.
  split.
  - exists j.
    split.
    + exists t, c. rewrite mark_other// eq_sym. by apply /negbTE.
    + move => x [t'][c'].
      case H: (x == i).
      * move /eqP in H. subst x.
        by rewrite (find_consume _ E)//.
      * rewrite mark_other//.
        eauto.
  - move=>k t' c'.
    case H: (k == i).
    + move /eqP in H. subst.
      rewrite (find_consume _ E) //.
    + rewrite mark_other//.
      eauto.
Qed.

Lemma msg_specE_consume1 s pt from to to' tg cnt i m :
  valid s ->
  find i s =
  Some {| content := m; from := from; to := to'; active := true |} ->
  (pt != from) ->
  msg_spec pt to tg cnt s ->
  msg_spec pt to tg cnt (consume_msg s i).
Proof.
  intros.
  eapply msg_specE_consume; eauto.
  apply /orP; auto.
Qed.

Lemma msg_specE_consume2 s pt from to to' tg cnt i m :
  valid s ->
  find i s =
  Some {| content := m; from := from; to := to'; active := true |} ->
  (to != to') ->
  msg_spec pt to tg cnt s ->
  msg_spec pt to tg cnt (consume_msg s i).
Proof.
  intros.
  eapply msg_specE_consume; eauto.
  apply /orP; auto.
Qed.

Definition no_msg_from_imp from to d :
  no_msg_from from d -> no_msg_from_to from to d.
Proof. by move=>H i; move: (H i to). Qed.


Lemma no_msg_from_toE from to s tms to':
  valid s -> 
  no_msg_from_to from to s -> to == to' = false ->
  no_msg_from_to from to (post_msg s (Msg tms from to' true)).1.
Proof.
move=>V H X/= i m b; rewrite findUnR ?valid_fresh?V//.
case: ifP; last by move=>_/H.
rewrite domPt inE/==>/eqP Z; subst i.
by rewrite findPt/=; case=>_ Z; subst to'; rewrite eqxx in X.
Qed.

Lemma no_msg_from_toE' from to s tms from' to':
  valid s -> 
  no_msg_from_to from to s -> from' == from = false ->
  no_msg_from_to from to (post_msg s (Msg tms from' to' true)).1.
Proof.
move=>V H X/= i m b; rewrite findUnR ?valid_fresh?V//.
case: ifP; last by move=>_/H.
rewrite domPt inE/==>/eqP Z; subst i.
by rewrite findPt/=; case=>Z' Z; subst from'; rewrite eqxx in X.
Qed.

Lemma msg_specE s from to tg cnt :
  valid s ->
  no_msg_from_to from to s ->
  msg_spec from to tg cnt (post_msg s (Msg (TMsg tg cnt) from to true)).1.
Proof.
move=>V H; split=>/=; last first.
- move=>i t c; rewrite findUnR ?valid_fresh?V//.
  case: ifP; last by move=>_/H.
  rewrite domPt inE/==>/eqP Z; subst i.
  by rewrite findPt/=; case=>E Z; subst c t; rewrite !eqxx.
exists (fresh s); split=>[|z[t][c]].
- exists tg, cnt; rewrite findUnR ?valid_fresh?V//.
  by rewrite domPt inE eqxx/=findPt/=.
rewrite findUnR ?valid_fresh?V// domPt !inE/=.
by case: ifP=>[|_/H]//; move/eqP=>->.  
Qed.

Lemma msg_specE' s from to to' tg cnt tms :
  valid s -> to == to' = false ->
  msg_spec from to tg cnt s ->
  msg_spec from to tg cnt (post_msg s (Msg tms from to' true)).1.
Proof.
move=>V N H; split=>//=; last first.
- move=>i t c; rewrite findUnR ?valid_fresh?V//.
  rewrite domPt inE/=; case:ifP; last by move=>_; move/(proj2 H).
  move/eqP=>Z; subst i; rewrite findPt/=; case=>_ Z.
  by subst to'; rewrite eqxx in N.   
case: (H)=>H' _; case: H'=>i; case=>[[t]][c] U1 U2.
exists i; split=>//.
- exists t, c; rewrite findUnR ?valid_fresh?V//.
  rewrite domPt inE/=; case:ifP=>//.
  move/eqP=>Z; subst i.
  by move/find_some: U1=>E; move:(dom_fresh s); rewrite E.
move=>z[t'][c']; rewrite findUnR ?valid_fresh?V//.
rewrite domPt inE/=; case:ifP=>//; last first.
- by move=>_ G; apply: (U2 z); exists t', c'. 
move/eqP=>Z; subst z.
rewrite findPt/=; case=>Z1 Z2. 
by subst to'; rewrite eqxx in N.
Qed.

Lemma msg_specE'' s from from' to to' tg cnt tms :
  valid s -> from == from' = false ->
  msg_spec from to tg cnt s ->
  msg_spec from to tg cnt (post_msg s (Msg tms from' to' true)).1.
Proof.
move=>V N H; split=>//=; last first.
- move=>i t c; rewrite findUnR ?valid_fresh?V//.
  rewrite domPt inE/=; case:ifP; last by move=>_; move/(proj2 H).
  move/eqP=>Z; subst i; rewrite findPt/=; case=>_ Z.
  by subst from'; rewrite eqxx in N.   
case: (H)=>H' _; case: H'=>i; case=>[[t]][c] U1 U2.
exists i; split=>//.
- exists t, c; rewrite findUnR ?valid_fresh?V//.
  rewrite domPt inE/=; case:ifP=>//.
  move/eqP=>Z; subst i.
  by move/find_some: U1=>E; move:(dom_fresh s); rewrite E.
move=>z[t'][c']; rewrite findUnR ?valid_fresh?V//.
rewrite domPt inE/=; case:ifP=>//; last first.
- by move=>_ G; apply: (U2 z); exists t', c'. 
move/eqP=>Z; subst z.
rewrite findPt/=; case=>Z1 Z2. 
by subst from'; rewrite eqxx in N.
Qed.

End SoupPredicates.

(************************************************************)
(*                       List lemmas                        *)
(************************************************************)

Lemma has_all_true xs (ps : seq nid) x:
  perm_eq [seq i.1 | i <- xs] ps ->
  all id [seq i.2 | i <- xs] ->
  x \in ps -> (x, true) \in xs.
Proof.
move=>P A D; move: (perm_eq_mem P x).
rewrite D=>/mapP[z] I Z; subst x.
rewrite all_map/= in A; move/allP: A=>/(_ z I)/=<-.
by rewrite -surjective_pairing.
Qed.

Lemma has_some_false (xs : seq (nid * bool)) ps x:
  perm_eq [seq i.1 | i <- xs] ps ->
  x \in ps -> exists b, (x, b) \in xs.
Proof.
move=>P D; move: (perm_eq_mem P x).
rewrite D=>/mapP[z] I Z; subst x.
by exists z.2; rewrite -surjective_pairing.
Qed.

(********************************************************)
(*** More elaborated versions of the same predicates  ***)
(********************************************************)

Definition no_msg_from_to' from to
           (criterion : nat -> seq nat -> bool) (d : soup) :=
  forall i t c,
    find i d = Some (Msg (TMsg t c) from to true) ->
    ~~criterion t c.

Lemma no_msg_from_to_consume' from to cond s i:
  valid s ->
  no_msg_from_to' from to cond s ->
  no_msg_from_to' from to cond (consume_msg s i).
Proof.
move=>V H m t c .
rewrite /consume_msg; case: (find i s); last by move=>F; apply: (H m t c F).
move=>ms; case B: (m == i).
- by move/eqP: B=>B; subst m; rewrite findU eqxx/= V.
by rewrite findU B/==>/(H m t c).
Qed.

(* Lemma msg_spec_consume' s from to tg cnt cond i : *)
(*   valid s ->  *)
(*   find i s = Some {| content := TMsg tg cnt; *)
(*                      from := from; to := to; active := true |} -> *)
(*   msg_in_soup from to cond s -> *)
(*   no_msg_from_to' from to cond (consume_msg s i). *)
(* Proof. *)
(* move=>V E[][j][[t][c]]F H1 H2.  *)
(* move=>m t' c'; rewrite /consume_msg; move: (find_some E). *)
(* case: dom_find=>// msg->_ _; case B: (m == i). *)
(* - by move/eqP: B=>B; subst m; rewrite findU eqxx/= V. *)
(* have X: j = i by apply: (H1 i); exists tg, cnt. *)
(* subst j; rewrite findU B/=. case: b=>// E' _. *)
(* suff X: i = m by subst i; rewrite eqxx in B. *)
(* by apply: (H1 m); exists t', c'.  *)
(* Qed. *)

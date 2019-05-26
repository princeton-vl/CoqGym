(*
    Copyright (C) 2012  G. Gonthier, B. Ziliani, A. Nanevski, D. Dreyer

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

From mathcomp
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq.
From LemmaOverloading
Require Import prelude prefix perms heaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(**************************************************************************)
(*                  Syntactic cancelation of heaps                        *)
(**************************************************************************)

(* Differences w.r.t. the paper:

In the paper we described the cancellation algorithm as producing a
proposition. Instead, it will produce a sequence of "facts" which are
later on evaluated into a proposition. We did this in order to further
simplify the proposition. Each fact is of the form t1 = t2, where t1
and t2 are heaps, pointers, or values.

Another simplification we made in the paper is that the values contained
in a heap are actually instances of a generic type 'dynamic'. This type
is defined in the file heaps.v, and is just a structure containing a
value and its type. So, instead of equating values, we are equating dynamics,
therefore we need some extra step to prove the values are equal
(see the examples at the bottom of the file). This can be avoided
with extra canonical structures machinery.
*)


(***************************)
(* interpretation contexts *)
(***************************)

Structure ctx := Context {heap_ctx : seq heap; ptr_ctx : seq ptr}.

Definition empc := Context [::] [::].

Definition subctx i j :=
  prefix (heap_ctx i) (heap_ctx j) /\ prefix (ptr_ctx i) (ptr_ctx j).

Lemma subctx_refl i: subctx i i.
Proof. by []. Qed.

Lemma subctx_trans j i k :
        subctx i j -> subctx j k -> subctx i k.
Proof.
move=>[H1 P1][H2 P2].
by split; [move: H2|move: P2]; apply: prefix_trans.
Qed.

(**************************************************************************)
(*                            Syntactic heaps                             *)
(* Pointers and heap variables are syntactified as indices in the context *)
(* Disjoint union is syntactified as concatenation of lists               *)
(**************************************************************************)

Inductive elem := Pts of nat & dynamic | Var of nat.
Definition synheap := seq elem.

(*****************************************************************************)
(* Validity of indices:                                                      *)
(*   valid i t  iif all the indices in t are in bounds of the contexts lists *)
(*****************************************************************************)

Fixpoint valid_ptrs i t :=
  match t with
    Pts sx _ :: s => (sx < size (ptr_ctx i)) && valid_ptrs i s
  | Var _ :: s => valid_ptrs i s
  | _ => true
  end.

Fixpoint valid_heaps i t :=
  match t with
    Pts _ _ :: s => valid_heaps i s
  | Var v :: s => (v < size (heap_ctx i)) && valid_heaps i s
  | _ => true
  end.

Definition valid i t := valid_ptrs i t && valid_heaps i t.

Lemma valid_cons i e t : valid i (e :: t) = valid i [:: e] && valid i t.
Proof.
case: e=>[x d|v] /=; rewrite /valid /=;
by [rewrite !andbT andbA | rewrite andbT andbCA].
Qed.

Lemma valid_ptrs_cat j t1 t2 :
        valid_ptrs j (t1 ++ t2) = valid_ptrs j t1 && valid_ptrs j t2.
Proof.
elim: t1 t2=>[//|v t1 IH /=] t2.
by case: v=>[x d | v]; rewrite IH // andbA.
Qed.

Lemma valid_heaps_cat j t1 t2 :
        valid_heaps j (t1 ++ t2) = valid_heaps j t1 && valid_heaps j t2.
Proof.
elim: t1 t2=>[//|v t1 IH /=] t2.
by case: v=>[x d | v]; rewrite IH // andbA.
Qed.

Lemma valid_cat j t1 t2 : valid j (t1 ++ t2) = valid j t1 && valid j t2.
Proof.
rewrite /valid valid_ptrs_cat valid_heaps_cat.
by rewrite -!andbA -!(andbCA (valid_ptrs j t2)).
Qed.

Lemma valid_subctx i j t : subctx i j -> valid i t -> valid j t.
Proof.
case: i j=>hs1 xs1 [hs2 xs2][/= P1 P2].
elim: t=>[//|e t IH]; rewrite -cat1s 2!valid_cat.
case/andP=>H; move/IH=>->.
case: e H=>[x d| v]; rewrite /valid /= !andbT => H; apply: leq_trans H _;
by [apply: (prefix_size P2) | apply: (prefix_size P1)].
Qed.

(*************************************)
(* interpretation of syntactic heaps *)
(*************************************)

(* lookup functions for heaps and pointers *)
Definition hlook := [fun i => onth (heap_ctx i)].
Definition plook := [fun i => onth (ptr_ctx i)].

(* notation for lookups with default *)
Notation plook' i x := (odflt null (plook i x)).

(* interpretation function for elements *)
Definition einterp i e :=
  match e with
    Pts x d =>
      if plook i x is Some x'
        then x' :-> Dyn.val d
      else Undef
  | Var h => if hlook i h is Some h' then h' else Undef
  end.

(* main interpretation function *)
Fixpoint interp i t :=
  if t is e :: t' then
    if t' is [::] then einterp i e else einterp i e :+ interp i t'
  else empty.

Lemma interp_cons i e t : interp i (e :: t) = einterp i e :+ interp i t.
Proof. by case:t=>//; rewrite unh0. Qed.

Lemma interp_cat i t1 t2 : interp i (t1 ++ t2) = interp i t1 :+ interp i t2.
Proof.
elim:t1 t2=>[/=|e t1 IH] t2; first by rewrite un0h.
by rewrite cat_cons !interp_cons IH unA.
Qed.

Lemma interp_perm i : forall t1 t2, perm t1 t2 -> interp i t1 = interp i t2.
Proof.
apply: perm_ind=>[s1 s2 ->-> //|t1 t2 x t1' t2' ->->|x y t1' t2' t ->->|x y t].
- by rewrite 2!interp_cons=>_ ->.
- by rewrite !interp_cons unCA.
by move=>_ -> _ ->.
Qed.

Lemma interp_subctx j k t: valid j t -> subctx j k -> interp j t = interp k t.
Proof.
move=>I [S1 S2]; elim:t I=>[//|e t IH].
rewrite 2!interp_cons valid_cons; case/andP=>H1.
move/IH=>->; case: e H1=>[x d|v] /=;
rewrite /valid /= !andbT; move/prefix_onth;
by [move/(_ _ S2)=>-> | move/(_ _ S1)=>->].
Qed.


Inductive fact :=
  eqH of synheap & synheap | eqD of dynamic & dynamic | eqX of nat & nat.

(* returns the proposition generated by a fact *)
Definition eval_fact i f :=
  match f with
  | eqH h1 h2 => interp i h1 = interp i h2
  | eqD d1 d2 => d1 = d2
  | eqX x1 x2 => plook i x1 = plook i x2
  end.

(* returns the logic concatenation of all the facts in the list *)
Fixpoint eval i s :=
  match s with
  | [:: f] => eval_fact i f
  | (f :: fs) => eval_fact i f /\ eval i fs
  | [::] => True
  end.

(* functions to collect pointers and heap variables indices out of a synheap *)
Fixpoint ptrs t : seq nat :=
  if t is e :: t' then
    if e is Pts x _ then x :: (ptrs t')
    else ptrs t'
  else [::].

Fixpoint vars t : seq nat :=
  if t is e :: t' then
    if e is Var h then h :: (vars t')
    else vars t'
  else [::].

Definition ptreq (x : nat) e := if e is Pts y _ then x == y else false.
Definition vareq (h : nat) e := if e is Var k then h == k else false.

Fixpoint pread x t :=
  match t with
    Pts y d :: s => if x == y then some d else pread x s
  | e :: s => pread x s
  | _ => None
  end.

Notation pread' x t := (odflt (dyn tt) (pread x t)).

Definition pfree x t := filter (predC (ptreq x)) t.
Definition hfree h t := filter (predC (vareq h)) t.


(* Main function to perform the cancelation of heaps. One difference to point
   out from the description in the paper, appart from the fact that it is
   returning a list of facts, is that in the base case we consider the special
   case x1 :-> v1 = x2 :-> v2 -> x1 = x2 /\ v1 = v2  *)
Fixpoint cancel' (i : ctx) (t1 t2 r : synheap) (f : seq fact) : seq fact :=
  match t1 with
  | [::] => match r, t2 with
            | [::], [::] => f
            | [:: Pts x d], [:: Pts x' d'] =>
                [:: eqX x x', eqD d d' & f]
            | _ , _ => [:: eqH r t2 & f]
            end
  | Pts x d :: t1' =>
      if x \in ptrs t2
        then cancel' i t1' (pfree x t2) r [:: eqD d (pread' x t2) & f]
      else cancel' i t1' t2 [:: Pts x d & r] f
  | Var h :: t1' =>
      if h \in vars t2 then cancel' i t1' (hfree h t2) r f
      else cancel' i t1' t2 [:: Var h & r] f
  end.

Definition cancel i t1 t2 := cancel' i t1 t2 [::] [::].

(* several auxiliary lemmas about the definitions given above *)

Lemma eval_cons i f s : eval i (f :: s) <-> eval_fact i f /\ eval i s.
Proof. by case:s=>//; split=>//; case. Qed.

Lemma eval_cat i s1 s2 : eval i (s1 ++ s2) <-> eval i s1 /\ eval i s2.
Proof.
elim: s1=>[/=|f s1 IH]; first tauto.
by rewrite cat_cons !eval_cons IH; tauto.
Qed.

Lemma eval_rcons i f s : eval i (rcons s f) <-> eval i s /\ eval_fact i f.
Proof. by rewrite -cats1 eval_cat. Qed.

Lemma pfreeE x t :
        pfree x t =
          if t is e :: t' then
            if e is Pts y d then
              if x == y then pfree x t' else e :: pfree x t'
            else e :: pfree x t'
          else [::].
Proof. by elim:t=>[|e t IH] //; case: e=>[y d|] //=; case: eqP. Qed.

Lemma hfreeE h t :
        hfree h t =
          if t is e :: t' then
            if e is Var k then
              if h == k then hfree h t' else e :: hfree h t'
            else e :: hfree h t'
          else [::].
Proof. by elim:t=>[|e t IH] //; case: e=>[| n] //=; case: eqP. Qed.

Lemma ptr_has x t : has (ptreq x) t = (x \in ptrs t).
Proof.
by elim:t=>[//|e t IH]; case: e=>[y d|//]; rewrite /= inE IH.
Qed.

Lemma var_has h t : has (vareq h) t = (h \in vars t).
Proof. by elim:t=>[//|e t IH]; case: e=>[//|n]; rewrite /= inE IH. Qed.

Lemma pfreeN x t : x \notin ptrs t -> pfree x t = t.
Proof.
rewrite -ptr_has; elim: t=>[|e t IH] //=; rewrite negb_or.
by case/andP=>->; move/IH=>->.
Qed.

Lemma pfree_subdom i x t :
        def (interp i t) -> subdom (interp i (pfree x t)) (interp i t).
Proof.
elim:t=>[//|e t IH]; rewrite interp_cons /= => D.
case: ifP=>_; last first.
- rewrite -(un0h (interp _ _)); apply: subdomUE=>//.
  - by apply: subdom_emp; rewrite (defUnl D).
  by apply: IH; rewrite (defUnr D).
rewrite interp_cons; apply: subdomUE=>//.
- by apply: subdom_refl; rewrite (defUnl D).
by apply: IH; rewrite (defUnr D).
Qed.

Lemma pfree_def i x t: def (interp i t) -> def (interp i (pfree x t)).
Proof. by move/(pfree_subdom x); move/subdom_def; move/andP=>[-> _]. Qed.

Lemma hfreeN h t : h \notin vars t -> hfree h t = t.
Proof.
rewrite -var_has; elim: t=>[|e t IH] //=; rewrite negb_or.
by case/andP=>->; move/IH=>->.
Qed.

Lemma vars_hfree (h1 h2 : nat) t :
        has (vareq h1) (hfree h2 t) = (h1 != h2) && (has (vareq h1) t).
Proof.
elim:t=>[|e t IH]; first by rewrite andbF.
case: e=>[//|n /=].
by case: ifP=>/= E; rewrite IH; case: (h1 =P n)=>// ->; rewrite eq_sym E.
Qed.

Lemma hfree_subdom i h t :
        def (interp i t) ->
          {subset dom (interp i (hfree h t)) <= dom (interp i t)}.
Proof.
elim:t=>[_ x //|e t IH]; rewrite interp_cons /= => D.
case: ifP=>_; last first.
- move=>x; move/(IH (defUnr D)).
  by rewrite domUn !inE D orbC => ->.
rewrite interp_cons => x; rewrite !domUn !inE D /=.
case/andP=>D2; case/orP; rewrite ?inE; first by move->.
by move/(IH (defUnr D) x)=>->; rewrite orbT.
Qed.

Lemma hfree_subdom' i h t :
        def (interp i t) ->
          subdom (interp i (hfree h t)) (interp i t).
Proof.
elim:t=>[//|e t IH]; rewrite interp_cons /= => D.
case: ifP=>_; last first.
- rewrite -(un0h (interp _ _)).
  apply: subdomUE=>//.
  - by apply: subdom_emp; rewrite (defUnl D).
  by apply: IH; rewrite (defUnr D).
rewrite interp_cons.
apply: subdomUE=>//.
- by apply: subdom_refl; rewrite (defUnl D).
by apply: IH; rewrite (defUnr D).
Qed.

Lemma hfree_def i h t : def (interp i t) -> def (interp i (hfree h t)).
Proof. by move/(hfree_subdom' h); move/subdom_def; move/andP=>[-> _]. Qed.

Lemma count0_hfree v t: count (pred1 v) (vars t) = 0 -> hfree v t = t.
Proof. by move/eqP; rewrite eqn0Ngt -has_count has_pred1; apply: hfreeN. Qed.

Lemma count1_hfree v t :
        count (pred1 v) (vars t) = 1 -> perm (Var v :: hfree v t) t.
Proof.
elim: t=>[//|w t IH]; case: w=>[x d H|v'] /=.
- rewrite perm_sym -(cat1s (Var v) _).
  apply: perm_cons_cat_consL.
  by rewrite perm_sym; apply: IH.
rewrite eq_sym; case: eqP=>[->|_] /=.
  rewrite -{2}[1]addn0; move/eqP; rewrite eqn_addl; move/eqP.
  by move/count0_hfree=>->.
rewrite add0n; move/IH=>H; rewrite perm_sym -(cat1s (Var v)).
by apply: perm_cons_cat_consL; rewrite perm_sym.
Qed.

Lemma countN_varfree i v t :
        count (pred1 v) (vars t) > 1 -> def (interp i t) ->
        hlook i v = Some empty.
Proof.
elim: t v=>[//|[x d|h] s IH] v H; rewrite interp_cons=>D.
- by apply: IH=>//; apply defUnr in D.
rewrite /= in H.
case: (h =P v) H=>[<-|_]; last by move/IH; apply; apply: defUnr D.
case H2: (count _ _)=>[//|[|n]] _; last first.
- by apply: IH; [rewrite H2 | apply: defUnr D].
move/count1_hfree: H2=>H2.
rewrite -(interp_perm i H2) interp_cons unA in D.
move: (defUnl D); rewrite defUnhh /=.
by case: (onth _ _)=>// a; move/empP=>->.
Qed.

Lemma empty_hfree i v t :
        hlook i v = Some empty -> interp i (hfree v t) = interp i t.
Proof.
elim: t=>[//|[x d|v'] t IH] H1; rewrite [hfree _ _]/=.
- by rewrite 2!interp_cons IH.
case: ifP=>H2; first by rewrite 2!interp_cons IH.
rewrite /= in H1; rewrite -(eqP (negbFE H2)) {}IH //= H1.
by case: t=>[//|e s]; rewrite un0h.
Qed.


(***********************************************)
(* Reflection lemmas                           *)
(* The following series of lemmas establish a  *)
(* bridge between syntax and semantics         *)
(***********************************************)

Lemma domR i (x : nat) t :
        def (interp i t) -> has (ptreq x) t ->
        plook' i x \in dom (interp i t).
Proof.
elim: t x=>[//|e1 t IH] x; rewrite interp_cons /= => D.
case/orP=>E; last by rewrite domUn !inE D (IH _ (defUnr D) E) orbT.
rewrite domUn !inE D.
case: e1 E D=>//= y d; move/eqP=><-; move/defUnl.
case: (onth _ _)=>[a|] //=.
by rewrite defPt domPt !inE eqxx => ->.
Qed.

Lemma lookR i t x :
        def (interp i t) -> has (ptreq x) t ->
        look (plook' i x) (interp i t) = pread' x t.
Proof.
elim: t x=>[//|e1 t IH] x; rewrite interp_cons /=.
case F: (ptreq x e1)=>/= D E; last first.
- rewrite (lookUnr _ D) (domR (defUnr D) E) (IH _ (defUnr D) E).
  by case: e1 F {D}=>//= y d ->.
case: e1 {E} F D=>// y d; move/eqP=><-{y} D.
rewrite (_ : einterp i _ = interp i [:: Pts x d]) // in D *.
rewrite (lookUnl _ D) (domR (defUnl D)) /= ?eqxx //.
move/defUnl: D=>/=; case: (onth _ x)=>[a|] //.
rewrite defPt lookU /= eqxx => ->.
by rewrite -dyn_eta.
Qed.

Lemma defR i t : def (interp i t) -> uniq (ptrs t).
Proof.
elim: t=>[//|e t IH]; rewrite interp_cons /=.
case: e=>[y d|n] /=; case E: (onth _ _)=>[a|//]; last by move/defUnr.
case: defUn=>// D1 D2 L _.
rewrite (IH D2) andbT -ptr_has.
apply: contra (L a _); first by move/(domR D2); rewrite /= E.
by rewrite defPt domPt !inE eqxx in D1 *.
Qed.

Lemma freeR i t x :
        def (interp i t) -> has (ptreq x) t ->
        free (plook' i x) (interp i t) = interp i (pfree x t).
Proof.
elim: t=>[//|e t IH]; rewrite interp_cons=>D /=.
case E: (ptreq x e)=>/=; last first.
- move=>H; rewrite freeUnl; first by rewrite (IH (defUnr D) H) -{1}interp_cons.
  case: defUn D=>// D1 D2 L _.
  apply: (contra (L (plook' i x))); rewrite negbK.
  by apply: domR.
case: e E D=>//= y d; move/eqP=><-{y}.
case F: (onth _ x)=>[a|//] D _.
rewrite freePtUn //= pfreeN // -ptr_has.
apply: contra (defPt_dom D); move/(domR (defPt_def D)).
by rewrite /= F.
Qed.

Lemma cancel_sound' i sh1 sh2 unm fs :
        interp i sh2 = interp i (sh1 ++ unm) ->
        def (interp i sh2) -> eval i fs ->
        eval i (cancel' i sh1 sh2 unm fs).
Proof.
elim: sh1 sh2 unm fs=>[|[sx sd|sv] sh1 IH] sh2 unm fs.
- case: unm=>[|[sxu sdu|svu] [|[sxu' sud'|svu'] unm']];
  case: sh2=>[|[sx2 sd2|sv2] sh2'] /=; try by case: fs.
  case A: (onth _ sx2)=>[a|]; last by case sh2'.
  case D: (onth _ sxu)=>[d|]; last by move->.
  case: sh2'=>[/= H2 Def|e sh2']; last by rewrite /= A D =>->; case: fs.
  case: (pts_injP Def H2)=>[H3 H4].
  rewrite A D H3; split=>//.
  case: sdu sd2 H4 H2 Def=>b1 b2 [c1 c2] /= H4; move: b2.
  rewrite -H4 H3=> b2 H2 Def.
  by move/(pts_inj Def): H2=>->; case: fs H.
- rewrite [eval _ (cancel' _ _ _ _ _)]/=.
  case: ifP=>H1 H2 D E; last first.
  - apply: (IH _ _ _ _ D E).
    by rewrite H2 2!interp_cat 2!interp_cons unCA unA.
  apply: IH; last 2 first.
  - by apply: pfree_def.
  - rewrite -ptr_has in H1; rewrite /= -(lookR D H1).
    rewrite H2 interp_cons /= in D *.
    case A: (onth _ sx)=>[a|//] in D *.
    by rewrite (lookPtUn D) -dyn_eta; case: fs E.
  rewrite -ptr_has in H1; rewrite -(freeR D H1).
  rewrite H2 cat_cons /= in D *.
  case A: (onth _ sx)=>[a /=|] in D *; last by case: (sh1 ++ unm) D.
  case: (sh1 ++ unm) D=>[|c s D]; last by rewrite (freePtUn D).
  by rewrite freeU defU eq_refl; case/andP; move/negbTE=>-> _; rewrite free0.
rewrite [eval _ (cancel' _ _ _ _ _)]/=.
case: ifP=>H1 H2 D E; last first.
- apply: (IH _ _ _ _ D E).
  by rewrite H2 2!interp_cat 2!interp_cons unCA unA.
apply: IH=>//; last by apply: hfree_def.
rewrite -has_pred1 has_count in H1.
case H1: (count _ _) H1=>[//|[|n]] _; last first.
- have H3: count (pred1 sv) (vars sh2) > 1 by rewrite H1.
  move: (countN_varfree H3 D)=>/= H4.
  by rewrite (empty_hfree sh2 H4) H2 interp_cons /= H4 un0h.
move/(interp_perm i): (count1_hfree H1)=>H6.
rewrite -H6 cat_cons 2!interp_cons in H2.
rewrite -H6 interp_cons H2 in D.
by apply: (unhKr D H2).
Qed.


(* Main lemma: the cancel algorithm is correct *)
Lemma cancel_sound i t1 t2 :
        def (interp i t1) -> interp i t1 = interp i t2 ->
        eval i (cancel i t1 t2).
Proof. by move=>D H; apply: cancel_sound'=>//; rewrite -H // cats0. Qed.


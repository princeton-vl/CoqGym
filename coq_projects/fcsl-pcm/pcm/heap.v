(*
Copyright 2010 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

(******************************************************************************)
(* This file defines heaps as possibly undefined finite maps from pointer     *)
(* type to dynamic type.                                                      *)
(* Heaps are a special case of Partial Commutative Monoids (pcm)              *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun Eqdep.
From mathcomp Require Import ssrnat eqtype seq path.
From fcsl Require Import axioms ordtype pcm finmap unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(*************)
(* Locations *)
(*************)

Inductive ptr := ptr_nat of nat.

Definition null := ptr_nat 0.

Definition nat_ptr (x : ptr) := let: ptr_nat y := x in y.

Definition eq_ptr (x y : ptr) : bool := 
  match x, y with ptr_nat m, ptr_nat n => m == n end.

Lemma eq_ptrP : Equality.axiom eq_ptr.
Proof. by case=>x [y] /=; case: eqP=>[->|*]; constructor=>//; case. Qed.

Definition ptr_eqMixin := EqMixin eq_ptrP. 
Canonical ptr_eqType := EqType ptr ptr_eqMixin.

(* some pointer arithmetic: offsetting from a base *)

Definition ptr_offset x i := ptr_nat (nat_ptr x + i).

Notation "x .+ i" := (ptr_offset x i) 
  (at level 3, format "x .+ i"). 

Lemma ptrE x y : (x == y) = (nat_ptr x == nat_ptr y).
Proof. by move: x y=>[x][y]. Qed.

Lemma ptr0 x : x.+0 = x.
Proof. by case: x=>x; rewrite /ptr_offset addn0. Qed.

Lemma ptrA x i j : x.+i.+j = x.+(i+j).
Proof. by case: x=>x; rewrite /ptr_offset addnA. Qed.

Lemma ptrK x i j : (x.+i == x.+j) = (i == j).
Proof. by case: x=>x; rewrite ptrE eqn_add2l. Qed.

Lemma ptr_null x m : (x.+m == null) = (x == null) && (m == 0).
Proof. by case: x=>x; rewrite !ptrE addn_eq0. Qed.

Lemma ptrT x y : {m : nat | (x == y.+m) || (y == x.+m)}.
Proof. 
case: x y=>x [y]; exists (if x <= y then (y - x) else (x - y)).
rewrite !ptrE leq_eqVlt /=.
by case: (ltngtP x y)=>/= E; rewrite subnKC ?(ltnW E) ?eq_refl ?orbT // E.
Qed.

Definition ltn_ptr (x y : ptr) := 
  match x, y with ptr_nat m, ptr_nat n => m < n end.

Lemma ltn_ptr_irr : irreflexive ltn_ptr.
Proof. by case=>x /=; rewrite ltnn. Qed.

Lemma ltn_ptr_trans : transitive ltn_ptr.
Proof. by case=>x [y][z]; apply: ltn_trans. Qed.

Lemma ltn_ptr_total : forall x y : ptr, [|| ltn_ptr x y, x == y | ltn_ptr y x].
Proof. by case=>x [y]; rewrite ptrE /=; case: ltngtP. Qed.

Definition ptr_ordMixin := OrdMixin ltn_ptr_irr ltn_ptr_trans ltn_ptr_total.
Canonical ptr_ordType := OrdType ptr ptr_ordMixin.

(*********)
(* Heaps *)
(*********)

Module Heap.

Inductive heap := 
  Undef | Def (finmap : {finMap ptr -> dynamic id}) of 
               null \notin supp finmap.

Section NullLemmas.
Variables (f g : {finMap ptr -> dynamic id}) (x : ptr) (v : dynamic id).

Lemma upd_nullP : 
        x != null -> null \notin supp f -> null \notin supp (ins x v f).
Proof. by move=>H1 H2; rewrite supp_ins negb_or /= inE /= eq_sym H1. Qed.

Lemma free_nullP : null \notin supp f -> null \notin supp (rem x f). 
Proof. by move=>H; rewrite supp_rem negb_and /= H orbT. Qed.

Lemma un_nullP : 
        null \notin supp f -> null \notin supp g -> 
          null \notin supp (fcat f g).
Proof. by move=>H1 H2; rewrite supp_fcat negb_or H1 H2. Qed.

Lemma filt_nullP (q : pred ptr) : 
        null \notin supp f -> null \notin supp (kfilter q f).
Proof. by move=>H; rewrite supp_kfilt mem_filter negb_and H orbT. Qed.

Lemma heap_base : null \notin supp f -> all (fun k => k != null) (supp f).
Proof. by move=>H; apply/allP=>k; case: eqP H=>// -> /negbTE ->. Qed.

Lemma base_heap : all (fun k => k != null) (supp f) -> null \notin supp f.
Proof. by move/allP=>H; apply: (introN idP); move/H. Qed.

Lemma heapE (h1 h2 : heap) : 
        h1 = h2 <-> 
        match h1, h2 with
          Def f' pf, Def g' pg => f' = g'
        | Undef, Undef => true
        | _, _ => false
        end.
Proof.
split; first by move=>->; case: h2.
case: h1; case: h2=>// f1 pf1 f2 pf2 E. 
rewrite {f2}E in pf1 pf2 *.
by congr Def; apply: bool_irrelevance.
Qed.

End NullLemmas.


(* methods *)

Definition def h := if h is Def _ _ then true else false.

Definition empty := @Def (finmap.nil _ _) is_true_true.

Definition upd k v h := 
  if h is Def hs ns then 
    if decP (@idP (k != null)) is left pf then 
      Def (@upd_nullP _ _ v pf ns)
    else Undef
  else Undef.

Definition dom h : seq ptr := 
  if h is Def f _ then supp f else [::].

Definition dom_eq h1 h2 :=
  match h1, h2 with
    Def f1 _, Def f2 _ => supp f1 == supp f2
  | Undef, Undef => true
  | _, _ => false
  end.

Definition free x h := 
  if h is Def hs ns then Def (free_nullP x ns) else Undef.

Definition find (x : ptr) h := 
  if h is Def hs _ then fnd x hs else None.

Definition union h1 h2 := 
  if (h1, h2) is (Def hs1 ns1, Def hs2 ns2) then  
    if disj hs1 hs2 then 
       Def (@un_nullP _ _ ns1 ns2)
    else Undef
  else Undef.

Definition um_filter q f := 
  if f is Def fs pf then Def (@filt_nullP fs q pf) else Undef.

Definition pts (x : ptr) v := upd x v empty. 

Definition empb h := if h is Def hs _ then supp hs == [::] else false. 

Definition undefb h := if h is Undef then true else false.

Definition keys_of h : seq ptr := 
  if h is Def f _ then supp f else [::].

Local Notation base := 
  (@UM.base ptr_ordType (dynamic id) (fun k => k != null)).

Definition from (f : heap) : base :=
  if f is Def hs ns then UM.Def (heap_base ns) else UM.Undef _ _.

Definition to (b : base) : heap := 
  if b is UM.Def hs ns then Def (base_heap ns) else Undef.

Lemma ftE b : from (to b) = b. 
Proof. by case: b=>// f H; rewrite UM.umapE. Qed.

Lemma tfE f : to (from f) = f. 
Proof. by case: f=>// f H; rewrite heapE. Qed.

Lemma undefE : Undef = to (@UM.Undef _ _ _). 
Proof. by []. Qed.

Lemma defE f : def f = UM.valid (from f). 
Proof. by case: f. Qed.

Lemma emptyE : empty = to (@UM.empty _ _ _). 
Proof. by rewrite heapE. Qed.

Lemma updE k v f : upd k v f = to (UM.upd k v (from f)). 
Proof. by case: f=>[|f H] //=; case: decP=>// H1; rewrite heapE. Qed.

Lemma domE f : dom f = UM.dom (from f). 
Proof. by case: f. Qed.

Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2). 
Proof. by case: f1 f2=>[|f1 H1][|f2 H2]. Qed.

Lemma freeE k f : free k f = to (UM.free k (from f)). 
Proof. by case: f=>[|f H] //; rewrite heapE. Qed.

Lemma findE k f : find k f = UM.find k (from f).
Proof. by case: f. Qed.

Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. 
case: f1 f2=>[|f1 H1][|f2 H2] //; rewrite /union /UM.union /=. 
by case: ifP=>D //; rewrite heapE.
Qed.

Lemma umfiltE q f : um_filter q f = to (UM.um_filter q (from f)).
Proof. by case: f=>[|f H] //; rewrite heapE. Qed.

Lemma empbE f : empb f = UM.empb (from f). 
Proof. by case: f. Qed.

Lemma undefbE f : undefb f = UM.undefb (from f). 
Proof. by case: f. Qed.

Lemma ptsE k (v : dynamic id) : pts k v = to (@UM.pts _ _ _ k v).
Proof. 
by rewrite /pts /UM.pts /UM.upd /=; case: decP=>// H; rewrite heapE. 
Qed.

Module Exports.

(* the inheritance from PCMs *)

Definition heapUMCMix := 
  UMCMixin ftE tfE defE undefE emptyE updE domE dom_eqE freeE
           findE unionE umfiltE empbE undefbE ptsE.
Canonical heapUMC := Eval hnf in UMC heap heapUMCMix.

Definition heapPCMMix := union_map_classPCMMix heapUMC.
Canonical heapPCM := Eval hnf in PCM heap heapPCMMix.

Definition heapCPCMMix := union_map_classCPCMMix heapUMC.
Canonical heapCPCM := Eval hnf in CPCM heap heapCPCMMix.

Definition heapTPCMMix := union_map_classTPCMMix heapUMC.
Canonical heapTPCM := Eval hnf in TPCM heap heapTPCMMix.

End Exports.

End Heap.

Export Heap.Exports.

Notation heap := Heap.heap.

Definition heap_pts A (x : ptr) (v : A) := 
  @UMC.pts _ _ heapUMC x (idyn v).

Notation "x :-> v" := (@heap_pts _ x v) (at level 30).

(*****************************)
(* Specific points-to lemmas *)
(*****************************)

Section HeapPointsToLemmas.
Implicit Types (x : ptr) (h : heap).

Lemma hcancelPtT A1 A2 x (v1 : A1) (v2 : A2) : 
        valid (x :-> v1) -> x :-> v1 = x :-> v2 -> A1 = A2.
Proof. by move=>V /(cancelPt V)/dyn_injT. Qed.

Lemma hcancelPtT2 A1 A2 x1 x2 (v1 : A1) (v2 : A2) : 
        valid (x1 :-> v1) -> x1 :-> v1 = x2 :-> v2 -> (x1, A1) = (x2, A2).
Proof. by move=>V; case/(cancelPt2 V)=>-> E _; rewrite E. Qed.

Lemma hcancelPtV A x (v1 v2 : A) : 
        valid (x :-> v1) -> x :-> v1 = x :-> v2 -> v1 = v2.
Proof. by move=>V; move/(cancelPt V)/dyn_inj. Qed.

Lemma hcancelPtV2 A x1 x2 (v1 v2 : A) : 
        valid (x1 :-> v1) -> x1 :-> v1 = x2 :-> v2 -> (x1, v1) = (x2, v2).
Proof. by move=>V /(cancelPt2 V) [->] /dyn_inj ->. Qed.

Lemma heap_eta x h : 
        x \in dom h -> exists A (v : A), 
        find x h = Some (idyn v) /\ h = x :-> v \+ free x h.
Proof. by case/um_eta; case=>A v H; exists A, v. Qed.

Lemma heap_eta2 A x h (v : A) : 
        find x h = Some (idyn v) -> h = x :-> v \+ free x h.
Proof.
move=>E; case: (heap_eta (find_some E))=>B [w][].
rewrite {}E; case=>E; rewrite -E in w *. 
by move/(@inj_pair2 _ _ _ _ _)=>->. 
Qed.

Lemma hcancelT A1 A2 x (v1 : A1) (v2 : A2) h1 h2 : 
        valid (x :-> v1 \+ h1) -> 
        x :-> v1 \+ h1 = x :-> v2 \+ h2 -> A1 = A2.
Proof. by move=>V; case/(cancel V); move/dyn_injT. Qed.

Lemma hcancelV A x (v1 v2 : A) h1 h2 : 
        valid (x :-> v1 \+ h1) -> 
        x :-> v1 \+ h1 = x :-> v2 \+ h2 -> [/\ v1 = v2, valid h1 & h1 = h2].
Proof. by move=>V; case/(cancel V); move/dyn_inj. Qed.

Lemma hcancel2V A x1 x2 (v1 v2 : A) h1 h2 : 
        valid (x1 :-> v1 \+ h1) ->
        x1 :-> v1 \+ h1 = x2 :-> v2 \+ h2 -> 
        if x1 == x2 then v1 = v2 /\ h1 = h2 
        else [/\ free x1 h2 = free x2 h1, 
                 h1 = x2 :-> v2 \+ free x1 h2 &  
                 h2 = x1 :-> v1 \+ free x2 h1].
Proof. by move=>V /(cancel2 V); case: ifP=>// _ [/dyn_inj]. Qed.

End HeapPointsToLemmas.

Prenex Implicits heap_eta2.

(******************************************)
(* additional stuff, on top of union maps *)
(* mostly random stuff, kept for legacy   *)
(* should be removed/redone eventually    *)
(******************************************)

Definition fresh (h : heap) := 
  (if h is Heap.Def hs _ then last null (supp hs) else null) .+ 1.

Definition pick (h : heap) := 
  if h is Heap.Def hs _ then head null (supp hs) else null.

(*********)
(* fresh *)
(*********)

Lemma path_last_nat n s x : path ord x s -> ord x (last x s).+(n+1).
Proof.
move: n s x.
suff L: forall s x, path ord x s -> ord x (last x s).+(1).
- elim=>[|n IH] // s x; move/IH=>E; apply: trans E _. 
  by case: (last x s)=>m; rewrite /ord /= addSn (addnS m).
elim=>[|y s IH x] /=; first by case=>x; rewrite /ord /= addn1.
by case/andP=>H1; move/IH; apply: trans H1.
Qed.

Lemma path_filter (A : ordType) (s : seq A) (p : pred A) x : 
        path ord x s -> path ord x (filter p s).
Proof.
elim: s x=>[|y s IH] x //=.
case/andP=>H1 H2.
case: ifP=>E; first by rewrite /= H1 IH.
apply: IH; elim: s H2=>[|z s IH] //=.
by case/andP=>H2 H3; rewrite (@trans _ y).
Qed.

Lemma dom_fresh h n : (fresh h).+n \notin dom h.
Proof.
suff L2: forall h x, x \in dom h -> ord x (fresh h).
- by apply: (contra (L2 _ _)); rewrite -leqNgt leq_addr. 
case=>[|[s H1]] //; rewrite /supp => /= H2 x.
rewrite /dom /fresh /supp /=. 
elim: s H1 null H2 x=>[|[y d] s IH] //= H1 x.
rewrite inE negb_or; case/andP=>H3 H4 z; rewrite inE.
case/orP; first by move/eqP=>->{z}; apply: (path_last_nat 0).
by apply: IH; [apply: path_sorted H1 | apply: notin_path H1].
Qed.

Lemma fresh_null h : fresh h != null.
Proof. by rewrite -lt0n addn1. Qed.

Opaque fresh.

Hint Resolve dom_fresh fresh_null : core.

(********)
(* pick *)
(********)

Lemma emp_pick (h : heap) : (pick h == null) = (~~ valid h || empb h).
Proof.
rewrite /empb; case: h=>[|h] //=; case: (supp h)=>[|x xs] //=.
by rewrite inE negb_or eq_sym; case/andP; move/negbTE=>->.
Qed.

Lemma pickP h : valid h && ~~ empb h = (pick h \in dom h).
Proof. 
rewrite /dom /empb; case: h=>[|h] //=.
by case: (supp h)=>// *; rewrite inE eq_refl. 
Qed.


(***********************)
(* Some derived lemmas *)
(***********************)

Lemma domPtUnX A (v : A) x i : valid (x :-> v \+ i) -> x \in dom (x :-> v \+ i).
Proof. by move=>D; rewrite domPtUn inE /= D eq_refl. Qed.

Lemma domPtX A (v : A) x : valid (x :-> v) -> x \in dom (x :-> v).
Proof. by move=>D; rewrite -(unitR (x :-> v)) domPtUnX // unitR. Qed.


(*******************************************)
(* Block update for reasoning about arrays *)
(*******************************************)

Section BlockUpdate.
Variable (A : Type).

Fixpoint updi x (vs : seq A) {struct vs} : heap := 
  if vs is v'::vs' then x :-> v' \+ updi (x .+ 1) vs' else Unit.

Lemma updiS x v vs : updi x (v :: vs) = x :-> v \+ updi (x .+ 1) vs.
Proof. by []. Qed.   

Lemma updi_last x v vs : 
        updi x (rcons vs v) = updi x vs \+ x.+(size vs) :-> v.
Proof.
elim: vs x v=>[|w vs IH] x v /=.
- by rewrite ptr0 unitR unitL.
by rewrite -(addn1 (size vs)) addnC -ptrA IH joinA.
Qed.

Lemma updi_cat x vs1 vs2 : 
        updi x (vs1 ++ vs2) = updi x vs1 \+ updi x.+(size vs1) vs2.
Proof.
elim: vs1 x vs2=>[|v vs1 IH] x vs2 /=.
- by rewrite ptr0 unitL.
by rewrite -(addn1 (size vs1)) addnC -ptrA IH joinA.
Qed.

Lemma updi_catI x y vs1 vs2 : 
        y = x.+(size vs1) -> updi x vs1 \+ updi y vs2 = updi x (vs1 ++ vs2).
Proof. by move=>->; rewrite updi_cat. Qed.

(* helper lemma *)
Lemma updiVm' x m xs : m > 0 -> x \notin dom (updi x.+m xs).
Proof. 
elim: xs x m=>[|v vs IH] x m //= H.
rewrite ptrA domPtUn inE /= negb_and negb_or -{4}(ptr0 x) ptrK -lt0n H /=.
by rewrite orbC IH // addn1.
Qed.

Lemma updiD x xs : valid (updi x xs) = (x != null) || (size xs == 0).
Proof.
elim: xs x=>[|v xs IH] x //=; first by rewrite orbC.
by rewrite validPtUn updiVm' // orbF IH ptr_null andbF andbC.
Qed.

Lemma updiVm x m xs : 
        x \in dom (updi x.+m xs) = [&& x != null, m == 0 & size xs > 0].
Proof.
case: m=>[|m] /=; last first.
- by rewrite andbF; apply/negbTE/updiVm'.
case: xs=>[|v xs]; rewrite ptr0 ?andbF ?andbT //=.
by rewrite domPtUn inE /= eq_refl -updiS updiD orbF andbT /=.
Qed.

Lemma updimV x m xs : 
        x.+m \in dom (updi x xs) = (x != null) && (m < size xs).
Proof.
case H: (x == null)=>/=.
- by case: xs=>// a s; rewrite (eqP H).
elim: xs x m H=>[|v vs IH] x m H //; case: m=>[|m].
- by rewrite ptr0 /= domPtUn inE /= eq_refl andbT -updiS updiD H.
rewrite -addn1 addnC -ptrA updiS domPtUn inE /= IH; last first.
- by rewrite ptrE /= addn1.
by rewrite -updiS updiD H /= -{1}(ptr0 x) ptrA ptrK. 
Qed.

Lemma updiP x y xs : 
        reflect (y != null /\ exists m, x = y.+m /\ m < size xs) 
                (x \in dom (updi y xs)).
Proof.
case H: (y == null)=>/=.
- by rewrite (eqP H); elim: xs=>[|z xs IH] //=; constructor; case.
case E: (x \in _); constructor; last first.
- by move=>[_][m][H1] H2; rewrite H1 updimV H2 H in E.
case: (ptrT x y) E=>m; case/orP; move/eqP=>->.
- by rewrite updimV H /= => H1; split=>//; exists m.
rewrite updiVm; case/and3P=>H1; move/eqP=>-> H2.
by split=>//; exists 0; rewrite ptrA addn0 ptr0.
Qed.

(* Invertibility *)
Lemma updi_inv x xs1 xs2 : 
        valid (updi x xs1) -> updi x xs1 = updi x xs2 -> xs1 = xs2.
Proof.
elim: xs1 x xs2 =>[|v1 xs1 IH] x /=; case=>[|v2 xs2] //= D;
[move/esym| |]; try by rewrite empbE empbUn empbPt.
by case/(hcancelV D)=><- {D} D /(IH _ _ D) <-.
Qed.

Lemma updi_iinv x xs1 xs2 h1 h2 : 
        size xs1 = size xs2 -> valid (updi x xs1 \+ h1) ->        
        updi x xs1 \+ h1 = updi x xs2 \+ h2 -> xs1 = xs2 /\ h1 = h2.
Proof.
elim: xs1 x xs2 h1 h2=>[|v1 xs1 IH] x /=; case=>[|v2 xs2] //= h1 h2.
- by rewrite !unitL.
move=>[E]; rewrite -!joinA=>D; case/(hcancelV D)=><- {D} D.
by case/(IH _ _ _ _ E D)=>->->.
Qed.

End BlockUpdate. 

Lemma domeqUP A1 A2 x (xs1 : seq A1) (xs2 : seq A2) : 
        size xs1 = size xs2 -> dom_eq (updi x xs1) (updi x xs2).
Proof.
move=>E; apply/domeqP; split; first by rewrite !updiD E. 
move=>z; case: updiP=>[[H][m][->]|X]; first by rewrite updimV H E.
by case: updiP=>// [[H]][m][Ez S]; elim: X; split=>//; exists m; rewrite Ez E.
Qed.

(*************************************)
(* the automation of the PtUn lemmas *)
(*************************************)

(* First, the mechanism for search-and-replace for the overloaded lemas, *)
(* pattern-matching on heap expressions.                                 *)

Structure tagged_heap := Tag {untag :> heap}.

Definition right_tag := Tag.
Definition left_tag := right_tag.
Canonical found_tag i := left_tag i.

Definition partition_axiom k r (h : tagged_heap) := untag h = k \+ r.

Structure partition (k r : heap) :=
  Partition {heap_of :> tagged_heap; 
             _ : partition_axiom k r heap_of}.

Lemma partitionE r k (f : partition k r) : untag f = k \+ r.
Proof. by case: f=>[[j]] /=; rewrite /partition_axiom /= => ->. Qed.

Lemma found_pf k : partition_axiom k Unit (found_tag k). 
Proof. by rewrite /partition_axiom unitR. Qed.

Canonical found_struct k := Partition (found_pf k).

Lemma left_pf h r (f : forall k, partition k r) k : 
        partition_axiom k (r \+ h) (left_tag (untag (f k) \+ h)).
Proof. by rewrite partitionE /partition_axiom /= joinA. Qed.

Canonical left_struct h r (f : forall k, partition k r) k :=
  Partition (left_pf h f k).

Lemma right_pf h r (f : forall k, partition k r) k :
        partition_axiom k (h \+ r) (right_tag (h \+ f k)).
Proof. by rewrite partitionE /partition_axiom /= joinCA. Qed.

Canonical right_struct h r (f : forall k, partition k r) k := 
  Partition (right_pf h f k).

(* now the actual lemmas *)

Lemma defPtUnO A h x (v : A) (f : partition (x :-> v) h) : 
        valid (untag f) = [&& x != null, valid h & x \notin dom h].
Proof. by rewrite partitionE validPtUn. Qed.

Arguments defPtUnO [A][h] x [v][f].

Lemma defPt_nullO A h x (v : A) (f : partition (x :-> v) h) : 
        valid (untag f) -> x != null.
Proof. by rewrite partitionE; apply: validPtUn_cond. Qed.

Arguments defPt_nullO [A h x v f] _.

Lemma defPt_defO A h x (v : A) (f : partition (x :-> v) h) : 
        valid (untag f) -> valid h.
Proof. by rewrite partitionE; apply: validPtUnV. Qed.

Arguments defPt_defO [A][h] x [v][f] _.

Lemma defPt_domO A h x (v : A) (f : partition (x :-> v) h) : 
        valid (untag f) -> x \notin dom h.
Proof. by rewrite partitionE; apply: validPtUnD. Qed.

Arguments defPt_domO [A][h] x [v][f] _.

Lemma domPtUnO A h x (v : A) (f : partition (x :-> v) h) : 
        dom (untag f) =i 
        [pred y | valid (untag f) & (x == y) || (y \in dom h)].
Proof. by rewrite partitionE; apply: domPtUn. Qed.

Arguments domPtUnO [A][h] x [v][f] _.

Lemma lookPtUnO A h x (v : A) (f : partition (x :-> v) h) : 
        valid (untag f) -> find x (untag f) = Some (idyn v).
Proof. by rewrite partitionE; apply: findPtUn. Qed.

Arguments lookPtUnO [A h x v f] _.

Lemma freePtUnO A h x (v : A) (f : partition (x :-> v) h) : 
        valid (untag f) -> free x (untag f) = h.
Proof. by rewrite partitionE; apply: freePtUn. Qed.

Arguments freePtUnO [A h x v f] _.

Lemma updPtUnO A1 A2 x i (v1 : A1) (v2 : A2) 
               (f : forall k, partition k i) : 
        upd x (idyn v2) (untag (f (x :-> v1))) = f (x :-> v2). 
Proof. by rewrite !partitionE; apply: updPtUn. Qed.

Arguments updPtUnO [A1 A2 x i v1 v2] f.

Lemma cancelTO A1 A2 h1 h2 x (v1 : A1) (v2 : A2) 
               (f1 : partition (x :-> v1) h1) 
               (f2 : partition (x :-> v2) h2) : 
        valid (untag f1) -> f1 = f2 :> heap -> A1 = A2. 
Proof. by rewrite !partitionE; apply: hcancelT. Qed.

Arguments cancelTO [A1 A2 h1 h2] x [v1 v2 f1 f2] _ _.

Lemma cancelO A h1 h2 x (v1 v2 : A) 
              (f1 : partition (x :-> v1) h1) 
              (f2 : partition (x :-> v2) h2) : 
        valid (untag f1) -> f1 = f2 :> heap -> 
        [/\ v1 = v2, valid h1 & h1 = h2].
Proof. by rewrite !partitionE; apply: hcancelV. Qed.

Arguments cancelO [A h1 h2] x [v1 v2 f1 f2] _ _.

Lemma domPtUnXO A (v : A) x i (f : partition (x :-> v) i) : 
        valid (untag f) -> x \in dom (untag f).
Proof. by rewrite partitionE; apply: domPtUnX. Qed.


(*******************************************************)
(*******************************************************)
(* Custom lemmas about singly-linked lists in the heap *)
(*******************************************************)
(*******************************************************)

Fixpoint llist A p (xs : seq A) {struct xs} := 
  if xs is x::xt then 
    fun h => exists r h', h = p :-> (x, r) \+ h' /\ llist r xt h'
  else fun h : heap => p = null /\ h = Unit.

Lemma llist_prec A p (l1 l2 : seq A) h1 h2 g1 g2 :
        valid (h1 \+ g1) ->
        llist p l1 h1 -> llist p l2 h2 -> 
        h1 \+ g1 = h2 \+ g2 -> 
        [/\ l1 = l2, h1 = h2 & g1 = g2].
Proof.
move=>V H1 H2 E; elim: l1 l2 h1 h2 p H1 H2 E V=>[|a1 l1 IH].
- case=>[|a2 l2] h1 h2 p /= [->->].
  - by case=>_ ->; rewrite !unitL. 
  by case=>r [h'][-> _ ->] /validL /validPtUn_cond. 
case=>[|a2 l2] h1 h2 p /= [p1][k1][-> H1].
- by case=>->-> _ /validL /validPtUn_cond. 
case=>p2 [k2][-> H2]; rewrite -!joinA => E V.
case: {E V} (hcancelV V E) H1 H2; case=>->-> V E H1 H2. 
by case: (IH _ _ _ _ H1 H2 E V)=>->->->. 
Qed.

Lemma first_exists A p h (ls : seq A) : 
        p != null -> llist p ls h ->
        exists x r h', 
          [/\ ls = x :: behead ls, h = p :-> (x, r) \+ h' & 
              llist r (behead ls) h'].
Proof.
case: ls=>[|a ls] /= H []; first by case: eqP H.
by move=>r [h'][-> H1]; eexists a, r, h'.
Qed.

Lemma llist_null A (xs : seq A) h : 
        valid h -> llist null xs h -> xs = [::] /\ h = Unit.
Proof.
case: xs=>[|x xs] /= V H; first by case: H.
by case: H V=>p [h'][-> _] /validPtUn_cond.
Qed. 

(******************************)
(******************************)
(* Custom lemmas about arrays *)
(******************************)
(******************************)

From mathcomp Require Import fintype tuple finfun.

Definition indx {I : finType} (x : I) := index x (enum I).

Prenex Implicits indx.

(***********************************)
(* Arrays indexed by a finite type *)
(***********************************)

Section Array.
Variables (p : ptr) (I : finType).
 
(* helper lemmas *)

Lemma enum_split k : 
        enum I = take (indx k) (enum I) ++ k :: drop (indx k).+1 (enum I). 
Proof.
rewrite -{2}(@nth_index I k k (enum I)) ?mem_enum //.
by rewrite -drop_nth ?index_mem ?mem_enum // cat_take_drop.
Qed.

Lemma updi_split T k (f : {ffun I -> T}) : 
        updi p (fgraph f) = updi p (take (indx k) (fgraph f)) \+ 
                            p.+(indx k) :-> f k \+ 
                            updi (p.+(indx k).+1) (drop (indx k).+1 (fgraph f)).
Proof.
rewrite fgraph_codom /= codomE {1}(enum_split k) map_cat updi_cat /=.
rewrite map_take map_drop size_takel ?joinA ?ptrA ?addn1 //.
by rewrite size_map index_size.
Qed.

Lemma takeord T k x (f : {ffun I -> T}) : 
        take (indx k) (fgraph [ffun y => [eta f with k |-> x] y]) = 
        take (indx k) (fgraph f).
Proof. 
set f' := (finfun _).
suff E: {in take (indx k) (enum I), f =1 f'}.
- by rewrite !fgraph_codom /= !codomE -2!map_take; move/eq_in_map: E. 
move: (enum_uniq I); rewrite {1}(enum_split k) cat_uniq /= =>H4. 
move=>y H5; rewrite /f' /= !ffunE /=; case: eqP H5 H4=>// -> ->.
by rewrite andbF.
Qed.

Lemma dropord T k x (f : {ffun I -> T}) :
        drop (indx k).+1 (fgraph [ffun y => [eta f with k |->x] y]) = 
        drop (indx k).+1 (fgraph f).
Proof.
set f' := (finfun _).
suff E: {in drop (indx k).+1 (enum I), f =1 f'}.
- by rewrite !fgraph_codom /= !codomE -2!map_drop; move/eq_in_map: E.
move: (enum_uniq I); rewrite {1}(enum_split k) cat_uniq /= => H4.
move=>y H5; rewrite /f' /= !ffunE /=; case: eqP H5 H4=>// -> ->.
by rewrite !andbF.
Qed.    

Lemma size_fgraph T1 T2 (r1 : {ffun I -> T1}) (r2 : {ffun I -> T2}) : 
        size (fgraph r1) = size (fgraph r2).
Proof. by rewrite !fgraph_codom /= !codomE !size_map. Qed.

Lemma fgraphE T (r1 r2 : {ffun I -> T}) : 
        fgraph r1 = fgraph r2 -> r1 = r2.
Proof. by case: r1; case=>r1 H1; case: r2; case=>r2 H2 /= ->. Qed.

End Array.


(*
Copyright 2013 IMDEA Software Institute
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

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path.
From fcsl Require Import ordtype finmap pcm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* This file contains the reference implementation of finite maps with keys   *)
(* satisfying condition p and supporting disjoint union via a top element.    *)
(******************************************************************************)

(* I decided to have union_map_class be a class, rather than a
structure. The class packages a condition on keys. Ordinary union_maps
have a trivially true condition. Heaps have a condition that the
pointers are non-null.  Then ordinary union maps, as well as heaps,
are declared as instances of this class, to automatically inherit all
the lemmas about the operations.

An alternative implementation would have been to define
union_map_class as a structure parametrized by the condition, and then
obtain heaps by taking the parameter condition of non-null pointers,
and ordinary union_maps by taking parameter condition to true.

I decided on the more complicated design to avoid the universe
jump. Heap values are dynamic, and live in Type(1), while most of the
times, ordinary union_maps store values from Type(0), and can be
nested. If the two structures (heaps and ordinary union maps) share
the same code, they will both lift to the common universe of Type(1),
preventing me from using maps at Type(0), and storing them in the heap.

With the class design, no code is shared, only the lemmas (i.e., only
the class type, but that can freely live in an arbitrary
universe). The price to pay is that the code of the methods has to be
duplicated when declaring instances (such as in heaps.v, or below for
union_mapUMC), just to keep the universes from jumping.  *)

Module UM.
Section UM.
Variables (K : ordType) (V : Type) (p : pred K).

Inductive base := 
  Undef | Def (f : {finMap K -> V}) of all p (supp f).

Section FormationLemmas.
Variable (f g : {finMap K -> V}). 

Lemma all_supp_insP k v : p k -> all p (supp f) -> all p (supp (ins k v f)).
Proof.
move=>H1 H2; apply/allP=>x; rewrite supp_ins inE /=.
by case: eqP=>[->|_] //=; move/(allP H2). 
Qed.

Lemma all_supp_remP k : all p (supp f) -> all p (supp (rem k f)). 
Proof. 
move=>H; apply/allP=>x; rewrite supp_rem inE /=.
by case: eqP=>[->|_] //=; move/(allP H).
Qed.

Lemma all_supp_fcatP : 
        all p (supp f) -> all p (supp g) -> all p (supp (fcat f g)).
Proof.
move=>H1 H2; apply/allP=>x; rewrite supp_fcat inE /=.
by case/orP; [move/(allP H1) | move/(allP H2)].
Qed.

Lemma all_supp_kfilterP q : 
        all p (supp f) -> all p (supp (kfilter q f)). 
Proof.
move=>H; apply/allP=>x; rewrite supp_kfilt mem_filter. 
by case/andP=>_ /(allP H).
Qed.

End FormationLemmas.

Implicit Types (k : K) (v : V) (f g : base).

Lemma umapE (f g : base) : 
        f = g <-> match f, g with
                     Def f' pf, Def g' pg => f' = g'
                  | Undef, Undef => true
                  | _, _ => false
                  end.
Proof.
split; first by move=>->; case: g.
case: f; case: g=>// f pf g pg E; rewrite {g}E in pg *.
by congr Def; apply: bool_irrelevance.
Qed.

Definition valid f := if f is Def _ _ then true else false.

Definition empty := @Def (finmap.nil K V) is_true_true.

Definition upd k v f := 
  if f is Def fs fpf then 
    if decP (@idP (p k)) is left pf then 
      Def (all_supp_insP v pf fpf)
    else Undef
  else Undef.

Definition dom f : seq K := 
  if f is Def fs _ then supp fs else [::].

Definition dom_eq f1 f2 :=
  match f1, f2 with
    Def fs1 _, Def fs2 _ => supp fs1 == supp fs2
  | Undef, Undef => true
  | _, _ => false
  end.

Definition free k f := 
  if f is Def fs pf then Def (all_supp_remP k pf) else Undef.

Definition find k f := if f is Def fs _ then fnd k fs else None. 

Definition union f1 f2 := 
  if (f1, f2) is (Def fs1 pf1, Def fs2 pf2) then  
    if disj fs1 fs2 then 
      Def (all_supp_fcatP pf1 pf2)
    else Undef
  else Undef.

Definition um_filter q f := 
  if f is Def fs pf then Def (all_supp_kfilterP q pf) else Undef.

Definition empb f := if f is Def fs _ then supp fs == [::] else false. 

Definition undefb f := if f is Undef then true else false.

Definition pts k v := upd k v empty.

(* forward induction *)
Lemma base_indf (P : base -> Prop) : 
         P Undef -> P empty ->
         (forall k v f, P f -> valid (union (pts k v) f) -> 
                        path ord k (dom f) ->
                        P (union (pts k v) f)) ->
         forall f, P f.
Proof.
rewrite /empty => H1 H2 H3; apply: base_ind=>//. 
apply: fmap_ind'=>[|k v f S IH] H. 
- by set f := Def _ in H2; rewrite (_ : Def H = f) // /f umapE.
have N : k \notin supp f by apply: notin_path S.
have [T1 T2] : p k /\ all p (supp f).
- split; first by apply: (allP H k); rewrite supp_ins inE /= eq_refl.
- apply/allP=>x T; apply: (allP H x).  
  by rewrite supp_ins inE /= T orbT. 
have E : FinMap (sorted_ins' k v (sorted_nil K V)) = ins k v (@nil K V) by [].
have: valid (union (pts k v) (Def T2)).
- rewrite /valid /union /pts /upd /=.
  case: decP; last by rewrite T1.
  by move=>T; case: ifP=>//; rewrite E disjC disj_ins N disj_nil.
move/(H3 k v _ (IH T2)).
rewrite (_ : union (pts k v) (Def T2) = Def H).
- by apply. 
rewrite umapE /union /pts /upd /=.
case: decP=>// T; rewrite /disj /= N /=.
by rewrite E fcat_inss // fcat0s.
Qed.

(* backward induction *)
Lemma base_indb (P : base -> Prop) : 
         P Undef -> P empty ->
         (forall k v f, P f -> valid (union (pts k v) f) -> 
                        (forall x, x \in dom f -> ord x k) ->
                        P (union (pts k v) f)) ->
         forall f, P f.
Proof.
rewrite /empty => H1 H2 H3; apply: base_ind=>//. 
apply: fmap_ind''=>[|k v f S IH] H. 
- by set f := Def _ in H2; rewrite (_ : Def H = f) // /f umapE.
have N : k \notin supp f by apply/negP; move/S; rewrite ordtype.irr. 
have [T1 T2] : p k /\ all p (supp f).
- split; first by apply: (allP H k); rewrite supp_ins inE /= eq_refl.
- apply/allP=>x T; apply: (allP H x).  
  by rewrite supp_ins inE /= T orbT. 
have E : FinMap (sorted_ins' k v (sorted_nil K V)) = ins k v (@nil K V) by [].
have: valid (union (pts k v) (Def T2)).
- rewrite /valid /union /pts /upd /=.
  case: decP; last by rewrite T1.
  by move=>T; case: ifP=>//; rewrite E disjC disj_ins N disj_nil.
move/(H3 k v _ (IH T2)).
rewrite (_ : union (pts k v) (Def T2) = Def H); first by apply; apply: S. 
rewrite umapE /union /pts /upd /=.
case: decP=>// T; rewrite /disj /= N /=.
by rewrite E fcat_inss // fcat0s.
Qed.

End UM.
End UM.

(* a class of union_map types *)

Module UMC.
Section MixinDef.
Variables (K : ordType) (V : Type) (p : pred K).

Structure mixin_of (T : Type) := Mixin {
  defined_op : T -> bool;
  empty_op : T;
  undef_op : T;
  upd_op : K -> V -> T -> T;
  dom_op : T -> seq K;
  dom_eq_op : T -> T -> bool;
  free_op : K -> T -> T;
  find_op : K -> T -> option V;
  union_op : T -> T -> T;
  um_filter_op : pred K -> T -> T;
  empb_op : T -> bool;
  undefb_op : T -> bool;
  pts_op : K -> V -> T;

  from_op : T -> UM.base V p;
  to_op : UM.base V p -> T;
  _ : forall b, from_op (to_op b) = b;
  _ : forall f, to_op (from_op f) = f;
  _ : forall f, defined_op f = UM.valid (from_op f);
  _ : undef_op = to_op (UM.Undef V p);
  _ : empty_op = to_op (UM.empty V p);
  _ : forall k v f, upd_op k v f = to_op (UM.upd k v (from_op f));
  _ : forall f, dom_op f = UM.dom (from_op f);
  _ : forall f1 f2, dom_eq_op f1 f2 = UM.dom_eq (from_op f1) (from_op f2);
  _ : forall k f, free_op k f = to_op (UM.free k (from_op f));
  _ : forall k f, find_op k f = UM.find k (from_op f);
  _ : forall f1 f2, 
        union_op f1 f2 = to_op (UM.union (from_op f1) (from_op f2));
  _ : forall q f, um_filter_op q f = to_op (UM.um_filter q (from_op f));
  _ : forall f, empb_op f = UM.empb (from_op f);
  _ : forall f, undefb_op f = UM.undefb (from_op f);
  _ : forall k v, pts_op k v = to_op (UM.pts p k v)}.
End MixinDef.

Section ClassDef.
Variables (K : ordType) (V : Type).

(* I used to package K and V into the class. I did that to get cond
function over keys to work without supplying the type parameter. I.e.,
with K and V out, I have to write cond U k, where U : union_map_class
K V. But the complication wasn't worth it. One has to frequently
reorder arguments to various operations in a "less-ad-hoc" style, to
get the types to be inferred properly. While fun, it's just an
unnecessary hassle, since cond is not used that much. The condition p
can be kept in the structure, however, since no types depend on it. *)

Structure class_of (T : Type) := Class {
  p : pred K;
  mixin : mixin_of V p T}.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Definition pack p (m : @mixin_of K V p T) := 
  @Pack T (@Class T p m).

(* Definition cond : pred K := @p _ class. *)
Definition cond := [pred x : K | @p _ class x].
Definition from := from_op (mixin class).
Definition to := to_op (mixin class).
Definition defined := defined_op (mixin class).
Definition um_undef := undef_op (mixin class).
Definition empty := empty_op (mixin class).
Definition upd : K -> V -> cT -> cT := upd_op (mixin class).
Definition dom : cT -> seq K := dom_op (mixin class).
Definition dom_eq := dom_eq_op (mixin class).
Definition free : K -> cT -> cT := free_op (mixin class).
Definition find : K -> cT -> option V := find_op (mixin class).
Definition union := union_op (mixin class).
Definition um_filter : pred K -> cT -> cT := um_filter_op (mixin class).
Definition empb := empb_op (mixin class).
Definition undefb := undefb_op (mixin class).
Definition pts : K -> V -> cT := pts_op (mixin class).

End ClassDef.

Arguments um_undef [K V cT].
Arguments empty [K V cT].
Arguments pts [K V cT] _ _.
Prenex Implicits to um_undef empty pts.

Section Lemmas.
Variables (K : ordType) (V : Type) (U : type K V).
Local Coercion sort : type >-> Sortclass.
Implicit Type f : U.

Lemma ftE (b : UM.base V (cond U)) : from (to b) = b.
Proof. by case: U b=>x [p][*]. Qed.

Lemma tfE f : to (from f) = f.
Proof. by case: U f=>x [p][*]. Qed.

Lemma eqE (b1 b2 : UM.base V (cond U)) : 
        to b1 = to b2 <-> b1 = b2. 
Proof. by split=>[E|-> //]; rewrite -[b1]ftE -[b2]ftE E. Qed.

Lemma defE f : defined f = UM.valid (from f).
Proof. by case: U f=>x [p][*]. Qed.

Lemma undefE : um_undef = to (UM.Undef V (cond U)).
Proof. by case: U=>x [p][*]. Qed.

Lemma emptyE : empty = to (UM.empty V (cond U)).
Proof. by case: U=>x [p][*]. Qed.

Lemma updE k v f : upd k v f = to (UM.upd k v (from f)).
Proof. by case: U k v f=>x [p][*]. Qed.

Lemma domE f : dom f = UM.dom (from f).
Proof. by case: U f=>x [p][*]. Qed.

Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Proof. by case: U f1 f2=>x [p][*]. Qed.

Lemma freeE k f : free k f = to (UM.free k (from f)).
Proof. by case: U k f=>x [p][*]. Qed.

Lemma findE k f : find k f = UM.find k (from f).
Proof. by case: U k f=>x [p][*]. Qed.

Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by case: U f1 f2=>x [p][*]. Qed.

Lemma um_filterE q f : um_filter q f = to (UM.um_filter q (from f)).
Proof. by case: U q f=>x [p][*]. Qed.

Lemma empbE f : empb f = UM.empb (from f).
Proof. by case: U f=>x [p][*]. Qed.

Lemma undefbE f : undefb f = UM.undefb (from f).
Proof. by case: U f=>x [p][*]. Qed.

Lemma ptsE k v : pts k v = to (UM.pts (cond U) k v).
Proof. by case: U k v=>x [p][*]. Qed.

End Lemmas.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation union_map_class := type.
Notation UMCMixin := Mixin.
Notation UMC T m := (@pack _ _ T _  m).

Notation "[ 'umcMixin' 'of' T ]" := (mixin (class _ _ _ : class_of T))
  (at level 0, format "[ 'umcMixin'  'of'  T ]") : form_scope.
Notation "[ 'um_class' 'of' T 'for' C ]" := (@clone _ _ T C _ id)
  (at level 0, format "[ 'um_class'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'um_class' 'of' T ]" := (@clone _ _ T _ _ id)
  (at level 0, format "[ 'um_class'  'of'  T ]") : form_scope.

Notation cond := cond.
Notation um_undef := um_undef.
Notation upd := upd.
Notation dom := dom.
Notation dom_eq := dom_eq.
Notation free := free.
Notation find := find.
Notation um_filter := um_filter.
Notation empb := empb.
Notation undefb := undefb.
Notation pts := pts.

Definition umEX := 
  (ftE, tfE, eqE, undefE, defE, emptyE, updE, domE, dom_eqE, 
   freeE, findE, unionE, um_filterE, empbE, undefbE, ptsE, UM.umapE).

End Exports.

End UMC.

Export UMC.Exports.


(***********************)
(* monoidal properties *)
(***********************)

Module UnionMapClassPCM.
Section UnionMapClassPCM.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Type f : U.

Local Notation "f1 \+ f2" := (@UMC.union _ _ _ f1 f2) 
  (at level 43, left associativity).
Local Notation valid := (@UMC.defined _ _ U).
Local Notation unit := (@UMC.empty _ _ U).

Lemma joinC f1 f2 : f1 \+ f2 = f2 \+ f1.
Proof.
rewrite !umEX /UM.union.
case: (UMC.from f1)=>[|f1' H1]; case: (UMC.from f2)=>[|f2' H2] //.
by case: ifP=>E; rewrite disjC E // fcatC.
Qed.

Lemma joinCA f1 f2 f3 : f1 \+ (f2 \+ f3) = f2 \+ (f1 \+ f3).
Proof.
rewrite !umEX /UM.union /=.
case: (UMC.from f1) (UMC.from f2) (UMC.from f3)=>[|f1' H1][|f2' H2][|f3' H3] //.
case E1: (disj f2' f3'); last first.
- by case E2: (disj f1' f3')=>//; rewrite disj_fcat E1 andbF.
rewrite disj_fcat andbC.
case E2: (disj f1' f3')=>//; rewrite disj_fcat (disjC f2') E1 /= andbT.
by case E3: (disj f1' f2')=>//; rewrite fcatAC // E1 E2 E3.
Qed.

Lemma joinA f1 f2 f3 : f1 \+ (f2 \+ f3) = (f1 \+ f2) \+ f3.
Proof. by rewrite (joinC f2) joinCA joinC. Qed.

Lemma validL f1 f2 : valid (f1 \+ f2) -> valid f1.
Proof. by rewrite !umEX; case: (UMC.from f1). Qed.

Lemma unitL f : unit \+ f = f.
Proof. 
rewrite -[f]UMC.tfE !umEX /UM.union /UM.empty.
by case: (UMC.from f)=>[//|f' H]; rewrite disjC disj_nil fcat0s.
Qed.

Lemma validU : valid unit. 
Proof. by rewrite !umEX. Qed.

End UnionMapClassPCM.

Module Exports.
Section Exports.
Variables (K : ordType) (V : Type) (U : union_map_class K V).

(* generic structure for PCM for *all* union maps *)
(* I will add specific ones too for individual types *)
(* so that the projections can match against a concrete type *)
(* not against another projection, as is the case *)
(* with the generic class here *)
Definition union_map_classPCMMix := 
  PCMMixin (@joinC K V U) (@joinA K V U) (@unitL K V U)
           (@validL K V U) (validU U).
Canonical union_map_classPCM := Eval hnf in PCM U union_map_classPCMMix.

End Exports.
End Exports.

End UnionMapClassPCM.

Export UnionMapClassPCM.Exports.


(*****************)
(* Cancelativity *)
(*****************)

Module UnionMapClassCPCM.
Section Cancelativity.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Type f : U.

Lemma joinKf f1 f2 f : valid (f1 \+ f) -> f1 \+ f = f2 \+ f -> f1 = f2.
Proof.
rewrite -{3}[f1]UMC.tfE -{2}[f2]UMC.tfE !pcmE /= !umEX /UM.valid /UM.union.
case: (UMC.from f) (UMC.from f1) (UMC.from f2)=>
[|f' H]; case=>[|f1' H1]; case=>[|f2' H2] //;
case: ifP=>//; case: ifP=>// D1 D2 _ E.  
by apply: fcatsK E; rewrite D1 D2.
Qed.

End Cancelativity.

Module Exports.
Section Exports.
Variables (K : ordType) (V : Type) (U : union_map_class K V).

Definition union_map_classCPCMMix := CPCMMixin (@joinKf K V U).
Canonical union_map_classCPCM := Eval hnf in CPCM U union_map_classCPCMMix.

End Exports.
End Exports.

End UnionMapClassCPCM.

Export UnionMapClassCPCM.Exports.

(*********************************************************)
(* if V is an equality type, then union_map_class is too *)
(*********************************************************)

Module UnionMapEq. 
Section UnionMapEq. 
Variables (K : ordType) (V : eqType) (p : pred K).
Variables (T : Type) (m : @UMC.mixin_of K V p T).

Definition unionmap_eq (f1 f2 : UMC T m) := 
  match (UMC.from f1), (UMC.from f2) with 
  | UM.Undef, UM.Undef => true
  | UM.Def f1' pf1, UM.Def f2' pf2 => f1' == f2'
  | _, _ => false
  end. 

Lemma unionmap_eqP : Equality.axiom unionmap_eq.
Proof.
move=>x y; rewrite -{1}[x]UMC.tfE -{1}[y]UMC.tfE /unionmap_eq.
case: (UMC.from x)=>[|f1 H1]; case: (UMC.from y)=>[|f2 H2] /=.
- by constructor. 
- by constructor; move/(@UMC.eqE _ _ (UMC T m)). 
- by constructor; move/(@UMC.eqE _ _ (UMC T m)). 
case: eqP=>E; constructor; rewrite (@UMC.eqE _ _ (UMC T m)).
- by rewrite UM.umapE.
by case.
Qed.

End UnionMapEq.

Module Exports.
Section Exports.
Variables (K : ordType) (V : eqType) (p : pred K).
Variables (T : Type) (m : @UMC.mixin_of K V p T).

Definition union_map_class_eqMix := EqMixin (@unionmap_eqP K V p T m).

End Exports.
End Exports.

End UnionMapEq.

Export UnionMapEq.Exports.


(*******)
(* dom *)
(*******)

Section DomLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f g : U).

Lemma dom_undef : dom (um_undef : U) = [::].
Proof. by rewrite !umEX. Qed.

Lemma dom0 : dom (Unit : U) = [::].
Proof. by rewrite pcmE /= !umEX. Qed.

Lemma dom0E f : valid f -> dom f =i pred0 -> f = Unit. 
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.dom /UM.empty -{3}[f]UMC.tfE.
case: (UMC.from f)=>[|f' S] //= _; rewrite !umEX fmapE /= {S}.
by case: f'; case=>[|kv s] //= P /= /(_ kv.1); rewrite inE eq_refl. 
Qed.

Lemma domU k v f : 
        dom (upd k v f) =i 
        [pred x | cond U k & if x == k then valid f else x \in dom f].
Proof.
rewrite pcmE /= !umEX /UM.dom /UM.upd /UM.valid /= /cond.
case: (UMC.from f)=>[|f' H] /= x.
- by rewrite !inE /= andbC; case: ifP.
case: decP; first by move=>->; rewrite supp_ins.
by move/(introF idP)=>->. 
Qed.

Lemma domF k f : 
        dom (free k f) =i 
        [pred x | if k == x then false else x \in dom f].
Proof.
rewrite !umEX; case: (UMC.from f)=>[|f' H] x; rewrite inE /=; 
by case: ifP=>// E; rewrite supp_rem inE /= eq_sym E.
Qed.

Lemma domUn f1 f2 :
        dom (f1 \+ f2) =i
        [pred x | valid (f1 \+ f2) & (x \in dom f1) || (x \in dom f2)].
Proof.
rewrite !pcmE /= !umEX /UM.dom /UM.valid /UM.union.
case: (UMC.from f1) (UMC.from f2)=>[|f1' H1] // [|f2' H2] // x.
by case: ifP=>E //; rewrite supp_fcat.
Qed.

Lemma dom_valid k f : k \in dom f -> valid f.
Proof. by rewrite pcmE /= !umEX; case: (UMC.from f). Qed.

Lemma dom_cond k f : k \in dom f -> cond U k.
Proof. by rewrite !umEX; case: (UMC.from f)=>[|f' F] // /(allP F). Qed.

Lemma dom_inIL k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f1 -> k \in dom (f1 \+ f2).
Proof. by rewrite domUn inE => ->->. Qed.

Lemma dom_inIR k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f2 -> k \in dom (f1 \+ f2).
Proof. by rewrite joinC; apply: dom_inIL. Qed.

Lemma dom_NNL k f1 f2 :
        valid (f1 \+ f2) -> k \notin dom (f1 \+ f2) -> k \notin dom f1.
Proof. by move=> D; apply/contra/dom_inIL. Qed.

Lemma dom_NNR k f1 f2 :
        valid (f1 \+ f2) -> k \notin dom (f1 \+ f2) -> k \notin dom f2.
Proof. by move=> D; apply/contra/dom_inIR. Qed.

Lemma dom_free k f : k \notin dom f -> free k f = f.
Proof. 
rewrite -{3}[f]UMC.tfE !umEX /UM.dom /UM.free.
by case: (UMC.from f)=>[|f' H] //; apply: rem_supp.
Qed.

CoInductive dom_find_spec k f : bool -> Type := 
| dom_find_none' : find k f = None -> dom_find_spec k f false
| dom_find_some' v : find k f = Some v -> 
    f = upd k v (free k f) -> dom_find_spec k f true.

Lemma dom_find k f : dom_find_spec k f (k \in dom f).
Proof.
rewrite !umEX /UM.dom -{1}[f]UMC.tfE.
case: (UMC.from f)=>[|f' H]. 
- by apply: dom_find_none'; rewrite !umEX.
case: suppP (allP H k)=>[v|] H1 I; last first.
- by apply: dom_find_none'; rewrite !umEX. 
apply: (dom_find_some' (v:=v)); rewrite !umEX // /UM.upd /UM.free.
case: decP=>H2; last by rewrite I in H2.
apply/fmapP=>k'; rewrite fnd_ins.
by case: ifP=>[/eqP-> //|]; rewrite fnd_rem => ->. 
Qed.

Lemma find_some k v f : find k f = Some v -> k \in dom f.
Proof. by case: dom_find=>// ->. Qed.

Lemma find_none k f : find k f = None -> k \notin dom f.
Proof. by case: dom_find=>// v ->. Qed.

Lemma dom_umfilt p f : dom (um_filter p f) =i [predI p & dom f].
Proof.
rewrite !umEX /UM.dom /UM.um_filter.
case: (UMC.from f)=>[|f' H] x; first by rewrite !inE /= andbF. 
by rewrite supp_kfilt mem_filter. 
Qed.

Lemma dom_prec f1 f2 g1 g2 : 
        valid (f1 \+ g1) -> 
        f1 \+ g1 = f2 \+ g2 -> 
        dom f1 =i dom f2 -> f1 = f2.
Proof.
rewrite -{4}[f1]UMC.tfE -{3}[f2]UMC.tfE !pcmE /= !umEX.
rewrite /UM.valid /UM.union /UM.dom; move=>D E.
case: (UMC.from f1) (UMC.from f2) (UMC.from g1) (UMC.from g2) E D=>
[|f1' F1][|f2' F2][|g1' G1][|g2' G2] //;
case: ifP=>// D1; case: ifP=>// D2 E _ E1; apply/fmapP=>k.
move/(_ k): E1=>E1. 
case E2: (k \in supp f2') in E1; last first.
- by move/negbT/fnd_supp: E1=>->; move/negbT/fnd_supp: E2=>->.
suff L: forall m s, k \in supp m -> disj m s -> 
          fnd k m = fnd k (fcat m s) :> option V.
- by rewrite (L _ _ E1 D1) (L _ _ E2 D2) E. 
by move=>m s S; case: disjP=>//; move/(_ _ S)/negbTE; rewrite fnd_fcat=>->. 
Qed.

Lemma domK f1 f2 g1 g2 : 
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        dom (f1 \+ g1) =i dom (f2 \+ g2) ->
        dom f1 =i dom f2 -> dom g1 =i dom g2.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2) (UMC.from g1) (UMC.from g2)=>
[|f1' F1][|f2' F2][|g1' G1][|g2' G2] //.
case: disjP=>// D1 _; case: disjP=>// D2 _ E1 E2 x. 
move: {E1 E2} (E2 x) (E1 x); rewrite !supp_fcat !inE /= => E.
move: {D1 D2} E (D1 x) (D2 x)=><- /implyP D1 /implyP D2.
case _ : (x \in supp f1') => //= in D1 D2 *.
by move/negbTE: D1=>->; move/negbTE: D2=>->.
Qed.

Lemma umfilt_dom f1 f2 : 
        valid (f1 \+ f2) -> um_filter (mem (dom f1)) (f1 \+ f2) = f1.
Proof.
rewrite -{4}[f1]UMC.tfE !pcmE /= !umEX.
rewrite /UM.valid /UM.union /UM.um_filter /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// D _; rewrite kfilt_fcat /=.
have E1: {in supp f1', supp f1' =i predT} by [].
have E2: {in supp f2', supp f1' =i pred0}.
- by move=>x; rewrite disjC in D; case: disjP D=>// D _ /D /negbTE ->. 
rewrite (eq_in_kfilter E1) (eq_in_kfilter E2).
by rewrite kfilter_predT kfilter_pred0 fcats0.
Qed.

Lemma sorted_dom f : sorted (@ord K) (dom f).
Proof. by rewrite !umEX; case: (UMC.from f)=>[|[]]. Qed.

Lemma uniq_dom f : uniq (dom f).
Proof. 
apply: sorted_uniq (sorted_dom f); 
by [apply: ordtype.trans | apply: ordtype.irr].
Qed.

Lemma perm_domUn f1 f2 : 
        valid (f1 \+ f2) -> perm_eq (dom (f1 \+ f2)) (dom f1 ++ dom f2). 
Proof.
move=>Vh; apply: uniq_perm_eq; last 1 first. 
- by move=>x; rewrite mem_cat domUn inE Vh.
- by apply: uniq_dom.
rewrite cat_uniq !uniq_dom /= andbT; apply/hasPn=>x.
rewrite !pcmE /= !umEX /UM.valid /UM.union /UM.dom in Vh *.
case: (UMC.from f1) (UMC.from f2) Vh=>// f1' H1 [//|f2' H2].
by case: disjP=>// H _; apply: contraL (H x).
Qed.

Lemma size_domUn f1 f2 : 
        valid (f1 \+ f2) -> 
        size (dom (f1 \+ f2)) = size (dom f1) + size (dom f2).
Proof. by move/perm_domUn/perm_eq_size; rewrite size_cat. Qed.

End DomLemmas.

Hint Resolve sorted_dom uniq_dom : core.
Prenex Implicits find_some find_none.


(**********)
(* filter *)
(**********)

Section FilterLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Type f : U.

Lemma eq_in_umfilt p1 p2 f : 
        {in dom f, p1 =1 p2} -> um_filter p1 f = um_filter p2 f.
Proof.
rewrite !umEX /UM.dom /UM.um_filter /= /dom.
by case: (UMC.from f)=>[|f' H] //=; apply: eq_in_kfilter.
Qed.

Lemma umfilt0 q : um_filter q Unit = Unit :> U.
Proof. by rewrite !pcmE /= !umEX /UM.um_filter /UM.empty kfilt_nil. Qed.

Lemma umfilt_undef q : um_filter q um_undef = um_undef :> U. 
Proof. by rewrite !umEX. Qed.

Lemma umfiltUn q f1 f2 : 
        valid (f1 \+ f2) -> 
        um_filter q (f1 \+ f2) = um_filter q f1 \+ um_filter q f2.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.union.
case: (UMC.from f1)=>[|f1' H1]; case: (UMC.from f2)=>[|f2' H2] //=. 
by case: ifP=>D //= _; rewrite kfilt_fcat disj_kfilt.
Qed.

Lemma umfilt_pred0 f : valid f -> um_filter pred0 f = Unit.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.empty.
case: (UMC.from f)=>[|f' H] //= _; case: f' H=>f' P H.
by rewrite fmapE /= /kfilter' filter_pred0.
Qed.

Lemma umfilt_predT f : um_filter predT f = f.
Proof. 
rewrite -[f]UMC.tfE !umEX /UM.um_filter.
by case: (UMC.from f)=>[|f' H] //; rewrite kfilter_predT.
Qed.

Lemma umfilt_predI p1 p2 f : 
        um_filter (predI p1 p2) f = um_filter p1 (um_filter p2 f).
Proof. 
rewrite -[f]UMC.tfE !umEX /UM.um_filter.
by case: (UMC.from f)=>[|f' H] //; rewrite kfilter_predI.
Qed.

Lemma umfilt_predU p1 p2 f : 
        um_filter (predU p1 p2) f = 
        um_filter p1 f \+ um_filter (predD p2 p1) f.
Proof.
rewrite pcmE /= !umEX /UM.um_filter /UM.union /=.
case: (UMC.from f)=>[|f' H] //=. 
rewrite in_disj_kfilt; last by move=>x _; rewrite /= negb_and orbA orbN. 
rewrite -kfilter_predU.
by apply: eq_in_kfilter=>x _; rewrite /= orb_andr orbN.
Qed.

Lemma umfilt_dpredU f p q : 
        {subset p <= predC q} -> 
        um_filter (predU p q) f = um_filter p f \+ um_filter q f. 
Proof.
move=>D; rewrite umfilt_predU (eq_in_umfilt (p1:=predD q p) (p2:=q)) //.
by move=>k _ /=; case X : (p k)=>//=; move/D/negbTE: X. 
Qed.

Lemma umfiltUnK p f1 f2 : 
        valid (f1 \+ f2) ->    
        um_filter p (f1 \+ f2) = f1 -> 
        um_filter p f1 = f1 /\ um_filter p f2 = Unit. 
Proof.
move=>V'; rewrite (umfiltUn _ V') => E.
have {V'} V' : valid (um_filter p f1 \+ um_filter p f2). 
- by rewrite E; move/validL: V'.
have F : dom (um_filter p f1) =i dom f1.
- move=>x; rewrite dom_umfilt inE /=.
  apply/andP/idP=>[[//]| H1]; split=>//; move: H1.
  rewrite -{1}E domUn inE /= !dom_umfilt inE /= inE /=.
  by case: (x \in p)=>//=; rewrite andbF.
rewrite -{2}[f1]unitR in E F; move/(dom_prec V' E): F=>X.
by rewrite X in E V' *; rewrite (joinxK V' E).
Qed.

Lemma umfiltU p k v f : 
        um_filter p (upd k v f) = 
        if p k then upd k v (um_filter p f) else 
          if cond U k then um_filter p f else um_undef.
Proof. 
rewrite !umEX /UM.um_filter /UM.upd /cond.
case: (UMC.from f)=>[|f' F]; first by case: ifP=>H1 //; case: ifP.
case: ifP=>H1; case: decP=>H2 //=.
- by rewrite !umEX kfilt_ins H1.
- by rewrite H2 !umEX kfilt_ins H1.
by case: ifP H2.
Qed.

Lemma umfiltF p k f : 
        um_filter p (free k f) = 
        if p k then free k (um_filter p f) else um_filter p f.
Proof. 
rewrite !umEX /UM.um_filter /UM.free.
by case: (UMC.from f)=>[|f' F]; case: ifP=>// E; rewrite !umEX kfilt_rem E.
Qed.

End FilterLemmas.


(*********)
(* valid *)
(*********)

Section ValidLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V). 
Implicit Types (k : K) (v : V) (f g : U).

Lemma invalidE f : ~~ valid f <-> f = um_undef.
Proof. by rewrite !pcmE /= !umEX -2![f]UMC.tfE !umEX; case: (UMC.from f). Qed.

Lemma valid_undef : valid (um_undef : U) = false.
Proof. by apply/negbTE; apply/invalidE. Qed.

Lemma validU k v f : valid (upd k v f) = cond U k && valid f.
Proof. 
rewrite !pcmE /= !umEX /UM.valid /UM.upd /cond.
case: (UMC.from f)=>[|f' F]; first by rewrite andbF.
by case: decP=>[|/(introF idP)] ->. 
Qed.

Lemma validF k f : valid (free k f) = valid f.
Proof. by rewrite !pcmE /= !umEX; case: (UMC.from f). Qed.

CoInductive validUn_spec f1 f2 : bool -> Type :=
| valid_false1 of ~~ valid f1 : validUn_spec f1 f2 false
| valid_false2 of ~~ valid f2 : validUn_spec f1 f2 false
| valid_false3 k of k \in dom f1 & k \in dom f2 : validUn_spec f1 f2 false
| valid_true of valid f1 & valid f2 & 
    (forall x, x \in dom f1 -> x \notin dom f2) : validUn_spec f1 f2 true.

Lemma validUn f1 f2 : validUn_spec f1 f2 (valid (f1 \+ f2)).
Proof.
rewrite !pcmE /= !umEX -{1}[f1]UMC.tfE -{1}[f2]UMC.tfE.
rewrite /UM.valid /UM.union /=.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] /=.
- by apply: valid_false1; rewrite pcmE /= !umEX.
- by apply: valid_false1; rewrite pcmE /= !umEX. 
- by apply: valid_false2; rewrite pcmE /= !umEX. 
case: ifP=>E.
- apply: valid_true; try by rewrite !pcmE /= !umEX.
  by move=>k; rewrite !umEX => H; case: disjP E=>//; move/(_ _ H).
case: disjP E=>// k T1 T2 _.
by apply: (valid_false3 (k:=k)); rewrite !umEX.
Qed.

Lemma validFUn k f1 f2 : 
        valid (f1 \+ f2) -> valid (free k f1 \+ f2).
Proof.
case: validUn=>// V1 V2 H _; case: validUn=>//; last 1 first.
- by move=>k'; rewrite domF inE; case: eqP=>// _ /H/negbTE ->.
by rewrite validF V1.
by rewrite V2.
Qed.

Lemma validUnF k f1 f2 : 
        valid (f1 \+ f2) -> valid (f1 \+ free k f2).
Proof. by rewrite !(joinC f1); apply: validFUn. Qed.

Lemma validUnU k v f1 f2 : 
        k \in dom f2 -> valid (f1 \+ upd k v f2) = valid (f1 \+ f2).
Proof.
move=>D; apply/esym; move: D; case: validUn.
- by move=>V' _; apply/esym/negbTE; apply: contra V'; move/validL. 
- move=>V' _; apply/esym/negbTE; apply: contra V'; move/validR. 
  by rewrite validU; case/andP. 
- move=>k' H1 H2 _; case: validUn=>//; rewrite validU => D1 /andP [/= H D2].
  by move/(_ k' H1); rewrite domU !inE H D2 H2; case: ifP.
move=>V1 V2 H1 H2; case: validUn=>//.
- by rewrite V1. 
- by rewrite validU V2 (dom_cond H2). 
move=>k'; rewrite domU (dom_cond H2) inE /= V2; move/H1=>H3. 
by rewrite (negbTE H3); case: ifP H2 H3=>// /eqP ->->.
Qed.

Lemma validUUn k v f1 f2 : 
        k \in dom f1 -> valid (upd k v f1 \+ f2) = valid (f1 \+ f2).
Proof. by move=>D; rewrite -!(joinC f2); apply: validUnU D. Qed.

Lemma valid_umfilt p f : valid (um_filter p f) = valid f.
Proof. by rewrite !pcmE /= !umEX; case: (UMC.from f). Qed.

Lemma dom_inNL k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f1 -> k \notin dom f2.
Proof. by case: validUn=>//_ _ H _; apply: H. Qed.

Lemma dom_inNR k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f2 -> k \notin dom f1.
Proof. by rewrite joinC; apply: dom_inNL. Qed.

End ValidLemmas.


(**********)
(* dom_eq *)
(**********)

Section DomEqLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Type f : U.

Lemma domeqP f1 f2 : 
        reflect (valid f1 = valid f2 /\ dom f1 =i dom f2) (dom_eq f1 f2).
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.dom /UM.dom_eq /in_mem.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] /=.
- by constructor.
- by constructor; case.
- by constructor; case.
by case: eqP=>H; constructor; [rewrite H | case=>_ /suppE].
Qed.

Lemma domeq0E f : dom_eq f Unit -> f = Unit.
Proof. by case/domeqP; rewrite valid_unit dom0; apply: dom0E. Qed.

Lemma domeq_refl f : dom_eq f f.
Proof. by case: domeqP=>//; case. Qed.

Hint Resolve domeq_refl : core.

Lemma domeq_sym f1 f2 : dom_eq f1 f2 = dom_eq f2 f1.
Proof. 
suff L f f' : dom_eq f f' -> dom_eq f' f by apply/idP/idP; apply: L.
by case/domeqP=>H1 H2; apply/domeqP; split.
Qed.

Lemma domeq_trans f1 f2 f3 : 
        dom_eq f1 f2 -> dom_eq f2 f3 -> dom_eq f1 f3.
Proof.
case/domeqP=>E1 H1 /domeqP [E2 H2]; apply/domeqP=>//.
by split=>//; [rewrite E1 E2 | move=>x; rewrite H1 H2]. 
Qed.

Lemma domeqVUnE f1 f2 f1' f2' : 
        dom_eq f1 f2 -> dom_eq f1' f2' -> 
        valid (f1 \+ f1') = valid (f2 \+ f2').
Proof.
have L f f' g : dom_eq f f' -> valid (f \+ g) -> valid (f' \+ g).
- case/domeqP=>E F; case: validUn=>// Vg1 Vf H _; case: validUn=>//.
  - by rewrite -E Vg1. 
  - by rewrite Vf.
  by move=>x; rewrite -F; move/H/negbTE=>->. 
move=>H H'; case X: (valid (f1 \+ f1')); apply/esym. 
- by move/(L _ _ _ H): X; rewrite !(joinC f2); move/(L _ _ _ H').
rewrite domeq_sym in H; rewrite domeq_sym in H'.
apply/negbTE; apply: contra (negbT X); move/(L _ _ _ H). 
by rewrite !(joinC f1); move/(L _ _ _ H').
Qed.

Lemma domeqVUn f1 f2 f1' f2' : 
        dom_eq f1 f2 -> dom_eq f1' f2' ->
        valid (f1 \+ f1') -> valid (f2 \+ f2').
Proof. by move=>D /(domeqVUnE D) ->. Qed.

Lemma domeqUn f1 f2 f1' f2' : 
        dom_eq f1 f2 -> dom_eq f1' f2' -> 
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof.
suff L f f' g : dom_eq f f' -> dom_eq (f \+ g) (f' \+ g).
- move=>H H'; apply: domeq_trans (L _ _ _ H).
  by rewrite !(joinC f1); apply: domeq_trans (L _ _ _ H').
move=>F; case/domeqP: (F)=>E H.
apply/domeqP; split; first by apply: domeqVUnE F _.
move=>x; rewrite !domUn /= inE.
by rewrite (domeqVUnE F (domeq_refl g)) H.
Qed.

Lemma domeqfUn f f1 f2 f1' f2' : 
        dom_eq (f \+ f1) f2 -> dom_eq f1' (f \+ f2') -> 
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof.
move=>D1 D2; apply: (domeq_trans (f2:=f1 \+ f \+ f2')).
- by rewrite -joinA; apply: domeqUn.
by rewrite -joinA joinCA joinA; apply: domeqUn.
Qed.

Lemma domeqUnf f f1 f2 f1' f2' : 
        dom_eq f1 (f \+ f2) -> dom_eq (f \+ f1') f2' -> 
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof. 
by move=>D1 D2; rewrite (joinC f1) (joinC f2); apply: domeqfUn D2 D1. 
Qed.

Lemma domeqK f1 f2 f1' f2' : 
        valid (f1 \+ f1') ->
        dom_eq (f1 \+ f1') (f2 \+ f2') ->
        dom_eq f1 f2 -> dom_eq f1' f2'.
Proof.
move=>V1 /domeqP [E1 H1] /domeqP [E2 H2]; move: (V1); rewrite E1=>V2.
apply/domeqP; split; first by rewrite (validR V1) (validR V2). 
by apply: domK V1 V2 H1 H2.
Qed.

End DomEqLemmas.

Hint Resolve domeq_refl : core.


(*************************)
(* some precision lemmas *)
(*************************)

Section Precision.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (x y : U).

Lemma prec_flip x1 x2 y1 y2 : 
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 -> 
        valid (y2 \+ x2) /\ y2 \+ x2 = y1 \+ x1. 
Proof. by move=>X /esym E; rewrite joinC E X joinC. Qed.

Lemma prec_domV x1 x2 y1 y2 : 
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 ->
        reflect {subset dom x1 <= dom x2} (valid (x1 \+ y2)).
Proof.
move=>V1 E; case V12 : (valid (x1 \+ y2)); constructor.
- move=>n Hs; have : n \in dom (x1 \+ y1) by rewrite domUn inE V1 Hs.
  rewrite E domUn inE -E V1 /= orbC.
  by case: validUn V12 Hs=>// _ _ L _ /L /negbTE ->.
move=>Hs; case: validUn V12=>//.
- by rewrite (validL V1).
- by rewrite E in V1; rewrite (validR V1). 
by move=>k /Hs; rewrite E in V1; case: validUn V1=>// _ _ L _ /L /negbTE ->.
Qed.

Lemma prec_filtV x1 x2 y1 y2 : 
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 ->
        reflect (x1 = um_filter (mem (dom x1)) x2) (valid (x1 \+ y2)).
Proof.
move=>V1 E; case X : (valid (x1 \+ y2)); constructor; last first.
- case: (prec_domV V1 E) X=>// St _ H; apply: St.
  by move=>n; rewrite H dom_umfilt inE; case/andP. 
move: (umfilt_dom V1); rewrite E umfiltUn -?E //.
rewrite (eq_in_umfilt (f:=y2) (p2:=pred0)).
- by rewrite umfilt_pred0 ?unitR //; rewrite E in V1; rewrite (validR V1).
by move=>n; case: validUn X=>// _ _ L _ /(contraL (L _)) /negbTE.
Qed.

End Precision.


(**********)
(* update *)
(**********)

Section UpdateLemmas.
Variable (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).

Lemma upd_invalid k v : upd k v um_undef = um_undef :> U.
Proof. by rewrite !umEX. Qed.

Lemma upd_inj k v1 v2 f : 
        valid f -> cond U k -> upd k v1 f = upd k v2 f -> v1 = v2.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.upd /cond. 
case: (UMC.from f)=>[|f' F] // _; case: decP=>// H _ E.
have: fnd k (ins k v1 f') = fnd k (ins k v2 f') by rewrite E.
by rewrite !fnd_ins eq_refl; case.
Qed.

Lemma updU k1 k2 v1 v2 f : 
        upd k1 v1 (upd k2 v2 f) = 
        if k1 == k2 then upd k1 v1 f else upd k2 v2 (upd k1 v1 f).
Proof.
rewrite !umEX /UM.upd. 
case: (UMC.from f)=>[|f' H']; case: ifP=>// E; 
case: decP=>H1; case: decP=>H2 //; rewrite !umEX.
- by rewrite ins_ins E.
- by rewrite (eqP E) in H2 *. 
by rewrite ins_ins E. 
Qed.

Lemma updF k1 k2 v f : 
        upd k1 v (free k2 f) = 
        if k1 == k2 then upd k1 v f else free k2 (upd k1 v f).
Proof.
rewrite !umEX /UM.dom /UM.upd /UM.free.
case: (UMC.from f)=>[|f' F] //; case: ifP=>// H1;
by case: decP=>H2 //; rewrite !umEX ins_rem H1. 
Qed.

Lemma updUnL k v f1 f2 : 
        upd k v (f1 \+ f2) = 
        if k \in dom f1 then upd k v f1 \+ f2 else f1 \+ upd k v f2. 
Proof.
rewrite !pcmE /= !umEX /UM.upd /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //=.
- by case: ifP=>//; case: decP.
case: ifP=>// D; case: ifP=>// H1; case: decP=>// H2.
- rewrite disjC disj_ins disjC D !umEX; case: disjP D=>// H _. 
  by rewrite (H _ H1) /= fcat_inss // (H _ H1).
- by rewrite disj_ins H1 D /= !umEX fcat_sins.
- by rewrite disjC disj_ins disjC D andbF.
by rewrite disj_ins D andbF.
Qed.

Lemma updUnR k v f1 f2 : 
        upd k v (f1 \+ f2) = 
        if k \in dom f2 then f1 \+ upd k v f2 else upd k v f1 \+ f2.
Proof. by rewrite joinC updUnL (joinC f1) (joinC f2). Qed.

End UpdateLemmas.


(********)
(* free *)
(********)

Section FreeLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).

Lemma free0 k : free k Unit = Unit :> U.
Proof. by rewrite !pcmE /= !umEX /UM.free /UM.empty rem_empty. Qed.

Lemma freeU k1 k2 v f : 
        free k1 (upd k2 v f) = 
        if k1 == k2 then         
          if cond U k2 then free k1 f else um_undef 
        else upd k2 v (free k1 f).
Proof.
rewrite !umEX /UM.free /UM.upd /cond.
case: (UMC.from f)=>[|f' F]; first by case: ifP=>H1 //; case: ifP.
case: ifP=>H1; case: decP=>H2 //=.
- by rewrite H2 !umEX rem_ins H1.
- by case: ifP H2.
by rewrite !umEX rem_ins H1.
Qed.

Lemma freeF k1 k2 f : 
        free k1 (free k2 f) = 
        if k1 == k2 then free k1 f else free k2 (free k1 f).
Proof. 
rewrite !umEX /UM.free.
by case: (UMC.from f)=>[|f' F]; case: ifP=>// E; rewrite !umEX rem_rem E.
Qed.

Lemma freeUn k f1 f2 : 
        free k (f1 \+ f2) = 
        if k \in dom (f1 \+ f2) then free k f1 \+ free k f2 
        else f1 \+ f2.
Proof.
rewrite !pcmE /= !umEX /UM.free /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// E1; rewrite supp_fcat inE /=.
case: ifP=>E2; last by rewrite !umEX rem_supp // supp_fcat inE E2.
rewrite disj_rem; last by rewrite disjC disj_rem // disjC.
rewrite !umEX; case/orP: E2=>E2.
- suff E3: k \notin supp f2' by rewrite -fcat_rems // (rem_supp E3).
  by case: disjP E1 E2=>// H _; move/H.
suff E3: k \notin supp f1' by rewrite -fcat_srem // (rem_supp E3).
by case: disjP E1 E2=>// H _; move/contra: (H k); rewrite negbK.
Qed.

Lemma freeUnV k f1 f2 : 
        valid (f1 \+ f2) -> free k (f1 \+ f2) = free k f1 \+ free k f2.
Proof.
move=>V'; rewrite freeUn domUn V' /=; case: ifP=>//.
by move/negbT; rewrite negb_or; case/andP=>H1 H2; rewrite !dom_free.
Qed.

Lemma freeUnL k f1 f2 : k \notin dom f1 -> free k (f1 \+ f2) = f1 \+ free k f2.
Proof.
move=>V1; rewrite freeUn domUn inE (negbTE V1) /=.
case: ifP; first by case/andP; rewrite dom_free.
move/negbT; rewrite negb_and; case/orP=>V2; last by rewrite dom_free.
suff: ~~ valid (f1 \+ free k f2) by move/invalidE: V2=>-> /invalidE ->. 
apply: contra V2; case: validUn=>// H1 H2 H _.
case: validUn=>//; first by rewrite H1.
- by move: H2; rewrite validF => ->.
move=>x H3; move: (H _ H3); rewrite domF inE /=.
by case: ifP H3 V1=>[|_ _ _]; [move/eqP=><- -> | move/negbTE=>->].
Qed.

Lemma freeUnR k f1 f2 : k \notin dom f2 -> free k (f1 \+ f2) = free k f1 \+ f2.
Proof. by move=>H; rewrite joinC freeUnL // joinC. Qed.

Lemma free_umfilt p k f : 
        free k (um_filter p f) = 
        if p k then um_filter p (free k f) else um_filter p f.
Proof.
rewrite !umEX /UM.free /UM.um_filter.
case: (UMC.from f)=>[|f' F]; case: ifP=>// E; rewrite !umEX. 
- by rewrite kfilt_rem E.
by rewrite rem_kfilt E.
Qed.

End FreeLemmas.


(********)
(* find *)
(********)

Section FindLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).

Lemma find0E k : find k (Unit : U) = None.
Proof. by rewrite pcmE /= !umEX /UM.find /= fnd_empty. Qed.

Lemma find_undef k : find k (um_undef : U) = None.
Proof. by rewrite !umEX /UM.find. Qed.

Lemma find_cond k f : ~~ cond U k -> find k f = None.
Proof.
simpl.
rewrite !umEX /UM.find; case: (UMC.from f)=>[|f' F] // H.
suff: k \notin supp f' by case: suppP. 
by apply: contra H; case: allP F=>// F _ /F.
Qed.

Lemma findU k1 k2 v f : 
        find k1 (upd k2 v f) = 
        if k1 == k2 then
          if cond U k2 && valid f then Some v else None
        else if cond U k2 then find k1 f else None.
Proof.
rewrite pcmE /= !umEX /UM.valid /UM.find /UM.upd /cond.
case: (UMC.from f)=>[|f' F]; first by rewrite andbF !if_same. 
case: decP=>H; first by rewrite H /= fnd_ins.
by rewrite (introF idP H) /= if_same.
Qed.

Lemma findF k1 k2 f : 
        find k1 (free k2 f) = if k1 == k2 then None else find k1 f. 
Proof. 
rewrite !umEX /UM.find /UM.free.
case: (UMC.from f)=>[|f' F]; first by rewrite if_same.
by rewrite fnd_rem.
Qed.

Lemma findUnL k f1 f2 : 
        valid (f1 \+ f2) -> 
        find k (f1 \+ f2) = if k \in dom f1 then find k f1 else find k f2.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.find /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// D _; case: ifP=>E1; last first.
- rewrite fnd_fcat; case: ifP=>// E2.
  by rewrite fnd_supp ?E1 // fnd_supp ?E2.
suff E2: k \notin supp f2' by rewrite fnd_fcat (negbTE E2).
by case: disjP D E1=>// H _; apply: H.
Qed.

Lemma findUnR k f1 f2 : 
        valid (f1 \+ f2) ->
        find k (f1 \+ f2) = if k \in dom f2 then find k f2 else find k f1.
Proof. by rewrite joinC=>D; rewrite findUnL. Qed.

Lemma find_eta f1 f2 :  
        valid f1 -> valid f2 ->
        (forall k, find k f1 = find k f2) -> f1 = f2.
Proof. 
rewrite !pcmE /= !umEX /UM.valid /UM.find -{2 3}[f1]UMC.tfE -{2 3}[f2]UMC.tfE.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] // _ _ H.
by rewrite !umEX; apply/fmapP=>k; move: (H k); rewrite !umEX. 
Qed.

Lemma find_umfilt p k f : 
        find k (um_filter p f) = if p k then find k f else None.
Proof. 
rewrite !umEX /UM.find /UM.um_filter.
case: (UMC.from f)=>[|f' F]; first by rewrite if_same.
by rewrite fnd_kfilt.
Qed.

End FindLemmas.

(* if maps store units, i.e., we keep them just for sets *)
(* then we can simplify the find_eta lemma a bit *)

Lemma domeq_eta (K : ordType) (U : union_map_class K unit) (f1 f2 : U) : 
        dom_eq f1 f2 -> f1 = f2.
Proof.
case/domeqP=>V E; case V1 : (valid f1); last first.
- by move: V1 (V1); rewrite {1}V; do 2![move/negbT/invalidE=>->].
apply: find_eta=>//; first by rewrite -V.
move=>k; case D : (k \in dom f1); move: D (D); rewrite {1}E.
- by do 2![case: dom_find=>// [[-> _]]]. 
by do 2![case: dom_find=>// ->].
Qed.

(********)
(* empb *)
(********)

Section EmpbLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).

Lemma empb_undef : empb (um_undef : U) = false.
Proof. by rewrite !umEX. Qed.

Lemma empbP f : reflect (f = Unit) (empb f).
Proof.
rewrite pcmE /= !umEX /UM.empty /UM.empb -{1}[f]UMC.tfE.
case: (UMC.from f)=>[|f' F]; first by apply: ReflectF; rewrite !umEX.
case: eqP=>E; constructor; rewrite !umEX.
- by move/supp_nilE: E=>->. 
by move=>H; rewrite H in E.
Qed.

Lemma empbU k v f : empb (upd k v f) = false. 
Proof. 
rewrite !umEX /UM.empb /UM.upd.
case: (UMC.from f)=>[|f' F] //; case: decP=>// H.
suff: k \in supp (ins k v f') by case: (supp _).
by rewrite supp_ins inE /= eq_refl.
Qed. 

Lemma empbUn f1 f2 : empb (f1 \+ f2) = empb f1 && empb f2.
Proof.
rewrite !pcmE /= !umEX /UM.empb /UM.union.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
- by rewrite andbF.
case: ifP=>E; case: eqP=>E1; case: eqP=>E2 //; last 2 first.
- by move: E2 E1; move/supp_nilE=>->; rewrite fcat0s; case: eqP.
- by move: E1 E2 E; do 2![move/supp_nilE=>->]; case: disjP.
- by move/supp_nilE: E2 E1=>-> <-; rewrite fcat0s eq_refl.
have [k H3]: exists k, k \in supp f1'.
- case: (supp f1') {E1 E} E2=>[|x s _] //.
  by exists x; rewrite inE eq_refl.
suff: k \in supp (fcat f1' f2') by rewrite E1.
by rewrite supp_fcat inE /= H3.
Qed.

(* some transformation lemmas *)

Lemma empbE f : f = Unit <-> empb f.
Proof. by case: empbP. Qed.

Lemma empb0 : empb (Unit : U).
Proof. by apply/empbE. Qed.

Lemma join0E f1 f2 : f1 \+ f2 = Unit <-> f1 = Unit /\ f2 = Unit.
Proof. by rewrite !empbE empbUn; case: andP. Qed.

Lemma validEb f : reflect (valid f /\ forall k, k \notin dom f) (empb f).
Proof.
case: empbP=>E; constructor; first by rewrite E valid_unit dom0. 
case=>V' H; apply: E; move: V' H.
rewrite !pcmE /= !umEX /UM.valid /UM.dom /UM.empty -{3}[f]UMC.tfE.
case: (UMC.from f)=>[|f' F] // _ H; rewrite !umEX.
apply/supp_nilE; case: (supp f') H=>// x s /(_ x). 
by rewrite inE eq_refl. 
Qed.

Lemma validUnEb f : valid (f \+ f) = empb f. 
Proof.
case E: (empb f); first by move/empbE: E=>->; rewrite unitL valid_unit. 
case: validUn=>// V' _ L; case: validEb E=>//; case; split=>// k.
by case E: (k \in dom f)=>//; move: (L k E); rewrite E. 
Qed.

Lemma empb_umfilt p f : empb f -> empb (um_filter p f).
Proof. 
rewrite !umEX /UM.empb /UM.um_filter.
case: (UMC.from f)=>[|f' F] //.
by move/eqP/supp_nilE=>->; rewrite kfilt_nil.
Qed.

End EmpbLemmas.


(*********)
(* undef *)
(*********)

Section UndefLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).

Lemma undefb_undef : undefb (um_undef : U).
Proof. by rewrite !umEX. Qed.

Lemma undefbP f : reflect (f = um_undef) (undefb f).
Proof.
rewrite !umEX /UM.undefb -{1}[f]UMC.tfE.
by case: (UMC.from f)=>[|f' F]; constructor; rewrite !umEX.
Qed.

Lemma undefbE f : f = um_undef <-> undefb f.
Proof. by case: undefbP. Qed.

Lemma join_undefL f : um_undef \+ f = um_undef.
Proof. by rewrite /PCM.join /= !umEX. Qed.

Lemma join_undefR f : f \+ um_undef = um_undef.
Proof. by rewrite joinC join_undefL. Qed.

End UndefLemmas.


(**********)
(* um_all *)
(**********)

(* this is a defined notion; so it does not appear in the signature *)

Section AllDefLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V) (P : V -> Prop).
Implicit Types (k : K) (v : V) (f : U).

Definition um_all f := forall k v, find k f = Some v -> P v.

Lemma umall_undef : um_all um_undef.
Proof. by move=>k v; rewrite find_undef. Qed.

Hint Resolve umall_undef : core.

Lemma umall0 : um_all Unit.
Proof. by move=>k v; rewrite find0E. Qed.

Lemma umallUn f1 f2 : um_all f1 -> um_all f2 -> um_all (f1 \+ f2).
Proof.
case W : (valid (f1 \+ f2)); last by move/invalidE: (negbT W)=>->.
by move=>X Y k v; rewrite findUnL //; case: ifP=>_; [apply: X|apply: Y].
Qed.

Lemma umallUnL f1 f2 : valid (f1 \+ f2) -> um_all (f1 \+ f2) -> um_all f1.
Proof.
by move=>W H k v F; apply: (H k v); rewrite findUnL // (find_some F).
Qed.

Lemma umallUnR f1 f2 : valid (f1 \+ f2) -> um_all (f1 \+ f2) -> um_all f2.
Proof. by rewrite joinC; apply: umallUnL. Qed.

End AllDefLemmas.

Hint Resolve umall_undef umall0 : core.


(********************************************)
(* Interaction of subset, dom and um_filter *)
(********************************************)

Section Interaction.
Variables (K : ordType) (A : Type) (U : union_map_class K A). 
Implicit Types (x y a b : U) (p q : pred K).

(* filter p x is lower bound for p *)
Lemma subdom_umfilt x p : {subset dom (um_filter p x) <= p}. 
Proof. by move=>a; rewrite dom_umfilt; case/andP. Qed.


(* Some equivalent forms for subset with dom *)
Lemma subdom_indomE x p : {subset dom x <= p} = {in dom x, p =1 predT}.
Proof. by []. Qed.

Lemma subdom_umfiltE x p : {subset dom x <= p} <-> um_filter p x = x.
Proof. 
split; last by move=><- a; rewrite dom_umfilt; case/andP.
by move/eq_in_umfilt=>->; rewrite umfilt_predT. 
Qed.

(* specific consequence of subdom_umfiltE *)
Lemma umfilt_memdomE x : um_filter (mem (dom x)) x = x. 
Proof. by apply/subdom_umfiltE. Qed.


(* Some equivalent forms for subset expressing disjointness *)

Lemma subset_disjE p q : {subset p <= predC q} <-> [predI p & q] =1 pred0.
Proof.
split=>H a /=; first by case X: (a \in p)=>//; move/H/negbTE: X.
by move=>D; move: (H a); rewrite inE /= D; move/negbT.
Qed.

Lemma subset_disjC p q : {subset p <= predC q} <-> {subset q <= predC p}.
Proof. by split=>H a; apply: contraL (H a). Qed.

Lemma valid_subdom x y : valid (x \+ y) -> {subset dom x <= [predC dom y]}. 
Proof. by case: validUn. Qed.

Lemma subdom_valid x y : 
        {subset dom x <= [predC dom y]} -> 
        valid x -> valid y -> valid (x \+ y).
Proof. by move=>H X Y; case: validUn; rewrite ?X ?Y=>// k /H /negbTE /= ->. Qed.

Lemma subdom_umfilt0 x p : 
        valid x -> {subset dom x <= predC p} <-> um_filter p x = Unit. 
Proof.
move=>V; split=>H.
- by rewrite (eq_in_umfilt (p2:=pred0)) ?umfilt_pred0 // => a /H /negbTE ->.
move=>k X; case: dom_find X H=>// a _ -> _; rewrite umfiltU !inE. 
by case: ifP=>// _ /empbE; rewrite /= empbU.
Qed.

End Interaction.


(************************)
(* PCM-induced ordering *)
(************************)

(* Union maps and pcm ordering. *)

Section UmpleqLemmas.
Variables (K : ordType) (A : Type) (U : union_map_class K A). 
Implicit Types (x y a b : U) (p : pred K).

Lemma umpleq_undef x : [pcm x <= um_undef].
Proof. by exists um_undef; rewrite join_undefR. Qed.

Hint Resolve umpleq_undef : core.

(* pcm-induced preorder, is an order in the case of union maps *)

Lemma umpleq_asym x y : [pcm x <= y] -> [pcm y <= x] -> x = y.
Proof.
case=>a -> [b]; case V : (valid x); last first.
- by move/invalidE: (negbT V)=>->; rewrite join_undefL. 
rewrite -{1 2}[x]unitR -joinA in V *.
by case/(joinxK V)/esym/join0E=>->; rewrite unitR.
Qed.

(* monotonicity lemmas *)

Lemma umpleq_filt2 x y p : [pcm x <= y] -> [pcm um_filter p x <= um_filter p y].
Proof.
move=>H; case V : (valid y).
- by case: H V=>a -> V; rewrite umfiltUn //; eexists _. 
by move/invalidE: (negbT V)=>->; rewrite umfilt_undef; apply: umpleq_undef.
Qed.

(* filter p x is lower bound for x *)
Lemma umpleq_filtI x p : [pcm um_filter p x <= x].
Proof.
exists (um_filter (predD predT p) x); rewrite -umfilt_predU.
by rewrite -{1}[x]umfilt_predT; apply: eq_in_umfilt=>a; rewrite /= orbT. 
Qed.

Hint Resolve umpleq_filtI : core.

(* in valid case, we can define the order by means of filter *)
Lemma umpleq_filtE a x : 
        valid x -> [pcm a <= x] <-> um_filter (mem (dom a)) x = a.
Proof. by move=>V; split=>[|<-] // H; case: H V=>b ->; apply: umfilt_dom. Qed.

(* filter p x is largest lower bound for x and p *)
Lemma umpleq_filt_meet a x p : 
        {subset dom a <= p} -> [pcm a <= x] -> [pcm a <= um_filter p x].
Proof. by move=>D /(umpleq_filt2 p); rewrite (eq_in_umfilt D) umfilt_predT. Qed.

(* join is the least upper bound *)
Lemma umpleq_join x a b : 
        valid (a \+ b) -> [pcm a <= x] -> [pcm b <= x] -> [pcm a \+ b <= x].
Proof.
case Vx : (valid x); last by move/invalidE: (negbT Vx)=>->.
move=>V /(umpleq_filtE _ Vx) <- /(umpleq_filtE _ Vx) <-.
by rewrite -umfilt_dpredU //; apply: valid_subdom V.
Qed.

(* x <= y and subdom *)

Lemma umpleq_subdom x y : valid y -> [pcm x <= y] -> {subset dom x <= dom y}.
Proof. by move=>V H; case: H V=>a -> V b D; rewrite domUn inE V D. Qed.

Lemma subdom_umpleq a x y :
        valid (x \+ y) -> [pcm a <= x \+ y] -> 
        {subset dom a <= dom x} -> [pcm a <= x].
Proof.
move=>V H Sx; move: (umpleq_filt_meet Sx H); rewrite umfiltUn //.
rewrite umfilt_memdomE; move/subset_disjC: (valid_subdom V). 
by move/(subdom_umfilt0 _ (validR V))=>->; rewrite unitR.
Qed.

(* meet is the greatest lower bound *)
Lemma umpleq_meet a x y1 y2 : 
        valid (x \+ y1 \+ y2) -> 
        [pcm a <= x \+ y1] -> [pcm a <= x \+ y2] -> [pcm a <= x].
Proof.
move=>V H1 H2. 
have {V} [V1 V V2] : [/\ valid (x \+ y1), valid (y1 \+ y2) & valid (x \+ y2)].
- rewrite (validL V); rewrite -joinA in V; rewrite (validR V). 
  by rewrite joinA joinAC in V; rewrite (validL V).
apply: subdom_umpleq (V1) (H1) _ => k D. 
move: {D} (umpleq_subdom V1 H1 D) (umpleq_subdom V2 H2 D).
rewrite !domUn !inE V1 V2 /=; case : (k \in dom x)=>//=. 
by case: validUn V=>// _ _ L _ /L /negbTE ->. 
Qed.

(* some/none lemmas *)

Lemma umpleq_some x1 x2 t s : 
        valid x2 -> [pcm x1 <= x2] -> find t x1 = Some s -> find t x2 = Some s.
Proof. by move=>V H; case: H V=>a -> V H; rewrite findUnL // (find_some H). Qed.

Lemma umpleq_none x1 x2 t : 
        valid x2 -> [pcm x1 <= x2] -> find t x2 = None -> find t x1 = None.
Proof. by case E: (find t x1)=>[a|] // V H <-; rewrite (umpleq_some V H E). Qed.

End UmpleqLemmas.


(****************************)
(* Generic points-to lemmas *)
(****************************)

(* Instances of union_maps have different definition of points-to, so
they need separate intances of each of following lemmas. I give the
lemmas complicated names prefixed by gen, because they are not
supposed to be used in applications *)

Section PointsToLemmas.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).

Lemma ptsU k v : pts k v = upd k v Unit :> U.
Proof. by rewrite !pcmE /= !umEX /UM.pts /UM.upd; case: decP. Qed.

Lemma domPtK k v : dom (pts k v : U) = if cond U k then [:: k] else [::]. 
Proof. 
rewrite !umEX /= /UM.dom /supp /UM.pts /UM.upd /UM.empty /=.
by case D : (decP _)=>[a|a] /=; rewrite ?a ?(introF idP a). 
Qed.

(* a weaker version of gen_domPtK, but legacy *)
Lemma domPt k v : dom (pts k v : U) =i [pred x | cond U k & k == x].
Proof. 
by move=>x; rewrite ptsU domU !inE eq_sym valid_unit dom0; case: eqP. 
Qed.

Lemma validPt k v : valid (pts k v : U) = cond U k. 
Proof. by rewrite ptsU validU valid_unit andbT. Qed.

Lemma domeqPt k v1 v2 : dom_eq (pts k v1 : U) (pts k v2). 
Proof. by apply/domeqP; rewrite !validPt; split=>// x; rewrite !domPt. Qed.

Lemma findPt k v : find k (pts k v : U) = if cond U k then Some v else None.
Proof. by rewrite ptsU findU eq_refl /= valid_unit andbT. Qed.

Lemma findPt2 k1 k2 v : 
        find k1 (pts k2 v : U) = 
        if (k1 == k2) && cond U k2 then Some v else None.
Proof. 
by rewrite ptsU findU valid_unit andbT find0E; case: ifP=>//=; case: ifP. 
Qed.

Lemma findPt_inv k1 k2 v w : 
        find k1 (pts k2 v : U) = Some w -> [/\ k1 = k2, v = w & cond U k2].
Proof.
rewrite ptsU findU; case: eqP; last by case: ifP=>//; rewrite find0E. 
by move=>->; rewrite valid_unit andbT; case: ifP=>// _ [->]. 
Qed.

Lemma freePt2 k1 k2 v : 
        cond U k2 ->
        free k1 (pts k2 v : U) = if k1 == k2 then Unit else pts k2 v.
Proof. by move=>N; rewrite ptsU freeU free0 N. Qed.

Lemma freePt k v : 
        cond U k -> free k (pts k v : U) = Unit.
Proof. by move=>N; rewrite freePt2 // eq_refl. Qed.

Lemma cancelPt k v1 v2 : 
        valid (pts k v1 : U) -> pts k v1 = pts k v2 :> U -> v1 = v2.
Proof. by rewrite validPt !ptsU; apply: upd_inj. Qed.

Lemma cancelPt2 k1 k2 v1 v2 : 
        valid (pts k1 v1 : U) -> 
        pts k1 v1 = pts k2 v2 :> U -> (k1, v1) = (k2, v2). 
Proof.
move=>H E; have : dom (pts k1 v1 : U) = dom (pts k2 v2 : U) by rewrite E. 
rewrite !domPtK -(validPt _ v1) -(validPt _ v2) -E H.
by case=>E'; rewrite -{k2}E' in E *; rewrite (cancelPt H E).
Qed.

Lemma updPt k v1 v2 : upd k v1 (pts k v2) = pts k v1 :> U.
Proof. by rewrite !ptsU updU eq_refl. Qed.

Lemma empbPt k v : empb (pts k v : U) = false.
Proof. by rewrite ptsU empbU. Qed.

(* valid *)

Lemma validPtUn k v f :
        valid (pts k v \+ f) = [&& cond U k, valid f & k \notin dom f].
Proof. 
case: validUn=>//; last 1 first.
- rewrite validPt=>H1 -> H2; rewrite H1 (H2 k) //.
  by rewrite domPtK H1 inE. 
- by rewrite validPt; move/negbTE=>->.
- by move/negbTE=>->; rewrite andbF.
rewrite domPtK=>x; case: ifP=>// _.
by rewrite inE=>/eqP ->->; rewrite andbF. 
Qed.

Lemma validUnPt k v f :
        valid (f \+ pts k v) = [&& cond U k, valid f & k \notin dom f].
Proof. by rewrite joinC; apply: validPtUn. Qed.

(* the projections from validPtUn are often useful *)

Lemma validPtUn_cond k v f : valid (pts k v \+ f) -> cond U k.
Proof. by rewrite validPtUn; case/and3P. Qed.

Lemma validUnPt_cond k v f : valid (f \+ pts k v) -> cond U k.
Proof. by rewrite joinC; apply: validPtUn_cond. Qed.

Lemma validPtUnV k v f : valid (pts k v \+ f) -> valid f.
Proof. by rewrite validPtUn; case/and3P. Qed.

Lemma validUnPtV k v f : valid (f \+ pts k v) -> valid f.
Proof. by rewrite joinC; apply: validPtUnV. Qed.

Lemma validPtUnD k v f : valid (pts k v \+ f) -> k \notin dom f.
Proof. by rewrite validPtUn; case/and3P. Qed.

Lemma validUnPtD k v f : valid (f \+ pts k v) -> k \notin dom f.
Proof. by rewrite joinC; apply: validPtUnD. Qed.

(* dom *)

Lemma domPtUn k v f : 
        dom (pts k v \+ f) =i 
        [pred x | valid (pts k v \+ f) & (k == x) || (x \in dom f)].
Proof. 
move=>x; rewrite domUn !inE !validPtUn domPt !inE.
by rewrite -!andbA; case: (UMC.p _ k).
Qed.

Lemma domUnPt k v f : 
        dom (f \+ pts k v) =i 
        [pred x | valid (f \+ pts k v) & (k == x) || (x \in dom f)].
Proof. by rewrite joinC; apply: domPtUn. Qed.

Lemma domPtUnE k v f : k \in dom (pts k v \+ f) = valid (pts k v \+ f).
Proof. by rewrite domPtUn inE eq_refl andbT. Qed.

Lemma domUnPtE k v f : k \in dom (f \+ pts k v) = valid (f \+ pts k v).
Proof. by rewrite joinC; apply: domPtUnE. Qed.

Lemma validxx f : valid (f \+ f) -> dom f =i pred0. 
Proof. by case: validUn=>// _ _ L _ z; case: (_ \in _) (L z)=>//; elim. Qed.

(* dom_eq *)

Lemma domeqPtUn k v1 v2 f1 f2 : 
        dom_eq f1 f2 -> dom_eq (pts k v1 \+ f1) (pts k v2 \+ f2).
Proof. by apply: domeqUn=>//; apply: domeqPt. Qed.

Lemma domeqUnPt k v1 v2 f1 f2 : 
        dom_eq f1 f2 -> dom_eq (f1 \+ pts k v1) (f2 \+ pts k v2).
Proof. by rewrite (joinC f1) (joinC f2); apply: domeqPtUn. Qed.

(* find *) 

Lemma findPtUn k v f : 
        valid (pts k v \+ f) -> find k (pts k v \+ f) = Some v.
Proof.
move=>V'; rewrite findUnL // domPt inE.
by rewrite ptsU findU eq_refl valid_unit (validPtUn_cond V'). 
Qed.

Lemma findUnPt k v f : 
        valid (f \+ pts k v) -> find k (f \+ pts k v) = Some v.
Proof. by rewrite joinC; apply: findPtUn. Qed.

Lemma findPtUn2 k1 k2 v f : 
         valid (pts k2 v \+ f) ->
         find k1 (pts k2 v \+ f) = 
         if k1 == k2 then Some v else find k1 f.
Proof.
move=>V'; rewrite findUnL // domPt inE eq_sym.
by rewrite findPt2 (validPtUn_cond V') andbT /=; case: ifP=>// ->.
Qed.

Lemma findUnPt2 k1 k2 v f : 
         valid (f \+ pts k2 v) ->
         find k1 (f \+ pts k2 v) = 
         if k1 == k2 then Some v else find k1 f.
Proof. by rewrite joinC; apply: findPtUn2. Qed.

(* free *)

Lemma freePtUn2 k1 k2 v f : 
        valid (pts k2 v \+ f) -> 
        free k1 (pts k2 v \+ f) = 
        if k1 == k2 then f else pts k2 v \+ free k1 f.
Proof.
move=>V'; rewrite freeUn domPtUn inE V' /= eq_sym. 
rewrite ptsU freeU (validPtUn_cond V') free0.
case: eqP=>/= E; first by rewrite E unitL (dom_free (validPtUnD V')).
by case: ifP=>// N; rewrite dom_free // N.
Qed.

Lemma freeUnPt2 k1 k2 v f : 
        valid (f \+ pts k2 v) -> 
        free k1 (f \+ pts k2 v) = 
        if k1 == k2 then f else free k1 f \+ pts k2 v.
Proof. by rewrite !(joinC _ (pts k2 v)); apply: freePtUn2. Qed.

Lemma freePtUn k v f : 
        valid (pts k v \+ f) -> free k (pts k v \+ f) = f.
Proof. by move=>V'; rewrite freePtUn2 // eq_refl. Qed.

Lemma freeUnPt k v f : 
        valid (f \+ pts k v) -> free k (f \+ pts k v) = f.
Proof. by rewrite joinC; apply: freePtUn. Qed.

(* upd *)

Lemma updPtUn k v1 v2 f : upd k v1 (pts k v2 \+ f) = pts k v1 \+ f.
Proof.
case V1 : (valid (pts k v2 \+ f)).
- by rewrite updUnL domPt inE eq_refl updPt (validPtUn_cond V1).
have V2 : valid (pts k v1 \+ f) = false.
- by rewrite !validPtUn in V1 *.
move/negbT/invalidE: V1=>->; move/negbT/invalidE: V2=>->.
by apply: upd_invalid.
Qed.

Lemma updUnPt k v1 v2 f : upd k v1 (f \+ pts k v2) = f \+ pts k v1.
Proof. by rewrite !(joinC f); apply: updPtUn. Qed.

(* empb *)

Lemma empbPtUn k v f : empb (pts k v \+ f) = false.
Proof. by rewrite empbUn empbPt. Qed.

Lemma empbUnPt k v f : empb (f \+ pts k v) = false.
Proof. by rewrite joinC; apply: empbPtUn. Qed.

(* undef *)

Lemma pts_undef k v1 v2 : pts k v1 \+ pts k v2 = um_undef :> U.
Proof.
apply/invalidE; rewrite validPtUn validPt domPt !negb_and negb_or eq_refl.
by case: (cond U k).
Qed.

(* um_filter *)

Lemma umfiltPt p k v : 
        um_filter p (pts k v : U) = 
        if p k then pts k v else if cond U k then Unit else um_undef.
Proof. by rewrite ptsU umfiltU umfilt0. Qed.

Lemma umfiltPtUn p k v f : 
        um_filter p (pts k v \+ f) = 
        if valid (pts k v \+ f) then 
          if p k then pts k v \+ um_filter p f else um_filter p f 
        else um_undef. 
Proof.
case: ifP=>X; last by move/invalidE: (negbT X)=>->; rewrite umfilt_undef. 
rewrite umfiltUn // umfiltPt (validPtUn_cond X).
by case: ifP=>//; rewrite unitL.
Qed.

(* um_all *)

Lemma umallPt (P : V -> Prop) k v : P v -> um_all P (pts k v : U).
Proof. by move=>X u w /findPt_inv [_ <-]. Qed.

Lemma umallPtUn (P : V -> Prop) k v f :
        P v -> um_all P f -> um_all P (pts k v \+ f).
Proof. by move/(umallPt (k:=k)); apply: umallUn. Qed.

Lemma umallPtE (P : V -> Prop) k v : cond U k -> um_all P (pts k v : U) -> P v. 
Proof. by move=>C /(_ k v); rewrite findPt C; apply. Qed.

Lemma umallPtUnE (P : V -> Prop) k v f : 
        valid (pts k v \+ f) -> um_all P (pts k v \+ f) -> P v /\ um_all P f.
Proof.
move=>W H; move: (umallUnL W H) (umallUnR W H)=>{H} H1 H2. 
by split=>//; apply: umallPtE H1; apply: validPtUn_cond W.
Qed.

(* others *)

Lemma um_eta k f : 
        k \in dom f -> exists v, find k f = Some v /\ f = pts k v \+ free k f.
Proof.
case: dom_find=>// v E1 E2 _; exists v; split=>//.
by rewrite {1}E2 -{1}[free k f]unitL updUnR domF inE /= eq_refl ptsU. 
Qed.

Lemma um_eta2 k v f : 
        find k f = Some v -> f = pts k v \+ free k f.
Proof. by move=>E; case/um_eta: (find_some E)=>v' []; rewrite E; case=><-. Qed.

Lemma cancel k v1 v2 f1 f2 : 
        valid (pts k v1 \+ f1) ->
        pts k v1 \+ f1 = pts k v2 \+ f2 -> [/\ v1 = v2, valid f1 & f1 = f2].
Proof.
move=>V' E.
have: find k (pts k v1 \+ f1) = find k (pts k v2 \+ f2) by rewrite E.
rewrite !findPtUn -?E //; case=>X.
by rewrite -{}X in E *; rewrite -(joinxK V' E) (validR V').
Qed.

Lemma cancel2 k1 k2 f1 f2 v1 v2 : 
        valid (pts k1 v1 \+ f1) ->
        pts k1 v1 \+ f1 = pts k2 v2 \+ f2 -> 
        if k1 == k2 then v1 = v2 /\ f1 = f2 
        else [/\ free k1 f2 = free k2 f1, 
                 f1 = pts k2 v2 \+ free k1 f2 &  
                 f2 = pts k1 v1 \+ free k2 f1].
Proof.
move=>V1 E; case: ifP=>X.
- by rewrite -(eqP X) in E; case/(cancel V1): E. 
move: (V1); rewrite E => V2.
have E' : f2 = pts k1 v1 \+ free k2 f1.
- move: (erefl (free k2 (pts k1 v1 \+ f1))). 
  rewrite {2}E freeUn E domPtUn inE V2 eq_refl /=. 
  by rewrite ptsU freeU eq_sym X free0 -ptsU freePtUn.
suff E'' : free k2 f1 = free k1 f2.
- by rewrite -E''; rewrite E' joinCA in E; case/(cancel V1): E.
move: (erefl (free k1 f2)).
by rewrite {1}E' freePtUn // -E'; apply: (validR V2).
Qed.

(* induction over union maps, expressed with pts and \+ *)

(* forward progressing over keys *)
Lemma um_indf (P : U -> Prop) : 
         P um_undef -> P Unit ->
         (forall k v f, P f -> valid (pts k v \+ f) -> 
             path ord k (dom f) ->
             P (pts k v \+ f)) ->
         forall f, P f.
Proof.
rewrite !pcmE /= !umEX => H1 H2 H3 f; rewrite -[f]UMC.tfE.
apply: (UM.base_indf (P := (fun b => P (UMC.to b))))=>//.
move=>k v g H V1; move: (H3 k v _ H); rewrite !pcmE /= !umEX. 
by apply.
Qed.

(* backward progressing over keys *)
Lemma um_indb (P : U -> Prop) : 
         P um_undef -> P Unit ->
         (forall k v f, P f -> valid (pts k v \+ f) -> 
            (forall x, x \in dom f -> ord x k) ->
            P (pts k v \+ f)) ->
         forall f, P f.
Proof.
rewrite !pcmE /= !umEX => H1 H2 H3 f; rewrite -[f]UMC.tfE.
apply: (UM.base_indb (P := (fun b => P (UMC.to b))))=>//.
move=>k v g H V1; move: (H3 k v _ H); rewrite !pcmE /= !umEX. 
by apply. 
Qed.

(* validity holds pairwise *)
Lemma um_valid3 f1 f2 f3 : 
        valid (f1 \+ f2 \+ f3) = 
        [&& valid (f1 \+ f2), valid (f2 \+ f3) & valid (f1 \+ f3)].
Proof.
apply/idP/idP.
- move=>W; rewrite (validL W). 
  rewrite -joinA in W; rewrite (validR W).
  by rewrite joinCA in W; rewrite (validR W).
case/and3P=>V1 V2 V3; case: validUn=>//.
- by rewrite V1.
- by rewrite (validR V2).
move=>k; rewrite domUn inE V1; case/orP.
- by case: validUn V3=>// _ _ X _ /X /negbTE ->.
by case: validUn V2=>// _ _ X _ /X /negbTE ->.
Qed.

(* points-to is a prime element of the monoid *)
Lemma um_prime f1 f2 k v : 
        cond U k -> 
        f1 \+ f2 = pts k v -> 
        f1 = pts k v /\ f2 = Unit \/ 
        f1 = Unit /\ f2 = pts k v.
Proof.
move: f1 f2; apply: um_indf=>[f1|f2 _|k2 w2 f1 _ _ _ f X E].
- rewrite join_undefL -(validPt _ v)=>W E.
  by rewrite -E in W; rewrite valid_undef in W.
- by rewrite unitL=>->; right. 
have W : valid (pts k2 w2 \+ (f1 \+ f)).
- by rewrite -(validPt _ v) -E -joinA in X. 
rewrite -[pts k v]unitR -joinA in E.
move/(cancel2 W): E; case: ifP.
- by move/eqP=>-> [->] /join0E [->->]; rewrite unitR; left.
by move=>_ [_ _] /esym/empbP; rewrite empbPtUn.
Qed.

End PointsToLemmas.

Hint Resolve domeqPt domeqPtUn domeqUnPt : core.
Prenex Implicits validPtUn_cond findPt_inv um_eta2.

(********************)
(* Topped structure *)
(********************)

Module UnionClassTPCM.
Section UnionClassTPCM.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Type f : U.

Lemma join0E f1 f2 : f1 \+ f2 = Unit -> f1 = Unit /\ f2 = Unit.
Proof. by rewrite join0E. Qed.

Lemma valid_undefN : ~~ valid (um_undef: U).
Proof. by rewrite valid_undef. Qed.

Lemma undef_join f : um_undef \+ f = um_undef.
Proof. by rewrite join_undefL. Qed.
End UnionClassTPCM.

Module Exports.
Definition union_map_classTPCMMix K V (U : union_map_class K V) := 
  TPCMMixin (@empbP K V U) (@join0E K V U)
            (@valid_undefN K V U) (@undef_join _ _ U). 
Canonical union_map_classTPCM K V (U : union_map_class K V) := 
  Eval hnf in TPCM _ (@union_map_classTPCMMix K V U).
End Exports.
End UnionClassTPCM.

Export UnionClassTPCM.Exports.


(********************************************************)
(********************************************************)
(* Instance of union maps with trivially true condition *)
(********************************************************)
(********************************************************)

(* We build it over the base type with a trival condition on keys. We
seal the definition to avoid any slowdowns (just in case). *)

Module Type UMSig.
Parameter tp : ordType -> Type -> Type.

Section Params.
Variables (K : ordType) (V : Type).
Notation tp := (tp K V).

Parameter um_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : K -> V -> tp -> tp.
Parameter dom : tp -> seq K.
Parameter dom_eq : tp -> tp -> bool.
Parameter free : K -> tp -> tp. 
Parameter find : K -> tp -> option V.
Parameter union : tp -> tp -> tp.
Parameter um_filter : pred K -> tp -> tp.
Parameter empb : tp -> bool.
Parameter undefb : tp -> bool.
Parameter pts : K -> V -> tp.

Parameter from : tp -> @UM.base K V predT. 
Parameter to : @UM.base K V predT -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : um_undef = to (@UM.Undef K V predT). 
Axiom defE : forall f, defined f = UM.valid (from f). 
Axiom emptyE : empty = to (@UM.empty K V predT). 
Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)). 
Axiom domE : forall f, dom f = UM.dom (from f). 
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2). 
Axiom freeE : forall k f, free k f = to (UM.free k (from f)). 
Axiom findE : forall k f, find k f = UM.find k (from f). 
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom umfiltE : forall q f, um_filter q f = to (UM.um_filter q (from f)).
Axiom empbE : forall f, empb f = UM.empb (from f). 
Axiom undefbE : forall f, undefb f = UM.undefb (from f). 
Axiom ptsE : forall k v, pts k v = to (@UM.pts K V predT k v).

End Params.

End UMSig.


Module UMDef : UMSig.
Section UMDef.
Variables (K : ordType) (V : Type).

Definition tp : Type := @UM.base K V predT.

Definition um_undef := @UM.Undef K V predT.
Definition defined f := @UM.valid K V predT f.
Definition empty := @UM.empty K V predT.
Definition upd k v f := @UM.upd K V predT k v f.
Definition dom f := @UM.dom K V predT f.
Definition dom_eq f1 f2 := @UM.dom_eq K V predT f1 f2.
Definition free k f := @UM.free K V predT k f.
Definition find k f := @UM.find K V predT k f.
Definition union f1 f2 := @UM.union K V predT f1 f2.
Definition um_filter q f := @UM.um_filter K V predT q f.
Definition empb f := @UM.empb K V predT f.
Definition undefb f := @UM.undefb K V predT f.
Definition pts k v := @UM.pts K V predT k v.

Definition from (f : tp) : @UM.base K V predT := f.
Definition to (b : @UM.base K V predT) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : um_undef = to (@UM.Undef K V predT). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty K V predT). Proof. by []. Qed.
Lemma updE k v f : upd k v f = to (UM.upd k v (from f)). Proof. by []. Qed.
Lemma domE f : dom f = UM.dom (from f). Proof. by []. Qed.
Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2). 
Proof. by []. Qed.
Lemma freeE k f : free k f = to (UM.free k (from f)). Proof. by []. Qed.
Lemma findE k f : find k f = UM.find k (from f). Proof. by []. Qed.
Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by []. Qed.
Lemma umfiltE q f : um_filter q f = to (UM.um_filter q (from f)).
Proof. by []. Qed.
Lemma empbE f : empb f = UM.empb (from f). Proof. by []. Qed.
Lemma undefbE f : undefb f = UM.undefb (from f). Proof. by []. Qed.
Lemma ptsE k v : pts k v = to (@UM.pts K V predT k v). Proof. by []. Qed.

End UMDef.
End UMDef.

Notation union_map := UMDef.tp.

Definition unionmapMixin K V := 
  UMCMixin (@UMDef.ftE K V) (@UMDef.tfE K V) (@UMDef.defE K V) 
           (@UMDef.undefE K V) (@UMDef.emptyE K V) (@UMDef.updE K V) 
           (@UMDef.domE K V) (@UMDef.dom_eqE K V) (@UMDef.freeE K V)
           (@UMDef.findE K V) (@UMDef.unionE K V) (@UMDef.umfiltE K V)
           (@UMDef.empbE K V) (@UMDef.undefbE K V) (@UMDef.ptsE K V).

Canonical union_mapUMC K V := 
  Eval hnf in UMC (union_map K V) (@unionmapMixin K V).

(* we add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition union_mapPCMMix K V := 
  union_map_classPCMMix (union_mapUMC K V).
Canonical union_mapPCM K V := 
  Eval hnf in PCM (union_map K V) (@union_mapPCMMix K V).

Definition union_mapCPCMMix K V := 
  union_map_classCPCMMix (@union_mapUMC K V).
Canonical union_mapCPCM K V := 
  Eval hnf in CPCM (union_map K V) (@union_mapCPCMMix K V).

Definition union_mapTPCMMix K V := 
  union_map_classTPCMMix (@union_mapUMC K V).
Canonical union_mapTPCM K V := 
  Eval hnf in TPCM (union_map K V) (@union_mapTPCMMix K V).

Definition union_map_eqMix K (V : eqType) := 
  @union_map_class_eqMix K V _ _ (@unionmapMixin K V).
Canonical union_map_eqType K (V : eqType) := 
  Eval hnf in EqType (union_map K V) (@union_map_eqMix K V).


Definition um_pts (K : ordType) V (k : K) (v : V) := 
  @UMC.pts K V (@union_mapUMC K V) k v. 

Notation "x \\-> v" := (@um_pts _ _ x v) (at level 30).

(* Finite sets are just union maps with unit range *)
Notation fset T := (@union_map T unit).
Notation "# x" := (x \\-> tt) (at level 20).

(* Does the notation work? *)
Lemma xx : 1 \\-> true = 1 \\-> false.
Abort.

(* does the pcm and the equality type work? *)
Lemma xx : ((1 \\-> true) \+ (2 \\-> false)) == (1 \\-> false).
simpl.
rewrite joinC. 
Abort.

(* can we use the base type? *)
Lemma xx (x : union_map nat_ordType nat) : x \+ x == x \+ x. 
Abort.

(* the default dom' lemmas don't work nicely *)
Lemma xx (f : union_map nat_ordType nat) : 3 \in dom (free 2 f).
try by rewrite domF' /=.  
rewrite (@domF _ _ (union_mapUMC _ _)).
Abort.

(* but the dom lemmas do work nicely *)
Lemma xx (f : union_map nat_ordType nat) : 3 \in dom (free 2 f).
rewrite domF /=.  
Abort.

Lemma xx : 1 \\-> (1 \\-> 3) = 2 \\-> (7 \\-> 3).
Abort.


(* Since the union map constructors are opaque, the decidable equality *)
(* does not simplify automatically; we need to export explicit equations *)
(* for simplification *)
(* so far, the ones I need are really just for points-to *)

Section UMDecidableEquality.
Variables (K : ordType) (V : eqType) (U : union_map_class K V).

Lemma umPtPtE (k1 k2 : K) (v1 v2 : V) : 
        (k1 \\-> v1 == k2 \\-> v2) = (k1 == k2) && (v1 == v2).
Proof.
rewrite {1}/eq_op /= /UnionMapEq.unionmap_eq /um_pts !umEX /=. 
by rewrite {1}/eq_op /= /feq eqseq_cons andbT. 
Qed.

Lemma umPt0E (k : K) (v : V) : (k \\-> v == Unit) = false.
Proof. by apply: (introF idP)=>/eqP/empbP; rewrite empbPt. Qed.

Lemma um0PtE (k : K) (v : V) : 
        (@Unit [pcm of union_map K V] == k \\-> v) = false.
Proof. by rewrite eq_sym umPt0E. Qed.

Lemma umPtUndefE (k : K) (v : V) : (k \\-> v == um_undef) = false.
Proof. by rewrite /eq_op /= /UnionMapEq.unionmap_eq /um_pts !umEX. Qed.

Lemma umUndefPtE (k : K) (v : V) : 
       ((um_undef : union_map_eqType K V) == k \\-> v) = false.
Proof. by rewrite eq_sym umPtUndefE. Qed.

Lemma umUndef0E : ((um_undef : union_map_eqType K V) == Unit) = false.
Proof. by apply/(introF idP)=>/eqP/empbP; rewrite empb_undef. Qed.

Lemma um0UndefE : ((Unit : union_mapPCM K V) == um_undef) = false.
Proof. by rewrite eq_sym umUndef0E. Qed.

Lemma umPtUE (k : K) (v : V) f : (k \\-> v \+ f == Unit) = false.
Proof. by apply: (introF idP)=>/eqP/join0E/proj1/eqP; rewrite umPt0E. Qed.

Lemma umUPtE (k : K) (v : V) f : (f \+ k \\-> v == Unit) = false.
Proof. by rewrite joinC umPtUE. Qed.

Lemma umPtUPtE (k1 k2 : K) (v1 v2 : V) f : 
         (k1 \\-> v1 \+ f == k2 \\-> v2) = [&& k1 == k2, v1 == v2 & empb f]. 
Proof.
apply/idP/idP; last first.
- by case/and3P=>/eqP -> /eqP -> /empbP ->; rewrite unitR.
move/eqP/(um_prime _); case=>//; case.
- move/(cancelPt2 _); rewrite validPt=>/(_ (erefl _)). 
  by case=>->->->; rewrite !eq_refl empb0. 
by move/empbP; rewrite empbPt. 
Qed.

Lemma umPtPtUE (k1 k2 : K) (v1 v2 : V) f : 
        (k1 \\-> v1 == k2 \\-> v2 \+ f) = [&& k1 == k2, v1 == v2 & empb f].
Proof. by rewrite eq_sym umPtUPtE (eq_sym k1) (eq_sym v1). Qed.

Lemma umUPtPtE (k1 k2 : K) (v1 v2 : V) f : 
        (f \+ k1 \\-> v1 == k2 \\-> v2) = [&& k1 == k2, v1 == v2 & empb f].
Proof. by rewrite joinC umPtUPtE. Qed.

Lemma umPtUPt2E (k1 k2 : K) (v1 v2 : V) f : 
        (k1 \\-> v1 == f \+ k2 \\-> v2) = [&& k1 == k2, v1 == v2 & empb f].
Proof. by rewrite joinC umPtPtUE. Qed.

Definition umE := (umPtPtE, umPt0E, um0PtE, umPtUndefE, 
                   umUndefPtE, um0UndefE, umUndef0E, 
                   umPtUE, umUPtE, umPtUPtE, umPtPtUE, umUPtPtE, umPtUPt2E, 
                   (* plus a bunch of safe simplifications *)
                   unitL, unitR, validPt, valid_unit, eq_refl, empb0, empbPt, 
                   join_undefL, join_undefR, empb_undef).

End UMDecidableEquality.



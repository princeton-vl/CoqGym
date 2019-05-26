From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL
Require Import Freshness EqTypeX.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* An implementation of a dependent map structure *)

Module DepMaps.

Section DepMaps.

Definition Label := [ordType of nat].

Variable V : Type.
Variable labF: V -> Label.

Definition dmDom (u : union_map Label V) : bool :=
    all (fun l => if find l u is Some p then (labF p) == l else false) (dom u).

Record depmap := DepMap {
   dmap : union_map Label V;
   pf   : dmDom dmap;
}.

Section PCMOps.

Variable dm : depmap.

Lemma dmDom_unit : dmDom Unit.
Proof. by apply/allP=>l; rewrite dom0. Qed.

Definition unit := DepMap dmDom_unit.

End PCMOps.

Section DJoin.

Variables (dm1 dm2 : depmap). 

Lemma dmDom_join um1 um2:
  dmDom um1 -> dmDom um2 -> dmDom (um1 \+ um2).
Proof.
case; case W: (valid (um1 \+ um2)); last first.
- by move=> _ _; apply/allP=>l; move/dom_valid; rewrite W.
move/allP=>D1/allP D2; apply/allP=>l.
rewrite domUn inE=>/andP[_]/orP; rewrite findUnL//; case=>E; rewrite ?E.
- by apply: D1.
rewrite joinC in W; case: validUn W=>// _ _ /(_ l E)/negbTE->_.
by apply: D2.
Qed.

Definition join : depmap := DepMap (dmDom_join (@pf dm1) (@pf dm2)).

Definition valid (dm : depmap) := valid (dmap dm).

End DJoin.

End DepMaps.

Section PCMLaws.

Variables (V : Type) (labF: V -> [ordType of nat]).
Implicit Type f : depmap labF.


Local Notation "f1 \+ f2" := (join f1 f2)
                               (at level 43, left associativity).

Local Notation unit := (unit labF).

Lemma joinC f1 f2 : f1 \+ f2 = f2 \+ f1.
Proof.
case: f1 f2=>d1 pf1[d2 pf2]; rewrite /join/=.
move: (dmDom_join pf1 pf2) (dmDom_join pf2 pf1); rewrite joinC=>G1 G2.
by move: (eq_irrelevance G1 G2)=>->.
Qed.

Lemma joinCA f1 f2 f3 : f1 \+ (f2 \+ f3) = f2 \+ (f1 \+ f3).
Proof.
case: f1 f2 f3=>d1 pf1[d2 pf2][d3 pf3]; rewrite /join/=.
move: (dmDom_join pf1 (dmDom_join pf2 pf3)) (dmDom_join pf2 (dmDom_join pf1 pf3)).
by rewrite joinCA=>G1 G2; move: (eq_irrelevance G1 G2)=>->.
Qed.

Lemma joinA f1 f2 f3 : f1 \+ (f2 \+ f3) = (f1 \+ f2) \+ f3.
Proof.
case: f1 f2 f3=>d1 pf1[d2 pf2][d3 pf3]; rewrite /join/=.
move: (dmDom_join pf1 (dmDom_join pf2 pf3)) (dmDom_join (dmDom_join pf1 pf2) pf3).
by rewrite joinA=>G1 G2; move: (eq_irrelevance G1 G2)=>->.
Qed.

Lemma validL f1 f2 : valid (f1 \+ f2) -> valid f1.
Proof. by rewrite /join/valid/==>/validL. Qed.

Lemma unitL f : unit \+ f = f.
Proof.
rewrite /join/unit/=; case: f=>//=u pf.
move: pf (dmDom_join (dmDom_unit labF) pf); rewrite unitL=>g1 g2.
by move: (eq_irrelevance g1 g2)=>->.
Qed.

Lemma validU : valid unit.
Proof. by rewrite /unit/valid/=. Qed.


End PCMLaws.

Module Exports.
Section Exports.
Variable V : Type.
Variable labF: V -> Label.
Definition depmap := depmap.
Definition DepMap := DepMap.

Lemma dep_unit (d : depmap labF) : dmap d = Unit -> d = unit labF.
Proof.
case: d=>u pf/=; rewrite /unit. move: (dmDom_unit labF)=>pf' Z; subst u.
by rewrite (eq_irrelevance pf).
Qed.

Coercion dmap := dmap.
Definition ddom (d : depmap labF) := dom (dmap d).
Definition dfind x (d : depmap labF) := find x (dmap d).

Definition depmap_classPCMMixin :=
  PCMMixin (@joinC V labF) (@joinA V labF) (@unitL V labF) (@validL V labF) (validU labF).

Canonical depmap_classPCM := Eval hnf in PCM (depmap labF) depmap_classPCMMixin.


End Exports.
End Exports.

End DepMaps.

Export DepMaps.Exports.


(*
Copyright 2015 IMDEA Software Institute
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
(* This file contains an implementation of maps over non-zero natural         *)
(* numbers, pcm instance for natmap, gapless natmaps, natmaps with binary     *)
(* range, several sorts of continuous natmaps.                                *)
(* Histories are a special case of natmaps.                                   *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path.
From fcsl Require Import prelude ordtype pcm finmap unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(************************)
(************************)
(* Maps over non-0 nats *)
(************************)
(************************)

Module Type NMSig.
Parameter tp : Type -> Type.

Section Params.
Variable A : Type.
Notation tp := (tp A).

Parameter nm_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : nat -> A -> tp -> tp.
Parameter dom : tp -> seq nat.
Parameter dom_eq : tp -> tp -> bool.
Parameter free : nat -> tp -> tp. 
Parameter find : nat -> tp -> option A.
Parameter union : tp -> tp -> tp.
Parameter nm_filter : pred nat -> tp -> tp.
Parameter empb : tp -> bool.
Parameter undefb : tp -> bool.
Parameter pts : nat -> A -> tp.

Parameter from : tp -> @UM.base nat_ordType A (fun x => x != 0).
Parameter to : @UM.base nat_ordType A (fun x => x != 0) -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : nm_undef = to (@UM.Undef nat_ordType A (fun x => x != 0)). 
Axiom defE : forall f, defined f = UM.valid (from f). 
Axiom emptyE : empty = to (@UM.empty nat_ordType A (fun x => x != 0)). 
Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)). 
Axiom domE : forall f, dom f = UM.dom (from f). 
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2). 
Axiom freeE : forall k f, free k f = to (UM.free k (from f)). 
Axiom findE : forall k f, find k f = UM.find k (from f). 
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom nmfiltE : forall q f, nm_filter q f = to (UM.um_filter q (from f)).
Axiom empbE : forall f, empb f = UM.empb (from f). 
Axiom undefbE : forall f, undefb f = UM.undefb (from f). 
Axiom ptsE : forall k v, pts k v = to (@UM.pts nat_ordType A (fun x => x != 0) k v).

End Params.
End NMSig.


Module NMDef : NMSig.
Section NMDef.
Variable A : Type.

Definition nonz x := x != 0.

Definition tp : Type := @UM.base nat_ordType A nonz.

Definition nm_undef := @UM.Undef nat_ordType A nonz.
Definition defined f := @UM.valid nat_ordType A nonz f.
Definition empty := @UM.empty nat_ordType A nonz.
Definition upd k v f := @UM.upd nat_ordType A nonz k v f.
Definition dom f := @UM.dom nat_ordType A nonz f.
Definition dom_eq f1 f2 := @UM.dom_eq nat_ordType A nonz f1 f2.
Definition free k f := @UM.free nat_ordType A nonz k f.
Definition find k f := @UM.find nat_ordType A nonz k f.
Definition union f1 f2 := @UM.union nat_ordType A nonz f1 f2.
Definition nm_filter q f := @UM.um_filter nat_ordType A nonz q f.
Definition empb f := @UM.empb nat_ordType A nonz f.
Definition undefb f := @UM.undefb nat_ordType A nonz f.
Definition pts k v := @UM.pts nat_ordType A nonz k v.

Definition from (f : tp) : @UM.base nat_ordType A nonz := f.
Definition to (b : @UM.base nat_ordType A nonz) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : nm_undef = to (@UM.Undef nat_ordType A nonz). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty nat_ordType A nonz). Proof. by []. Qed.
Lemma updE k v f : upd k v f = to (UM.upd k v (from f)). Proof. by []. Qed.
Lemma domE f : dom f = UM.dom (from f). Proof. by []. Qed.
Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2). 
Proof. by []. Qed.
Lemma freeE k f : free k f = to (UM.free k (from f)). Proof. by []. Qed.
Lemma findE k f : find k f = UM.find k (from f). Proof. by []. Qed.
Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by []. Qed.
Lemma nmfiltE q f : nm_filter q f = to (UM.um_filter q (from f)).
Proof. by []. Qed.
Lemma empbE f : empb f = UM.empb (from f). Proof. by []. Qed.
Lemma undefbE f : undefb f = UM.undefb (from f). Proof. by []. Qed.
Lemma ptsE k v : pts k v = to (@UM.pts nat_ordType A nonz k v). 
Proof. by []. Qed.

End NMDef.
End NMDef.

Notation natmap := NMDef.tp.

Definition natmapMixin A := 
  UMCMixin (@NMDef.ftE A) (@NMDef.tfE A) (@NMDef.defE A) 
           (@NMDef.undefE A) (@NMDef.emptyE A) (@NMDef.updE A) 
           (@NMDef.domE A) (@NMDef.dom_eqE A) (@NMDef.freeE A)
           (@NMDef.findE A) (@NMDef.unionE A) (@NMDef.nmfiltE A)
           (@NMDef.empbE A) (@NMDef.undefbE A) (@NMDef.ptsE A).

Canonical nat_mapUMC A := 
  Eval hnf in UMC (natmap A) (@natmapMixin A).

(* we add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition nat_mapPCMMix A := union_map_classPCMMix (nat_mapUMC A).
Canonical nat_mapPCM A := Eval hnf in PCM (natmap A) (@nat_mapPCMMix A).

Definition nat_mapCPCMMix A := union_map_classCPCMMix (nat_mapUMC A).
Canonical nat_mapCPCM A := Eval hnf in CPCM (natmap A) (@nat_mapCPCMMix A).

Definition nat_mapTPCMMix A := union_map_classTPCMMix (nat_mapUMC A).
Canonical nat_mapTPCM A := Eval hnf in TPCM (natmap A) (@nat_mapTPCMMix A).

Definition nat_map_eqMix (A : eqType) := 
  @union_map_class_eqMix nat_ordType A _ _ (@natmapMixin A).
Canonical nat_map_eqType (A : eqType) := 
  Eval hnf in EqType (natmap A) (@nat_map_eqMix A).

Definition nm_pts A (k : nat) (v : A) := 
  @UMC.pts nat_ordType A (@nat_mapUMC A) k v. 

Notation "x \-> v" := (@nm_pts _ x v) (at level 30).


Lemma nm_dom0 A (h : natmap A) : (h = um_undef \/ h = Unit) <-> (dom h = [::]).
Proof.
split=>[|E]; first by case=>->; rewrite ?dom_undef ?dom0. 
case V : (valid h); last by move/invalidE: (negbT V)=>->; left.
by rewrite (dom0E V) ?E //; right.
Qed.

(***************************************)
(***************************************)
(* Constructions of last_key and fresh *)
(***************************************)
(***************************************)

Section FreshLastKey.
Variable A : Type.
Implicit Type h : natmap A. 

Definition last_key h := last 0 (dom h).
Definition fresh h := (last_key h).+1. 

Lemma lastkey_undef : last_key um_undef = 0.
Proof. by rewrite /last_key !umEX. Qed.

Lemma lastkey0 : last_key Unit = 0.
Proof. by rewrite /last_key /Unit /= !umEX. Qed.

Lemma lastkey_dom h : valid h -> last_key h \notin dom h -> h = Unit. 
Proof.
rewrite /valid /= /last_key /Unit /= !umEX /= -{4}[h]UMC.tfE.
case: (UMC.from h)=>//=; case=>s H /= H1 _ /seq_last_in. 
rewrite /UM.empty UMC.eqE UM.umapE /supp fmapE /= {H H1}.
by elim: s.
Qed.

Lemma dom_lastkey0P h : last_key h = 0 <-> dom h = [::].
Proof.
rewrite -nm_dom0; split; last first. 
- by case=>E; subst h; rewrite ?lastkey_undef ?lastkey0.
move=>E; case V : (valid h); last by left; move/invalidE: (negbT V). 
right; apply: lastkey_dom=>//; rewrite E.
by apply: contraT; rewrite negbK; apply: dom_cond.
Qed.

Lemma dom_lastkey h :  valid h -> ~~ empb h -> last_key h \in dom h.
Proof. by move=>X; apply: contraR; move/(lastkey_dom X)=>->; apply/empbP. Qed.

Lemma lastkeyxx h : valid h -> last_key h = 0 -> h = Unit.
Proof.
by move=>V H; apply: lastkey_dom V _; apply/negP=>/dom_cond; rewrite H.
Qed.

Lemma dom_lastkeyE h a : a < last_key h -> last_key h \in dom h.
Proof.
move=>H; case V : (valid h); last first.
- by move/invalidE: (negbT V) H=>->; rewrite lastkey_undef.
by apply: dom_lastkey V (contraL _ H)=>/empbE ->; rewrite lastkey0. 
Qed.

Lemma lastkey_max h x : x \in dom h -> x <= last_key h.
Proof.
rewrite /last_key /= !umEX; case: (UMC.from h)=>//; case=>s H _ /=. 
rewrite /supp /ord /= (leq_eqVlt x) orbC. 
by apply: sorted_last_key_max (sorted_oleq H).
Qed.

Lemma max_lastkey h x : 
        x \in dom h -> {in dom h, forall y, y <= x} -> last_key h = x.
Proof.
rewrite /last_key !umEX; case: (UMC.from h)=>//; case=>s H _ /=.
move=>H1 /= H2; apply: sorted_max_key_last (sorted_oleq H) H1 _. 
by move=>z /(H2 z); rewrite leq_eqVlt orbC. 
Qed.

Lemma lastkeyPt (x : nat) v : x != 0 -> last_key (x \-> v) = x.
Proof. by rewrite /last_key domPtK /= => ->. Qed.

Lemma hist_path h : path oleq 0 (dom h).
Proof.
rewrite !umEX; case: (UMC.from h)=>// {h} h /= _; case: h; case=>//= x s H.
rewrite {1}/oleq /ord /= orbC -leq_eqVlt /=.
by apply: sub_path H=>z y; rewrite /oleq=>->. 
Qed.

Lemma lastkey_mono h1 h2 : 
        {subset dom h1 <= dom h2} -> last_key h1 <= last_key h2.
Proof. by rewrite leq_eqVlt orbC; apply: seq_last_mono; apply: hist_path. Qed.

Lemma lastkeyfUn h1 h2 : 
        valid (h1 \+ h2) -> last_key h1 <= last_key (h1 \+ h2).
Proof. by move=>X; apply: lastkey_mono=>x; rewrite domUn inE X => ->. Qed.

Lemma lastkeyUnf h1 h2 : 
        valid (h1 \+ h2) -> last_key h2 <= last_key (h1 \+ h2).
Proof. by rewrite joinC; apply: lastkeyfUn. Qed.

(* a convenient rephrasing of above lemmas *)

Lemma lastkeyUn_mono h1 h2 t :
        valid (h1 \+ h2) -> last_key (h1 \+ h2) < t -> last_key h1 < t.
Proof.
move=>V; apply/leq_trans/lastkey_mono.
by move=>x D; rewrite domUn inE V D. 
Qed.

Lemma lastkeyUn0 h1 h2 : 
        valid (h1 \+ h2) -> 
        last_key h1 = last_key h2 -> (h1 = Unit) * (h2 = Unit).
Proof.
move=>V E.
case E1: (empb h1). 
- move/empbE: E1 E V=>->; rewrite unitL lastkey0.
  by case/esym/dom_lastkey0P/nm_dom0=>-> //; rewrite valid_undef.
case E2: (empb h2). 
- move/empbE: E2 E V=>->; rewrite unitR lastkey0.
  by case/dom_lastkey0P/nm_dom0=>-> //; rewrite valid_undef.
case: validUn (V)=>// _ _ /(_ _ (dom_lastkey (validL V) (negbT E1))).
by rewrite E (dom_lastkey (validR V) (negbT E2)).
Qed.

Lemma lastkeyUn h1 h2 :  
        last_key (h1 \+ h2) = 
        if valid (h1 \+ h2) then maxn (last_key h1) (last_key h2) else 0.
Proof.
have H k1 k2 : valid (k1 \+ k2) -> 
  last_key k1 < last_key k2 -> last_key (k1 \+ k2) = last_key k2.
- move=>V H; apply: max_lastkey=>[|x]. 
  - by rewrite domUn inE V (dom_lastkeyE H) orbT.
  rewrite domUn inE V; case/orP; move/lastkey_max=>// T;
  by apply: leq_trans T (ltnW H).
case V : (valid _); last first. 
- by move/invalidE: (negbT V)=>->; rewrite lastkey_undef.
rewrite /maxn; case: ltngtP. 
- by rewrite joinC in V *; apply: H.
- by apply: H.
by move/esym/(lastkeyUn0 V)=>E; rewrite !E unitL.
Qed.

Lemma lastkeyPtUn h t u : 
        valid h -> last_key h < t -> valid (t \-> u \+ h).
Proof.
move=>V L; rewrite validPtUn; apply/and3P; split=>//=.
- by rewrite -lt0n; apply: leq_ltn_trans L.
by apply: contraL L; move/lastkey_max; case: leqP.
Qed.

(* freshness *)

Lemma dom_ordfresh h x : x \in dom h -> x < fresh h.
Proof. by move/lastkey_max. Qed.

Lemma dom_freshn h n : fresh h + n \notin dom h.
Proof. by apply: contra (@dom_ordfresh _ _) _; rewrite -leqNgt leq_addr. Qed.

Lemma dom_freshUn h1 h2 : valid h1 -> [pcm h2 <= h1] -> fresh h1 \notin dom h2.
Proof.
move=>V [x E]; rewrite {h1}E in V *; apply: contra (@dom_ordfresh _ _) _.
by rewrite joinC in V *; rewrite -leqNgt; apply: lastkeyUnf. 
Qed.

Lemma dom_fresh h : fresh h \notin dom h.
Proof. by move: (dom_freshn h 0); rewrite addn0.  Qed.

Lemma valid_freshUn h1 h2 v : 
        valid h1 -> [pcm h2 <= h1] -> valid (fresh h1 \-> v \+ h2) = valid h2.
Proof.
move=>V [x E]; rewrite {h1}E in V *.
by rewrite validPtUn dom_freshUn // andbT.
Qed.

Lemma valid_fresh h v : valid (fresh h \-> v \+ h) = valid h.
Proof. by rewrite validPtUn dom_fresh andbT. Qed.

Lemma lastkey_freshUn h1 h2 v : 
        valid h1 -> [pcm h2 <= h1] -> 
        last_key (fresh h1 \-> v \+ h2) = fresh h1.
Proof.
move=>V [x E]; rewrite {h1}E in V *.
apply: max_lastkey=>[|y] /=.
- by rewrite domUn inE valid_freshUn // (validL V) domPt inE eq_refl.  
rewrite domUn inE valid_freshUn // (validL V) /= domPt inE /= eq_sym.
rewrite leq_eqVlt; case: eqP=>//= _ D.
by apply: lastkey_max; rewrite domUn inE V D.
Qed.

Lemma lastkey_fresh h v : valid h -> last_key (fresh h \-> v \+ h) = fresh h.
Proof. 
move=>Vf; apply: max_lastkey=>[|x] /=.
- by rewrite domUn inE valid_fresh Vf domPt inE eq_refl. 
rewrite domUn inE /= valid_fresh Vf /= domPt inE /= eq_sym.
by rewrite leq_eqVlt; case: eqP=>//= _; apply: dom_ordfresh.
Qed.

(* pcm induced ordering *)

Lemma umpleq_lastkey h1 h2 : 
        valid h2 -> [pcm h1 <= h2] -> last_key h1 <= last_key h2.
Proof.
by move=>V H; case: H V=>z->V; apply: lastkey_mono=>k D; rewrite domUn inE V D.
Qed.

(* backward induction on valid natmaps *)

Lemma valid_indb (P : natmap A -> Prop) : 
        P Unit ->
        (forall u, P (1 \-> u)) ->
        (forall t u h, P h -> last_key h < t -> 
                       valid (t \-> u \+ h) -> P (t \-> u \+ h)) ->
        forall h, valid h -> P h.
Proof.
move=>H1 H2 H3; elim/um_indb=>//=.
- by rewrite -[valid _]negbK; move/negP/invalidE.
move=>k v f H V K _.
case E: (empb f); last first.
- apply: H3=>//; first by apply: H (validR V).
  apply: K; apply: contraR (negbT E).
  by rewrite -empbE; apply: lastkey_dom (validR V).
move/empbE: {K H} E V=>->; rewrite unitR => V. 
move: (H3 k v Unit H1); rewrite unitR lastkey0 lt0n.
by apply=>//; rewrite validPt /= in V.
Qed.

(* forward induction on valid natmaps *)

Lemma valid_indf (P : natmap A -> Prop) : 
        P Unit ->
        (forall t u h, P h -> 
           (forall x, x \in dom h -> t < x) ->
           valid (t \-> u \+ h) -> P (t \-> u \+ h)) ->
        forall h, valid h -> P h.
Proof.
move=>H1 H2; elim/um_indf=>//=.
- by rewrite -[valid _]negbK; move/negP/invalidE.
move=>k v f H V K _.
apply: H2=>//; first by apply: H (validR V).
move=>x; move/(order_path_min (@ordtype.trans _)): K. 
by case: allP=>// X _; apply: X. 
Qed.

End FreshLastKey.


(*******************)
(*******************)
(* Gapless natmaps *)
(*******************)
(*******************)

Section Gapless.
Variable A : Type.
Implicit Type h : natmap A.

Definition gapless h := forall k, 0 < k <= last_key h -> k \in dom h.

Lemma gp_undef : gapless um_undef. 
Proof. by move=>k; rewrite lastkey_undef; case: k. Qed.

Lemma gp0 : gapless Unit.
Proof. by move=>k; rewrite lastkey0; case: k. Qed.

Lemma gp_fresh h u : gapless (fresh h \-> u \+ h) <-> gapless h.
Proof. 
case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite join_undefR.
split=>H k; move: (V); rewrite -(valid_fresh _ u)=>V'; last first. 
- rewrite lastkey_fresh // domPtUn inE V' /= (leq_eqVlt k) eq_sym.
  by move: (H k); rewrite -(ltnS k); case: ltngtP.
rewrite -(ltnS k) -/(fresh h); case/andP=>Z N.
move: (H k); rewrite lastkey_fresh // domPtUn inE V' Z /= leq_eqVlt eq_sym.
by case: ltngtP N=>//= _ _; apply. 
Qed.

Lemma gpPtUn h k u : 
        valid (k \-> u \+ h) -> 
        gapless (k \-> u \+ h) -> last_key h < k -> k = fresh h.
Proof.
move=>V C N; apply/eqP/contraT=>X. 
have Y : fresh h < k by rewrite leq_eqVlt eq_sym (negbTE X) in N.
suff Z : last_key (k \-> u \+ h) = k. 
- move: (C (fresh h)); rewrite Z (leq_eqVlt _ k) Y orbT andbT => /(_ erefl).
  rewrite domPtUn inE (negbTE X) /=; case/andP=>_ /dom_ordfresh.
  by rewrite ltnn.
apply: max_lastkey (find_some (findPtUn V)) _ => x. 
rewrite domUn inE; case/andP=>_ /orP [].
- by rewrite domPt inE; case/andP=>_ /eqP ->. 
by move/lastkey_max/leq_ltn_trans/(_ N)/ltnW.
Qed.
End Gapless.

Arguments gp_fresh [A][h] u. 


(*****************************)
(*****************************)
(* Natmaps with binary range *)
(*****************************)
(*****************************)

Section AtVal.
Variable A : Type.
Implicit Type h : natmap (A * A). 

Definition atval v t h := oapp snd v (find t h).

Lemma umpleq_atval v t h1 h2 : 
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 -> 
        atval v t h2 = atval v t h1.
Proof.
move=>G V H K; rewrite /atval; case E1 : (find t h1)=>[a|].
- by rewrite (umpleq_some V H E1).
case: t K E1 => [|t] K E1; last by move: (G t.+1 K) (find_none E1)=>->.
by case E2 : (find 0 h2)=>//; move/find_some/dom_cond: E2. 
Qed.

Definition last_val v h := atval v (last_key h) h.

Lemma lastval0 v : last_val v Unit = v. 
Proof. by rewrite /last_val /atval lastkey0 find0E. Qed.

Lemma lastvalPt v p x : p != 0 -> last_val v (p \-> x) = x.2.
Proof.
by move=>V; rewrite /last_val /atval lastkeyPt // findPt /= V. 
Qed.

Lemma lastval_fresh v x h : 
        valid h -> last_val v (fresh h \-> x \+ h) = x.2.
Proof. 
by move=>V; rewrite /last_val /atval lastkey_fresh // findPtUn // valid_fresh. 
Qed.

Lemma lastvalUn v h1 h2 :
        last_val v (h1 \+ h2) = 
        if valid (h1 \+ h2) then 
          if last_key h1 < last_key h2 then last_val v h2 else last_val v h1
        else v.
Proof.
rewrite /last_val /atval lastkeyUn maxnC /maxn.
case: ifP; last by move/negbT/invalidE=>->; rewrite find_undef. 
case: ltngtP=>N V.
- by rewrite findUnR // (dom_lastkeyE N).
- by rewrite findUnL // (dom_lastkeyE N).
by rewrite !(lastkeyUn0 V N) unitL lastkey0 find0E.
Qed.

Lemma lastval_freshUn v x h1 h2 : 
        valid h1 -> [pcm h2 <= h1] -> 
        last_val v (fresh h1 \-> x \+ h2) = x.2.
Proof.
move=>V H; rewrite /last_val /atval.
rewrite lastkey_freshUn // findPtUn // valid_freshUn //.
by case: H V=>h -> /validL.
Qed.

End AtVal.

(* Continuous maps with binary range *)

Section Continuous.
Variable A : Type.
Implicit Type h : natmap (A * A). 

Definition continuous v h := 
  forall k x, find k.+1 h = Some x -> oapp snd v (find k h) = x.1.

Lemma cn_undef v : continuous v um_undef.
Proof. by move=>x w; rewrite find_undef. Qed.

Lemma cn0 v : continuous v Unit.
Proof. by move=>x w; rewrite find0E. Qed.

Lemma cn_fresh v h x : 
        valid h -> 
        continuous v (fresh h \-> x \+ h) <-> 
        continuous v h /\ last_val v h = x.1.
Proof.
rewrite -(valid_fresh _ x)=>V; split; last first. 
- case=>C H k y; rewrite !findPtUn2 // eqSS; case: ltngtP=>N.
  - by rewrite ltn_eqF; [apply: C | apply: (ltn_trans N _)].
  - by move/find_some /dom_ordfresh /(ltn_trans N); rewrite ltnn. 
  by case=><-; rewrite N ltn_eqF.
move=>C; split; last first.
- move: (C (last_key h) x).
  by rewrite !findPtUn2 // eq_refl ltn_eqF //; apply. 
move=>k w; case: (ltnP k (last_key h))=>N; last first.
- by move/find_some /dom_ordfresh /(leq_ltn_trans N); rewrite ltnn. 
by move: (C k w); rewrite !findPtUn2 // eqSS !ltn_eqF // (ltn_trans N _).
Qed.

Lemma cn_sub v h x y k : 
        valid (k.+1 \-> (x, y) \+ h) -> continuous v (k.+1 \-> (x, y) \+ h) ->
        oapp snd v (find k h) = x.
Proof. 
by move=>V /(_ k (x, y)); rewrite !findPtUn2 // eq_refl ltn_eqF //; apply.
Qed.

End Continuous.

Arguments cn_fresh [A][v][h][x] _.

(* Complete natmaps with binary range *)

Section Complete.
Variable A : Type.
Implicit Type h : natmap (A * A).

Definition complete v0 h vn := 
  [/\ valid h, gapless h, continuous v0 h & last_val v0 h = vn].

Lemma cm_valid v0 h vn : complete v0 h vn -> valid h.
Proof. by case. Qed.

Lemma cm0 v : complete v Unit v.
Proof. by split=>//; [apply: gp0 | apply: cn0 | rewrite lastval0]. Qed.

Lemma cm_fresh v0 vn h x : 
        complete v0 (fresh h \-> x \+ h) vn <-> vn = x.2 /\ complete v0 h x.1. 
Proof.
split.
- by case=>/validR V /gp_fresh G /(cn_fresh V) []; rewrite lastval_fresh.
case=>-> [V] /(gp_fresh x) G C E; split=>//; 
by [rewrite valid_fresh | apply/(cn_fresh V) | rewrite lastval_fresh].
Qed.

Lemma cmPtUn v0 vn h k x : 
        complete v0 (k \-> x \+ h) vn -> last_key h < k -> k = fresh h.
Proof. by case=>V /(gpPtUn V). Qed.

Lemma cmPt v0 vn k x : complete v0 (k \-> x) vn -> k = 1 /\ x = (v0, vn). 
Proof.
case; rewrite validPt; case: k=>//= k _ /(_ 1).
rewrite lastkeyPt //= domPt inE /= => /(_ (erefl _))/eqP ->.
move/(_ 0 x); rewrite findPt findPt2 /= => -> //. 
by rewrite /last_val lastkeyPt // /atval findPt /= => <-; case: x. 
Qed.

Lemma cmCons v0 vn k x h : 
        complete v0 (k \-> x \+ h) vn -> last_key h < k -> 
         [/\ k = fresh h, vn = x.2 & complete v0 h x.1].
Proof. by move=>C H; move: {C} (cmPtUn C H) (C)=>-> /cm_fresh []. Qed.

End Complete.

Prenex Implicits cm_valid cmPt.


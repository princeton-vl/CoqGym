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
(* This file defines finitely supported maps with keys drawn from             *)
(* an ordered type and values from an arbitrary type.                         *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path.
From fcsl Require Import ordtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Def. 
Variables (K : ordType) (V : Type).

Definition key (x : K * V) := x.1.
Definition value (x : K * V) := x.2.
Definition predk k := preim key (pred1 k).  
Definition predCk k := preim key (predC1 k).

Record finMap := FinMap {
  seq_of : seq (K * V); 
  _ : sorted ord (map key seq_of)}.

Definition finMap_for of phant (K -> V) := finMap.

Identity Coercion finMap_for_finMap : finMap_for >-> finMap.
End Def.

Notation "{ 'finMap' fT }" := (finMap_for (Phant fT))
  (at level 0, format "{ 'finMap'  '[hv' fT ']' }") : type_scope.

Prenex Implicits key value predk predCk seq_of.

Section Ops.     
Variables (K : ordType) (V : Type).
Notation fmap := (finMap K V). 
Notation key := (@key K V). 
Notation value := (@value K V).
Notation predk := (@predk K V).
Notation predCk := (@predCk K V). 

Lemma fmapE (s1 s2 : fmap) : s1 = s2 <-> seq_of s1 = seq_of s2.
Proof.
split=>[->|] //.
move: s1 s2 => [s1 H1] [s2 H2] /= H.
by rewrite H in H1 H2 *; rewrite (bool_irrelevance H1 H2).
Qed.   

Lemma sorted_nil : sorted ord (map key [::]). Proof. by []. Qed.
Definition nil := FinMap sorted_nil.

Definition fnd k (s : fmap) := 
  if (filter (predk k) (seq_of s)) is (_, v):: _ 
  then Some v else None.

Fixpoint ins' (k : K) (v : V) (s : seq (K * V)) {struct s} : seq (K * V) :=
  if s is (k1, v1)::s1 then 
    if ord k k1 then (k, v)::s else
      if k == k1 then (k, v)::s1 else (k1, v1)::(ins' k v s1)
  else [:: (k, v)]. 
        
Lemma path_ins' s k1 k2 v : 
        ord k1 k2 -> path ord k1 (map key s) ->
          path ord k1 (map key (ins' k2 v s)).
Proof.
elim: s k1 k2 v=>[|[k' v'] s IH] k1 k2 v H1 /=; first by rewrite H1.
case/andP=>H2 H3; case: ifP=>/= H4; first by rewrite H1 H3 H4.
case: ifP=>H5 /=; first by rewrite H1 (eqP H5) H3.
by rewrite H2 IH //; move: (total k2 k'); rewrite H4 H5.
Qed.

Lemma sorted_ins' s k v : 
        sorted ord (map key s) -> sorted ord (map key (ins' k v s)). 
Proof.
case: s=>// [[k' v']] s /= H.
case: ifP=>//= H1; first by rewrite H H1.
case: ifP=>//= H2; first by rewrite (eqP H2).
by rewrite path_ins' //; move: (total k k'); rewrite H1 H2.
Qed.

Definition ins k v s := let: FinMap s' p' := s in FinMap (sorted_ins' k v p').

Lemma sorted_filter' k s : 
        sorted ord (map key s) -> sorted ord (map key (filter (predCk k) s)).
Proof. by move=>H; rewrite -filter_map sorted_filter //; apply: trans. Qed.

Definition rem k s := let: FinMap s' p' := s in FinMap (sorted_filter' k p').

Definition supp s := map key (seq_of s).

End Ops.

Prenex Implicits fnd ins rem supp.

Section Laws.
Variables (K : ordType) (V : Type). 
Notation fmap := (finMap K V). 
Notation nil := (nil K V).

Lemma ord_path (x y : K) s : ord x y -> path ord y s -> path ord x s.
Proof.
elim: s x y=>[|k s IH] x y //=.
by move=>H1; case/andP=>H2 ->; rewrite (trans H1 H2).
Qed.

Lemma last_ins' (x : K) (v : V) s : 
        path ord x (map key s) -> ins' x v s = (x, v) :: s.
Proof. by elim: s=>[|[k1 v1] s IH] //=; case: ifP. Qed.

Lemma first_ins' (k : K) (v : V) s : 
        (forall x, x \in map key s -> ord x k) -> 
        ins' k v s = rcons s (k, v).
Proof.
elim: s=>[|[k1 v1] s IH] H //=.
move: (H k1); rewrite inE eq_refl; move/(_ (erefl _)).
case: totalP=>// O _; rewrite IH //.
by move=>x H'; apply: H; rewrite inE /= H' orbT.
Qed.

Lemma notin_path (x : K) s : path ord x s -> x \notin s.
Proof. 
elim: s=>[|k s IH] //=.
rewrite inE negb_or; case/andP=>T1 T2; case: eqP=>H /=.
- by rewrite H irr in T1.
by apply: IH; apply: ord_path T2.
Qed. 

Lemma path_supp_ord (s : fmap) k : 
        path ord k (supp s) -> forall m, m \in supp s -> ord k m.
Proof.
case: s=>s H; rewrite /supp /= => H1 m H2; case: totalP H1 H2=>//.
- by move=>H1 H2; move: (notin_path (ord_path H1 H2)); case: (m \in _). 
by move/eqP=>->; move/notin_path; case: (k \in _).
Qed.

Lemma notin_filter (x : K) s : 
        x \notin (map key s) -> filter (predk V x) s = [::].
Proof.
elim: s=>[|[k v] s IH] //=.
rewrite inE negb_or; case/andP=>H1 H2.
by rewrite eq_sym (negbTE H1); apply: IH.
Qed.         
   
Lemma fmapP (s1 s2 : fmap) : (forall k, fnd k s1 = fnd k s2) -> s1 = s2. 
Proof.
rewrite /fnd; move: s1 s2 => [s1 P1][s2 P2] H; rewrite fmapE /=.
elim: s1 P1 s2 P2 H=>[|[k v] s1 IH] /= P1.
- by case=>[|[k2 v2] s2 P2] //=; move/(_ k2); rewrite eq_refl.
have S1: sorted ord (map key s1) by apply: path_sorted P1.
case=>[|[k2 v2] s2] /= P2; first by move/(_ k); rewrite eq_refl.
have S2: sorted ord (map key s2) by apply: path_sorted P2.
move: (IH S1 s2 S2)=>{IH} /= IH H.
move: (notin_path P1) (notin_path P2)=>N1 N2.
case E: (k == k2).
- rewrite -{k2 E}(eqP E) in P2 H N2 *.
  move: (H k); rewrite eq_refl=>[[E2]]; rewrite -E2 {v2 E2} in H *.
  rewrite IH // => k'.
  case E: (k == k'); first by rewrite -(eqP E) !notin_filter.
  by move: (H k'); rewrite E.
move: (H k); rewrite eq_refl eq_sym E notin_filter //.
move: (total k k2); rewrite E /=; case/orP=>L1.
- by apply: notin_path; apply: ord_path P2.
move: (H k2); rewrite E eq_refl notin_filter //.
by apply: notin_path; apply: ord_path P1.
Qed.

Lemma predkN (k1 k2 : K) : predI (predk V k1) (predCk V k2) =1 
                           if k1 == k2 then pred0 else predk V k1.
Proof. 
by move=>x; case: ifP=>H /=; [|case: eqP=>//->]; rewrite ?(eqP H) ?andbN ?H. 
Qed.

CoInductive supp_spec x (s : fmap) : bool -> Type :=
| supp_spec_some v of fnd x s = Some v : supp_spec x s true
| supp_spec_none of fnd x s = None : supp_spec x s false. 

Lemma suppP x (s : fmap) : supp_spec x s (x \in supp s).
Proof. 
move E: (x \in supp s)=>b; case: b E; move/idP; last first.
- move=>H; apply: supp_spec_none.
  case E: (fnd _ _)=>[v|] //; case: H.
  rewrite /supp /fnd in E *; case: s E=>/=.
  elim=>[|[y w] s IH] H1 //=.
  case: ifP=>H; first by rewrite (eqP H) inE eq_refl.
  rewrite -topredE /= eq_sym H; apply: IH.
  by apply: path_sorted H1.
case: s; elim=>[|[y w] s IH] /= H1 //; rewrite /supp /= inE in IH *.
case: eqP=>[-> _|H] //=.
- by apply: (@supp_spec_some _ _ w); rewrite /fnd /= eq_refl.
move: (path_sorted H1)=>H1'; move/(IH H1'); case=>[v H2|H2]; 
[apply: (@supp_spec_some _ _ v) | apply: supp_spec_none];
by rewrite /fnd /=; case: eqP H=>// ->.
Qed.

Lemma suppE (s1 s2 : fmap) : supp s1 =i supp s2 <-> supp s1 = supp s2.
Proof.
split; last by move=>->.
case: s1 s2=>s1 H1 [s2 H2]; rewrite /supp /=. 
elim: s1 s2 H1 H2=>[|[k1 _] s1 IH][|[k2 _] s2] //=.
- by move=>_ _; move/(_ k2); rewrite inE eq_refl. 
- by move=>_ _; move/(_ k1); rewrite inE eq_refl.
case: (totalP k1 k2)=>/= O H1 H2.
- move/(_ k1); rewrite !inE eq_refl /= eq_sym.
  case: totalP O => //= O _.
  by move/(ord_path O)/notin_path/negbTE: H2=>->.
- rewrite -{k2 O}(eqP O) in H1 H2 *.
  move=>H; congr (_ :: _); apply: IH.
  - by apply: path_sorted H1.
  - by apply: path_sorted H2.
  move=>x; move: (H x); rewrite !inE /=. case: eqP=>// -> /= _.
  by move/notin_path/negbTE: H1=>->; move/notin_path/negbTE: H2=>->. 
move/(_ k2); rewrite !inE eq_refl /= eq_sym.
case: totalP O=>//= O _.
by move/(ord_path O)/notin_path/negbTE: H1=>->. 
Qed.

Lemma supp_nil : supp nil = [::]. Proof. by []. Qed.

Lemma supp_nilE (s : fmap) : (supp s = [::]) <-> (s = nil).
Proof. by split=>[|-> //]; case: s; case=>// H; rewrite fmapE. Qed.

Lemma supp_rem k (s : fmap) : 
        supp (rem k s) =i predI (predC1 k) (mem (supp s)).
Proof.
case: s => s H1 x; rewrite /supp inE /=.
by case H2: (x == k)=>/=; rewrite -filter_map mem_filter /= H2.
Qed.
 
Lemma supp_ins k v (s : fmap) : 
        supp (ins k v s) =i [predU pred1 k & supp s].
Proof. 
case: s => s H x; rewrite /supp inE /=.
elim: s x k v H=>[|[k1 v1] s IH] //= x k v H.
case: ifP=>H1 /=; first by rewrite inE.
case: ifP=>H2 /=; first by rewrite !inE (eqP H2) orbA orbb.
by rewrite !inE (IH _ _ _ (path_sorted H)) orbCA.
Qed.

Lemma fnd_empty k : fnd k nil = None. Proof. by []. Qed.   

Lemma fnd_rem k1 k2 (s : fmap) : 
        fnd k1 (rem k2 s) = if k1 == k2 then None else fnd k1 s.
Proof. 
case: s => s H; rewrite /fnd -filter_predI (eq_filter (predkN k1 k2)).
by case: eqP=>//; rewrite filter_pred0. 
Qed.

Lemma fnd_ins k1 k2 v (s : fmap) : 
        fnd k1 (ins k2 v s) = if k1 == k2 then Some v else fnd k1 s. 
Proof.
case: s => s H; rewrite /fnd /=.
elim: s k1 k2 v H=>[|[k' v'] s IH] //= k1 k2 v H.
- by case: ifP=>H1; [rewrite (eqP H1) eq_refl | rewrite eq_sym H1].
case: ifP=>H1 /=.
- by case: ifP=>H2; [rewrite (eqP H2) eq_refl | rewrite (eq_sym k1) H2].
case: ifP=>H2 /=. 
- rewrite (eqP H2).   
  by case: ifP=>H3; [rewrite (eqP H3) eq_refl | rewrite eq_sym H3].
case: ifP=>H3; first by rewrite -(eqP H3) eq_sym H2.
by apply: IH; apply: path_sorted H.
Qed.
 
Lemma ins_rem k1 k2 v (s : fmap) : 
        ins k1 v (rem k2 s) = 
        if k1 == k2 then ins k1 v s else rem k2 (ins k1 v s).
Proof.
move: k1 k2 v s.
have L3: forall (x : K) s, 
  path ord x (map key s) -> filter (predCk V x) s = s.
- move=>x t; move/notin_path; elim: t=>[|[k3 v3] t IH] //=.
  rewrite inE negb_or; case/andP=>T1 T2. 
  by rewrite eq_sym T1 IH.
have L5: forall (x : K) (v : V) s, 
  sorted ord (map key s) -> ins' x v (filter (predCk V x) s) = ins' x v s.
- move=>x v s; elim: s x v=>[|[k' v'] s IH] x v //= H.
  case H1: (ord x k').
  - case H2: (k' == x)=>/=; first by rewrite (eqP H2) irr in H1.
    by rewrite H1 L3 //; apply: ord_path H1 H.
  case H2: (k' == x)=>/=.
  - rewrite (eqP H2) eq_refl in H *.
    by rewrite L3 //; apply: last_ins' H.
  rewrite eq_sym H2 H1 IH //.
  by apply: path_sorted H.
move=>k1 k2 v [s H]. 
case: ifP=>H1; rewrite /ins /rem fmapE /=.
- rewrite {k1 H1}(eqP H1).
  elim: s k2 v H=>[|[k' v'] s IH] //= k2 v H.
  case H1: (k' == k2)=>/=.
  - rewrite eq_sym H1 (eqP H1) irr in H *.
    by rewrite L3 // last_ins'.
  rewrite eq_sym H1; case: ifP=>H3.
  - by rewrite L3 //; apply: ord_path H3 H.
  by rewrite L5 //; apply: path_sorted H.
elim: s k1 k2 H1 H=>[|[k' v'] s IH] //= k1 k2 H1 H; first by rewrite H1.
case H2: (k' == k2)=>/=.
- rewrite (eqP H2) in H *; rewrite H1. 
  case H3: (ord k1 k2)=>/=.
  - by rewrite H1 eq_refl /= last_ins' // L3 //; apply: ord_path H.
  by rewrite eq_refl /= IH //; apply: path_sorted H.
case H3: (ord k1 k')=>/=; first by rewrite H1 H2.
case H4: (k1 == k')=>/=; first by rewrite H1.
by rewrite H2 IH //; apply: path_sorted H.
Qed.
       
Lemma ins_ins k1 k2 v1 v2 (s : fmap) : 
        ins k1 v1 (ins k2 v2 s) = if k1 == k2 then ins k1 v1 s 
                                  else ins k2 v2 (ins k1 v1 s).
Proof.
rewrite /ins; case: s => s H; case H1: (k1 == k2); rewrite fmapE /=.
- rewrite (eqP H1) {H1}.
  elim: s H k2 v1 v2=>[|[k3 v3] s IH] /= H k2 v1 v2; 
    first by rewrite irr eq_refl.
  case: (totalP k2 k3)=>H1 /=; rewrite ?irr ?eq_refl //.
  case: (totalP k2 k3) H1=>H2 _ //.
  by rewrite IH //; apply: path_sorted H.
elim: s H k1 k2 H1 v1 v2=>[|[k3 v3] s IH] H k1 k2 H1 v1 v2 /=.
- rewrite H1 eq_sym H1.
  by case: (totalP k1 k2) H1=>H2 H1.
case: (totalP k2 k3)=>H2 /=.
- case: (totalP k1 k2) (H1)=>H3 _ //=; last first.
  - by case: (totalP k1 k3)=>//= H4; rewrite ?H2 ?H3.
  case: (totalP k1 k3)=>H4 /=.
  - case: (totalP k2 k1) H3=>//= H3.
    by case: (totalP k2 k3) H2=>//=.
  - rewrite (eqP H4) in H3. 
    by case: (totalP k2 k3) H2 H3.
  by case: (totalP k1 k3) (trans H3 H2) H4.
- rewrite -(eqP H2) {H2} (H1).
  case: (totalP k1 k2) (H1)=>//= H2 _; rewrite ?irr ?eq_refl //.
  rewrite eq_sym H1.
  by case: (totalP k2 k1) H1 H2.
case: (totalP k1 k3)=>H3 /=.  
- rewrite eq_sym H1.
  case: (totalP k2 k1) H1 (trans H3 H2)=>//.
  by case: (totalP k2 k3) H2=>//=.
- rewrite (eqP H3).
  by case: (totalP k2 k3) H2.
case: (totalP k2 k3)=>H4 /=.
- by move: (trans H4 H2); rewrite irr.
- by rewrite (eqP H4) irr in H2.
by rewrite IH //; apply: path_sorted H.
Qed. 

Lemma rem_empty k : rem k nil = nil. 
Proof. by rewrite fmapE. Qed.

Lemma rem_rem k1 k2 (s : fmap) : 
        rem k1 (rem k2 s) = if k1 == k2 then rem k1 s else rem k2 (rem k1 s).
Proof.
rewrite /rem; case: s => s H /=.
case H1: (k1 == k2); rewrite fmapE /= -!filter_predI; apply: eq_filter=>x /=.
- by rewrite (eqP H1) andbb.
by rewrite andbC.
Qed.

Lemma rem_ins k1 k2 v (s : fmap) : 
        rem k1 (ins k2 v s) = 
        if k1 == k2 then rem k1 s else ins k2 v (rem k1 s).
Proof.
rewrite /rem; case: s => s H /=; case H1: (k1 == k2); rewrite /= fmapE /=.
- rewrite (eqP H1) {H1}.
  elim: s k2 H=>[|[k3 v3] s IH] k2 /= H; rewrite ?eq_refl 1?eq_sym //.
  case: (totalP k3 k2)=>H1 /=; rewrite ?eq_refl //=; 
  case: (totalP k3 k2) H1=>//= H1 _.
  by rewrite IH //; apply: path_sorted H.
elim: s k1 k2 H1 H=>[|[k3 v3] s IH] k1 k2 H1 /= H; first by rewrite eq_sym H1.
case: (totalP k2 k3)=>H2 /=.
- rewrite eq_sym H1 /=.
  case: (totalP k3 k1)=>H3 /=; case: (totalP k2 k3) (H2)=>//=.
  rewrite -(eqP H3) in H1 *.
  rewrite -IH //; last by apply: path_sorted H. 
  rewrite last_ins' /= 1?eq_sym ?H1 //.
  by apply: ord_path H.
- by move: H1; rewrite (eqP H2) /= eq_sym => -> /=; rewrite irr eq_refl.
case: (totalP k3 k1)=>H3 /=.
- case: (totalP k2 k3) H2=>//= H2 _.
  by rewrite IH //; apply: path_sorted H.
- rewrite -(eqP H3) in H1 *.
  by rewrite IH //; apply: path_sorted H.
case: (totalP k2 k3) H2=>//= H2 _.
by rewrite IH //; apply: path_sorted H.
Qed.

Lemma rem_supp k (s : fmap) : 
        k \notin supp s -> rem k s = s.
Proof.
case: s => s H1; rewrite /supp !fmapE /= => H2.
elim: s H1 H2=>[|[k1 v1] s1 IH] //=; move/path_sorted=>H1.
rewrite inE negb_or; case/andP=>H2; move/(IH H1)=>H3.
by rewrite eq_sym H2 H3.
Qed.

Lemma fnd_supp k (s : fmap) : 
        k \notin supp s -> fnd k s = None.
Proof. by case: suppP. Qed.

Lemma fnd_supp_in k (s : fmap) : 
        k \in supp s -> exists v, fnd k s = Some v.
Proof. by case: suppP=>[v|]; [exists v|]. Qed.

Lemma cancel_ins k v (s1 s2 : fmap) : 
       k \notin (supp s1) -> k \notin (supp s2) -> 
         ins k v s1 = ins k v s2 -> s1 = s2.
Proof.
move: s1 s2=>[s1 p1][s2 p2]; rewrite !fmapE /supp /= {p1 p2}.
elim: s1 k v s2=>[k v s2| [k1 v1] s1 IH1 k v s2] /=.
- case: s2=>[| [k2 v2] s2] //= _.
  rewrite inE negb_or; case/andP=>H1 _; case: ifP=>// _.   
  by rewrite (negbTE H1); case=>E; rewrite E eq_refl in H1.
rewrite inE negb_or; case/andP=>H1 H2 H3. 
case: ifP=>H4; case: s2 H3=>[| [k2 v2] s2] //=.
- rewrite inE negb_or; case/andP=>H5 H6. 
  case: ifP=>H7; first by case=>->->->.
  by rewrite (negbTE H5); case=>E; rewrite E eq_refl in H5.
- by rewrite (negbTE H1)=>_; case=>E; rewrite E eq_refl in H1.
rewrite inE negb_or (negbTE H1); case/andP=>H5 H6.
rewrite (negbTE H5); case: ifP=>H7 /=.
- by case=>E; rewrite E eq_refl in H1.
by case=>->-> H; congr (_ :: _); apply: IH1 H.
Qed.

End Laws.

Section Append. 
Variable (K : ordType) (V : Type).
Notation fmap := (finMap K V).  
Notation nil := (nil K V).

Lemma seqof_ins k v (s : fmap) : 
        path ord k (supp s) -> seq_of (ins k v s) = (k, v) :: seq_of s.
Proof. by case: s; elim=>[|[k1 v1] s IH] //= _; case/andP=>->. Qed.

Lemma path_supp_ins k1 k v (s : fmap) : 
        ord k1 k -> path ord k1 (supp s) -> path ord k1 (supp (ins k v s)).
Proof.
case: s=>s p.
elim: s p k1 k v=>[| [k2 v2] s IH] //= p k1 k v H2; first by rewrite H2.
case/andP=>H3 H4.
have H5: path ord k1 (map key s) by apply: ord_path H4.
rewrite /supp /=; case: (totalP k k2)=>H /=.
- by rewrite H2 H H4.
- by rewrite H2 (eqP H) H4.
rewrite H3 /=.
have H6: sorted ord (map key s) by apply: path_sorted H5. 
by move: (IH H6 k2 k v H H4); case: s {IH p H4 H5} H6.
Qed.

Lemma path_supp_ins_inv k1 k v (s : fmap) :
        path ord k (supp s) -> path ord k1 (supp (ins k v s)) -> 
        ord k1 k && path ord k1 (supp s).
Proof.
case: s=>s p; rewrite /supp /= => H1; rewrite last_ins' //=.
by case/andP=>H2 H3; rewrite H2; apply: ord_path H3.
Qed.

(* forward induction principle *)
Lemma fmap_ind' (P : fmap -> Prop) : 
        P nil -> (forall k v s, path ord k (supp s) -> P s -> P (ins k v s)) -> 
        forall s, P s.
Proof.
move=>H1 H2; case; elim=>[|[k v] s IH] /= H.
- by rewrite (_ : FinMap _ = nil); last by rewrite fmapE.
have S: sorted ord (map key s) by apply: path_sorted H.  
rewrite (_ : FinMap _ = ins k v (FinMap S)); last by rewrite fmapE /= last_ins'.
by apply: H2.
Qed.

(* backward induction principle *)
Lemma fmap_ind'' (P : fmap -> Prop) : 
        P nil -> (forall k v s, (forall x, x \in supp s -> ord x k) -> 
                    P s -> P (ins k v s)) ->
        forall s, P s.
Proof.
move=>H1 H2; case; elim/last_ind=>[|s [k v] IH] /= H. 
- by rewrite (_ : FinMap _ = nil); last by rewrite fmapE.
have Sb: subseq (map key s) (map key (rcons s (k, v))).
- by elim: s {IH H}=>[|x s IH] //=; rewrite eq_refl. 
have S : sorted ord (map key s).
- by apply: subseq_sorted Sb H; apply: ordtype.trans.
have T : forall x : K, x \in map key s -> ord x k.
- elim: {IH Sb S} s H=>[|[k1 v1] s IH] //= L x.
  rewrite inE; case/orP; last by apply: IH; apply: path_sorted L.
  move/eqP=>->; elim: s {IH} L=>[|[x1 w1] s IH] /=; first by rewrite andbT. 
  by case/andP=>O /(ord_path O) /IH.  
rewrite (_ : FinMap _ = ins k v (FinMap S)). 
- by apply: H2 (IH _)=>x /T.
by rewrite fmapE /= first_ins'.
Qed.


Fixpoint fcat' (s1 : fmap) (s2 : seq (K * V)) {struct s2} : fmap :=
  if s2 is (k, v)::t then fcat' (ins k v s1) t else s1.

Definition fcat s1 s2 := fcat' s1 (seq_of s2).

Lemma fcat_ins' k v s1 s2 : 
        k \notin (map key s2) -> fcat' (ins k v s1) s2 = ins k v (fcat' s1 s2). 
Proof.
move=>H; elim: s2 k v s1 H=>[|[k2 v2] s2 IH] k1 v1 s1 //=.
rewrite inE negb_or; case/andP=>H1 H2.
by rewrite -IH // ins_ins eq_sym (negbTE H1).
Qed.

Lemma fcat_nil' s : fcat' nil (seq_of s) = s.
Proof.
elim/fmap_ind': s=>[|k v s L IH] //=.
by rewrite seqof_ins //= (_ : FinMap _ = ins k v nil) // 
     fcat_ins' ?notin_path // IH.
Qed.

Lemma fcat0s s : fcat nil s = s. Proof. by apply: fcat_nil'. Qed.
Lemma fcats0 s : fcat s nil = s. Proof. by []. Qed.

Lemma fcat_inss k v s1 s2 : 
        k \notin supp s2 -> fcat (ins k v s1) s2 = ins k v (fcat s1 s2).
Proof. by case: s2=>s2 p2 H /=; apply: fcat_ins'. Qed.

Lemma fcat_sins k v s1 s2 : 
        fcat s1 (ins k v s2) = ins k v (fcat s1 s2).
Proof.
elim/fmap_ind': s2 k v s1=>[|k1 v1 s1 H1 IH k2 v2 s2] //.
case: (totalP k2 k1)=>//= H2.
- have H: path ord k2 (supp (ins k1 v1 s1)).
  - by apply: (path_supp_ins _ H2); apply: ord_path H1.
  by rewrite {1}/fcat seqof_ins //= fcat_ins' ?notin_path.
- by rewrite IH ins_ins H2 IH ins_ins H2.
have H: path ord k1 (supp (ins k2 v2 s1)) by apply: (path_supp_ins _ H2).
rewrite ins_ins.
case: (totalP k2 k1) H2 => // H2 _.
rewrite {1}/fcat seqof_ins //= fcat_ins' ?notin_path // IH ?notin_path //. 
rewrite ins_ins; case: (totalP k2 k1) H2 => // H2 _; congr (ins _ _ _).
by rewrite -/(fcat s2 (ins k2 v2 s1)) IH.
Qed. 

Lemma fcat_rems k s1 s2 : 
        k \notin supp s2 -> fcat (rem k s1) s2 = rem k (fcat s1 s2).
Proof.
elim/fmap_ind': s2 k s1=>[|k2 v2 s2 H IH] k1 v1.
- by rewrite !fcats0.
rewrite supp_ins inE /= negb_or; case/andP=>H1 H2.
by rewrite fcat_sins IH // ins_rem eq_sym (negbTE H1) -fcat_sins.
Qed.

Lemma fcat_srem k s1 s2 : 
        k \notin supp s1 -> fcat s1 (rem k s2) = rem k (fcat s1 s2).
Proof.
elim/fmap_ind': s2 k s1=>[|k2 v2 s2 H IH] k1 s1.
- rewrite rem_empty fcats0.
  elim/fmap_ind': s1=>[|k3 v3 s3 H1 IH]; first by rewrite rem_empty.
  rewrite supp_ins inE /= negb_or.
  case/andP=>H2; move/IH=>E; rewrite {1}E . 
  by rewrite ins_rem eq_sym (negbTE H2).
move=>H1; rewrite fcat_sins rem_ins; case: ifP=>E.
- by rewrite rem_ins E IH.
by rewrite rem_ins E -IH // -fcat_sins.
Qed.

Lemma fnd_fcat k s1 s2 :  
        fnd k (fcat s1 s2) = 
        if k \in supp s2 then fnd k s2 else fnd k s1.
Proof.
elim/fmap_ind': s2 k s1=>[|k2 v2 s2 H IH] k1 s1.
- by rewrite fcats0.
rewrite supp_ins inE /=; case: ifP; last first.
- move/negbT; rewrite negb_or; case/andP=>H1 H2.
  by rewrite fcat_sins fnd_ins (negbTE H1) IH (negbTE H2).
case/orP; first by move/eqP=><-; rewrite fcat_sins !fnd_ins eq_refl.
move=>H1; rewrite fcat_sins !fnd_ins.
by case: ifP=>//; rewrite IH H1.
Qed.

Lemma supp_fcat s1 s2 : supp (fcat s1 s2) =i [predU supp s1 & supp s2].
Proof.
elim/fmap_ind': s2 s1=>[|k v s L IH] s1.
- by rewrite supp_nil fcats0 => x; rewrite inE /= orbF.
rewrite fcat_sins ?notin_path // => x.
rewrite supp_ins !inE /=. 
case E: (x == k)=>/=.
- by rewrite supp_ins inE /= E orbT.
by rewrite IH supp_ins inE /= inE /= E. 
Qed.

End Append.

(* an induction principle for pairs of finite maps with equal support *)

Section FMapInd.
Variables (K : ordType) (V : Type).
Notation fmap := (finMap K V).
Notation nil := (@nil K V).

Lemma supp_eq_ins (s1 s2 : fmap) k1 k2 v1 v2 :
        path ord k1 (supp s1) -> path ord k2 (supp s2) ->
          supp (ins k1 v1 s1) =i supp (ins k2 v2 s2) -> 
        k1 = k2 /\ supp s1 =i supp s2.
Proof.
move=>H1 H2 H; move: (H k1) (H k2).
rewrite !supp_ins !inE /= !eq_refl (eq_sym k2).
case: totalP=>/= E; last 1 first.
- by move: H1; move/(ord_path E); move/notin_path; move/negbTE=>->.
- by move: H2; move/(ord_path E); move/notin_path; move/negbTE=>->.
rewrite (eqP E) in H1 H2 H * => _ _; split=>// x; move: (H x).
rewrite !supp_ins !inE /=; case: eqP=>//= -> _.
by rewrite (negbTE (notin_path H1)) (negbTE (notin_path H2)).
Qed. 

Lemma fmap_ind2 (P : fmap -> fmap -> Prop) :
        P nil nil -> 
        (forall k v1 v2 s1 s2, 
           path ord k (supp s1) -> path ord k (supp s2) -> 
           P s1 s2 -> P (ins k v1 s1) (ins k v2 s2)) ->
        forall s1 s2, supp s1 =i supp s2 -> P s1 s2.
Proof.
move=>H1 H2; elim/fmap_ind'=>[|k1 v1 s1 T1 IH1];
elim/fmap_ind'=>[|k2 v2 s2 T2 _] //.
- by move/(_ k2); rewrite supp_ins inE /= eq_refl supp_nil.
- by move/(_ k1); rewrite supp_ins inE /= eq_refl supp_nil.
by case/supp_eq_ins=>// E; rewrite -{k2}E in T2 *; move/IH1; apply: H2.
Qed.

End FMapInd.






Section Filtering.
Variables (K : ordType) (V : Type).
Notation fmap := (finMap K V). 
Notation nil := (nil K V).

Definition kfilter' (p : pred K) (s : fmap) := 
  filter (fun kv => p kv.1) (seq_of s).

Lemma sorted_kfilter (p : pred K) s : sorted ord (map key (kfilter' p s)).
Proof.
by case: s=>s H; rewrite -filter_map path.sorted_filter //; apply: trans.
Qed.

Definition kfilter (p : pred K) (s : fmap) := FinMap (sorted_kfilter p s).

Lemma supp_kfilt (p : pred K) (s : fmap) : 
        supp (kfilter p s) = filter p (supp s).
Proof.
case: s; rewrite /supp /kfilter /kfilter' /=. 
elim=>[|[k v] s IH] //= /path_sorted /IH {IH} H.
by case E: (p k)=>//=; rewrite H.
Qed.

Lemma kfilt_nil (p : pred K) : kfilter p nil = nil.
Proof. by apply/fmapE. Qed.

Lemma fnd_kfilt (p : pred K) k (s : fmap) : 
        fnd k (kfilter p s) = 
        if p k then fnd k s else None.
Proof.
case: s; rewrite /fnd /kfilter /kfilter' /=.
elim=>[|[k1 v] s IH] /=; first by case: ifP.
move/path_sorted=>/IH {IH} H.
case: ifP=>E1 /=; first by case: ifP=>E2 //; rewrite -(eqP E2) E1.
case: ifP H=>E2 H //=; rewrite H; case: eqP=>// E3.
by rewrite -E3 E1 in E2.
Qed.

Lemma kfilt_ins (p : pred K) k v (s : fmap) : 
        kfilter p (ins k v s) = 
        if p k then ins k v (kfilter p s) else kfilter p s.
Proof.
apply/fmapP=>k2; case: ifP=>E1.
- by rewrite fnd_ins !fnd_kfilt fnd_ins; case: eqP=>// ->; rewrite E1. 
by rewrite !fnd_kfilt fnd_ins; case: eqP=>// ->; rewrite E1. 
Qed.

Lemma rem_kfilt (p : pred K) k (s : fmap) : 
        rem k (kfilter p s) = 
        if p k then kfilter p (rem k s) else kfilter p s.
Proof.
apply/fmapP=>k2; case: ifP=>E1.
- by rewrite fnd_rem !fnd_kfilt fnd_rem; case: eqP=>// ->; rewrite E1.  
by rewrite fnd_rem fnd_kfilt; case: eqP=>// ->; rewrite E1.
Qed.

Lemma kfilt_rem (p : pred K) k (s : fmap) : 
        kfilter p (rem k s) = 
        if p k then rem k (kfilter p s) else kfilter p s.
Proof.
apply/fmapP=>k2; case: ifP=>E1.
- by rewrite fnd_kfilt !fnd_rem fnd_kfilt; case: eqP=>// ->; rewrite E1.  
by rewrite !fnd_kfilt fnd_rem; case: eqP=>// ->; rewrite E1.
Qed.

(* filter and fcat *)

Lemma kfilt_fcat (p : pred K) (s1 s2 : fmap) : 
        kfilter p (fcat s1 s2) = fcat (kfilter p s1) (kfilter p s2).
Proof.
apply/fmapP=>k; rewrite fnd_kfilt !fnd_fcat !fnd_kfilt supp_kfilt mem_filter.
by case: ifP. 
Qed.

Lemma kfilter_pred0 (s : fmap) : kfilter pred0 s = nil.
Proof. by apply/fmapE; rewrite /= /kfilter' filter_pred0. Qed.

Lemma kfilter_predT (s : fmap) : kfilter predT s = s.
Proof. by apply/fmapE; rewrite /= /kfilter' filter_predT. Qed.

Lemma kfilter_predI p1 p2 (s : fmap) : 
        kfilter (predI p1 p2) s = kfilter p1 (kfilter p2 s).
Proof. by apply/fmapE; rewrite /= /kfilter' filter_predI. Qed.

Lemma kfilter_predU p1 p2 (s : fmap) : 
        kfilter (predU p1 p2) s = fcat (kfilter p1 s) (kfilter p2 s).
Proof.
apply/fmapP=>k; rewrite fnd_kfilt fnd_fcat !fnd_kfilt supp_kfilt mem_filter.
rewrite inE /=; case: (ifP (p1 k)); case: (ifP (p2 k))=>//=;
by [case: ifP | case: suppP].
Qed.

Lemma eq_in_kfilter p1 p2 s : 
        {in supp s, p1 =1 p2} -> kfilter p1 s = kfilter p2 s.
Proof.
move=>H; apply/fmapE; rewrite /= /kfilter'. 
case: s H; rewrite /supp /=; elim=>[|[k v] s IH] //=.
move/path_sorted/IH=>{IH} H H1.
have ->: p1 k = p2 k by apply: H1; rewrite inE /= eq_refl. 
by rewrite H // => x E; apply: H1; rewrite inE /= E orbT.
Qed.

End Filtering.

Section DisjointUnion.
Variable (K : ordType) (V : Type).
Notation fmap := (finMap K V).  
Notation nil := (nil K V).

Definition disj (s1 s2 : fmap) := 
  all (predC (fun x => x \in supp s2)) (supp s1). 

CoInductive disj_spec (s1 s2 : fmap) : bool -> Type :=
| disj_true of (forall x, x \in supp s1 -> x \notin supp s2) : 
    disj_spec s1 s2 true
| disj_false x of x \in supp s1 & x \in supp s2 : 
    disj_spec s1 s2 false.

Lemma disjP s1 s2 : disj_spec s1 s2 (disj s1 s2).
Proof.
rewrite /disj; case E: (all _ _); first by apply/disj_true/allP.
move: E; rewrite all_predC=>/negbFE H.
case E: {-1}(supp s1) (H)=>[|k ?]; first by rewrite E.
move/(nth_find k); move: H; rewrite has_find=>/(mem_nth k).
by apply: disj_false.
Qed.

Lemma disjC s1 s2 : disj s1 s2 = disj s2 s1.
Proof.
case: disjP; case: disjP=>//.
- by move=>x H1 H2; move/(_ x H2); rewrite H1.
by move=>H1 x H2; move/H1; rewrite H2.
Qed.  

Lemma disj_nil (s : fmap) : disj s nil.
Proof. by case: disjP. Qed.

Lemma disj_ins k v (s1 s2 : fmap) : 
        disj s1 (ins k v s2) = (k \notin supp s1) && (disj s1 s2).
Proof.
case: disjP=>[H|x H1]. 
- case E: (k \in supp s1)=>/=.
  - by move: (H _ E); rewrite supp_ins inE /= eq_refl.
  case: disjP=>// x H1 H2.
  by move: (H _ H1); rewrite supp_ins inE /= H2 orbT.
rewrite supp_ins inE /=; case/orP=>[|H2].
- by move/eqP=><-; rewrite H1.
rewrite andbC; case: disjP=>[H|y H3 H4] //=.
by move: (H _ H1); rewrite H2.
Qed.
   
Lemma disj_rem k (s1 s2 : fmap) : 
        disj s1 s2 -> disj s1 (rem k s2).
Proof.
case: disjP=>// H _; case: disjP=>// x; move/H. 
by rewrite supp_rem inE /= andbC; move/negbTE=>->.
Qed.

Lemma disj_remE k (s1 s2 : fmap) : 
        k \notin supp s1 -> disj s1 (rem k s2) = disj s1 s2.
Proof.
move=>H; case: disjP; case: disjP=>//; last first.
- move=>H1 x; move/H1; rewrite supp_rem inE /= => E.
  by rewrite (negbTE E) andbF.
move=>x H1 H2 H3; move: (H3 x H1) H. 
rewrite supp_rem inE /= negb_and H2 orbF negbK.
by move/eqP=><-; rewrite H1. 
Qed.

Lemma disj_fcat (s s1 s2 : fmap) : 
        disj s (fcat s1 s2) = disj s s1 && disj s s2.
Proof.
elim/fmap_ind': s s1 s2=>[|k v s L IH] s1 s2.
- by rewrite !(disjC nil) !disj_nil.
rewrite !(disjC (ins _ _ _)) !disj_ins supp_fcat inE /= negb_or. 
case: (k \in supp s1)=>//=.
case: (k \in supp s2)=>//=; first by rewrite andbF.
by rewrite -!(disjC s) IH.
Qed.

Lemma fcatC (s1 s2 : fmap) : disj s1 s2 -> fcat s1 s2 = fcat s2 s1.
Proof.
rewrite /fcat.
elim/fmap_ind': s2 s1=>[|k v s2 L IH] s1 /=; first by rewrite fcat_nil'.
rewrite disj_ins; case/andP=>D1 D2.
by rewrite fcat_ins' // -IH  // seqof_ins //= -fcat_ins' ?notin_path.
Qed.

Lemma fcatA (s1 s2 s3 : fmap) : 
        disj s2 s3 -> fcat (fcat s1 s2) s3 = fcat s1 (fcat s2 s3).
Proof.
move=>H.
elim/fmap_ind': s3 s1 s2 H=>[|k v s3 L IH] s1 s2 /=; first by rewrite !fcats0.
rewrite disj_ins; case/andP=>H1 H2.  
by rewrite fcat_sins ?notin_path // IH // fcat_sins ?notin_path // fcat_sins.
Qed.         

Lemma fcatAC (s1 s2 s3 : fmap) : 
        [&& disj s1 s2, disj s2 s3 & disj s1 s3] -> 
        fcat s1 (fcat s2 s3) = fcat s2 (fcat s1 s3).
Proof. by case/and3P=>H1 H2 H3; rewrite -!fcatA // (@fcatC s1 s2). Qed.

Lemma fcatCA (s1 s2 s3 : fmap) : 
        [&& disj s1 s2, disj s2 s3 & disj s1 s3] -> 
        fcat (fcat s1 s2) s3 = fcat (fcat s1 s3) s2.
Proof. 
by case/and3P=>H1 H2 H3; rewrite !fcatA // ?(@fcatC s2 s3) ?(disjC s3). 
Qed.

Lemma fcatsK (s s1 s2 : fmap) : 
        disj s1 s && disj s2 s -> fcat s1 s = fcat s2 s -> s1 = s2.
Proof.
elim/fmap_ind': s s1 s2=>// k v s.
move/notin_path=>H IH s1 s2; rewrite !disj_ins.
case/andP; case/andP=>H1 H2; case/andP=>H3 H4.
rewrite !fcat_sins // => H5.
apply: IH; first by rewrite H2 H4.
by apply: cancel_ins H5; rewrite supp_fcat negb_or /= ?H1?H3 H.
Qed.

Lemma fcatKs (s s1 s2 : fmap) : 
        disj s s1 && disj s s2 -> fcat s s1 = fcat s s2 -> s1 = s2.
Proof.
case/andP=>H1 H2. 
rewrite (fcatC H1) (fcatC H2); apply: fcatsK.
by rewrite -!(disjC s) H1 H2.
Qed.  

Lemma disj_kfilt p1 p2 s1 s2 : 
        disj s1 s2 -> disj (kfilter p1 s1) (kfilter p2 s2).
Proof.
elim/fmap_ind': s2 s1=>[|k v s _ IH] s1 /=.
- by rewrite kfilt_nil => _; case: disjP.
rewrite disj_ins; case/andP=>H1 H2; rewrite kfilt_ins.
case: ifP=>E; last by apply: IH.
rewrite disj_ins supp_kfilt mem_filter negb_and H1 orbT /=. 
by apply: IH.
Qed.

Lemma in_disj_kfilt p1 p2 s : 
        {in supp s, forall x, ~~ p1 x || ~~ p2 x} ->
        disj (kfilter p1 s) (kfilter p2 s).
Proof.
elim/fmap_ind': s=>[|k v s _ IH] //= H.
rewrite !kfilt_ins; case: ifP=>E1; case: ifP=>E2.
- move: (H k); rewrite E1 E2 supp_ins inE /= eq_refl /=. 
  by move/(_ (erefl _)).  
- rewrite disjC disj_ins disjC supp_kfilt mem_filter negb_and E2 /=.
  by apply: IH=>x S; apply: H; rewrite supp_ins inE /= S orbT. 
- rewrite disj_ins supp_kfilt mem_filter negb_and E1 /=.
  by apply: IH=>x S; apply: H; rewrite supp_ins inE /= S orbT. 
by apply: IH=>x S; apply: H; rewrite supp_ins inE /= S orbT. 
Qed.

End DisjointUnion. 

Section EqType. 
Variables (K : ordType) (V : eqType).

Definition feq (s1 s2 : finMap K V) := seq_of s1 == seq_of s2.

Lemma feqP : Equality.axiom feq.
Proof.
move=>s1 s2; rewrite /feq.
case: eqP; first by move/fmapE=>->; apply: ReflectT.
by move=>H; apply: ReflectF; move/fmapE; move/H.
Qed.

Canonical Structure fmap_eqMixin := EqMixin feqP. 
Canonical Structure fmap_eqType := EqType (finMap K V) fmap_eqMixin.
End EqType.

(* mapping a function over a contents of a finite map *)

Section Map.
Variables (K : ordType) (U V : Type) (f : U -> V). 

Definition mapf' (m : seq (K * U)) : seq (K * V) := 
  map (fun kv => (key kv, f (value kv))) m.

Lemma map_key_mapf (m : seq (K * U)) : map key (mapf' m) = map key m.
Proof. by elim: m=>[|[k v] m IH] //=; rewrite IH. Qed.

Lemma sorted_map (m : seq (K * U)) : 
        sorted ord (map key m) -> sorted ord (map key (mapf' m)). 
Proof.
elim: m=>[|[k v] m IH] //= H. 
rewrite path_min_sorted; first by apply: IH; apply: path_sorted H. 
move=>y; rewrite map_key_mapf. 
by apply/allP; apply: order_path_min H; apply: trans.
Qed.

Definition mapf (m : finMap K U) : finMap K V := 
  let: FinMap _ pf := m in FinMap (sorted_map pf).

Lemma mapf_ins k v s : mapf (ins k v s) = ins k (f v) (mapf s).
Proof.
case: s=>s H; apply/fmapE=>/=. 
elim: s k v H=>[|[k1 v1] s IH] //= k v H.
rewrite eq_sym; case: totalP=>O //=.
by rewrite IH // (path_sorted H).
Qed.
 
Lemma mapf_fcat s1 s2 : mapf (fcat s1 s2) = fcat (mapf s1) (mapf s2).
Proof.
elim/fmap_ind': s2 s1=>[|k v s2 H IH] s1 /=.
- rewrite fcats0; set j := FinMap _.
  by rewrite (_ : j = nil K V) ?fcat0s //; apply/fmapE.
by rewrite fcat_sins mapf_ins IH -fcat_sins mapf_ins.
Qed.

Lemma mapf_disjL s1 s2 s : mapf s1 = mapf s2 -> disj s1 s = disj s2 s.
Proof.
case: s1 s2 s=>s1 S1 [s2 S2][s S] /fmapE /=.
elim: s1 S1 s2 S2 s S=>[|[k v] s1 IH] /= S1; case=>//= [[k2 v2]] s2 S2 s S.
case=>E _; rewrite -{k2}E in S2 *.
move/(IH (path_sorted S1) _ (path_sorted S2) _ S).
by rewrite /disj /supp /= => ->.
Qed.

Lemma mapf_disj s1 s2 s1' s2' : 
        mapf s1 = mapf s2 -> mapf s1' = mapf s2' -> 
        disj s1 s1' = disj s2 s2'.
Proof.
move=>X1 X2; apply: eq_trans (mapf_disjL _ X1) _. 
by rewrite !(disjC s2); apply: mapf_disjL X2.
Qed.

End Map.

Section FoldFMap. 
Variables (A B: ordType) (V C: Type).

Definition foldfmap g (e: C) (s: finMap A V) :=
  foldr g e (seq_of s).


Lemma foldf_nil g e : foldfmap g e (@nil A V) = e.
Proof. by rewrite /foldfmap //=. Qed.

Lemma foldf_ins g e k v f: 
  path ord k (supp f) ->
  foldfmap g e (ins k v f) = g (k, v) (foldfmap g e f).
Proof. by move=> H; rewrite /foldfmap //= seqof_ins //. Qed.
End FoldFMap.

Section KeyMap.

Section MapDef.
Variables (A B: ordType) (V : Type).

Variable (f: A -> B).
Hypothesis Hf : forall x y, strictly_increasing f x y.

Definition mapk (m : finMap A V) : finMap B V := 
  foldfmap (fun p s => ins (f (key p)) (value p) s) (nil B V) m.

(* mapK preserves sorted *)

Lemma sorted_mapk m: 
  sorted ord (supp (mapk  m)).
Proof. case: (mapk m)=>[s]I //=. Qed.


Lemma path_mapk m k: path ord k (supp m) -> path ord (f k) (supp (mapk m)).
Proof.
elim/fmap_ind': m k =>// k1 v1 s P IH k.
rewrite {1}/supp //= {1}seqof_ins // /= => /andP [H]; move/IH=>H1.
by rewrite /mapk foldf_ins // /supp /= seqof_ins //= H1 andbT (Hf H).
Qed.

Lemma mapk_nil : mapk (nil A V) = nil B V.
Proof. by rewrite /mapk //=. Qed.


Lemma mapk_ins k v s :
   path  ord k (supp s) ->
  mapk (ins k v s) = ins (f k) v (mapk s).
Proof. by move=> H; rewrite /mapk foldf_ins =>//. Qed.
End MapDef.
Arguments mapk {A B V} f m.

Variables (A B C : ordType)(V : Type)(f : A -> B) (g : B -> C).
Hypothesis Hf : forall x y, strictly_increasing f x y.


Lemma map_id m : @mapk A A V id m = m.
Proof. 
by elim/fmap_ind': m=>// k v s L IH; rewrite -{2}IH /mapk foldf_ins //.
Qed.

Lemma map_comp m:
       mapk g (@mapk A B V f m) = mapk (comp g f) m.
Proof.
elim/fmap_ind': m  =>//= k v s P IH. 
rewrite [mapk (g \o f) _]mapk_ins //.
rewrite mapk_ins // mapk_ins //; first by rewrite IH. 
exact: (path_mapk Hf P).
Qed.
End KeyMap.
Arguments mapk {A B V} f m.

(* zipping two finite maps with equal domains and ranges *)
(* zip_p predicate is a test for when contents of the two maps *)
(* at a given key are "combinable". typically zip_p will test *)
(* that the types of contents are equal, in the case the map is *)
(* storing dynamics *)

Section Zip.
Variables (K : ordType) (V : Type) (zip_f : V -> V -> option V).
Variable (unit_f : V -> V).
Variable (comm : commutative zip_f). 
Variable (assoc : forall x y z, 
  obind (zip_f x) (zip_f y z) = obind (zip_f^~ z) (zip_f x y)).
Variable (unitL : forall x, zip_f (unit_f x) x = Some x). 
Variable (unitE : forall x y, 
  (exists z, zip_f x y = Some z) <-> unit_f x = unit_f y).

Fixpoint zip' (s1 s2 : seq (K * V)) :=
  match s1, s2 with 
    [::], [::] => Some [::]
  | (k1, v1)::s1', (k2, v2)::s2' => 
      if k1 == k2 then 
        if zip_f v1 v2 is Some v then 
          if zip' s1' s2' is Some s' then Some ((k1, v) :: s')
          else None
        else None
      else None
  | _, _ => None
  end.

Definition zip_unit' (s : seq (K * V)) := mapf' unit_f s.

Lemma zipC' s1 s2 : zip' s1 s2 = zip' s2 s1.
Proof.
elim: s1 s2=>[|[k1 v1] s1 IH]; first by case=>//; case. 
case=>[|[k2 v2] s2] //=; rewrite eq_sym; case: eqP=>// ->{k2}.
by rewrite comm IH.
Qed.

Lemma zipA' s1 s2 s3 : 
        obind (zip' s1) (zip' s2 s3) = obind (zip'^~ s3) (zip' s1 s2).
Proof.
elim: s1 s2 s3=>[|[k1 v1] s1 IH].
- case=>[|[k2 v2] s2]; case=>[|[k3 v3] s3] //=; case: eqP=>// ->{k2}.  
  by case: (zip_f v2 v3)=>// v; case: (zip' s2 s3).
case=>[|[k2 v2] s2]; case=>[|[k3 v3] s3] //=. 
- by case: eqP=>// ->{k1}; case: (zip_f v1 v2)=>// v; case: (zip' s1 s2).
case: (k2 =P k3)=>[->{k2}|E1] /=; last first. 
- case: (k1 =P k2)=>E2 //=.
  case: (zip_f v1 v2)=>// v.
  case: (zip' s1 s2)=>//= s.
  by rewrite E2; case: eqP E1.
case: (k1 =P k3)=>[->{k1}|E1] /=; last first.
- by case: (zip_f v2 v3)=>// v; case: (zip' s2 s3)=>//= s; case: eqP E1.
case E1: (zip_f v2 v3)=>[w1|]; last first.
- case E3: (zip_f v1 v2)=>[w3|] //.
  case S3: (zip' s1 s2)=>[t3|] //=; rewrite eq_refl.
  by move: (assoc v1 v2 v3); rewrite /obind/oapp E1 E3=><-. 
case S1: (zip' s2 s3)=>[t1|] /=; last first.
- case E3: (zip_f v1 v2)=>[w3|//].
  case S3: (zip' s1 s2)=>[t3|] //=; rewrite eq_refl.
  move: (IH s2 s3); rewrite /obind/oapp S1 S3=><-. 
  by case: (zip_f w3 v3).
rewrite eq_refl.
case E3: (zip_f v1 v2)=>[w3|]; 
move: (assoc v1 v2 v3); rewrite /obind/oapp E1 E3=>-> //=. 
case S3: (zip' s1 s2)=>[t3|]; 
move: (IH s2 s3); rewrite /obind/oapp S3 S1=>-> /=.
- by rewrite eq_refl.
by case: (zip_f w3 v3).
Qed.

Lemma zip_unitL' s : zip' (zip_unit' s) s = Some s. 
Proof. by elim: s=>[|[k v] s IH] //=; rewrite eq_refl unitL IH. Qed.

Lemma map_key_zip' s1 s2 s : 
        zip' s1 s2 = Some s -> map key s = map key s1.
Proof.
elim: s1 s2 s=>[|[k1 v1] s1 IH]; case=>[|[k2 v2] s2] //= s; first by case=><-.
case: eqP=>// ->{k1}; case: (zip_f v1 v2)=>// w; case Z: (zip' s1 s2)=>[t|//].
by case=><-; rewrite -(IH _ _ Z).
Qed.

Lemma zip_unitE' s1 s2 : 
        (exists s, zip' s1 s2 = Some s) <-> zip_unit' s1 = zip_unit' s2.
Proof.
split.
- case; elim: s1 s2 =>[|[k1 v1] s1 IH]; case=>// [[k2 v2] s2] s //=.
  case: eqP=>// <-{k2}.
  case E1: (zip_f v1 v2)=>[w|//]; case E2: (zip' s1 s2)=>[t|//] _.
  by move/IH: E2=>->; congr ((_, _)::_); apply/unitE; exists w. 
elim: s1 s2=>[|[k1 v1] s1 IH]; case=>//; first by exists [::]. 
case=>k2 v2 s2 //= [<-{k2}]; case/unitE=>s ->; case/IH=>t ->. 
by exists ((k1, s)::t); rewrite eq_refl. 
Qed.

Lemma zip_sorted' s1 s2 : 
        sorted ord (map key s1) -> 
        forall s, zip' s1 s2 = Some s -> sorted ord (map key s).
Proof. by move=>H s; move/map_key_zip'=>->. Qed.

Definition zip f1 f2 : option (finMap K V) := 
  match f1, f2 with 
    FinMap s1 pf1, FinMap s2 pf2 => 
      match zip' s1 s2 as z return zip' s1 s2 = z -> _ with 
        Some s => fun pf => Some (FinMap (zip_sorted' pf1 pf))
      | None => fun pf => None
     end (erefl _) 
  end.

Lemma zip_unit_sorted' s : 
        sorted ord (map key s) -> 
        sorted ord (map key (zip_unit' s)).
Proof.
rewrite (_ : map key s = map key (zip_unit' s)) //.
by apply: (map_key_zip' (s2:=s)); apply: zip_unitL'.
Qed.

Definition zip_unit f := 
  let: FinMap s pf := f in FinMap (zip_unit_sorted' pf).

Lemma zip_unitE f1 f2 : 
        (exists f, zip f1 f2 = Some f) <-> zip_unit f1 = zip_unit f2.
Proof.
case: f1 f2=>s1 H1 [s2 H2] /=; split.
- case=>s; move: (zip_sorted' _). 
  case E: (zip' s1 s2)=>[t|//] _ _; apply/fmapE=>/=. 
  by apply/zip_unitE'; exists t. 
case; case/zip_unitE'=>s E; move/(zip_sorted' H1): (E)=>T.
exists (FinMap T); move: (zip_sorted' _); rewrite E=>pf.
by congr Some; apply/fmapE. 
Qed.

(* Now lemmas for interaction of zip with the other primitives *)

Lemma zip_supp' s1 s2 s : zip' s1 s2 = Some s -> map key s = map key s1.
Proof.
elim: s1 s2 s=>[|[k1 v1] s1 IH] /=; first by case=>// s [<-].
case=>[|[k2 v2] s2] // s; case: eqP=>// ->{k1}.
case E: (zip_f v1 v2)=>[w|//]; case F: (zip' s1 s2)=>[t|//].
by move/IH: F=><- [<-]. 
Qed.

Lemma zip_supp f1 f2 f : 
        zip f1 f2 = Some f -> supp f =i supp f1.
Proof.
case: f1 f2 f=>s1 H1 [s2 H2] [s3 H3] /=; move: (zip_sorted' _).
case E: (zip' s1 s2)=>[t|//]; move=>pf [F x]; rewrite -{s3}F in H3 *.
by rewrite /supp (zip_supp' E).
Qed.

Lemma zip_filter' s1 s2 s x : 
        zip' s1 s2 = Some s -> 
        zip' (filter (predCk V x) s1) (filter (predCk V x) s2) = 
        Some (filter (predCk V x) s).
Proof.
elim: s1 s2 s=>[|[k1 v1] s1 IH]; case=>[|[k2 v2] s2] //= s; first by case=><-.
case: eqP=>// <-{k2}; case E1: (zip_f v1 v2)=>[a|//].
case E2: (zip' s1 s2)=>[t|//]; move/IH: E2=>E2 [<-{s}].
case: eqP=>[->{k1}|] /=; first by rewrite E2 eq_refl. 
by rewrite eq_refl E1 E2; case: eqP. 
Qed.

Lemma zip_rem f1 f2 f x :
        zip f1 f2 = Some f -> zip (rem x f1) (rem x f2) = Some (rem x f).
Proof.
case: f1 f2 f=>s1 H1 [s2 H2] [s3 H3] /=; do 2![move: (zip_sorted' _)].
case E1: (zip' s1 s2)=>[t|//]; case E2 : (zip' _ _)=>[q|];
rewrite (@zip_filter' _ _ _ _ E1) // in E2.
by case: E2=><-{q} pf1 pf2 [E]; congr Some; apply/fmapE; rewrite /= E. 
Qed.

Lemma zip_fnd f1 f2 f x (v : V) : 
        zip f1 f2 = Some f -> fnd x f = Some v ->
        exists v1, exists v2, 
          [/\ zip_f v1 v2 = Some v, fnd x f1 = Some v1 & fnd x f2 = Some v2].
Proof.
case: f1 f2 f=>s1 H1 [s2 H2] [s3 H3] /=; move: (zip_sorted' _).
case E1: (zip' s1 s2)=>[s|//] pf [E]; rewrite /fnd /=. 
clear H1 H2 H3 pf; rewrite -{s3}E.
elim: s1 s2 s E1=>[|[k1 v1] s1 IH]; case=>[|[k2 v2] s2] //= s.
- by case=><-.
case: eqP=>// <-{k2}; case E1: (zip_f v1 v2)=>[w|//].
case E2: (zip' s1 s2)=>[t|//][<-{s}] /=.
case: eqP=>[_ [<-]|_]; first by exists v1, v2. 
by case: (filter (predk V x) t) (IH _ _ E2).
Qed.

(* The other direction of the zip_fnd lemma *)

Lemma fnd_zip f1 f2 f x (v1 v2 : V) : 
        fnd x f1 = Some v1 -> fnd x f2 = Some v2 ->
        zip f1 f2 = Some f -> fnd x f = zip_f v1 v2.
Proof.
case: f1 f2=>s1 H1 [s2 H2] /=; move: (zip_sorted' _).
case E: (zip' s1 s2)=>[s|//] pf; rewrite /fnd /= => F1 F2. 
case=><-{f} /= {pf H1 H2}.
elim: s1 s2 s E F1 F2=>[|[k1 w1] s1 IH]; case=>[|[k2 w2] s2] //= s.
case: eqP=>// <-{k2}; case E1: (zip_f w1 w2)=>[w|//].
case E2: (zip' s1 s2)=>[t|//] [<-{s}]. 
case: eqP=>/=; last by case: eqP=>// _ _; apply: IH.
by move=>->{k1}; rewrite eq_refl; case=><- [<-]. 
Qed.

Lemma zunit0 : zip_unit (nil K V) = nil K V.
Proof. by apply/fmapE. Qed. 

Lemma zunit_ins f k v : zip_unit (ins k v f) = ins k (unit_f v) (zip_unit f).
Proof.
case: f=>s H; apply/fmapE=>/=; rewrite /zip_unit'.
elim: s k v H=>[|[k1 v1] s IH] //= k v H.
rewrite eq_sym; case: totalP=>//= O.
by rewrite IH // (path_sorted H).
Qed.

Lemma zunit_fcat f1 f2 : 
        zip_unit (fcat f1 f2) = fcat (zip_unit f1) (zip_unit f2).
Proof.
elim/fmap_ind': f2 f1=>[|k v f2 H IH] f1 /=.
- rewrite fcats0; set j := FinMap _.
  by rewrite (_ : j = nil K V) ?fcat0s //; apply/fmapE.
by rewrite fcat_sins zunit_ins IH -fcat_sins zunit_ins.
Qed.

Lemma zunit_supp f : supp (zip_unit f) = supp f.
Proof.          
case: f=>s H; rewrite /supp /= {H}. 
by elim: s=>[|[k v] s IH] //=; rewrite IH.
Qed.

Lemma zunit_disj f1 f2 : disj f1 f2 = disj (zip_unit f1) (zip_unit f2).
Proof.
case: disjP; case: disjP=>//; rewrite !zunit_supp.
- by move=>x H1 H2; move/(_ _ H1); rewrite H2. 
by move=>H x; move/H/negbTE=>->. 
Qed.

End Zip.


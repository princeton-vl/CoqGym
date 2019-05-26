From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
From fcsl
Require Import pred prelude ordtype finmap pcm unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Keys.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).

Lemma keys_last_mono f1 f2 k :
        path oleq k (dom f1) ->
        path oleq k (dom f2) ->
        (forall x, x \in dom f1 -> x \in dom f2) ->
        oleq (last k (dom f1)) (last k (dom f2)).
Proof.
rewrite !umEX; case: (UMC.from f1); first by move=>_ H _; apply: path_last H.
move=>{f1} f1 /= _ H1; case: (UMC.from f2)=>/=.
- by move=>_ /allP; case: (supp f1)=>//; rewrite /oleq eq_refl orbT.
by move=>{f2} f2 /= _; apply: seq_last_mono H1.
Qed.

End Keys.

(* Last_key and Fresh are constructs that work *)
(* for any union map with integer keys *)
(* Should be developed more generally for any union map class *)
(* with a proof that key U = nat, but I can't bother right now *)

Section FreshLastKey.
Variable V : Type.
Implicit Type f : union_map [ordType of nat] V.

Definition last_key f := last 0 (dom f).

Lemma last_key0 : last_key Unit = 0.
Proof. by rewrite /last_key /Unit /= !umEX. Qed.

Lemma last_key_dom f : valid f -> last_key f \notin dom f -> f = Unit.
Proof.
rewrite /valid /= /last_key /Unit /= !umEX /= -{4}[f]UMC.tfE.
case: (UMC.from f)=>//=; case=>s H /= H1 _ /seq_last_in.
rewrite /UM.empty UMC.eqE UM.umapE /supp fmapE /= {H H1}.
by elim: s.
Qed.

Lemma dom_last_key f :  valid f -> ~~ empb f -> last_key f \in dom f.
Proof. by move=>X; apply: contraR; move/(last_key_dom X)=>->; apply/empbP. Qed.

Lemma last_key_max f x : x \in dom f -> x <= last_key f.
Proof.
rewrite /last_key /= !umEX; case: (UMC.from f)=>//; case=>s H _ /=.
rewrite /supp /ord /= (leq_eqVlt x) orbC.
by apply: sorted_last_key_max (sorted_oleq H).
Qed.

Lemma max_key_last f x :
        x \in dom f -> {in dom f, forall y, y <= x} -> last_key f = x.
Proof.
rewrite /last_key !umEX; case: (UMC.from f)=>//; case=>s H _ /=.
move=>H1 /= H2; apply: sorted_max_key_last (sorted_oleq H) H1 _.
by move=>z /(H2 z); rewrite leq_eqVlt orbC.
Qed.

Lemma last_keyPt (x : nat) v : last_key (x \\-> v) = x.
Proof. by rewrite /last_key /um_pts /= !umEX. Qed.

Lemma hist_path f : path oleq 0 (dom f).
Proof.
rewrite !umEX; case: (UMC.from f)=>// {f} f /= _; case: f; case=>//= x s H.
rewrite {1}/oleq /ord /= orbC -leq_eqVlt /=.
by apply: sub_path H=>z y; rewrite /oleq=>->.
Qed.

Lemma last_key_mono f1 f2 :
        {subset dom f1 <= dom f2} -> last_key f1 <= last_key f2.
Proof.
rewrite leq_eqVlt orbC=>H; apply: (@keys_last_mono _ _ _ f1 f2);
try by apply: hist_path.
by move=>x /=; move: (H x).
Qed.

Lemma last_keyfUn f1 f2 :
        valid (f1 \+ f2) -> last_key f1 <= last_key (f1 \+ f2).
Proof. by move=>X; apply: last_key_mono=>x; rewrite domUn inE X => ->. Qed.

Lemma last_keyUnf f1 f2 :
        valid (f1 \+ f2) -> last_key f2 <= last_key (f1 \+ f2).
Proof. by rewrite joinC; apply: last_keyfUn. Qed.

(* freshness *)

Definition fresh f := (last_key f).+1.

Lemma dom_ordfresh f x : x \in dom f -> x < fresh f.
Proof. by move/last_key_max. Qed.

Lemma dom_freshn f n : fresh f + n \notin dom f.
Proof. by apply: contra (@dom_ordfresh _ _) _; rewrite -leqNgt leq_addr. Qed.

Lemma dom_fresh f : fresh f \notin dom f.
Proof. by move: (dom_freshn f 0); rewrite addn0.  Qed.

Lemma valid_fresh f v : valid (f \+ fresh f \\-> v) = valid f.
Proof. by rewrite joinC validPtUn dom_fresh andbT. Qed.

Lemma valid_fresh' f v i w :
  valid (f \+ i \\-> w) ->
  valid (f \+ fresh (f \+ i \\-> w) \\-> v).
Proof.
move=> W; rewrite joinC validPtUn.
move: (dom_fresh (f \+ i \\-> w)); rewrite domUn inE; rewrite W/=.
by rewrite negb_or=>/andP; case=>-> _;move/validL: W=>->.
Qed.

Lemma last_fresh f v : valid f -> last_key (f \+ fresh f \\-> v) = fresh f.
Proof.
move=>Vf; apply: max_key_last=>[|x] /=.
- by rewrite domUn inE valid_fresh Vf domPt inE eq_refl orbT.
rewrite domUn inE /= valid_fresh Vf /= domPt inE /= orbC eq_sym.
by rewrite leq_eqVlt; case: eqP=>//= _; apply: dom_ordfresh.
Qed.

End FreshLastKey.


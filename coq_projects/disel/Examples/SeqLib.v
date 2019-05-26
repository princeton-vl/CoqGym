From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Require Import Eqdep.

(*************************************************************)
(************ Some useful facts about sequences **************)
(*************************************************************)

Fixpoint remove_elem (xs : seq (nat * nat * seq nat)) e :=
  match xs with
  | x :: xs => if x == e then xs else x :: (remove_elem xs e)
  | [::] => [::]
  end.

Lemma remove_elem_all xs p e :
  all p xs -> all p (remove_elem xs e).
Proof.
elim:xs=>//x xs Hi/=/andP[H1 H2].
by case B: (x==e)=>//=; rewrite H1 (Hi H2).
Qed.  

Lemma remove_elem_in xs e :
  if e \in xs
  then perm_eq (e :: (remove_elem xs e)) xs = true
  else (remove_elem xs e) = xs.
Proof.
elim: xs=>//x xs Hi.
rewrite inE; case: ifP=>/=; last first.
- case/negbT/norP=>/negbTE; rewrite eq_sym=>->/negbTE Z.
  by rewrite Z in Hi; rewrite Hi.
case/orP.
- by move/eqP=>Z; subst e; rewrite eqxx; apply: perm_eq_refl.
move=>Z; rewrite Z in Hi; case: ifP=>X. 
- by move/eqP: X=>?; subst e; apply: perm_eq_refl.
rewrite -cat1s -[x::_]cat1s-[x::xs]cat0s -[x::xs]cat1s.
apply/perm_eqlP.
move: (perm_catCA [::e] [::x] (remove_elem xs e))=>/perm_eqlP H1.
rewrite !cat1s in H1.
rewrite  -(perm_cons x (e :: remove_elem xs e) xs) in Hi.
rewrite !cat1s !cat0s; apply/perm_eqlP.
by apply: (perm_eq_trans H1 Hi).
Qed.


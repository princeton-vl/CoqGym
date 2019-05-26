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
(* This file defines ordType - the structure for types with a decidable       *)
(* (strict) order relation.                                                   *)
(* ordType is a subclass of mathcomp's eqType                                 *)
(* This file also defines some important instances of ordType                 *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Module Ordered. 

Section RawMixin.

Structure mixin_of (T : eqType) := 
  Mixin {ordering : rel T; 
         _ : irreflexive ordering;
         _ : transitive ordering;
         _ : forall x y, [|| ordering x y, x == y | ordering y x]}.

End RawMixin.

(* the class takes a naked type T and returns all the *)
(* relatex mixins; the inherited ones and the added ones *)
Section ClassDef.

Record class_of (T : Type) := Class {
   base : Equality.class_of T; 
   mixin : mixin_of (EqType T base)}.

Local Coercion base : class_of >-> Equality.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

(* produce an ordered type out of the inherited mixins *)
(* equalize m0 and m by means of a phantom; will be exploited *)
(* further down in the definition of OrdType *)
Definition pack b (m0 : mixin_of (EqType T b)) := 
  fun m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := Eval hnf in EqType cT class.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Notation ordType := Ordered.type.
Notation OrdMixin := Mixin.
Notation OrdType T m := (@pack T _ m _ id).
Definition ord T : rel (sort T) := (ordering (mixin (class T))).
Notation "[ 'ordType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'ordType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType'  'of'  T ]") : form_scope.
End Exports.
End Ordered.
Export Ordered.Exports.

Definition oleq (T : ordType) (t1 t2 : T) := ord t1 t2 || (t1 == t2).

Prenex Implicits ord oleq.

Section Lemmas.
Variable T : ordType.
Implicit Types x y : T.

Lemma irr : irreflexive (@ord T). 
Proof. by case: T=>s [b [m]]. Qed.

Lemma trans : transitive (@ord T). 
Proof. by case: T=>s [b [m]]. Qed.

Lemma total x y : [|| ord x y, x == y | ord y x].
Proof. by case: T x y=>s [b [m]]. Qed. 

Lemma nsym x y : ord x y -> ord y x -> False.
Proof. by move=>E1 E2; move: (trans E1 E2); rewrite irr. Qed. 

Lemma orefl x : oleq x x.
Proof. by rewrite /oleq eq_refl orbT. Qed.

Lemma otrans : transitive (@oleq T).
Proof.
move=>x y z /=; case/orP; last by move/eqP=>->.
rewrite /oleq; move=>T1; case/orP; first by move/(trans T1)=>->.
by move/eqP=><-; rewrite T1. 
Qed.

Lemma sorted_oleq s : sorted (@ord T) s -> sorted (@oleq T) s.
Proof. by elim: s=>[|x s IH] //=; apply: sub_path=>z y; rewrite /oleq=>->. Qed.

End Lemmas. 

Hint Resolve orefl : core.

Section Totality.
Variable K : ordType.  
 
CoInductive total_spec (x y : K) : bool -> bool -> bool -> Type :=
| total_spec_lt of ord x y : total_spec x y true false false
| total_spec_eq of x == y : total_spec x y false true false
| total_spec_gt of ord y x : total_spec x y false false true.

Lemma totalP x y : total_spec x y (ord x y) (x == y) (ord y x).
Proof.
case H1: (x == y).
- by rewrite (eqP H1) irr; apply: total_spec_eq.
case H2: (ord x y); case H3: (ord y x). 
- by case: (nsym H2 H3). 
- by apply: total_spec_lt H2.
- by apply: total_spec_gt H3.
by move: (total x y); rewrite H1 H2 H3.
Qed.
End Totality. 


(* Monotone (i.e. strictly increasing) functions for Ord Types *)
Section Mono.
Variables (A B :ordType).

Definition strictly_increasing f x y := @ord A x y -> @ord B (f x) (f y).

Structure mono : Type := Mono 
           {fun_of: A -> B; _: forall x y, strictly_increasing fun_of x y}.

End Mono.
Arguments strictly_increasing {A B} f x y.
Arguments Mono {A B _} _.

Section NatOrd.
Lemma irr_ltn_nat : irreflexive ltn. Proof. by move=>x; rewrite /= ltnn. Qed.
Lemma trans_ltn_nat : transitive ltn. Proof. by apply: ltn_trans. Qed.
Lemma total_ltn_nat x y : [|| x < y, x == y | y < x].
Proof. by case: ltngtP. Qed.

Definition nat_ordMixin := OrdMixin irr_ltn_nat trans_ltn_nat total_ltn_nat.
Canonical Structure nat_ordType := OrdType nat nat_ordMixin.
End NatOrd.

Section ProdOrd.
Variables K T : ordType.

(* lexicographic ordering *)
Definition lex : rel (K * T) := 
  fun x y => if x.1 == y.1 then ord x.2 y.2 else ord x.1 y.1.

Lemma irr_lex : irreflexive lex.
Proof. by move=>x; rewrite /lex eq_refl irr. Qed.

Lemma trans_lex : transitive lex.
Proof.
move=>[x1 x2][y1 y2][z1 z2]; rewrite /lex /=.
case: ifP=>H1; first by rewrite (eqP H1); case: eqP=>// _; apply: trans.
case: ifP=>H2; first by rewrite (eqP H2) in H1 *; rewrite H1.
case: ifP=>H3; last by apply: trans. 
by rewrite (eqP H3)=>R1; move/(nsym R1).
Qed.

Lemma total_lex : forall x y, [|| lex x y, x == y | lex y x].
Proof.
move=>[x1 x2][y1 y2]; rewrite /lex /=.
case: ifP=>H1.
- rewrite (eqP H1) eq_refl -pair_eqE /= eq_refl /=; exact: total.
rewrite (eq_sym y1) -pair_eqE /= H1 /=.
by move: (total x1 y1); rewrite H1.
Qed.

Definition prod_ordMixin := OrdMixin irr_lex trans_lex total_lex.
Canonical Structure prod_ordType := Eval hnf in OrdType (K * T) prod_ordMixin.
End ProdOrd.

Section FinTypeOrd.
Variable T : finType.

Definition ordf : rel T :=
  fun x y => index x (enum T) < index y (enum T). 

Lemma irr_ordf : irreflexive ordf.
Proof. by move=>x; rewrite /ordf ltnn. Qed.

Lemma trans_ordf : transitive ordf.
Proof. by move=>x y z; rewrite /ordf; apply: ltn_trans. Qed.

Lemma total_ordf x y : [|| ordf x y, x == y | ordf y x].
Proof.
rewrite /ordf; case: ltngtP=>//= H; rewrite ?orbT ?orbF //.
have [H1 H2]: x \in enum T /\ y \in enum T by rewrite !mem_enum.
by rewrite -(nth_index x H1) -(nth_index x H2) H eq_refl.
Qed.

Definition fin_ordMixin := OrdMixin irr_ordf trans_ordf total_ordf.
End FinTypeOrd.

(* notation to let us write I_n instead of (ordinal_finType n) *)
Notation "[ 'fin_ordMixin' 'of' T ]" :=
  (fin_ordMixin _ : Ordered.mixin_of [eqType of T]) (at level 0).

Definition ordinal_ordMixin n := [fin_ordMixin of 'I_n].
Canonical Structure ordinal_ordType n := OrdType 'I_n (ordinal_ordMixin n).

Section SeqOrd.
Variable (T : ordType).

Fixpoint ords x  : pred (seq T) :=
  fun y => match x , y with
                 | [::] , [::] => false
                 | [::] ,  t :: ts => true
                 | x :: xs , y :: ys => if x == y then ords xs ys 
                                        else ord x y
                 | _ :: _ , [::] => false  
             end.

Lemma irr_ords : irreflexive ords.
Proof. by elim=>//= a l ->; rewrite irr; case:eqP=> //=. Qed.

Lemma trans_ords : transitive ords.
Proof.
elim=>[|y ys IHy][|x xs][|z zs]//=.
case:eqP=>//[->|H0];case:eqP=>//H; first by move/IHy; apply.
- by case:eqP=>//; rewrite -H; first (by move/H0).
case:eqP=>//[->|H1] H2; first by move/(nsym H2).
by move/(trans H2).
Qed.
 
Lemma total_ords : forall x y, [|| ords x y, x == y | ords y x].
Proof.
elim=>[|x xs IH][|y ys]//=; case:eqP=>//[->|H1]; 
 (case:eqP=>//= H; first (by rewrite orbT //=)). 
- by case:eqP=>//H3 ; case: (or3P (IH ys))=> [-> | /eqP H0 | ->];
 [ rewrite orTb // | apply: False_ind; apply: H; rewrite H0 | rewrite orbT //].
case:eqP; first by move/(esym)/H1. 
by move=>_ ;case: (or3P (total x y))=>[-> //| /eqP /H1 //| -> //]; rewrite orbT.
Qed.

Definition seq_ordMixin := OrdMixin irr_ords trans_ords total_ords.
Canonical Structure seq_ordType := Eval hnf in OrdType (seq T) seq_ordMixin.
End SeqOrd.

(* A trivial total ordering for Unit *)
Section unitOrd.
Let ordtt (x y : unit ) := false.

Lemma irr_tt : irreflexive ordtt.
Proof. by []. Qed.

Lemma trans_tt : transitive ordtt.
Proof. by []. Qed.

Lemma total_tt x y : [|| ordtt x y, x == y | ordtt y x ].
Proof. by []. Qed.

Let unit_ordMixin := OrdMixin irr_tt trans_tt total_tt.
Canonical Structure unit_ordType := Eval hnf in OrdType unit unit_ordMixin.
End unitOrd.


(* ordering with path, seq and last *)

Lemma seq_last_in (A : eqType) (s : seq A) x : 
        last x s \notin s -> s = [::].
Proof.
case: (lastP s)=>// {s} s y; case: negP=>//; elim; rewrite last_rcons.  
by elim: s=>[|y' s IH]; rewrite /= inE // IH orbT.
Qed.

Lemma path_last (A : ordType) (s : seq A) x : 
        path oleq x s -> oleq x (last x s).
Proof.
move/(order_path_min (@otrans _)); rewrite -nth_last.
by case: s =>// h s' /all_nthP->.
Qed.

(* in a sorted list, the last element is maximal *)
(* and the maximal element is last *)

Lemma sorted_last_key_max (A : ordType) (s : seq A) x y : 
        sorted oleq s -> x \in s -> oleq x (last y s).
Proof.
elim: s x y=>[|z s IH] //= x y H; rewrite inE /=.
case: eqP=>[->|] /= _; first by apply: path_last.
by apply: IH (path_sorted H).
Qed.

Lemma sorted_max_key_last (A : ordType) (s : seq A) x y : 
        sorted oleq s -> x \in s ->
        (forall z, z \in s -> oleq z x) -> last y s = x.
Proof.
elim: s x y => [|w s IH] //= x y; rewrite inE /=.
case: eqP=>[<- /= H1 _ H2 | _ H /= H1 H2]; last first.
- apply: IH (path_sorted H) H1 _ => z H3; apply: H2.
  by rewrite inE /= H3 orbT.
apply/eqP; move: (H2 (last x s)) (path_last H1); rewrite inE /= /oleq eq_sym.
case: totalP=>//=; case E: (last x s \in s)=>//. 
by move/negbT/seq_last_in: E=>->; rewrite irr. 
Qed.

Lemma seq_last_mono (A : ordType) (s1 s2 : seq A) x : 
        path oleq x s1 -> path oleq x s2 ->
        {subset s1 <= s2} -> 
        oleq (last x s1) (last x s2).
Proof.
case: s1=>/= [_ H1 _|a s]; first by apply: path_last H1.
case/andP=>H1 H2 H3 H; apply: sorted_last_key_max (path_sorted H3) _.
apply: {x s2 H1 H3} H; rewrite inE orbC -implyNb.
by case E: (_ \notin _) (@seq_last_in _ s a)=>//= ->. 
Qed.






(******************************************************************************
Finite orbit-stabilizer theorem.  Based on proof from Rahbar Virk's notes from
the University of Wisconsin
(www.math.wisc.edu/~virk/notes/pdf/orphans/orbit-stabilizer_thm.pdf)
Copyright 2008 Robert Kam

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************)

From Algebra Require Export Group_util.
From Algebra Require Export Fpart2.
From Algebra Require Export Parts3.
From Algebra Require Export Fmap.
From LinAlg Require Export seq_set_facts.
From LinAlg Require Export has_n_elements.
From LinAlg Require Export finite_subsets.
Require Export ClassicalDescription.

Fixpoint nsum (n:Nat) {struct n} : seq n Nat -> Nat :=
match n return (seq n Nat -> Nat) with
|O => fun x:seq 0 Nat => 0
|S m => fun x:seq (S m) Nat => (head x) + (nsum m (Seqtl x)) end.

Lemma nsum_comp:forall (n:Nat) (f f':seq n Nat),
f =' f' in _ -> nsum n f =' nsum n f' in _.
induction n. intros. simpl. auto.
intros. unfold nsum. fold nsum.
assert (HEADHEAD:head f = head f'). unfold head. apply H.
rewrite HEADHEAD.
assert (TLTL:nsum n (Seqtl f) =' nsum n (Seqtl f')). apply IHn.
change (Seqtl f =' Seqtl f' in _). apply Seqtl_comp. exact H.
rewrite TLTL. apply Refl. Qed.

Lemma pluscomp2:forall (n m p:Nat),n='m -> n+p =' m+p in Nat.
intros. rewrite H. apply Refl. Qed.

Lemma nsum_increment4:
forall (n:Nat) (v:seq n Nat) (i:fin n) (a:Nat) (H:a =' (v i) + 1),
nsum n (modify_seq v i a) =' nsum n v + 1.
intros. induction n. elimtype False; intuition.
unfold nsum in |- *. fold nsum in |- *.
elim (classic (i =' Build_finiteT (lt_O_Sn n) in _)).
intro I_ZERO.
assert (P1 : head (modify_seq v i a) =' a in _).
 apply Trans with (head (modify_seq v (Build_finiteT (lt_O_Sn n)) a)).
 apply head_comp. apply modify_comp. apply Refl. apply Refl. exact I_ZERO.
 apply modify_hd_hd.
rewrite P1.
assert (P2 : nsum n (Seqtl (modify_seq v i a)) =' nsum n (Seqtl v) in _).
 apply nsum_comp.
 apply Trans with (Seqtl (modify_seq v (Build_finiteT (lt_O_Sn n)) a)).
 change (Seqtl (modify_seq v i a)
 =' Seqtl (modify_seq v (Build_finiteT (lt_O_Sn n)) a) in _) in |- *.
 apply Seqtl_comp. apply modify_comp. apply Refl. apply Refl. exact I_ZERO.
 change (Seqtl (modify_seq v (Build_finiteT (lt_O_Sn n)) a)
 =' Seqtl v in _) in |- *. apply modify_hd_tl.
rewrite P2.
rewrite H.
assert (P3 : v i =' head v in _).
 unfold head in |- *. apply Map_compatible_prf. exact I_ZERO.
rewrite P3.
rewrite plus_comm. rewrite plus_permute. rewrite plus_assoc. apply Refl.
intro I_NZ.
assert (P4 : head (modify_seq v i a) =' head v in _).
 destruct i.
 assert (H''' : S (pred index) < S n).
 induction index. elimtype False; intuition. auto.
 apply Trans with (head (modify_seq v (Build_finiteT H''') a)).
 apply head_comp. apply modify_comp. apply Refl. apply Refl. simpl in |- *.
 induction index. elimtype False; intuition. auto.
 apply modify_tl_hd.
rewrite P4.
assert(P10:nsum n (Seqtl(modify_seq v i a)) =' nsum n (Seqtl v)+1 in _).
 destruct i.
 assert (H' : pred index < n).
 induction index. elimtype False; intuition.
 simpl in |- *. apply lt_S_n. exact in_range_prf.
 assert (H'' : S (pred index) < S n).
 apply lt_n_S. exact H'.
 apply Trans with (nsum n (Seqtl (modify_seq v (Build_finiteT H'') a))).
 apply nsum_comp.
 change (Seqtl (modify_seq v (Build_finiteT in_range_prf) a)
 =' Seqtl (modify_seq v (Build_finiteT H'') a) in _) in |- *.
 apply Seqtl_comp. apply modify_comp. apply Refl. apply Refl. simpl in |- *.
 induction index. elimtype False; intuition. auto.
 apply Trans with (nsum n (modify_seq (Seqtl v) (Build_finiteT H') a)).
 apply nsum_comp. apply modify_tl_tl with (v := v).
 apply IHn.
 rewrite H. apply pluscomp2. apply Trans with (v (Build_finiteT H'')).
 apply Map_compatible_prf. simpl in |- *.
 induction index. elimtype False; intuition. auto.
 apply Sym.
 change (Seqtl v (Build_finiteT H') =' v (Build_finiteT H'') in _) in |- *.
 apply Seqtl_to_seq.
rewrite P10. rewrite plus_assoc. apply Refl. Qed.

Lemma nsum_of_zeros:forall(n:Nat)(v:seq n Nat)
(Z:forall i:fin n,v i =' 0),nsum n v =' 0.
induction n. intros v Z. simpl. auto.
intros v Z.
apply Trans with (nsum(S n)(v(Build_finiteT(lt_O_Sn n));;Seqtl v)).
apply nsum_comp. apply conseq_hdtl. unfold nsum. fold nsum.
apply Trans with (head v+nsum n(Seqtl(v(Build_finiteT(lt_O_Sn n));;Seqtl v))).
apply pluscomp2. simpl. unfold head. auto.
apply Trans with (0+nsum n(Seqtl(v(Build_finiteT(lt_O_Sn n));;Seqtl v))).
apply pluscomp2. unfold head. apply Z. rewrite plus_0_l.
apply Trans with (nsum n(Seqtl v)). apply nsum_comp.
change (Seqtl(v(Build_finiteT(lt_O_Sn n));;Seqtl v) =' Seqtl v).
apply Seqtl_comp. apply Sym. apply conseq_hdtl.
apply IHn. destruct i.
apply Trans with (v(Build_finiteT(lt_n_S index n in_range_prf))).
apply (Seqtl_to_seq v). apply Z. Qed.

Lemma undo_modify:forall(c:Nat)(Q:seq c Nat)(i:fin c)(z:Nat),
modify_seq (modify_seq Q i z) i (Q i) =' Q.
intros. simpl. unfold Map_eq. intro j. destruct i. destruct j.
rename index into i. rename index0 into j.
rename in_range_prf into iH. rename in_range_prf0 into jH.
elim(classic(i=j)). intro H.
apply Trans with (modify_seq(modify_seq Q(Build_finiteT jH)z)
(Build_finiteT jH) (Q(Build_finiteT jH)) (Build_finiteT jH)).
apply modify_comp. apply Map_compatible_prf. auto.
apply modify_comp. apply Refl. apply Refl. auto. auto.
apply modify_seq_defprop. intro H.
apply Trans with
(modify_seq Q(Build_finiteT iH)z(Build_finiteT jH)).
apply modify_seq_modifies_one_elt. auto.
apply modify_seq_modifies_one_elt. auto. Qed.

Lemma P4helpr:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)(AH':full A =' seq_set AH)(AH'':distinct AH)
(c:Nat)(V:seq c(part_set G))
(Va:forall(i:fin c)(g:G),in_part g(V i)->in_part g A)
(Vb:forall(g:G)(H:in_part g A),exists i:fin c,in_part g(V i))
(Vc:forall(g:G)(H:in_part g A)(i i':fin c),
in_part g(V i)->in_part g(V i')->i =' i')
(V':seq c Nat)(V'a:forall(i:fin c),has_n_elements(V' i)(V i))
(i_:fin c)(i_H:in_part (subtype_elt(head AH))(V i_))
(j:fin c)(g:G)(gH:in_part g (
(modify_seq V i_(minus_part(V i_)(subtype_elt(head AH))))j
)),~g =' head(Map_embed AH).
intros. elim(classic(i_=' j)).
intro H.
assert(gH':in_part g(minus_part(V i_)(subtype_elt(head AH)))).
apply in_part_comp_r with (modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))j). exact gH.
apply Trans with (modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))i_).
apply Map_compatible_prf. apply Sym. exact H.
apply modify_seq_defprop.
simpl in gH'. elim gH'. intros gH1 gH2. exact gH2.
intro H.
assert(gH':in_part g(V j)).
apply in_part_comp_r with(modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))j). exact gH.
apply modify_seq_modifies_one_elt. unfold not. intro H1.
apply H. apply Sym. exact H1.
unfold not. intro gHEAD. apply H.
apply Vc with (g:=g)(i:=i_)(i':=j). apply (Va j). exact gH'.
apply in_part_comp_l with (subtype_elt(head AH)). exact i_H.
exact gHEAD. exact gH'. Qed.

Lemma P4helprr:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)(AH':full A =' seq_set AH)(AH'':distinct AH),
A =' seq_set(Map_embed AH).
intros. simpl. unfold eq_part. intro x. split.
intro H. assert(HYP:Pred_fun A x). auto.
set(hx:=Build_subtype(P:=A)(subtype_elt:=x)HYP).
set(M:=Map_to_equal_subsets AH' (set_to_full A)).
elim(has_index(M hx)). intros j jH. simpl. exists j.
apply Trans with (subtype_elt(seq_set AH(M hx))).
simpl. apply Refl. apply subtype_elt_comp. exact jH.
intro H. assert(HYP:Pred_fun (seq_set(Map_embed AH)) x). auto.
set(hx:=Build_subtype(P:=seq_set(Map_embed AH))(subtype_elt:=x)HYP).
elim(has_index hx). intros j jH.
apply in_part_comp_l with (Map_embed AH j).
apply Map_embed_prop.
apply Trans with(seq_set(Map_embed AH)hx). simpl. apply Refl.
exact jH. Qed.

Lemma P4:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)(AH':full A =' seq_set AH)(AH'':distinct AH)
(c:Nat)(V:seq c(part_set G))
(Va:forall(i:fin c)(g:G),in_part g(V i)->in_part g A)
(Vb:forall(g:G)(H:in_part g A),exists i:fin c,in_part g(V i))
(Vc:forall(g:G)(H:in_part g A)(i i':fin c),
in_part g(V i)->in_part g(V i')->i =' i')
(V':seq c Nat)(V'a:forall(i:fin c),has_n_elements(V' i)(V i))
(i_:fin c)(i_H:in_part (subtype_elt(head AH))(V i_))
(j:fin c)(g:G)(gH:in_part g (
(modify_seq V i_(minus_part(V i_)(subtype_elt(head AH))))j
)),in_part g (seq_set(Seqtl(Map_embed AH))).
intros. apply seq_set_head_or_tail. 
2:exact(P4helpr n G A AH AH' AH'' c V Va Vb Vc V' V'a i_ i_H j g gH).
apply in_part_comp_r with A. 2:exact(P4helprr n G A AH AH' AH'').
elim(classic(i_ =' j)).
intro H.
assert(H1:in_part g(minus_part(V i_)(subtype_elt(head AH)))).
apply in_part_comp_r with
(modify_seq V i_(minus_part(V i_)(subtype_elt(head AH)))j).
exact gH. apply Trans with
(modify_seq V i_(minus_part(V i_)(subtype_elt(head AH)))i_).
apply Map_compatible_prf. apply Sym. exact H.
apply modify_seq_defprop. simpl in H1. elim H1. intros H1a H1b.
apply (Va i_). exact H1a.
intro H.
assert(H1:in_part g(V j)). apply in_part_comp_r with
(modify_seq V i_(minus_part(V i_)(subtype_elt(head AH)))j).
exact gH. apply modify_seq_modifies_one_elt. unfold not.
intro H'. apply H. apply Sym. exact H'. apply(Va j). exact H1.
Qed.

Lemma seqtlobv:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)
(g:G)(gH:in_part g (seq_set(Seqtl(Map_embed AH)))),
in_part g A.
intros. assert(HYP:Pred_fun(seq_set(Seqtl(Map_embed AH)))g). auto.
set(hx:=Build_subtype(P:=seq_set(Seqtl(Map_embed AH)))
(subtype_elt:=g)HYP). elim(has_index hx).
intros j jH. apply in_part_comp_l with ((Map_embed(Seqtl AH))j).
apply Map_embed_prop. apply Trans with (Seqtl(Map_embed AH)j).
exact jH. apply Sym. apply Map_embed_Seqtl. Qed.

Lemma seq_set_head_or_tail_inv:
forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)(AH':full A =' seq_set AH)(AH'':distinct AH)
(g:G)(gH:in_part g (seq_set(Seqtl(Map_embed AH)))),
~g =' subtype_elt(head AH).
intros. assert(gH'':in_part g(seq_set(Map_embed(omit AH
(Build_finiteT(lt_O_Sn n)))))).
apply in_part_comp_r with(seq_set(Map_embed(Seqtl AH))).
apply in_part_comp_r with(seq_set(Seqtl(Map_embed AH))).
exact gH. apply seq_set_comp. apply Sym. apply Map_embed_Seqtl.
apply seq_set_comp. change(Map_embed(Seqtl AH) ='
Map_embed(omit AH(Build_finiteT(lt_O_Sn n)))).
apply Map_embed_comp. apply Sym.
change (omit AH(Build_finiteT(lt_O_Sn n)) =' Seqtl AH).
apply omit_head_is_seqtl. elim gH''. intros j2 j2H.
assert(DORA:~omit AH(Build_finiteT(lt_O_Sn n))j2
=' AH(Build_finiteT(lt_O_Sn n))).
apply distinct_omit_removes_all. exact AH''.
unfold not. intro H. apply DORA. Opaque omit.
simpl. unfold subtype_image_equal. apply Trans with g.
apply Sym. exact j2H. exact H. Qed.
Transparent omit.

Lemma P5:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)(AH':full A =' seq_set AH)(AH'':distinct AH)
(c:Nat)(V:seq c(part_set G))
(Va:forall(i:fin c)(g:G),in_part g(V i)->in_part g A)
(Vb:forall(g:G)(H:in_part g A),exists i:fin c,in_part g(V i))
(Vc:forall(g:G)(H:in_part g A)(i i':fin c),
in_part g(V i)->in_part g(V i')->i =' i')
(V':seq c Nat)(V'a:forall(i:fin c),has_n_elements(V' i)(V i))
(i_:fin c)(i_H:in_part (subtype_elt(head AH))(V i_)),
forall(g:G)(gH:in_part g (seq_set(Seqtl(Map_embed AH)))),
(exists i:fin c,in_part g
((modify_seq V i_ (minus_part(V i_)(subtype_elt(head AH)))) i)).
intros. elim(Vb g(seqtlobv n G A AH g gH)). intros j jH.
elim(classic(i_ =' j)). intro H. exists i_.
apply in_part_comp_r with(minus_part(V i_)(subtype_elt(head AH))).
2:apply Sym. 2:apply modify_seq_defprop.
simpl. split. apply in_part_comp_r with(V j). exact jH.
apply Map_compatible_prf. apply Sym. exact H.
exact (seq_set_head_or_tail_inv n G A AH AH' AH'' g gH).
intro H. exists j. apply in_part_comp_r with (V j). exact jH.
apply Sym. apply modify_seq_modifies_one_elt. unfold not.
intro H'. apply H. apply Sym. exact H'. Qed.

Lemma P6:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)(AH':full A =' seq_set AH)(AH'':distinct AH)
(c:Nat)(V:seq c(part_set G))
(Va:forall(i:fin c)(g:G),in_part g(V i)->in_part g A)
(Vb:forall(g:G)(H:in_part g A),exists i:fin c,in_part g(V i))
(Vc:forall(g:G)(H:in_part g A)(i i':fin c),
in_part g(V i)->in_part g(V i')->i =' i')
(V':seq c Nat)(V'a:forall(i:fin c),has_n_elements(V' i)(V i))
(i_:fin c)(i_H:in_part (subtype_elt(head AH))(V i_)),
forall(g:G)(H:in_part g (seq_set(Seqtl(Map_embed AH)))),
forall(i i':fin c),
in_part g((modify_seq V i_
(minus_part(V i_)(subtype_elt(head AH)))) i)->
in_part g((modify_seq V i_
(minus_part(V i_)(subtype_elt(head AH)))) i')->
i =' i'.
intros n G A AH AH' AH'' c V Va Vb Vc V' V'a i_ i_H g H
i i' iH i'H.
apply Vc with (g:=g). apply seqtlobv with (AH:=AH). exact H.
elim(classic(i_=' i)). intro iH'.
assert(G1:in_part g(minus_part(V i_)(subtype_elt(head AH)))).
apply in_part_comp_r with (modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))i). exact iH.
apply Trans with (modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))i_). apply Map_compatible_prf.
apply Sym. exact iH'. apply modify_seq_defprop.
simpl in G1. elim G1. intros iH'a iH'b.
apply in_part_comp_r with (V i_). exact iH'a.
apply Map_compatible_prf. exact iH'.
intro iH'.
apply in_part_comp_r with(modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))i). exact iH.
apply modify_seq_modifies_one_elt. unfold not. intro iH''.
apply iH'. apply Sym. exact iH''.
rename i' into j. rename i'H into jH.
elim(classic(i_=' j)). intro jH2.
assert(G3:in_part g(minus_part(V i_)(subtype_elt(head AH)))).
apply in_part_comp_r with (modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))j). exact jH.
apply Trans with (modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))i_). apply Map_compatible_prf.
apply Sym. exact jH2. apply modify_seq_defprop.
simpl in G3. elim G3. intros jHa jHb.
apply in_part_comp_r with (V i_). exact jHa.
apply Map_compatible_prf. exact jH2.
intro jHH.
apply in_part_comp_r with(modify_seq V i_(minus_part(V i_)
(subtype_elt(head AH)))j). exact jH.
apply modify_seq_modifies_one_elt. unfold not. intro jHHH.
apply jHH. apply Sym. exact jHHH. Qed.

Lemma Q8:forall(G:Setoid)(a:G)(A:part_set G)(n:Nat)
(FINA:has_n_elements n A)(H:in_part a A),n>0.
intros.
assert (H0:in_part a(empty G)->False). auto.
assert (H1:A =' empty G -> False).
intro H1a. simpl in H1a. unfold eq_part in H1a.
elim (H1a a). intros H1b H1c. apply H0. apply H1b. exact H.
assert (H2:n=0->False).
intro H2a. apply H1. apply has_zero_elements_then_empty.
rewrite H2a in FINA. exact FINA. apply (neq_O_lt n). auto. Qed.

Lemma shrink_one:forall(E:Setoid)(B:part_set E)
(k:Nat)(H:has_n_elements k B)(x:E)(Hx:in_part x B),
has_n_elements (k-1) (minus_part B x).
intros E B k H x xH. assert(K_POS:k>0).
apply (Q8 E x B k H xH).
induction k. assert(~0<0). apply (lt_irrefl 0).
elimtype False; intuition.
apply has_n_elements_comp with (n:=k) (B:=minus_part B x)
(C:=minus_part B x). 2:apply Refl. 2:induction k.
2:simpl. 2:auto. 2:simpl. 2:auto.
elim H. intros. inversion H0.
assert (HYP:Pred_fun B x). auto.
set (hx:=Build_subtype (P:=B)(subtype_elt:=x) HYP).
set (M:=Map_to_equal_subsets H1 (set_to_full B)).
assert (HASIND:exists i:fin (S k),seq_set x0 (M hx) =' x0 i).
apply has_index.
elim HASIND. intros i iH.
assert(G1:subtype_elt(x0 i)='x).
apply Trans with (subtype_elt(seq_set x0 (M hx))).
apply subtype_elt_comp. apply Sym. exact iH. simpl. apply Refl.
assert(F1:minus_part B x =' seq_set(Map_embed(omit x0 i))).
Opaque omit. simpl. unfold eq_part. intro z. split. intro zH.
simpl in zH. elim zH. intros zHa zHb.
assert(zHYP:Pred_fun B z). auto.
set(hz:=Build_subtype(P:=B)(subtype_elt:=z)zHYP).
elim(has_index(M hz)). intros k1 k1H.
assert(F2:~i =' k1). unfold not. intro F3. apply zHb.
apply Trans with (subtype_elt(x0 k1)).
apply Trans with (subtype_elt(seq_set x0(M hz))).
simpl. apply Refl. apply subtype_elt_comp. exact k1H.
apply Trans with (subtype_elt(x0 i)). apply subtype_elt_comp.
apply Map_compatible_prf. apply Sym. exact F3. exact G1.
elim(omit_removes' x0 F2). intros k2 k2H.
exists k2. simpl.
apply Trans with (subtype_elt(x0 k1)).
apply Trans with (subtype_elt(seq_set x0(M hz))).
simpl. apply Refl. apply subtype_elt_comp. exact k1H.
apply subtype_elt_comp. exact k2H.
intro zH. simpl in zH. elim zH. intros k2 k2H.
simpl. split. apply in_part_comp_l with (subtype_elt(omit x0 i k2)).
apply in_part_subtype_elt. exact k2H.
elim(omit_removes x0 i k2). intros k1 k1H.
assert(F4:~omit x0 i k2 =' x0 i). apply distinct_omit_removes_all.
exact H2. unfold not. intro F5.
assert(F6:subtype_elt(omit x0 i k2) =' subtype_elt(x0 i)).
apply Trans with z. apply Sym. exact k2H.
apply Trans with x. exact F5. apply Sym. exact G1.
apply F4. exact F6.
Transparent omit.
assert(F2:distinct(Map_embed(omit x0 i))).
apply Map_embed_preserves_distinct. apply omit_preserves_distinct.
exact H2.
apply seq_set_n_element_subset. exists(Map_embed(omit x0 i)).
split. exact F1. exact F2. Qed.

Lemma P7:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)(AH':full A =' seq_set AH)(AH'':distinct AH)
(c:Nat)(V:seq c(part_set G))
(Va:forall(i:fin c)(g:G),in_part g(V i)->in_part g A)
(Vb:forall(g:G)(H:in_part g A),exists i:fin c,in_part g(V i))
(Vc:forall(g:G)(H:in_part g A)(i i':fin c),
in_part g(V i)->in_part g(V i')->i =' i')
(V':seq c Nat)(V'a:forall(i:fin c),has_n_elements(V' i)(V i))
(i_:fin c)(i_H:in_part (subtype_elt(head AH))(V i_)),
forall(i:fin c),has_n_elements
(modify_seq V' i_ (V' i_ - 1) i)
((modify_seq V i_ (minus_part(V i_)(subtype_elt(head AH)))) i).
intros. rename i into j. elim(classic(i_ =' j)). intro H.
apply has_n_elements_comp with (n:=V' i_-1)
(B:=modify_seq V i_(minus_part(V i_)(subtype_elt(head AH)))i_).
apply has_n_elements_comp with (n:=V' i_-1)
(B:=minus_part(V i_)(subtype_elt(head AH))).
apply shrink_one. exact (V'a i_). exact i_H.
apply Sym. apply modify_seq_defprop. apply Refl.
apply Map_compatible_prf. exact H.
apply Trans with (modify_seq V' i_(V' i_-1)i_).
apply Sym. apply modify_seq_defprop. apply Map_compatible_prf.
exact H.
intro H. apply has_n_elements_comp with (n:=V' j)
(B:=modify_seq V i_(minus_part(V i_)(subtype_elt(head AH)))j).
apply has_n_elements_comp with (n:=V' j) (B:=V j).
exact (V'a j). apply Sym. apply modify_seq_modifies_one_elt.
unfold not. intro H'. apply H. apply Sym. exact H'.
apply Refl. apply Refl. apply Sym.
apply modify_seq_modifies_one_elt.
unfold not. intro H'. apply H. apply Sym. exact H'. Qed.

Lemma sqtlsqtl:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq(S n)A)(AH':full A =' seq_set AH)(AH'':distinct AH),
full(seq_set(Seqtl(Map_embed AH)))
=' seq_set(seq_set_seq(Seqtl(Map_embed AH))).
intros. Opaque Seqtl. simpl. unfold eq_part. intro x. split.
intro H. destruct x. simpl in subtype_prf.
simpl. unfold subtype_image_equal. simpl. exact subtype_prf.
intro H. simpl. auto. Qed.
Transparent Seqtl.

Lemma incexc3_basecase:forall(G:Setoid)(A:part_set G)
(AH:seq 0 A)(AH':full A =' seq_set AH)(AH'':distinct AH)
(c:Nat)(V:seq c(part_set G))
(Va:forall(i:fin c)(g:G),in_part g(V i)->in_part g A)
(Vb:forall(g:G)(H:in_part g A),exists i:fin c,in_part g(V i))
(Vc:forall(g:G)(H:in_part g A)(i i':fin c),
in_part g(V i)->in_part g(V i')->i =' i')
(V':seq c Nat)(V'a:forall(i:fin c),has_n_elements(V' i)(V i)),
nsum c V' =' 0.
intros. apply nsum_of_zeros. intro i.
apply has_n_elements_inj with (B:=V i)(C:=V i).
exact (V'a i). apply empty_then_has_zero_elements.
simpl. unfold eq_part. intro g. split.
intro H. apply in_part_comp_r with A. apply(Va i). exact H.
apply has_zero_elements_then_empty. unfold has_n_elements.
exists AH. split. exact AH'. exact AH''.
simpl. intuition. apply Refl. Qed.

Lemma incexc3:forall(n:Nat)(G:Setoid)(A:part_set G)
(AH:seq n A)(AH':full A =' seq_set AH)(AH'':distinct AH)
(c:Nat)(V:seq c(part_set G))
(Va:forall(i:fin c)(g:G),in_part g(V i)->in_part g A)
(Vb:forall(g:G)(H:in_part g A),exists i:fin c,in_part g(V i))
(Vc:forall(g:G)(H:in_part g A)(i i':fin c),
in_part g(V i)->in_part g(V i')->i =' i')
(V':seq c Nat)(V'a:forall(i:fin c),has_n_elements(V' i)(V i)),
nsum c V' =' n.
induction n. apply incexc3_basecase. intros.
set(a:=subtype_elt(head AH)). elim(Vb a). intros i_ i_H.
2:unfold a. 2:apply in_part_subtype_elt.
set(V_:=modify_seq V i_(minus_part(V i_)a)).
set(V_':=modify_seq V' i_(V' i_-1)).
assert(V_'a:forall i:fin c,has_n_elements(V_' i)(V_ i)).
apply (P7 n G A AH AH' AH'' c V Va Vb Vc V' V'a i_ i_H).
assert(V_a:forall(i:fin c)(g:G),in_part g(V_ i)
->in_part g(seq_set(Seqtl(Map_embed AH)))).
apply (P4 n G A AH AH' AH'' c V Va Vb Vc V' V'a i_ i_H).
assert(V_b:forall g:G,in_part g(seq_set(Seqtl(Map_embed AH)))
->exists i:fin c,in_part g(V_ i)).
apply (P5 n G A AH AH' AH'' c V Va Vb Vc V' V'a i_ i_H).
assert(V_c:forall g:G,in_part g(seq_set(Seqtl(Map_embed AH)))
->forall i i':fin c,in_part g(V_ i)->in_part g(V_ i')->i=' i').
apply (P6 n G A AH AH' AH'' c V Va Vb Vc V' V'a i_ i_H).
assert(DSTNCT:distinct(seq_set_seq(Seqtl(Map_embed AH)))).
apply seq_set_seq_preserves_distinct.
apply Seqtl_preserves_distinct.
apply Map_embed_preserves_distinct. exact AH''.
apply Trans with(nsum c V_'+1).
apply Trans with(nsum c(modify_seq V_' i_(V_' i_+1))).
apply nsum_comp. apply Sym.
apply Trans with(modify_seq V_' i_(V' i_-1+1)).
apply modify_comp. apply pluscomp2. unfold V_'.
apply modify_seq_defprop. apply Refl. apply Refl.
apply Trans with(modify_seq V_' i_(S(pred(V' i_))-1+1)).
apply modify_comp. 2:apply Refl. 2:apply Refl.
induction(V' i_). simpl. auto. simpl. auto.
apply Trans with(modify_seq V_' i_(S(pred(V' i_)))).
apply modify_comp. 2:apply Refl. 2:apply Refl.
rewrite plus_comm. simpl. intuition.
apply Trans with(modify_seq V_' i_(V' i_)).
apply modify_comp. 2:apply Refl. 2:apply Refl.
apply Sym. change(V' i_=S(pred(V' i_))).
apply S_pred with (n:=V' i_)(m:=0).
exact(Q8 G a(V i_)(V' i_)(V'a i_)i_H). unfold V_'.
apply undo_modify.
apply nsum_increment4. apply Refl. apply Trans with(n+1).
2:rewrite plus_comm. 2:simpl. 2:auto. apply pluscomp2.
apply(IHn G (seq_set(Seqtl(Map_embed AH)))
(seq_set_seq(Seqtl(Map_embed AH)))
(sqtlsqtl n G A AH AH' AH'')DSTNCT c V_ V_a V_b V_c V_' V_'a).
Qed.

Definition Orb7_s(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(monoid_unit G)s)=' s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)=' f(couple g1(f(couple g2 s))))
(p:S):part_set S.
intros. apply(Build_Predicate
(Pred_fun:=fun s:S=>exists g:G,f(couple g p)=' s)).
unfold pred_compatible. intros s1 s2 H H1. elim H. intros g H2.
exists g. apply Trans with s1. exact H2. apply Sym. exact H1.
Defined.

Lemma finfull:forall(G:Setoid)(n:Nat)(H:has_n_elements n G),
has_n_elements n(full G).
intros. unfold has_n_elements. elim H. intros v vH. elim vH.
clear H vH. intros vH1 vH2.
assert(H:forall i:fin n,in_part(v i)(full G)). simpl. auto.
exists(cast_map_to_subset H). split. simpl. unfold eq_part.
intro g. split. simpl. intro T. clear T.
elim(has_index(Map_to_equal_subsets vH1(Id(full G))g)).
intros i iH. exists i. unfold subtype_image_equal.
apply Trans with(seq_set v(Map_to_equal_subsets vH1
(Id(full G))g)). simpl.
apply Sym. apply subtype_elt_eats_map_between_equal_subsets.
apply Trans with(v i). exact iH. apply Sym.
apply cast_doesn't_change. simpl. auto.
unfold distinct. intros i j H1. unfold distinct in vH2.
unfold not. intro H2. apply(vH2 i j). exact H1.
apply Trans with(subtype_elt(cast_map_to_subset H i)).
simpl. apply Sym. apply cast_doesn't_change.
apply Trans with(subtype_elt(cast_map_to_subset H j)).
exact H2. simpl. apply cast_doesn't_change. Qed.

Definition Hx_s(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(monoid_unit G)s)=' s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)=' f(couple g1(f(couple g2 s))))
(p:S)(x:Orb7_s G S f LA1 LA2 p):part_set G.
intros. apply(Build_Predicate(Pred_fun:=
fun g':G=>f(couple g' p)=' subtype_elt x)).
unfold pred_compatible. intros g1 g2 H H1.
apply Trans with(f(couple g1 p)). apply Map_compatible_prf.
apply couple_comp. exact H1. apply Refl. exact H. Defined.

Lemma Hxcomp(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(monoid_unit G)s)=' s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)=' f(couple g1(f(couple g2 s))))
(p:S)(x1 x2:Orb7_s G S f LA1 LA2 p)(H:x1=' x2):
Hx_s G S f LA1 LA2 p x1 =' Hx_s G S f LA1 LA2 p x2.
intros. simpl. unfold eq_part. intro g. split. simpl. intro H1.
apply Trans with(subtype_elt x1). exact H1. exact H.
simpl. intro H1. apply Trans with(subtype_elt x2). exact H1.
apply Sym. exact H. Qed.

Lemma stillsurj:forall(E:Setoid)(A:part_set E)
(n:Nat)(v:seq n E)(i j:fin n)
,   A=' seq_set v   ->   ~i=' j   ->   v i=' v j
->   A=' seq_set(omit v i).
(***)
intros E A n v i j X Z1 Z2. simpl. unfold eq_part. intro x.
split. intro G0. elim(classic(x=' v j)). intro G1. simpl.
elim(omit_removes' v Z1). intros i' i'H. exists i'.
apply Trans with(v j). exact G1. exact i'H. intro G1.
assert(G2:~x=' v i). unfold not. intro G2. apply G1.
apply Trans with(v i). exact G2. exact Z2. set(x':=
Map_to_equal_subsets X(Id A)(Build_subtype(P:=A)
(subtype_elt:=x)G0)). elim(has_index x'). intros i' i'H.
simpl. assert(G3:~i =' i'). unfold not. intro G3.
apply G2. apply Trans with(seq_set v x'). simpl.
apply Refl. apply Trans with(v i'). exact i'H.
apply Map_compatible_prf. apply Sym. exact G3.
elim(omit_removes' v G3). intros m mH. exists m.
apply Trans with(v i'). apply Trans with(seq_set v x').
simpl. apply Refl. exact i'H. exact mH.
intro G1. simpl in G1. elim G1. clear G1. intros m mH.
apply in_part_comp_l with(omit v i m). 2:exact mH.
apply in_part_comp_r with(seq_set v). 2:exact(Sym X).
apply omit_seq_in_seq_set. Qed.

Lemma existbij_c:forall(E:Setoid)(A:part_set E),
(forall(c:Nat)(v:seq c E)(H:A =' seq_set v),~distinct v)
->
(exists k:Nat,exists w:seq k E,A =' seq_set w /\ ~distinct w)
->False.
(***)
Opaque omit. intros E A H H1. elim H1. clear H1.
intros k H1. elim H1. clear H1. intros w H1. elim H1. clear H1.
intros wH wH1. induction k. apply wH1. unfold distinct.
intuition.
apply wH1.
unfold distinct. intros i j i_not_j. unfold not. intro wi_wj.
apply IHk with(w:=omit w i).
exact(stillsurj E A (S k) w i j wH i_not_j wi_wj). apply H.
exact(stillsurj E A (S k) w i j wH i_not_j wi_wj). Qed.
Transparent omit.

Lemma existbij:forall(E:Setoid)(A:part_set E)(H:is_finite_set E)
(F:MAP E A)(sF:surjective F),
exists k:Nat,exists w:seq k E,A =' seq_set w /\ distinct w.
(***)
intros. unfold is_finite_set in H. elim H. clear H. intros c H.
elim H. clear H. intros v vH.
assert(Q:seq_set(Map_embed(comp_map_map F v))=' A).
simpl. unfold eq_part. intro e. split. simpl. intro H.
elim H. clear H. intros i iH. apply in_part_comp_l with
(subtype_elt(comp_map_fun F v i)). apply in_part_subtype_elt.
exact iH. intro H.
(***)
unfold surjective in sF. elim(sF(Build_subtype(P:=A)
(subtype_elt:=e)H)). intros e' e'H. elim(has_index
(Map_to_equal_subsets vH(set_to_full E)e')). intros i iH.
simpl. exists i. unfold comp_map_fun.
apply Trans with(subtype_elt(F(seq_set v
(Map_to_equal_subsets vH(set_to_full E)e')))). simpl.
exact e'H. simpl. apply subtype_elt_comp.
apply Map_compatible_prf. exact iH.
(***)
elim(classic(distinct(Map_embed(comp_map_map F v)))). intro H.
exists c. exists(Map_embed(comp_map_map F v)). split. apply Sym.
exact Q. exact H.
(***)
intro H. apply NNPP. unfold not. intro this.
apply existbij_c with(A:=A). intros what the heck. unfold not.
intro is. apply this. exists what. exists the. split.
exact heck. exact is.
exists c. exists(Map_embed(comp_map_map F v)). split.
apply Sym. exact Q. exact H. Qed.

Lemma stillsurj2:forall(G E:Setoid)(A:part_set E)(F:MAP G E)
(c:Nat)(v:seq(S c)G)
(Y:A=' seq_set(comp_map_map F v))
(i j:fin(S c))(IJ:~i=' j)
(W:comp_map_map F v i=' comp_map_map F v j),
A=' seq_set(comp_map_map F(omit v i)).
(***)
Opaque omit. intros. set(w:=comp_map_map F v).
simpl. unfold eq_part. intro x. split. intro H.
assert(H1:in_part x(seq_set w)). apply in_part_comp_r with A.
assumption. exact Y. elim H1. clear H H1. intros k kH. simpl.
unfold comp_map_fun.
(***)
elim(classic(i=' k)).
intro IK. elim(omit_removes' v IJ). intros j1 j1H. exists j1.
apply Trans with (F(v j)). 2:apply Map_compatible_prf. 2:exact
j1H. apply Trans with(w k). exact kH. apply Trans with(w i).
apply Map_compatible_prf. exact(Sym IK). exact W.
(***)
intro IK. elim(omit_removes' v IK). intros k1 k1H. exists k1.
apply Trans with(F(v k)). exact kH. apply Map_compatible_prf.
exact k1H.
(***)
intro H. elim H. clear H. intros k kH. simpl in kH. unfold
comp_map_fun in kH. apply in_part_comp_r with(seq_set w).
2:exact(Sym Y). simpl. unfold comp_map_fun. elim
(omit_removes v i k). intros k1 k1H.
(***)
elim(classic(i=' k1)).
intro IK. exists j. apply Trans with(w i). 2:exact W. apply
Trans with (F(omit v i k)). exact kH. apply Trans with(w k1).
unfold w. simpl. unfold comp_map_fun. apply Map_compatible_prf.
exact(Sym k1H). apply Map_compatible_prf. exact(Sym IK).
(***)
intro IK. exists k1. apply Trans with(F(omit v i k)). exact kH.
apply Map_compatible_prf. exact(Sym k1H). Qed. Transparent omit.

Lemma existbij2_c:forall(G:Setoid)(E:Setoid)(A:part_set E)
(F:MAP G E),
(forall(c:Nat)(v:seq c G)(H:distinct v)
(H':A=' seq_set(comp_map_map F v)),~distinct(comp_map_map F v))
->
(exists c:Nat,exists v:seq c G,distinct v/\
A=' seq_set(comp_map_map F v)/\~distinct(comp_map_map F v))
->False.
(***)
Opaque omit. intros G E A F H H0. elim H0. clear H0. intros
c H0. elim H0. clear H0. intros v H0. elim H0. clear H0. intros
vDIST H0. elim H0. clear H0. intros SURJ NOTDIST. induction c.
apply NOTDIST. unfold distinct. intuition.
(***)
apply NOTDIST. unfold distinct. intros i j i_not_j.
set(w:=comp_map_map F v). unfold not. intro wi_wj.
apply (IHc(omit v i)). apply(omit_preserves_distinct vDIST).
apply stillsurj2 with(j:=j). exact SURJ. exact i_not_j. exact
wi_wj. apply H. apply(omit_preserves_distinct vDIST). apply
stillsurj2 with(j:=j). exact SURJ. exact i_not_j. exact wi_wj.
Qed. Transparent omit.

(***************************************************************
I call the composition of a serial numbering of G with the left
action map F the "F-derivative".  I also call the weird lengthy
forall statement that is the second to last hypothesis of
existbij2_c "P".
existbij2_c says: if all injective serial numberings of G that
F-cover A .m.u.s.t. have their F-derivative be nondistinct, then
the existence of a single injective serial numbering of G that
F-covers A and has a nondistinct F-derivative implies a contra-
diction.
But here is a single injective serial numbering of G that
F-covers A.  (the "v" argument)
Now suppose its F-derivative is distinct.  Then we have the
desired product; we are immediately done.
But if its F-derivative is nondistinct?  Well suppose P.  Then
contradiction by existbij2_c, so P can't be true.  But if P is
not true, then we have ~P which by forall-exists conversion,
shows that exists injective serial numbering of G that F-covers
A and its F-derivative is ~~distinct.  q.e.d.  (The forall-
exists conversion is done by NNPP in the proof.  I think.)
***************************************************************)
Lemma existbij2:
forall(G:Setoid)(c:Nat)(v:seq c G)(V:full G=' seq_set v)
(V'':distinct v)
(E:Setoid)(A:part_set E)
(F:MAP G E)(sF:A=' seq_set(comp_map_map F v)),
exists k:Nat,exists w:seq k E,A=' seq_set w/\distinct w.
(***)
intros. elim(classic(distinct(comp_map_map F v))). intro
DISTINCT. exists c. exists(comp_map_map F v). split. exact sF.
exact DISTINCT. intro NOT_DISTINCT.
(***)
elim(classic(forall(c:Nat)(v:seq c G)(H:distinct v)(H':A='
seq_set(comp_map_map F v)),~distinct(comp_map_map F v))).
intro P. elimtype False. apply existbij2_c with(A:=A)(F:=F).
exact P. exists c. exists v. split. exact V''. split. exact sF.
exact NOT_DISTINCT.
(***)
intro NOT_P. apply NNPP. unfold not. intro H. apply NOT_P.
unfold not. intros c0 v0 distinct0 Fcovers0 Fderiv0. apply H.
exists c0. exists(comp_map_map F v0). auto. Qed.

Lemma lacomp:forall(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(monoid_unit G)s)=' s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)=' f(couple g1(f(couple g2 s))))
(p:S), fun_compatible(fun g:G=>f(couple g p)).
intros. unfold fun_compatible. intros. apply Map_compatible_prf.
apply couple_comp. assumption. apply Refl. Qed.

Lemma finGOrb:forall(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(monoid_unit G)s)=' s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)=' f(couple g1(f(couple g2 s))))
(p:S)(n:Nat)(H:has_n_elements n G),
exists c:Nat,exists v:seq c S,
Orb7_s G S f LA1 LA2 p=' seq_set v /\ distinct v.
(***)
intros. unfold has_n_elements in H. elim H. intros v H'.
elim H'. intros vv vvv. clear H H'. set(F:=Build_Map
(lacomp G S f LA1 LA2 p)). apply existbij2 with(F:=F)(v:=v).
exact vv. exact vvv. simpl. unfold eq_part. intro s. split.
simpl. intro H. elim H. clear H. intros g g'. elim(has_index
(Map_to_equal_subsets vv(set_to_full G)g)). intros i iH. exists
i. simpl in iH. apply Trans with(f(couple g p)). exact(Sym g').
apply Map_compatible_prf. apply couple_comp. exact iH. apply
Refl. simpl. intro H. elim H. clear H. intros i iH. exists
(v i). exact(Sym iH). Qed.

Lemma samecardB:forall(E F:Setoid)(M:MAP F E)
(S:surjective M)(I:injective M)(n:Nat)(C:has_n_elements n F),
has_n_elements n E.
(***)
intros. unfold has_n_elements in C. elim C. clear C. intros v
C. elim C. clear C. intros v' v''. exists(comp_map_map M v).
split. simpl. unfold eq_part. intro e. split. simpl. intro H.
clear H. elim(S e). intros f f'. elim(has_index
(Map_to_equal_subsets v'(set_to_full F)f)). intros i iH. exists
i. simpl in iH. unfold comp_map_fun. apply Trans with(M f).
exact f'. apply Map_compatible_prf. exact iH. simpl. auto.
unfold distinct. intros i j IJ. simpl. unfold comp_map_fun.
assert(V:~v i=' v j). apply v''. exact IJ. unfold not. intro.
apply V. apply I. assumption. Qed.

Lemma samecardA:forall(E F:Setoid)(M:MAP E F)
(S:surjective M)(I:injective M)(n:Nat)(C:has_n_elements n E),
has_n_elements n F.
(***)
intros. unfold has_n_elements in C. elim C. clear C. intros v
C. elim C. clear C. intros v' v''. exists(comp_map_map M v).
split. simpl. unfold eq_part. intro f. split. simpl. intro H.
clear H. elim(S f). intros e e'. elim(has_index
(Map_to_equal_subsets v'(set_to_full E)e)). intros i iH. exists
i. simpl in iH. unfold comp_map_fun. apply Trans with(M e).
exact e'. apply Map_compatible_prf. exact iH. simpl. auto.
unfold distinct. intros i j IJ. simpl. unfold comp_map_fun.
assert(V:~v i=' v j). apply v''. exact IJ. unfold not. intro.
apply V. apply I. assumption. Qed.

Definition Stab2_s(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(monoid_unit G)s)=' s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)=' f(couple g1(f(couple g2 s))))
(p:S):part_set G.
(***)
intros. apply(Build_Predicate(Pred_fun:=fun g:G=>f(couple g p)
=' p)). unfold pred_compatible. intros g g' H H'. apply Trans
with(f(couple g p)). apply Map_compatible_prf. apply
couple_comp. exact H'. apply Refl. exact H. Defined.

Lemma LEFTACTION_reg_left:
forall(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(monoid_unit G)s)=' s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)=' f(couple g1(f(couple g2 s))))
(x:G)(y z:S)(H:f(couple x y)=' f(couple x z)),y=' z.
(***)
intros. apply Trans with(f(couple(zero G)y)). auto with
algebra. apply Trans with(f(couple(zero G)z)). apply Trans with
(f(couple((min x)+'x)y)). auto with algebra. apply Trans with
(f(couple((min x)+' x)z)). apply Trans with(f(couple(min x)
(f(couple x y)))). apply LA2. apply Trans with(f(couple(min x)
(f(couple x z)))). auto with algebra. apply Sym. apply LA2.
auto with algebra. auto with algebra. Qed.

Lemma StabHx_bij:forall(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(monoid_unit G)s)=' s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)=' f(couple g1(f(couple g2 s))))
(p:S)(x:Orb7_s G S f LA1 LA2 p),
exists M:MAP(Stab2_s G S f LA1 LA2 p)(Hx_s G S f LA1 LA2 p x),
injective M /\ surjective M.
(***)
intros. cut(in_part(subtype_elt x)(Orb7_s G S f LA1 LA2 p)).
2:apply in_part_subtype_elt. intro H. elim H. clear H. intros
y Y.
(***)
assert(RESULT_IN_HX:forall h:Stab2_s G S f LA1 LA2 p,
Pred_fun(Hx_s G S f LA1 LA2 p x)(y+' subtype_elt h)). intro h.
simpl. apply Trans with(f(couple y p)). apply Trans with
(f(couple y(f(couple(subtype_elt h)p)))). apply LA2. apply
Map_compatible_prf. apply couple_comp. apply Refl. elim h.
simpl. auto. exact Y.
(***)
assert(Q:fun_compatible(fun h:Stab2_s G S f LA1 LA2 p=>Id(Hx_s
G S f LA1 LA2 p x)(Build_subtype(RESULT_IN_HX h)))). unfold
fun_compatible. intros h h' H. simpl. unfold
subtype_image_equal. simpl. auto with algebra. exists(Build_Map
Q). split.
(***)
unfold injective. intros h h' H. simpl. unfold
subtype_image_equal. simpl. apply GROUP_reg_left with(x:=y).
exact H.
(***)
unfold surjective. intro h''. assert(R:Pred_fun(Stab2_s G S f
LA1 LA2 p)((min y)+' subtype_elt h'')). simpl. apply
(LEFTACTION_reg_left G S f LA1 LA2 y). apply Trans with(f
(couple(y+'((min y)+' subtype_elt h''))p)). apply Sym. apply
LA2. apply Trans with(subtype_elt x). 2:exact(Sym Y). apply
Trans with(f(couple(subtype_elt h'')p)). apply
Map_compatible_prf. apply couple_comp. 2:apply Refl. apply
Trans with(y+'(min y)+' subtype_elt h''). apply Sym. apply
SGROUP_assoc. apply Trans with((zero G)+' subtype_elt h'').
auto with algebra. auto with algebra. elim h''. simpl. auto.
(***)
exists(Build_subtype R). simpl. red. simpl. apply Trans with(y
+'(min y)+'subtype_elt h''). 2:apply SGROUP_assoc. apply Trans
with((zero G)+'subtype_elt h''). auto with algebra. auto with
algebra. Qed.

Lemma collide:forall(E:Setoid)(n:Nat)(E':has_n_elements n E)
(A:Setoid)(m:Nat)(A':has_n_elements m A)(H:~m='n)
(M:MAP E A)(sM:surjective M), ~injective M.
(***)
intros. elim E';intros v H';elim H';intros v' v'';clear H'.
assert(SURJ_Mv:surjective(comp_map_map M v)). unfold
surjective. intro a. elim(sM a). intros e e_goes_to_a. elim
(has_index(Map_to_equal_subsets v'(set_to_full E)e)). intros i
iH. simpl in iH. exists i. simpl;unfold comp_map_fun. apply
Trans with(M e);auto;intuition. unfold not;intro INJ.
(***)
assert(INJ_Mv:distinct(comp_map_map M v)). unfold distinct.
intros i j ij. simpl;unfold comp_map_fun. assert(vivj:~v i='
v j). apply v'';auto. unfold not;intro. apply vivj. apply INJ.
auto.
(***)
assert(SURJ_Mv_2:full A='seq_set(comp_map_map M v)). simpl;
unfold eq_part. intro a;split. simpl. intro. unfold surjective
in SURJ_Mv. elim(SURJ_Mv a). intros i iH. exists i. auto.
simpl;auto.
(***)
assert(has_n_elements n A). exists(comp_map_map M v). split.
exact SURJ_Mv_2. exact INJ_Mv. assert(has_n_elements m(full A)).
apply full_preserves_has_n_elements;auto. assert(has_n_elements
n(full A)). apply full_preserves_has_n_elements;auto. assert(m
='n). apply has_n_elements_inj with(B:=full A)(C:=full A).
auto. auto. apply Refl. apply H;auto. Qed.

Lemma nsum_const:forall(k:Nat)(C:Nat)(v:seq k Nat)
(H:forall(i:fin k),v i='C), nsum k v='k*C.
(***)
induction k. intuition. intros. unfold nsum;fold nsum. apply
Trans with(C+nsum k(Seqtl v)). apply pluscomp2. unfold head.
apply H. rewrite plus_comm. apply Trans with(k*C+C). apply
pluscomp2. apply IHk. induction i. simpl. apply H. simpl.
rewrite plus_comm. auto. Qed.

Lemma G2Stab:forall(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(zero G)s)='s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+' g2)s)='f(couple g1(f(couple g2 s))))
(p:S)(g:G),Stab2_s G S f LA1 LA2 p.
(***)
intros. elim(excluded_middle_informative(f(couple g p)='p)).
intro a. exists g;simpl;auto. intro b. exists(zero G);simpl;
auto. Defined.

Lemma G2Stab_compat:forall(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(zero G)s)='s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+'g2)s)='f(couple g1(f(couple g2 s))))
(p:S),fun_compatible(G2Stab G S f LA1 LA2 p).
(***)
intros. red. intros g1 g2 H. elim(classic(Pred_fun(Stab2_s G S
f LA1 LA2 p)g1)). intro H1. assert(H2:Pred_fun(Stab2_s G S f
LA1 LA2 p)g2). simpl;simpl in H1. apply Trans with(f(couple g1
p)). intuition. auto. apply Trans with(Build_subtype H1).
unfold G2Stab;unfold sumbool_rect;destruct
excluded_middle_informative. simpl;red;apply Refl. intuition.
unfold G2Stab;unfold sumbool_rect;destruct
excluded_middle_informative. intuition. intuition.
(***)
intro H1. assert(H2:~Pred_fun(Stab2_s G S f LA1 LA2 p)g2).
unfold not;intro H2. apply H1. simpl;simpl in H2. apply Trans
with(f(couple g2 p)). intuition. auto. assert(H0:Pred_fun
(Stab2_s G S f LA1 LA2 p)(zero G)). simpl;apply LA1. apply
Trans with(Build_subtype H0). unfold G2Stab;unfold
sumbool_rect;destruct excluded_middle_informative. intuition.
simpl;red;apply Refl. unfold G2Stab;unfold sumbool_rect;
destruct excluded_middle_informative. intuition. simpl;red;
apply Refl. Qed.

Lemma orbstab2:forall(G:group)(S:Setoid)(f:Map(cart G S)S)
(LA1:forall(s:S),f(couple(zero G)s)='s)
(LA2:forall(g1 g2:G)(s:S),
f(couple(g1+'g2)s)='f(couple g1(f(couple g2 s))))
(p:S)(n:Nat)(H:has_n_elements n G),
exists c:Nat,exists k:Nat,
has_n_elements c(Orb7_s G S f LA1 LA2 p)/\
has_n_elements k(Stab2_s G S f LA1 LA2 p)/\n='c*k.
(***)
intros. elim(finGOrb G S f LA1 LA2 p n H). intros c H0. elim
H0. intros v H1. elim H1. intros v' v''. clear H0 H1. set(V:=
comp_map_map(Build_Map(Hxcomp G S f LA1 LA2 p))(comp_map_map
(Map_to_equal_subsets(Sym v')(Id(seq_set v)))(seq_set_seq v))).
(***)
elim H;clear H. intros u H. elim H;clear H. intros u' u''.
assert(H:forall i:fin n,in_part(u i)(full G)).
simpl;auto. set(U:=cast_map_to_subset H). assert(U':full(full
G)='seq_set U). simpl;red. intro g. split. 2:simpl;auto. simpl.
intro H0;clear H0. elim(has_index(Map_to_equal_subsets u'(Id
(full G))g)). intros i iH. exists i. red. simpl in iH. apply
Trans with(subtype_elt(map_between_equal_subsets u' g)). apply
Sym;apply subtype_elt_eats_map_between_equal_subsets. apply
Trans with(u i). auto. apply Sym;apply cast_doesn't_change.
assert(U'':distinct U). apply distinct_comp with(v:=u)(v':=
Map_embed U). auto. simpl;red. intro i. simpl. apply Sym;apply
cast_doesn't_change.
(***)
assert(Va:forall(i:fin c)(g:G),in_part g(V i)->in_part g(full
G)). simpl;auto.
(***)
assert(Vb:forall(g:G),in_part g(full G)->exists i:fin c,in_part
g(V i)). intros g g'. assert(x:Pred_fun(Orb7_s G S f LA1 LA2 p)
(f(couple g p))). simpl;exists g;apply Refl. elim(has_index
(Map_to_equal_subsets v'(Id(Orb7_s G S f LA1 LA2 p))
(Build_subtype x))). intros i iH. exists i. intuition.
(***)
assert(Vc:forall(g:G),in_part g(full G)->forall(i i':fin c),
in_part g(V i)->in_part g(V i')->i='i'). intros g g' i i' iH
i'H. apply NNPP. unfold not;intro H1. red in v'';red in v''.
apply v'' with(i:=i)(j:=i'). auto. simpl in iH;simpl in i'H.
apply Trans with(f(couple g p)). intuition. auto.
(***)
assert(sF:surjective(Build_Map(G2Stab_compat G S f LA1 LA2 p)))
. red. intro h. exists(subtype_elt h). elim h. simpl. intros g
g'. simpl;red. unfold G2Stab;unfold sumbool_rect;destruct
excluded_middle_informative. apply Refl. intuition. assert(F:
is_finite_set G). exists n. exists u. auto. elim(existbij G
(Stab2_s G S f LA1 LA2 p)F (Build_Map(G2Stab_compat G S f LA1
LA2 p))sF). intros k H0. elim H0;clear H0. intros w H0. elim
H0;clear H0. intros w' w''. clear sF F.
(***)
assert(H1:fun_compatible(fun i:fin c=>k)). red;intuition. set
(V':=Build_Map H1). assert(V'a:forall i:fin c,has_n_elements(V'
i)(V i)). intro i. set(x:=Map_to_equal_subsets(Sym v')
(seq_set_seq v)i). apply has_n_elements_comp with(n:=V' i)(B:=
Hx_s G S f LA1 LA2 p x). 3:apply Refl. 2:intuition. elim
(StabHx_bij G S f LA1 LA2 p x). intros M H0. elim H0;clear H0.
intros M' M''. apply samecardB with(M:=M). auto. auto. apply
seq_set_n_element_subset. exists w. auto.
(***)
exists c. exists k. split. apply seq_set_n_element_subset.
exists v. auto. split. apply seq_set_n_element_subset. exists
w. auto. apply Trans with(nsum c V'). apply Sym. exact(incexc3
n G(full G)U U' U'' c V Va Vb Vc V' V'a). apply nsum_const.
intuition. Qed.

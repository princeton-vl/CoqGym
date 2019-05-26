(******************************************************************************
Markov's inequality.  Based on Wikipedia proof
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





(* sigalg = sigma algebra
   preimg = preimage
   cntabl = countable
   msur = measure function
   msurable = measurable
   simple = simple function 
   lebint = Lebesgue integral 
   lebint_s = Lebesgue integral for simple function
   borl = Borel set
   unoin = union *)





(******************************************************************************
Note: chicli_pottier_simpson, classic, Extensionality_Ensembles, NNPP are used
frequently
Also lemmas from Rtopology which use classic as well as R_total_order
******************************************************************************)

Require Import Setoid.
Require Export Powerset.
Require Export Rtopology.
Require Export Raxioms.
Require Export Rfunctions.
Require Export Image.
Require Export RIneq.
Require Export PartSum.

Axiom constructive_definite_description:forall(A:Type)(P:A->Prop),
(exists!x:A,P x)->{x:A|P x}.

(******************************************************************************
from Coq.Logic.ChoiceFacts
******************************************************************************)
Lemma chicli_pottier_simpson(P:Prop):P\/~P->{P}+{~P}.
intros EM. pose(select:=fun b:bool=>if b then P else ~P). assert{b:bool|
select b}as([|],HP). apply constructive_definite_description. rewrite<-
unique_existence;split. destruct EM. exists true;trivial. exists false;trivial.
intros[|][|]H1 H2;simpl in *;reflexivity||contradiction. left;trivial. right;
trivial. Qed.

Lemma if_l:forall(A B:Prop)(C:Type)(H:{A}+{B})(x y:C),
~B->(if H then x else y)=x. intuition. Qed.

Lemma if_r:forall(A B:Prop)(C:Type)(H:{A}+{B})(x y:C),
~A->(if H then x else y)=y. intuition. Qed.

Definition cntabl(U:Type)(C:Ensemble(Ensemble U)):=
exists f:nat->Ensemble U,forall c,C c->exists i:nat,f i=c.

(******************************************************************************
from http://cl.cse.wustl.edu/classes/cse545/lec/sni.v
accessed 13 July 2007
******************************************************************************)
Lemma aaron_stump_cse545(Q:nat->Prop):
(forall n:nat,(forall n':nat,n'<n->Q n')->Q n)->
forall n:nat,forall n':nat,n'<=n->Q n'.
(**)
intros sIH n. induction n. intros n' Hn'. apply sIH. intros. elimtype False;
intuition. intuition. Qed.

Lemma first_sat(Q:nat->Prop):forall k:nat,Q k
->exists m:nat,Q m/\forall n:nat,Q n->m<=n.
(**)
intros k. apply aaron_stump_cse545 with(Q:=fun z=>Q z->exists m,Q m/\forall n
,Q n->m<=n)(n:=k). 2:auto. intros n H H1. elim(classic(forall i,i<n->~Q i)).
intro H2. exists n. split. auto. intros j H3. apply NNPP. red;intro H4. apply(
H2 j). intuition. auto.
(**)
intro H2. assert(H3:exists i:nat,i<n/\Q i). apply NNPP. red;intro H3. apply H2.
intros i H4. red;intro H5. apply H3. exists i. auto. elim H3. intros ii H4.
elim(H ii). intros m H5. exists m. auto. tauto. tauto. Qed.



(******************************************************************************
You can actually prove this without using constructive_definite_description,
you can use Yevgeniy Marakov's constructive_indefinite_description_nat from
Coq.Logic.ConstructiveEpsilon, which is purely constructive -- probably don't
even need classic really to do this proof.
******************************************************************************)
Lemma cntabl_P0(U:Type)(C:Ensemble(Ensemble U))
:cntabl _ C->
exists g:forall c,C c->nat,
(forall c c' c'',g c c'=g c c'')
/\forall c cc c' cc',g c c'=g cc cc'->c=cc.
(**)
intros H. elim H. intros f H1. assert(H2:forall c,C c->{i|f i=c/\forall j,f
j=c->i<=j}). intros c H2. apply constructive_definite_description. elim(H1 c).
intros k H3. elim(first_sat(fun i=>f i=c)k). intros m H4. exists m. red. split.
auto. intuition. auto. auto.
(**)
exists(fun c c'=>proj1_sig(H2 c c')). split. intros. elim(proj2_sig(H2 c c')).
elim(proj2_sig(H2 c c'')). intuition. intros c cc c' cc' H3. elim(proj2_sig(H2
c c')). elim(proj2_sig(H2 cc cc')). intros H4 H5 H6 H7. rewrite<-H4. rewrite<-
H6. auto. Qed.

(*-----------------------------------------------------------------------------
The 'other half' of cntabl_P0; just proving two common definitions of
countability equivalent.  g assigns a 'serial number' to each set in the
countable collection, and the two hypotheses say g is proof-irrelevant and
injective.
-----------------------------------------------------------------------------*)
Lemma cntabl_P1(U:Type)(C:Ensemble(Ensemble U))
:forall g:forall c,C c->nat,
(forall c c' c'',g c c'=g c c'')->
(forall c cc c' cc',g c c'=g cc cc'->c=cc)->cntabl _ C.
(**)
intros g g' g''. red. elim(classic(Inhabited _ C)). 2:intro H;exists(fun _:
nat=>Empty_set U);intros;elimtype False;apply H;exists c;auto. intro H. elim H.
intros d d'. assert(Q:forall i,{c|C c/\(forall z z',g z z'=i->c=z)/\((forall z
z',g z z'<>i)->c=d)}). intro. elim(chicli_pottier_simpson(exists z,C z/\forall
z',g z z'=i)(classic(exists z,C z/\forall z',g z z'=i))).
(**)
intro H1. assert(H2:exists!z,C z/\forall z',g z z'=i). elim H1. intros z z'.
exists z. split. auto. intros Z Z'. elim z';elim Z'. intros Z'' Z''' z'' z'''.
apply(g'' z Z z'' Z''). rewrite(Z''' Z''). auto. elim(
constructive_definite_description _ _ H2). intros z z'. elim z'. intros z''
z'''. exists z. split. auto. split. intros Z Z' Z''. apply(g'' z Z z'' Z').
rewrite Z'';auto. intro H3. elimtype False. apply(H3 z z''). auto.
(**)
intro H1. exists d. split. auto. split. intros z z' z''. elimtype False. apply
H1. exists z. split. auto. intro z'''. rewrite<-z''. apply g'. auto.
(**)
exists(fun i=>proj1_sig(Q i)). intros c c'. exists(g c c'). elim(proj2_sig(Q(g
c c'))). intros H1 H2. elim H2;intros H3 H4. eapply H3. intuition. Qed.



Definition unoin(U:Type)(C:Ensemble(Ensemble U)):=
fun x:U=>exists c,C c/\c x.

(*-----------------------------------------------------------------------------
This and the following other two Definitions are the three parts of the
definition of what it means to be a sigma-algebra.
-----------------------------------------------------------------------------*)
Definition sigalg_0(U:Type)(F:Ensemble(Ensemble U)):=
Inhabited _ F.

Definition sigalg_1(U:Type)(F:Ensemble(Ensemble U)):=
forall A:Ensemble U,F A->F(Complement _ A).

Definition sigalg_2(U:Type)(F:Ensemble(Ensemble U)):=
forall C:Ensemble(Ensemble U),Included _ C F->cntabl _ C
->F(unoin _ C).

(*-----------------------------------------------------------------------------
This and the following are simple facts about sigma-algebras: union of two sets
from the sigma-algebra is also in the sigma-algebra, and so on.
-----------------------------------------------------------------------------*)
Lemma sigalg_P0:
forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F),
forall A B:Ensemble U,F A->F B->F(Union _ A B).
(**)
intros U F F' F'' F''' A B A' B'. set(f:=fun i:nat=>if(eq_nat_dec i 0)then A
else B). assert(H:unoin _(fun A=>exists i,f i=A)=Union _ A B). apply(
Extensionality_Ensembles U). split. red. intros x H. elim H. intros c H1. elim
H1. intros H2 H3. elim H2. intros i H4. rewrite<-H4 in H3. red in H3. elim(
eq_nat_dec i 0). intro a. rewrite a in H3. intuition. intro b. assert(H5:(if
eq_nat_dec i 0 then A else B)=B). elim(eq_nat_dec i 0). intuition. auto.
rewrite H5 in H3. intuition.
(**)
red. intros x H. elim H. intros. exists A. split. exists 0. auto. auto. intros.
exists B. split. exists 1. auto. auto. rewrite<-H. apply F'''. red. intros c c'
. elim c'. intros i i'. elim i'. elim(eq_nat_dec i 0). intro a. rewrite a. auto
. intro b. assert(H1:f i=B). unfold f. elim(eq_nat_dec i 0). intuition. auto.
rewrite H1. auto. red. exists f. auto. Qed.

Lemma sigalg_P1:
forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F),
F(Empty_set _).
(**)
intros. elim F'. intros A A'. cut(Empty_set U=Complement _(Union _ A(Complement
_ A))). intro H. rewrite H. apply F''. apply(sigalg_P0 _ F F' F'' F'''). auto.
apply F''. auto.
(**)
apply Extensionality_Ensembles. split. intuition. red. intros x x'. elimtype
False. elim(classic(A x)). intuition. intuition. Qed.

Lemma sigalg_P2:
forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F),
forall(A B:Ensemble U),F A->F B->F(Intersection _ A B).
(**)
intros U F F' F'' F''' A B A' B'. cut(Intersection _ A B=Complement _(Union _(
Complement _ A)(Complement _ B))). intro H. rewrite H. apply F''. apply(
sigalg_P0 _ F F' F'' F'''). apply F''. auto. apply F''. auto.
(**)
apply Extensionality_Ensembles. split. red. unfold Complement;unfold In;unfold
not. intros x x' x''. elim(Intersection_inv _ _ _ _ x'). elim(Union_inv _ _ _ _
x''). auto. auto. split. apply NNPP. auto with sets. apply NNPP. auto with sets
. Qed.

Lemma sigalg_P3:
forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F),
F(Full_set U).
(**)
intros. cut(Full_set U=Complement _(Empty_set U)). intro H. rewrite H. apply
F''. apply(sigalg_P1 _ F F' F'' F'''). apply Extensionality_Ensembles. split.
red. unfold Complement;unfold In. intuition. red. intros. apply Full_intro. Qed
.



Inductive borl(D:Ensemble R):Prop:=
|borl_0:open_set D->borl D
|borl_1:borl(Complement _ D)->borl D
|borl_2:forall C:Ensemble(Ensemble R),(forall c,C c->borl c)
->cntabl _ C->D=_D(unoin _ C)->borl D.

Definition preimg(U:Type)(f:U->R)(D:Ensemble R):=
fun x:U=>D(f x).

Definition msurable(U:Type)(F:Ensemble(Ensemble U))
(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':sigalg_2 _ F)
(f:U->R):=forall(D:Ensemble R),borl D->F(preimg _ f D).

(*-----------------------------------------------------------------------------
helper for msurable_P1; i forget exactly what its for
-----------------------------------------------------------------------------*)
Lemma msurable_P0:
(forall(U:Type),
forall a:R,forall f:U->R,
let P:=fun i:nat=>fun x:U=>a<=f x<=a+INR i in
(fun x:U=>exists j:nat,P j x)=fun x:U=>f x>=a)%R.
(**)
intros. apply(Extensionality_Ensembles U). split. red;unfold In. intros x x'.
elim x'. unfold P. intuition. red;unfold In. intros x x'. unfold P. elim(
archimed(f x-a)). intros H H1;clear H1. induction(up(f x-a)). simpl in H.
elimtype False. apply(Rlt_not_ge(f x-a)0). auto. apply(Rplus_ge_reg_l a).
replace(a+(f x-a))%R with(f x). 2:ring. replace(a+0)%R with a. 2:ring. auto.
(**)
exists(nat_of_P p). split. intuition. unfold IZR in H. rewrite <- INR_IPR in H. apply Rge_le. apply Rgt_ge.
apply(Rplus_gt_reg_l(-a)%R). replace(-a+(a+INR(nat_of_P p)))%R with (INR(
nat_of_P p)). 2:ring. replace(-a+f x)%R with(f x-a)%R. 2:ring. auto.
(**)
unfold IZR in H; rewrite <- INR_IPR in H. elimtype False. apply(Rlt_not_ge(f x-a)0). apply Rgt_trans with(-
INR(nat_of_P p))%R. intuition. auto. apply(Rplus_ge_reg_l a). replace(a+(f x-a)
)%R with(f x). 2:ring. replace(a+0)%R with a. 2:ring. auto. Qed.

(*-----------------------------------------------------------------------------
That 'f(x)>=a' set which is central to the proof (and statement) of Markov's
inequality is indeed measurable.
-----------------------------------------------------------------------------*)
Lemma msurable_P1:
(forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F'''
:sigalg_2 _ F)(f:U->R)(f':forall x:U,f x>=0)(f'':msurable _ _ F' F'' F''' f),
forall a:R,0<a->F(fun x:U=>f x>=a))%R.
(**)
intros U F F' F'' F''' f f' f'' a a'. rewrite<-(msurable_P0 _ a f). set(P:=fun
i=>fun x=>(a<=f x<=a+INR i)%R). set(C:=fun A=>exists i,P i=A). assert(H:unoin _
C=fun x=>exists i,P i x%R). apply(Extensionality_Ensembles U). split. red.
intros x H. elim H. intros c H1. elim H1. intros H2 H3. elim H2. intros i H4.
red. exists i. rewrite<-H4 in H3. auto. red. intros x H. elim H. intros i H1.
red;red. exists(P i). split. exists i. auto. auto.
(**)
unfold P in H. rewrite<-H. apply F'''. intros c c'. elim c'. intros i i'.
rewrite<-i'. apply f'' with(D:=fun x=>(a<=x<=a+INR i)%R). apply borl_1. apply
borl_0. apply compact_P2. apply compact_P3. red. exists P. intuition. Qed.



Definition msur_0
(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(u:forall A,F A->R):=
u(Empty_set _)(sigalg_P1 U F F' F'' F''')=0%R.

(*-----------------------------------------------------------------------------
Countable additivity.  C is the countable collection, g is again the injective
proof-irrelevant serial number mapping, and us is a list of the measures of the
sets in the collection (sprinkled with zeroes throughout).
-------------------------------------------------------------------------------
One note that might be interesting is that even though the hypotheses about
'us' 'force' the measure function u to be compatible when dealing with sets
that are actually in C (as opposed to sets in the sigma-algebra F which are not
known for sure if they are in C), one cannot generally prove (I think) that the
measure function u is compatible from the hypotheses given here.  This was kind
of a stumbling block and why I eventually had to add the 'msur_3' axiom below.
-----------------------------------------------------------------------------*)
Definition msur_1
(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(u:forall A,F A->R):=
forall C:Ensemble(Ensemble U),
forall C1:Included _ C F,
forall C2:forall c cc,C c->C cc->c<>cc->Disjoint _ c cc,
forall g:forall c,C c->nat,
forall g1:forall c c' c'',g c c'=g c c'',
forall g2:forall c cc c' cc',g c c'=g cc cc'->c=cc,
forall us:nat->R,
(forall c c',us(g c c')=u c(C1 _ c'))->
(forall n:nat,(forall c c',n<>g c c')->us n=0%R)->
forall l,infinit_sum us l->l
=u(unoin _ C)(F''' C C1(cntabl_P1 _ _ g g1 g2)).

(*-----------------------------------------------------------------------------
probability spaces have measure 1
-----------------------------------------------------------------------------*)
Definition msur_2
(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(u:forall A,F A->R):=
u (Full_set U) (sigalg_P3 U F F' F'' F''')=1%R.

Definition msur_3
(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(u:forall A,F A->R):=
forall A A' A'',u A A'=u A A''.



Definition simple_0(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U)
:=forall i j:nat,i<>j->Disjoint _(w i)(w j).

Definition simple_1(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U)
:=forall x:U,exists i:nat,i<n/\w i x.

(*-----------------------------------------------------------------------------
the list of range values for a simple function doesnt HAVE to be injective, but
i thought itd be nice
-----------------------------------------------------------------------------*)
Definition simple_2(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U)
:=forall i j:nat,v i=v j->i=j.

Definition simple_3(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U)
:=forall i:nat,(v i>=0)%R.

(*-----------------------------------------------------------------------------
constructive 'get_index_of'-type function
-----------------------------------------------------------------------------*)
Definition simple_P0
(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U):simple_0 _ n v w->simple_1 _ n v w
->simple_2 _ n v w->simple_3 _ n v w->
forall x:U,{i:nat|i<n/\w i x/\forall i',w i' x->i'=i}.
(**)
intros S0 S1 S2 S3 x. assert(H:exists!i:nat,i<n/\w i x/\forall i',w i'
x->i'=i). elim(S1 x). intros i H. elim H. intros H1 H2. exists i. split. split.
auto. split. auto. intros i' H3. apply NNPP. unfold not;intro H4. elim(S0 i i')
. intro H5. apply(H5 x). intuition. auto. intuition. apply
constructive_definite_description. auto. Defined.

Lemma simple_P1:
forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(n:nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:
simple_1 _ n v w)(S2:simple_2 _ n v w)(S3:simple_3 _ n v w),
msurable _ _ F' F'' F''' (fun x:U=>v(proj1_sig(simple_P0 _ n v w S0 S1 S2 S3 x)
))->forall i:nat,F(w i).
(**)
intros U F F' F'' F''' n v w S0 S1 S2 S3 M i. assert(H:w i=preimg _(fun x:U=>v(
proj1_sig(simple_P0 _ _ _ _ S0 S1 S2 S3 x)))(fun r:R=>v i<=r<=v i)%R). apply
Extensionality_Ensembles. split. red. red. red. intros x H1. elim(simple_P0 _ n
v w S0 S1 S2 S3 x). simpl. intros j H2. elim H2. intros H3 H4. elim H4.
intros H5 H6. elim(H6 i). intuition. auto.
(**)
red. unfold preimg;unfold In. intros x H1. rewrite(S2 i (proj1_sig(simple_P0 _
n v w S0 S1 S2 S3 x))). 2:intuition. elim(simple_P0 _ n v w S0 S1 S2 S3 x).
simpl. intuition. rewrite H. apply M. apply borl_1. apply borl_0. apply
compact_P2. apply compact_P3. Qed.

Lemma simple_P4:
forall(U:Type)(A:Ensemble U),
simple_0 _ 2(fun i:nat=>INR i)(fun i:nat=>if eq_nat_dec i 0 then Complement _ A
else if eq_nat_dec i 1 then A else Empty_set _).
(**)
intros. red. intros i j H. split. intro x. red. intro H1. elim H1. intros y H2
H3. elim(eq_nat_dec i 0). intro a. rewrite a in H2. simpl in H2. elim(
eq_nat_dec j 0). intuition. intro bb. rewrite(if_r _ _ _(eq_nat_dec j 0)(
Complement _ A)(if eq_nat_dec j 1 then A else Empty_set _)bb)in H3. elim(
eq_nat_dec j 1). intro aaa. rewrite aaa in H3. simpl in H3. auto. intro bbb.
rewrite(if_r _ _ _(eq_nat_dec j 1)A(Empty_set _)bbb)in H3. elim H3.
(**)
intro b. rewrite(if_r _ _ _(eq_nat_dec i 0)(Complement _ A)(if eq_nat_dec i 1
then A else Empty_set _)b)in H2. elim(eq_nat_dec i 1). intro aa. rewrite aa in
H2. simpl in H2. elim(eq_nat_dec j 0). intro aaa. rewrite aaa in H3. simpl in
H3. auto. intro bbb. rewrite(if_r _ _ _(eq_nat_dec j 0)(Complement _ A)(if
eq_nat_dec j 1 then A else Empty_set _)bbb)in H3. elim(eq_nat_dec j 1).
intuition. intro bbbb. rewrite(if_r _ _ _(eq_nat_dec j 1)A(Empty_set _)bbbb) in
H3. elim H3. intro bb. rewrite(if_r _ _ _(eq_nat_dec i 1)A(Empty_set _)bb)in H2
. elim H2. Qed.

Lemma simple_P5:
forall(U:Type)(A:Ensemble U),
simple_1 _ 2(fun i:nat=>INR i)(fun i:nat=>if eq_nat_dec i 0 then Complement _ A
else if eq_nat_dec i 1 then A else Empty_set _).
(**)
intros. red. intro x. elim(classic(A x)). intro. exists 1. auto. intro. exists
0. auto. Qed.

Lemma simple_P6:
forall(U:Type)(A:Ensemble U),
simple_2 _ 2(fun i:nat=>INR i)(fun i:nat=>if eq_nat_dec i 0 then Complement _ A
else if eq_nat_dec i 1 then A else Empty_set _).
(**)
intros. red. intuition. Qed.

Lemma simple_P7:
forall(U:Type)(A:Ensemble U),
simple_3 _ 2(fun i:nat=>INR i)(fun i:nat=>if eq_nat_dec i 0 then Complement _ A
else if eq_nat_dec i 1 then A else Empty_set _).
(**)
intros. red. intuition. Qed.

Lemma simple_P8:
forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F),
forall A:Ensemble U,F A->
let n:=2 in
let v:=fun i:nat=>INR i in
let w:=fun i:nat=>if eq_nat_dec i 0 then Complement _ A else if
eq_nat_dec i 1 then A else Empty_set _ in
msurable _ _ F' F'' F''' (fun x:U=>v(proj1_sig(simple_P0 _ n v w
(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _) x))).
(**)
intros U F F' F'' F''' A A' n v w. set(I:=simple_P0 _ _ _ _(simple_P4 _ A)(
simple_P5 _ A)(simple_P6 _ A)(simple_P7 _ A)). fold n v w in I. assert(V:forall
x:U,v(proj1_sig(I x))=0%R\/v(proj1_sig(I x))=1%R). intro. elim(eq_nat_dec(
proj1_sig(I x))0). intro a. rewrite a;auto. intro b. elim(eq_nat_dec(proj1_sig(
I x))1). intro a. rewrite a;auto. intro c. elimtype False. elim(proj2_sig(I x))
. intuition.
(**)
assert(Z0:forall x:U,v(proj1_sig(I x))=0%R->(Complement _ A)x). intros. assert(
Z:proj1_sig(I x)=0). apply(simple_P6 _ A). auto. elim(proj2_sig(I x)). rewrite
Z;intuition. assert(Z1:forall x:U,v(proj1_sig(I x))=1%R->A x). intros. assert(Z
:proj1_sig(I x)=1). apply(simple_P6 _ A). auto. elim(proj2_sig(I x)). rewrite Z
;intuition.
(**)
assert(Q0:forall x:U,~A x->v(proj1_sig(I x))=0%R). intros. assert(Q:w 0 x).
auto. elim(proj2_sig(I x)). intros q1 q2. elim q2. intros q3 q4. rewrite<-(q4 0
Q). auto. assert(Q1:forall x:U,A x->v(proj1_sig(I x))=1%R). intros. assert(Q:w
1 x). auto. elim(proj2_sig(I x)). intros q1 q2. elim q2. intros q3 q4. rewrite
<-(q4 1 Q). auto.
(**)
red. fold I. intros D B. unfold preimg. elim(classic(D(INR 0))). elim(classic(D
(INR 1))). intros H1 H0. cut(Full_set _=fun x=>D(v(proj1_sig(I x)))). intro H.
rewrite<-H. apply sigalg_P3. elim F'. intros x K;exists x;auto. auto. auto.
apply Extensionality_Ensembles. split. red. intros x H. clear H. red. elim(
classic(A x)). intro H. rewrite(Q1 x H). auto. intro H. rewrite(Q0 x H). auto.
red. intros. apply Full_intro. intros H1 H0. cut(Complement _ A=fun x=>D(v(
proj1_sig(I x)))). intro H. rewrite<-H. apply F''. auto. apply
Extensionality_Ensembles. split. red. intros x H. red. elim(V x). intro HH.
rewrite HH. auto. intro. elimtype False. apply H. red. apply Z1. auto. red.
intros x H. red in H. elim(V x). intro. red. apply Z0. auto. intro HH. rewrite
HH in H. intuition.
(**)
elim(classic(D(INR 1))). intros H1 H0. cut(A=fun x=>D(v(proj1_sig(I x)))).
intro H. rewrite<-H. auto. apply Extensionality_Ensembles. split. red. intros x
H. red. rewrite(Q1 x H). auto. red. intros x H. red in H. elim(V x). intro HH.
rewrite HH in H. intuition. intuition. intros H1 H0. cut(Empty_set _=fun x=>D(v
(proj1_sig(I x)))). intro H. rewrite<-H. apply sigalg_P1. elim F'. intros x K;
exists x;auto. auto. auto. apply Extensionality_Ensembles. split. intuition.
red. intros x H. red in H. elim(V x). intro HH. rewrite HH in H. intuition.
intro HH. rewrite HH in H. intuition. Qed.

Lemma simple_P9:
(forall(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:
simple_1 _ n v w)(S2:simple_2 _ n v w)(S3:simple_3 _ n v w),
forall c:R,0<c->simple_0 _ n (fun i:nat=>v i*c)w)%R. auto. Qed.

Lemma simple_P10:
(forall(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:
simple_1 _ n v w)(S2:simple_2 _ n v w)(S3:simple_3 _ n v w),
forall c:R,0<c->simple_1 _ n (fun i:nat=>v i*c)w)%R. auto. Qed.

Lemma simple_P11:
(forall(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:
simple_1 _ n v w)(S2:simple_2 _ n v w)(S3:simple_3 _ n v w),
forall c:R,0<c->simple_2 _ n (fun i:nat=>v i*c)w)%R.
(**)
intros. red. intros i j Z. apply S2. apply(Rmult_eq_reg_l c). rewrite
Rmult_comm. rewrite Z. intuition. apply Rgt_not_eq. auto. Qed.

Lemma simple_P12:
(forall(U:Type)(n:nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:
simple_1 _ n v w)(S2:simple_2 _ n v w)(S3:simple_3 _ n v w),
forall c:R,0<c->simple_3 _ n (fun i:nat=>v i*c) w)%R.
(**)
intros. red. intro. replace 0%R with(0*c)%R. 2:ring. apply Rmult_ge_compat_r.
apply Rle_ge. intuition. auto. Qed.

Lemma simple_P13:
(forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F'''
:sigalg_2 _ F)(n:nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:
simple_1 _ n v w)(S2:simple_2 _ n v w)(S3:simple_3 _ n v w)(M:msurable _ _ F'
F'' F''' (fun x:U=>v(proj1_sig(simple_P0 _ n v w S0 S1 S2 S3 x)
))),
forall c:R,forall c':0<c,msurable _ _ F' F'' F''' (fun x:U=>(fun i:nat=>v i*c)(
proj1_sig(simple_P0 _ n (fun i:nat=>v i*c) w (simple_P9 _ n v w S0 S1 S2 S3 c
c')(simple_P10 _ n v w S0 S1 S2 S3 c c')(simple_P11 _ n v w S0 S1 S2 S3 c c')(
simple_P12 _ n v w S0 S1 S2 S3 c c') x))))%R.
(**)
intros. red. intros D D'. set(I:=simple_P0 _ n(fun i:nat=>v i*c)%R w(simple_P9
_ _ _ _ S0 S1 S2 S3 c c')(simple_P10 _ _ _ _ S0 S1 S2 S3 c c')(simple_P11 _ _ _
_ S0 S1 S2 S3 c c')(simple_P12 _ _ _ _ S0 S1 S2 S3 c c')). unfold preimg.
assert(H:forall i:nat,{D(v i*c)%R}+{~D(v i*c)%R}). intro. apply
chicli_pottier_simpson. apply classic. set(W:=fun i=>if H i then w i else
Empty_set _). set(C:=fun z=>exists i:nat,z=W i). cut(unoin _ C=fun x=>D(v(
proj1_sig(I x))*c)%R). intro H1. rewrite<-H1. apply F'''. red. intros z H2. red
in H2;red in H2;unfold W in H2. elim H2. intros i H3. red. rewrite H3. elim(H i
). intro. apply(simple_P1 _ _ _ _ _ _ _ _ _ _ _ _ M i). intro. apply(sigalg_P1
_ _ F' F'' F'''). red. exists W. intros z H2. red in H2. elim H2. intros i H3.
exists i. auto.
(**)
apply(Extensionality_Ensembles U). split. red. intros x H1. red. red in H1;red
in H1;unfold C in H1. elim H1. intros z H2. elim H2. intros H3 H4. elim H3.
intros i H5. unfold W in H5. rewrite H5 in H4. elim(H i). intro H6. assert(H7:~
~D(v i*c)%R). auto. rewrite(if_l _ _ _(H i)(w i)(Empty_set _)H7)in H4. elim(
proj2_sig(I x)). intros H8 H9. elim H9. intros H10 H11. rewrite<-(H11 i H4).
auto. intro H6. rewrite(if_r _ _ _(H i)(w i)(Empty_set _)H6)in H4. intuition.
(**)
red. intros x H1. red. red. red in H1. exists(w(proj1_sig(I x))). unfold C.
split. exists(proj1_sig(I x)). unfold W. elim(proj2_sig(I x)). intros H2 H3.
assert(H4:~~D(v(proj1_sig(I x))*c)%R). auto. exact(sym_eq(if_l _ _ _(H(
proj1_sig(I x)))(w(proj1_sig(I x)))(Empty_set _)H4)). elim(proj2_sig(I x)).
intuition. Qed.



Definition lebint_s
(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(u:forall A,F A->R)(u':msur_0 _ _ F' F'' F''' u)(u'':msur_1 _ _ F'
F'' F''' u)(u''':msur_2 _ _ F' F'' F''' u)(u'''':msur_3 _ _ F' F'' F''' u)(n:
nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:simple_1 _ n v w)(S2:
simple_2 _ n v w)(S3:simple_3 _ n v w)(M:msurable _ _ F' F'' F'''(fun x:U=>v(
proj1_sig(simple_P0 _ n v w S0 S1 S2 S3 x))))(E:Ensemble U)(E':F E)
:=sum_f_R0 (fun i:nat=>((v i)*(u(Intersection _(w i)E)(sigalg_P2 _ _ F' F''
F'''(w i)E(simple_P1 _ _ F' F'' F''' n v w S0 S1 S2 S3 M i)E')))%R) n.

Definition lebint
(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(u:forall A,F A->R)(u':msur_0 _ _ F' F'' F''' u)(u'':msur_1 _ _ F'
F'' F''' u)(u''':msur_2 _ _ F' F'' F''' u)(u'''':msur_3 _ _ F' F'' F''' u)(f:U
->R)(f':forall x:U,(f x>=0)%R)(M:msurable _ _ F' F'' F''' f)(E:Ensemble U)(E':F
E)
:=let B:=fun l=>forall n,forall v,forall w,forall S0,forall S1,forall S2,forall
S3,forall M',(forall x:U,(0<=(fun y:U=>v(proj1_sig(simple_P0 _ n v w S0 S1 S2
S3 y)))x<=f x)%R)->(lebint_s _ _ _ _ _ u u' u'' u''' u'''' n v w S0 S1 S2 S3 M'
E E'<=l)%R in fun L=>B L/\forall L',B L'->(L'<=L)%R.

(*-----------------------------------------------------------------------------
A simple function that is less than or equal to a general function g
everywhere, has its Lebesgue integral less than or equal to the Lebesgue
integral of the general function g.  This fact is true for nonsimple functions
too, but we just prove only what we need for the final theorem.
-----------------------------------------------------------------------------*)
Lemma lebint_P0:
(forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F'''
:sigalg_2 _ F)(u:forall A,F A->R)(u':msur_0 _ _ F' F'' F''' u)(u'':msur_1 _ _
F' F'' F''' u)(u''':msur_2 _ _ F' F'' F''' u)(u'''':msur_3 _ _ F' F'' F''' u)(n
:nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:simple_1 _ n v w)(S2
:simple_2 _ n v w)(S3:simple_3 _ n v w)(M:msurable _ _ F' F'' F'''(fun x:U=>v(
proj1_sig(simple_P0 _ n v w S0 S1 S2 S3 x))))(g:U->R)(g':forall x:U,g x>=0)(g''
:msurable _ _ F' F'' F''' g)(E:Ensemble U)(E':F E),
(forall y:U,(fun x:U=>v(proj1_sig(simple_P0 _ n v w S0 S1 S2 S3 x)))y<=g y)->
forall L,lebint _ _ _ _ _ u u' u'' u''' u'''' g g' g'' E E' L->lebint_s _ _ F'
F'' F''' u u' u'' u''' u'''' n v w S0 S1 S2 S3 M E E'<=L)%R.
(**)
intros U F F' F'' F''' u u' u'' u''' u'''' n v w S0 S1 S2 S3 M g g' g'' E E' H
L H1. elim H1. intros H2 H3. apply H2. split. apply Rge_le. apply S3. apply H.
Qed.

Lemma u_cmp:
forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(u:forall A,F A->R)(u'''':msur_3 _ _ F' F'' F''' u)A B A' B',
A=B->u A A'=u B B'.
(**)
intros U F F' F'' F''' u u'''' A B A' B' H. generalize B'. rewrite<-H. apply
u''''. Qed.

(*-----------------------------------------------------------------------------
The Lebesgue integral of an indicator function is just the measure of the event
interval.
-----------------------------------------------------------------------------*)
Lemma lebint_P1:
forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F''':
sigalg_2 _ F)(u:forall A,F A->R)(u':msur_0 _ _ F' F'' F''' u)(u'':msur_1 _ _ F'
F'' F''' u)(u''':msur_2 _ _ F' F'' F''' u)(u'''':msur_3 _ _ F' F'' F''' u)(f:U
->R)(f':forall x:U,(f x>=0)%R)(f'':msurable _ _ F' F'' F''' f)(E:Ensemble U)(E'
:F E),
forall(A:Ensemble U)(A':F A)(A'':Included _ A E),
lebint_s _ _ F' F'' F''' u u' u'' u''' u'''' 2(fun i:nat=>INR i)(fun i:nat=>if
eq_nat_dec i 0 then Complement _ A else if eq_nat_dec i 1 then A else Empty_set
_)(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)(simple_P8 _ _ F'
F'' F''' A A')E E'=u A A'.
(**)
intros. unfold lebint_s. simpl. assert(H:Intersection _(Empty_set U)E=Empty_set
U). apply Extensionality_Ensembles. split. red. intros x H1. elim H1. auto. red
. intros. split. auto. red in H. intuition.
(**)
replace(u(Intersection _(Empty_set _)E)(sigalg_P2 U F F' F'' F'''(Empty_set U)E
(simple_P1 U F F' F'' F''' 2(fun i=>INR i)(fun i=>if eq_nat_dec i 0 then
Complement _ A else if eq_nat_dec i 1 then A else Empty_set _)(simple_P4 _ A)(
simple_P5 _ A)(simple_P6 _ A)(simple_P7 _ A)(simple_P8 _ _ F' F'' F''' A A')2)
E'))with(u(Empty_set _)(sigalg_P1 _ _ F' F'' F''')). 2:apply sym_eq. 2:apply(
u_cmp U F F' F'' F''' u u''''(Intersection _(Empty_set _)E)(Empty_set _)). 2:
exact H. replace(u(Empty_set _)(sigalg_P1 _ F F' F'' F'''))with 0%R.
(**)
replace(0*u(Intersection _(Complement _ A)E)(sigalg_P2 U F F' F'' F'''(
Complement _ A)E(simple_P1 U F F' F'' F''' 2(fun i=>INR i)(fun i=>if eq_nat_dec
i 0 then Complement _ A else if eq_nat_dec i 1 then A else Empty_set _)(
simple_P4 _ A)(simple_P5 _ A)(simple_P6 _ A)(simple_P7 _ A)(simple_P8 _ _ F'
F'' F''' A A')0)E'))%R with 0%R.
(**)
2:apply sym_eq. 2:apply Rmult_eq_0_compat_r. 2:auto. rewrite Rplus_0_l. rewrite
Rmult_1_l. replace((1+1)*0)%R with 0%R. 2:ring. rewrite Rplus_0_r.
(**)
apply(u_cmp U F F' F'' F''' u u''''(Intersection _ A E)A). apply
Extensionality_Ensembles. split. red. intros x H1. elim H1. auto. intuition.
Qed.

Lemma misc_P0
(U:Type)(f:U->R)(f':forall x:U,(f x>=0)%R)
:forall a:R,(0<a)%R->forall x:U,((fun y:U=>(f y*a))x>=0)%R.
(**)
intros a a' x. rewrite<-(Rmult_0_l a). apply Rle_ge. apply
Rmult_le_compat_r. red. auto. apply Rge_le. auto. Qed.

(******************************************************************************
Latter half of this proof adapted from scal_sum in Coq.Reals.PartSum
******************************************************************************)
(*-----------------------------------------------------------------------------
For a simple function s and constant c, integral(c*s)=c*integral(s).
-----------------------------------------------------------------------------*)
Lemma lebint_P2:
(forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F'''
:sigalg_2 _ F)(u:forall A,F A->R)(u':msur_0 _ _ F' F'' F''' u)(u'':msur_1 _ _
F' F'' F''' u)(u''':msur_2 _ _ F' F'' F''' u)(u'''':msur_3 _ _ F' F'' F''' u)(n
:nat)(v:nat->R)(w:nat->Ensemble U)(S0:simple_0 _ n v w)(S1:simple_1 _ n v w)(S2
:simple_2 _ n v w)(S3:simple_3 _ n v w)(M:msurable _ _ F' F'' F'''(fun x:U=>v(
proj1_sig(simple_P0 _ n v w S0 S1 S2 S3 x))))(E:Ensemble U)(E':F E),
forall(c:R)(c':0<c),lebint_s _ _ _ _ _ u u' u'' u''' u'''' n(fun i:nat=>v i*c)w
(simple_P9 _ n v w S0 S1 S2 S3 c c')(simple_P10 _ n v w S0 S1 S2 S3 c c')(
simple_P11 _ n v w S0 S1 S2 S3 c c')(simple_P12 _ n v w S0 S1 S2 S3 c c')(
simple_P13 _ _ F' F'' F''' n v w S0 S1 S2 S3 M c c') E E' =
c*lebint_s _ _ _ _ _ u u' u'' u''' u'''' n v w S0 S1 S2 S3 M E E')%R.
(**)
intros. unfold lebint_s. cut(forall(An Bn:nat->R)(N:nat)(x:R),(forall i,Bn i=(x
*An i)%R)->(x*sum_f_R0 An N)%R=sum_f_R0 Bn N). intro H. apply sym_eq. apply H.
(**)
intro. rewrite Rmult_assoc. rewrite Rmult_comm. rewrite Rmult_assoc. apply
Rmult_eq_compat_l. rewrite Rmult_comm. apply Rmult_eq_compat_l. apply(u_cmp U F
F' F'' F''' u u''''). auto.
(**)
intros An Bn N x H. induction N as[|N HrecN]. simpl. auto. do 2 rewrite tech5.
rewrite Rmult_plus_distr_l. rewrite<-HrecN. apply Rplus_eq_compat_l. apply
sym_eq. apply H. Qed.



Theorem markov:
(forall(U:Type)(F:Ensemble(Ensemble U))(F':sigalg_0 _ F)(F'':sigalg_1 _ F)(F'''
:sigalg_2 _ F)(u:forall A,F A->R)(u':msur_0 _ _ F' F'' F''' u)(u'':msur_1 _ _
F' F'' F''' u)(u''':msur_2 _ _ F' F'' F''' u)(u'''':msur_3 _ _ F' F'' F''' u)(f
:U->R)(f':forall x:U,f x>=0)(f'':msurable _ _ F' F'' F''' f)(a:R)(a':0<a),
forall L,lebint _ _ _ _ _ u u' u'' u''' u'''' f f' f''(Full_set U)(sigalg_P3 U
F F' F'' F''') L
->u(fun x:U=>f x>=a)(msurable_P1 _ _ F' F'' F''' f f' f'' a a')<=/a*L)%R.

intros U F F' F'' F''' u u' u'' u''' u'''' f f' f'' a a' L L'.
apply(Rmult_le_reg_l a). auto.
replace(a*(/a*L))%R with L.
2:rewrite<-Rmult_assoc. 2:rewrite Rinv_r. 2:ring. 2:auto with real.
set(A:=(fun x:U=>f x>=a)%R).
set(A':=msurable_P1 U F F' F'' F''' f f' f'' a a').
set(v:=fun i:nat=>INR i).
set(w:=fun i:nat=>if eq_nat_dec i 0 then Complement _ A
       else if eq_nat_dec i 1 then A else Empty_set _).
set(I:=lebint_s U F F' F'' F''' u u' u'' u''' u'''' 2 v w
       (simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)
       (simple_P8 _ _ F' F'' F''' A A')(Full_set _)
       (sigalg_P3 U F F' F'' F''')).

replace(u A A')with I.
2:unfold I.
2:unfold w.
2:apply lebint_P1 with(f:=f). 2:auto. 2:auto.
2:red. 2:intros. 2:apply Full_intro.

replace(a*I)%R with(lebint_s U F F' F'' F''' u u' u'' u''' u'''' 2(fun i=>v i*a)w
 (simple_P9 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P10 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P11 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P12 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P13 U F F' F'' F''' 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)
 (simple_P7 _ _)(simple_P8 U F F' F'' F''' A A')a a')
 (Full_set _)(sigalg_P3 U F F' F'' F'''))%R.
2:apply(lebint_P2 U F F' F'' F''' u u' u'' u''' u'''' 2 v w
(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)
(simple_P8 U F F' F'' F''' A A')(Full_set U)(sigalg_P3 U F F' F'' F''')a a').

apply(lebint_P0 U F F' F'' F''' u u' u'' u''' u'''' 2(fun i:nat=>v i*a)w
 (simple_P9 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P10 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P11 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P12 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P13 U F F' F'' F''' 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)
 (simple_P7 _ _)(simple_P8 U F F' F'' F''' A A')a a')f f' f'')%R.
2:exact L'.

intro y.
elim(simple_P0 U 2(fun i=>v i*a)w
 (simple_P9 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P10 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P11 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
(simple_P12 _ 2 v w(simple_P4 _ _)(simple_P5 _ _)(simple_P6 _ _)(simple_P7 _ _)a a')
y)%R.

intros i p. elim(classic(i=0)).
intro H. simpl. rewrite H. simpl. replace(0*a)%R with 0%R. intuition. ring.
intro H. assert(H1:i=1). intuition. simpl. rewrite H1. simpl. replace(1*a)%R with a.
2:ring.
rewrite H1 in p. intuition. Qed.

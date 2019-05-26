From mathcomp Require Import all_ssreflect all_algebra all_field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory UnityRootTheory.
Open Scope ring_scope.

(** Starting from cyril exercise *)

Section PreliminaryLemmas.
(**
* Preliminaries

Let's extend the library on rings and algebraic numbers
with some easy lemmas first.

** Question -2: prove that if a product of natural numbers is 1 then each factor is 1.

Note that we do not consider nat but the copy of nat which is embeded
in the algebraic numbers algC. The theorem already exists for nat, and
we suggest you use a compatibility lemma numbers between nat and Cnat
*)
Lemma Cnat_mul_eq1 : {in Cnat &, forall x y, (x * y == 1) = (x == 1) && (y == 1)}.
Proof.
by move=> x y /CnatP [n ->] /CnatP [m ->]; rewrite -natrM !pnatr_eq1 muln_eq1.
Qed.

Lemma Cnat_add_eq1 : {in Cnat &, forall x y,
   (x + y == 1) = ((x == 1) && (y == 0)) || ((x == 0) && (y == 1))}.
Proof.
move=> x y /CnatP [n ->] /CnatP [m ->]; rewrite -natrD !pnatr_eq1 ?pnatr_eq0.
by move: n m => [|[|?]] [|[|?]].
Qed.

(**
** Question -1: The real part of product
*)
Lemma algReM (x y : algC) : 
  'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof.
rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect Re_rect //;
by rewrite rpredD ?rpredN // rpredM // ?Creal_Re ?Creal_Im.
Qed.

(**
** Question 0: The imaginary part of product
*)
Lemma algImM (x y : algC) : 'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect Im_rect //;
by rewrite rpredD ?rpredN // rpredM // ?Creal_Re ?Creal_Im.
Qed.

Lemma algReV (x : algC) : 
  'Re (x^-1) = 'Re x / `|x| ^+ 2.
Proof.
have [|/mulfV H] := boolP (x^* == 0).
  rewrite conjC_eq0 => /eqP->.
  by rewrite invr0 normr0 (Creal_ReP _ _) ?mul0r.
rewrite -{1}[_ ^-1]mul1r -H -mulrA -invfM.
rewrite {1}[x]algCrect conjC_rect ?Creal_Re ?Creal_Im //.
have F : (x^* * x)^-1 \is Creal.
  by rewrite rpredV CrealE rmorphM conjCK mulrC.
rewrite mulrBl -mulrN -['i * _ * _]mulrA Re_rect ?normCKC //.
  by rewrite rpredM ?Creal_Re.
by rewrite mulrN rpredN rpredM  // Creal_Im.
Qed.

Lemma algImV (x : algC) : 
  'Im (x^-1) = - ('Im x / `|x| ^+ 2).
Proof.
have [|/mulfV H] := boolP (x^* == 0).
  rewrite conjC_eq0 => /eqP->.
  by rewrite invr0 normr0 (Creal_ImP _ _) ?mul0r ?oppr0.
rewrite -{1}[_ ^-1]mul1r -H -mulrA -invfM.
rewrite {1}[x]algCrect conjC_rect ?Creal_Re ?Creal_Im //.
have F : (x^* * x)^-1 \is Creal.
  by rewrite rpredV CrealE rmorphM conjCK mulrC.
rewrite mulrBl -mulrN -['i * _ * _]mulrA Im_rect ?normCKC //.
- by rewrite mulrN.
- by rewrite rpredM ?Creal_Re.
by rewrite mulrN rpredN rpredM  // Creal_Im.
Qed.

Lemma algRe_div (x y : algC) : 
  'Re (x/y) = ('Re x * 'Re y + 'Im x * 'Im y) / `|y| ^+ 2.
Proof.
by rewrite algReM algReV algImV mulrN opprK mulrA ['Im x * _]mulrA mulrDl.
Qed.

Lemma algIm_div (x y : algC) : 
  'Im (x/y) = ('Re y * 'Im x - 'Re x * 'Im y) / `|y| ^+ 2.
Proof.
rewrite algImM algReV algImV addrC mulrN mulrA ['Re x * _]mulrA mulrBl.
by rewrite mulrAC.
Qed.

Definition cdivz (x y : int) : int :=
  (let q := (x %/ y) in
   if (y == 0) || (2%:R * (x %% y)%Z <= `|y|) then
    q else q + (-1) ^+ (y < 0)%R)%Z.

Infix "%c/" := cdivz (at level 40) : int_scope.

Lemma cdivz0 x : (x %c/ 0)%Z = 0.
Proof. by rewrite /cdivz eqxx divz0. Qed.

Lemma cdiv0z y : (0 %c/ y)%Z = 0.
Proof.  by rewrite /cdivz div0z mod0z mulr0 normr_ge0 orbT. Qed.

Lemma cdivz1 x : (x %c/ 1)%Z = x.
Proof. by rewrite /cdivz oner_eq0 divz1 modz1 normr1 mulr0. Qed.

Lemma cdivzz x : x != 0 -> (x %c/ x)%Z = 1.
Proof. 
move=> xNz.
by rewrite /cdivz (negPf xNz) divzz xNz modzz mulr0.
Qed.

Definition cmodz (x y : int) : int := x - (x %c/ y)%Z * y.
 
Infix "%c%" := cmodz (at level 40) : int_scope.

Lemma cdivz_eq (x y :  int) : x = (x %c/ y)%Z * y + (x %c% y)%Z.
Proof. by rewrite /cmodz addrC subrK. Qed.

Lemma cmodz0 x : (x %c% 0)%Z = x.
Proof. by rewrite {2}(cdivz_eq x 0) mulr0 add0r. Qed.

Lemma cmod0z y : (0 %c% y)%Z = 0.
Proof. by rewrite {2}(cdivz_eq 0 y) cdiv0z mul0r add0r. Qed.

Lemma cmodz1 x : (x %c% 1)%Z = 0.
Proof. by rewrite /cmodz cdivz1 mulr1 subrr. Qed.

Lemma cmodzz x : (x %c% x)%Z = 0.
Proof.
have [/eqP->|xNz] := boolP (x == 0); first by rewrite cmod0z. 
by rewrite /cmodz cdivzz // mul1r subrr.
Qed.

Lemma cmodz_lt (x y : int) : y != 0 -> (2%:R * `|x %c% y| <= `|y|)%Z.
Proof.
move=> yNz; rewrite /cmodz /cdivz (negPf yNz) /=.
have [mLe|eLm] := boolP (2%:R * (_ %% _)%Z <= `|_|).
  rewrite  {1}(divz_eq x y) [_ * _ + _]addrC addrK.
  by rewrite [`|(_ %% _)%Z|]ger0_norm // modz_ge0.
rewrite mulrDl opprD addrA {1}(divz_eq x y) [_ * _ + _]addrC addrK.
have F := ltz_mod x yNz.
rewrite -normrEsign ler0_norm; last first.
  by rewrite subr_le0; apply: ltrW.
rewrite mulrN mulrBr opprB lter_sub_addl (_ : 2%:R = 1 + 1) //.
by rewrite mulrDl mul1r ler_add // ltrW // ltrNge.
Qed.

End PreliminaryLemmas.
(**
----
* The ring of Gauss integers

 - Ref: exercices de mathematiques oraux X-ENS algebre 1
 - Exercice 3.10. ENS Lyon

*)
Section GaussIntegers.
(**
First we define a predicate for the algebraic numbers which are gauss integers.
*)
Definition gaussInteger := [qualify a x | ('Re x \in Cint) && ('Im x \in Cint)].
(**

** Question 1: Prove that integers are gauss integers

*)
Lemma Cint_GI (x : algC) : x \in Cint -> x \is a gaussInteger.
Proof.
move=> x_int; rewrite qualifE (Creal_ReP _ _) ?(Creal_ImP _ _) ?Creal_Cint //.
by rewrite x_int rpred0.
Qed.
(**

** Question 2: Prove that gauss integers form a subfield
*)
Lemma GI_subring : subring_closed gaussInteger.
Proof.
split => [|x y /andP[??] /andP[??]|x y /andP[??] /andP[??]].
- by rewrite Cint_GI.
- by rewrite qualifE !raddfB /= ?rpredB.
by rewrite qualifE algReM algImM rpredB ?rpredD // rpredM.
Qed.
(**

There follows the boilerplate to use the proof GI_subring in order to
canonically provide a subring structure to the predicate gaussInteger.

*)
Fact GI_key : pred_key gaussInteger. Proof. by []. Qed.
Canonical GI_keyed := KeyedQualifier GI_key.
Canonical GI_opprPred := OpprPred GI_subring.
Canonical GI_addrPred := AddrPred GI_subring.
Canonical GI_mulrPred := MulrPred GI_subring.
Canonical GI_zmodPred := ZmodPred GI_subring.
Canonical GI_semiringPred := SemiringPred GI_subring.
Canonical GI_smulrPred := SmulrPred GI_subring.
Canonical GI_subringPred := SubringPred GI_subring.
(**

Finally, we define the type of Gauss Integer, as a sigma type of
algebraic numbers. We soon prove that this is in fact a sub type.

*)
Record GI := GIof {
  algGI : algC;
  algGIP : algGI \is a gaussInteger }.
(** We make the defining property of GI a Hint *)
Hint Resolve algGIP.
(**

We provide the subtype property.

- This makes it possible to use the generic operator "val" to get an
  algC from a Gauss Integer.

*)
Canonical GI_subType := [subType for algGI].
(**
We deduce that the real and imaginary parts of a GI are integers
*)
Lemma GIRe (x : GI) : 'Re (val x) \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Lemma GIIm (x : GI) : 'Im (val x) \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Hint Resolve GIRe GIIm.

Canonical ReGI x := GIof (Cint_GI (GIRe x)).
Canonical ImGI x := GIof (Cint_GI (GIIm x)).
(**

We provide a ring structure to the type GI, using the subring
canonical property for the predicate gaussInteger

*)
Definition eqGIMixin := [eqMixin of GI by <:].
Canonical eqGIType := EqType GI eqGIMixin.
Definition GI_choiceMixin := [choiceMixin of GI by <:].
Canonical GI_choiceType := ChoiceType GI GI_choiceMixin.
Definition GI_countMixin := [countMixin of GI by <:].
Canonical GI_countType := CountType GI GI_countMixin.
Definition GI_zmodMixin := [zmodMixin of GI by <:].
Canonical GI_zmodType := ZmodType GI GI_zmodMixin.
Definition GI_ringMixin := [ringMixin of GI by <:].
Canonical GI_ringType := RingType GI GI_ringMixin.
Definition GI_comRingMixin := [comRingMixin of GI by <:].
Canonical GI_comRingType := ComRingType GI GI_comRingMixin.
(* Definition GI_unitRingMixin := [unitRingMixin of GI by <:]. *)
(* Canonical GI_unitRingType := UnitRingType GI GI_unitRingMixin. *)
(**

 - Now we build the unitRing and comUnitRing structure of gauss
   integers. Contrarily to the previous structures, the operator is
   not the same as on algebraics. Indeed the invertible algebraics are
   not necessarily invertible gauss integers.

 - Hence, we define the inverse of gauss integers as follow : if the
   algebraic inverse happens to be a gauss integer we recover the
   proof and package it together with the element and get a gauss
   integer, otherwise, we default to the identity.

 - A gauss integer is invertible if the algbraic inverse is a gauss
   integer.

*)
Definition invGI (x : GI) := insubd x (val x)^-1.
Definition unitGI (x : GI) :=
  (x != 0) && ((val x)^-1 \is a gaussInteger).
(**

** Question 3: prove a few facts in order to find a comUnitRingMixin
for GI, and then instantiate the interfaces of unitRingType and
comUnitRingType.


*)
Fact mulGIr : {in unitGI, left_inverse 1 invGI *%R}.
Proof.
move=> x /andP [x_neq0 xVGI]; rewrite /invGI.
by apply: val_inj; rewrite /= insubdK // mulVr ?unitfE.
Qed.

Fact unitGIP (x y : GI) : y * x = 1 -> unitGI x.
Proof.
rewrite /unitGI => /(congr1 val) /=.
have [-> /eqP|x_neq0] := altP (x =P 0); first by rewrite mulr0 eq_sym oner_eq0.
by move=> /(canRL (mulfK x_neq0)); rewrite mul1r => <- /=.
Qed.

Fact unitGI_out : {in [predC unitGI], invGI =1 id}.
Proof.
move=> x; rewrite inE /= -topredE /= /unitGI.
rewrite negb_and negbK => /predU1P [->|/negPf xGIF];
by apply: val_inj; rewrite /invGI ?val_insubd /= ?xGIF // invr0 if_same.
Qed.

Definition GI_comUnitRingMixin :=
  ComUnitRingMixin mulGIr unitGIP unitGI_out.
Canonical GI_unitRingType := UnitRingType GI GI_comUnitRingMixin.
Canonical GI_comUnitRingType := [comUnitRingType of GI].
(**

** Question 4: Show that gauss integers are stable by conjugation.

*)
Lemma conjGIE x : (x^* \is a gaussInteger) = (x \is a gaussInteger).
Proof. by rewrite ![_ \is a _]qualifE Re_conj Im_conj rpredN. Qed.
(**

We use this fact to build the conjugation of a gauss Integers

*)
Fact conjGI_subproof (x : GI) : (val x)^* \is a gaussInteger.
Proof. by rewrite conjGIE. Qed.

Canonical conjGI x := GIof (conjGI_subproof x).

Fact conjGI_sub : {morph conjGI : a b / a - b}.
Proof. by move=> a b; apply/val_eqP; rewrite /= raddfB. Qed.

Canonical conjGI_additive := Additive conjGI_sub.

Fact conjGI_multiplicative : multiplicative conjGI.
Proof. by split=> [a b|]; apply/val_eqP; rewrite /= ?(rmorphM,rmorph1). Qed.

Canonical conjGI_rmorphism := AddRMorphism conjGI_multiplicative.

Lemma algGI_nat n : algGI n%:R = n%:R.
Proof. by elim: n => //= n IH; rewrite -addn1 !natrD -IH. Qed.

Lemma conjGI_nat n : conjGI n%:R = n%:R.
Proof. by apply/val_eqP; rewrite /= algGI_nat conjC_nat. Qed.

Lemma conjGIK : involutive conjGI.
Proof. by move=> x; apply/val_eqP/eqP; exact: conjCK. Qed.


(**

We now define the norm (stasm) for gauss integer, we don't need to
specialize it to gauss integer so we define it over algebraic numbers
instead.

*)
Definition gaussNorm (x : algC) := x * x^*.

(**

** Question 4: Show that the gaussNorm of x is the square of the complex modulus of x

*)
Lemma gaussNormE x : gaussNorm x = `|x| ^+ 2.
Proof. by rewrite normCK. Qed.
(**

** Question 5: Show that the gaussNorm of an gauss integer is a natural number.

*)
Lemma gaussNormCnat (x : GI) : gaussNorm (val x) \in Cnat.
Proof. by rewrite /gaussNorm -normCK normC2_Re_Im rpredD // Cnat_exp_even. Qed.
Hint Resolve gaussNormCnat.


Delimit Scope GI_scope with GI.

Open Scope GI_scope.

Definition normGI (x : GI) := truncC (gaussNorm (val x)).
Local Notation "'N x" := (normGI x%R) (at level 10) : GI_scope.

(**

** Question 6: Show that gaussNorm is multiplicative (on all algC).

*)
Lemma gaussNorm0 : gaussNorm 0 = 0.
Proof. by rewrite /gaussNorm mul0r. Qed.

Lemma normGI0 : 'N 0 = 0%N.
Proof. by rewrite /normGI gaussNorm0 (natCK 0). Qed.

Lemma gaussNorm1 : gaussNorm 1 = 1.
Proof. by rewrite /gaussNorm rmorph1 mulr1. Qed.

Lemma normGI1 : 'N 1 = 1%N.
Proof. by rewrite /normGI gaussNorm1 (natCK 1). Qed.

Lemma gaussNormM : {morph gaussNorm : x y / x * y}.
Proof. by move=> x y; rewrite /gaussNorm rmorphM mulrACA. Qed.

Lemma normGIM x y : 'N (x * y) = ('N x * 'N y)%N.
Proof. by rewrite /normGI gaussNormM truncCM. Qed.

Lemma normGIX x n : 'N (x ^+ n) = ('N x ^ n)%N.
Proof.
elim: n => [|n IH].
  by rewrite expr0 normGI1 expn0.
by rewrite exprS normGIM IH expnS.
Qed.

Lemma gaussNorm_eq0 (x : GI) : (gaussNorm (algGI x) == 0) = (x == 0).
Proof. by rewrite gaussNormE sqrf_eq0 normr_eq0. Qed.

Lemma normGI_eq0 (x : GI) : ('N x == 0%N) = (x == 0).
Proof.
have /charf0P<- := Cchar.
by rewrite truncCK // gaussNorm_eq0.
Qed.

Lemma normGI_gt0 (x : GI) : ('N x > 0)%N = (x != 0).
Proof. by rewrite ltn_neqAle andbT eq_sym normGI_eq0. Qed.

Lemma normGI_le (x y : GI) : y != 0 -> ('N x <= 'N (x * y))%N.
Proof.
rewrite -!normGI_eq0 normGIM; case: ('N _) => // n _.
by rewrite leq_pmulr.
Qed.

Lemma normGI_nat n : 'N n%:R = (n ^ 2)%N.
Proof.
by rewrite /normGI [val _]algGI_nat gaussNormE normr_nat truncCX // natCK.
Qed.

Lemma normGIE (x : GI) : ('N(x) = truncC (`|'Re (val x)|) ^ 2 + truncC (`|'Im (val x)|) ^ 2)%N.
Proof.
rewrite /normGI gaussNormE normC2_Re_Im truncCD ?Cnat_exp_even //; last first.
  by rewrite qualifE Cnat_ge0 // Cnat_exp_even.
by rewrite -!truncCX ?Cnat_norm_Cint // !Cint_normK.
Qed.

Lemma truncC_Cint (x : algC) :
  x \in Cint -> x = (-1) ^+ (x < 0)%R * (truncC `|x|)%:R.
Proof.
by move=> xCint; rewrite {1}[x]CintEsign // truncCK // Cnat_norm_Cint.
Qed.

Lemma normGI_eq1 (x : GI) : ('N(x) == 1)%N = (val x \in [::1;-1;'i;-'i]).
Proof.
apply/idP/idP; last first.
  by rewrite normGIE !inE => /or4P[] /eqP->;
     rewrite ?raddfN /= ?(Creal_ReP 1 _) ?(Creal_ImP 1 _) ?Re_i ?Im_i //=
          ?normrN ?normr1 ?normr0 ?truncC0 ?truncC1.
rewrite  [val x]algCrect normGIE.
have /andP[/truncC_Cint {2}-> /truncC_Cint {2}->] := algGIP x.
by case: truncC => [|[|m]] //; case: truncC => [|[|n]] // _; 
   rewrite !(mulr1, mulr0, add0r, addr0); case: (_ < _)%R;
   rewrite ?(expr1, expr0, mulrN, mulr1, inE, eqxx, orbT).
Qed.

(**

** Question 7: Find the invertible elements of GI

 - This is question 1 of the CPGE exercice

 - Suggested strategy: sketch the proof on a paper first, don't let
   Coq divert you from your proofsketch

*)
Lemma unitGIE (x : GI) : (x \in GRing.unit) =
 (val x \in 4.-unity_root).
Proof.
have eq_algC (a b : algC) : (a == b) = ('Re a == 'Re b) && ('Im a == 'Im b).
  rewrite {1}[a]algCrect {1}[b]algCrect -subr_eq0 opprD addrACA -mulrBr.
  rewrite -normr_eq0 -sqrf_eq0 normC2_rect ?rpredB ?Creal_Re ?Creal_Im //.
  rewrite paddr_eq0 ?real_exprn_even_ge0 // ?rpredB ?Creal_Re ?Creal_Im //.
  by rewrite !expf_eq0 /= !subr_eq0.
have N1Creal : -1 \is Creal by rewrite rpredN.
have oneE :    1 = 1 + 'i * 0 :> algC by rewrite mulr0 addr0.
have N1E  :  - 1 = - 1 + 'i * 0 :> algC by rewrite mulr0 addr0.
have iE   :   'i = 0 + 'i * 1 :> algC by rewrite mulr1 add0r.
have NiE  : - 'i = 0 + 'i * (- 1) :> algC by rewrite mulrN1 add0r.
have onerN1 : (1 == -1 :> algC) = false.
  by rewrite -subr_eq0 opprK paddr_eq0 ?oner_eq0 ?ler01.
pose my := @id algC.
transitivity (gaussNorm (val x) == 1).
  apply/idP/eqP; last first.
    by move=> gNx; apply/unitrPr; exists (conjGI x); apply: val_inj.
  move=> x_unit; have /(congr1 (gaussNorm \o val)) /= /eqP := mulrV x_unit.
  by rewrite gaussNormM gaussNorm1 Cnat_mul_eq1 //= => /andP [/eqP].
rewrite (@mem_unity_roots _ 4 (map my [:: 1; -1; 'i; -'i])) //; last 2 first.
- rewrite /= !unity_rootE /= [(- 'i) ^+ _]exprNn expr1n  -signr_odd ?expr0.
  by rewrite -[4]/(2 * 2)%N exprM sqrCi -signr_odd ?expr0 mulr1 !eqxx.
- rewrite /= ![my _](iE, oneE, N1E, NiE).
  rewrite /= !in_cons !in_nil /= !negb_or -!andbA !andbT /=.
  rewrite ![_ + 'i * _ == _]eq_algC ?Re_rect ?Im_rect //.
  rewrite ![_ == -1]eq_sym ![_ == 1]eq_sym oppr_eq0.
  by rewrite eqxx onerN1 oner_eq0.
rewrite gaussNormE [val x]algCrect normC2_rect ?Creal_Re ?Creal_Im //.
rewrite Cnat_add_eq1 ?Cnat_exp_even ?expf_eq0 //=.
rewrite -Cint_normK // -['Im _ ^+ 2]Cint_normK //.
rewrite !expr2 !Cnat_mul_eq1 ?andbb ?Cnat_norm_Cint //.
rewrite !real_eqr_norml ?Creal_Re ?Creal_Im ?ler01 ?andbT //=.
rewrite !inE ![my _](iE, oneE, N1E, NiE).
rewrite ![_ + 'i * _ == _]eq_algC
   ?Re_rect ?Im_rect // ?Creal_Re ?Creal_Im //.
by rewrite andb_orl andb_orr -orbA.
Qed.

Lemma algC_eqE (x y : algC) : (x == y) = (('Re x == 'Re y) && ('Im x == 'Im y)).
Proof.
apply/eqP/andP=> [->//|[/eqP H1 /eqP H2]].
by rewrite [x]algCrect H1 H2 -algCrect.
Qed.

Lemma normGI_unit (x : GI) : ('N(x) == 1)%N = (x \in GRing.unit).
Proof.
rewrite normGI_eq1 unitGIE.
rewrite (@mem_unity_roots _ 4 (map id [:: 1; -1; 'i; -'i])) //.
  rewrite /= !unity_rootE /= [(- 'i) ^+ _]exprNn expr1n  -signr_odd ?expr0.
  by rewrite -[4]/(2 * 2)%N exprM sqrCi -signr_odd ?expr0 mulr1 !eqxx.
rewrite /= !in_cons !in_nil /= !negb_or -!andbA !andbT /= eqr_opp.
rewrite -addr_eq0 (eqC_nat 2 0) andTb.
rewrite algC_eqE (Creal_ImP _ _) // Im_i (eqC_nat 0 1) andbF andTb.
rewrite algC_eqE raddfN (Creal_ReP _ _) //= Re_i oppr0 (eqC_nat 1 0) andFb andTb.
rewrite algC_eqE !raddfN /= (Creal_ImP _ _) // Im_i oppr0 (eqC_nat 0 1) andbF andTb.
by rewrite -addr_eq0 (@mulrn_eq0 _ 'i 2) negb_or neq0Ci.
Qed.

Fact GI_idomainAxiom (x y : GI) : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> /(congr1 (gaussNorm \o val)) /= /eqP.
by rewrite gaussNorm0 gaussNormM mulf_eq0 !gaussNorm_eq0.
Qed.

Canonical GI_idomainType :=
  Eval hnf in IdomainType GI GI_idomainAxiom.

Fact divGI_subproof (x y : int) : x%:~R + 'i * y%:~R \is a gaussInteger.
Proof. by rewrite qualifE /= Re_rect ?Im_rect ?Creal_Cint ?Cint_int. Qed.

Definition divGI (x y : GI) : GI :=
  let zr := floorC ('Re (val x) * 'Re (val y) + 'Im (val x) * 'Im (val y)) in
  let zi := floorC ('Re (val y) * 'Im (val x) - 'Re (val x) * 'Im (val y)) in
  let n := 'N y in
  GIof (divGI_subproof (cdivz zr n) (cdivz zi n)).

Notation " x %/ y " := (divGI x y) : GI_scope.

Lemma divGI0 x : x %/ 0 = 0.
Proof.
apply/val_eqP=> /=.
by rewrite !raddf0 !(mul0r, mulr0, subrr, add0r, floorC0, normGI0, cdiv0z).
Qed.

Lemma div0GI y : 0 %/ y = 0.
Proof.
apply/val_eqP=> /=.
by rewrite !raddf0 !(mul0r, mulr0, subrr, add0r, floorC0, normGI0, cdiv0z).
Qed.

Lemma divGI1 x : x %/ 1 = x.
Proof.
apply/val_eqP=> /=.
have /andP[CR CI] := algGIP x.
rewrite normGI1 !cdivz1 (Creal_ReP 1 _) ?(Creal_ImP 1 _) //
   !(mul1r, mulr1, mulr0, mul0r, addr0, add0r, subr0).
by rewrite 2?floorCK ?Creal_Cint // -algCrect.
Qed.

Lemma divGIxx (x : GI) : x != 0 -> x %/ x = 1.
Proof.
move=> xNz; apply/val_eqP => /=.
rewrite subrr floorC0 cdiv0z mulr0 addr0.
have := xNz.
rewrite -normGI_eq0.
rewrite /normGI gaussNormE [val x]algCrect normC2_rect ?(Creal_Cint, Cint_int) //.
set u :=_ + _ * _ => uNz.
have->: floorC u = truncC u.
  apply: floorC_def.
  rewrite [(_+ 1)%Z]addrC -intS truncC_itv //.
  rewrite addr_ge0 // -expr2 real_exprn_even_ge0 ?(Creal_Cint, Cint_int) //.
by rewrite cdivzz ?mul1r ?subrr.
Qed.

Definition modGI (x y : GI) : GI := x - (x %/ y)%GI * y.

Notation " x %% y " := (modGI x y) : GI_scope.

Lemma modGI0 x : x %% 0 = x.
Proof. by apply/val_eqP; rewrite /= !raddf0 !mulr0 subr0. Qed.

Lemma mod0GI y : 0 %% y = 0.
Proof.
apply/val_eqP.
by rewrite /= !(raddf0, mul0r, mulr0, add0r, floorC0, cdiv0z).
Qed.

Lemma modGI1 x : x %% 1 = 0.
Proof. by rewrite /modGI divGI1 mulr1 subrr. Qed.

Lemma divGI_eq (x y : GI) : x = (x %/ y)%GI * y + (x %% y)%GI.
Proof. by rewrite /modGI addrC subrK. Qed.

Lemma ltn_modGI(x y : GI) : ('N (x %% y)%GI < 'N y)%N = (y != 0).
Proof.
have [/eqP->|yNz] := boolP (y == 0).
  by rewrite normGI0 modGI0.
have /ltn_pmul2r<-: (0 < 'N(y) ^ 2)%N by rewrite sqrn_gt0 lt0n normGI_eq0.
rewrite -{1}normGI_nat -!normGIM /modGI /divGI.
set Ux := floorC _.
set Uy := floorC _.
have UxRe : Ux%:~R = 'Re (algGI x / algGI y * ('N y)%:R).
  rewrite algReM ['Re _%:R](Creal_ReP _ _) ?qualifE ?ler0n //.
  rewrite ?['Im _%:R](Creal_ImP _ _) ?qualifE ?ler0n // mulr0 subr0.
  rewrite /normGI truncCK // algRe_div -gaussNormE divfK; last first.
    by rewrite gaussNorm_eq0.
  by rewrite floorCK // rpredD // rpredM.
have UyIm : Uy%:~R = 'Im (algGI x / algGI y * ('N(y))%GI%:R).
  rewrite algImM ['Re _%:R](Creal_ReP _ _) ?qualifE ?ler0n //.
  rewrite ?['Im _%:R](Creal_ImP _ _) ?qualifE ?ler0n // mulr0 add0r mulrC.
  rewrite /normGI truncCK // algIm_div -gaussNormE divfK; last first.
    by rewrite gaussNorm_eq0.
  by rewrite floorCK // rpredB // rpredM.
rewrite ['N (_ * _)]/normGI /= -[algGI x](divfK yNz).
rewrite -mulrBl -mulrA -[algGI y * _]mulrC mulrA algGI_nat mulrBl.
rewrite [_ * _%:R]algCrect -UxRe -UyIm [_ * _%:R]mulrDl -['i * _ * _]mulrA.
rewrite {1}(cdivz_eq Ux ('N y)) {1}(cdivz_eq Uy ('N y)).
rewrite subC_rect ![_ + cmodz _ _]addrC.
rewrite rmorphD /= rmorphM /= addrK.
rewrite [(_ + _)%:~R]rmorphD /= rmorphM /= addrK.
rewrite !gaussNormM gaussNormE normC2_rect ?(Creal_Cint, Cint_int) //.
rewrite truncCM //; last by rewrite rpredD // Cnat_exp_even // Cint_int.
rewrite mulnC ltn_pmul2l; last by rewrite lt0n normGI_eq0.
rewrite -!rmorphX /= -!rmorphD /=.
rewrite -[_ + _]gez0_abs ?natCK; last first.
  by rewrite addr_ge0 // exprn_even_ge0.
set x1 := _ ^+ 2; set x2 := _ ^+ 2.
apply: leq_ltn_trans (_ : (`|x1| + `|x2| < _)%N).
  have := leq_add_dist (x1) (x1 - x2) (-x2).
  by rewrite !opprK subrK opprB [_ + (_ - _)]addrC subrK [(`|_| + _)%N]addnC.
rewrite -(ltn_pmul2l (isT: (0 < 2 ^ 2)%N)) mulnDr.
apply: leq_ltn_trans (_ : 2 * 'N y ^ 2 < _)%N; last first.
  by rewrite ltn_mul2r sqrn_gt0 lt0n normGI_eq0 yNz.
have F : Posz ('N y) != 0.
  by rewrite eqz_nat normGI_eq0.
by rewrite mul2n -addnn leq_add // !abszX -!expnMn leq_exp2r //
       -(@ler_nat [numDomainType of int]) natrM !natz /= cmodz_lt.
Qed.

Lemma ltn_modGIN0 x y : y != 0 -> ('N (x %% y)%GI < 'N y)%N.
Proof. by rewrite ltn_modGI. Qed.

Lemma modGIxx x : (x %% x)%GI = 0.
Proof.
have [/eqP->|xNz] := boolP (x == 0); first by rewrite mod0GI.
by rewrite /modGI divGIxx // mul1r subrr.
Qed.

Lemma divGIKl (x y : GI) : x != 0 -> (y * x %/ x) = y.
Proof.
move=> xNz.
apply/eqP; rewrite eq_sym -subr_eq0.
have := xNz; rewrite -(ltn_modGI (y * x)).
have -> : ((y * x) %% x)%GI  = (y - ((y * x) %/ x)%GI) * x.
  by rewrite mulrBl {2}(divGI_eq (y * x) x) [_ + (_ %% _)%GI]addrC addrK.
by rewrite normGIM -{2}['N x]mul1n ltn_mul2r ltnS leqn0 normGI_eq0 => /andP[].
Qed.

Lemma divGIKr (x y : GI) : x != 0 -> (x * y %/ x) = y.
Proof. by rewrite mulrC; exact: divGIKl. Qed.

Lemma modGIKl (x y : GI) : (y * x %% x) = 0.
Proof.
have [/eqP->|xNz] := boolP (x == 0); first by rewrite modGI0 mulr0.
by rewrite /modGI divGIKl // subrr.
Qed.

Lemma modGIKr (x y : GI) : (x * y %% x) = 0.
Proof. by rewrite mulrC modGIKl. Qed.

Definition dvdGI x y := (y %% x)%GI == 0.

Notation " x %| y " := (dvdGI x y) : GI_scope.

Lemma dvdGI0 x : (x %| 0)%GI.
Proof. by rewrite /dvdGI mod0GI. Qed.

Lemma dvdGIP (x y : GI) :
  reflect (exists q : GI, y = q * x) (x %| y)%GI.
Proof.
apply: (iffP idP) => [/eqP xDy|[q ->]].
  exists (y %/ x)%GI; first by rewrite {1}(divGI_eq y x) xDy addr0.
by rewrite /dvdGI modGIKl.
Qed.

Lemma dvd0GI x : (0 %| x) = (x == 0).
Proof.
apply/dvdGIP/eqP => [[q ->]|->]; first by rewrite mulr0.
by exists 0; rewrite mulr0.
Qed.

Lemma dvdGI_mull z x y : (x %| y) -> (x %| z * y).
Proof. by move=> /dvdGIP[u ->]; apply/dvdGIP; exists (z * u); exact: mulrA. Qed.

Lemma dvdGI_mulr z x y : (x %| y) -> (x %| y * z).
Proof. by rewrite mulrC; exact: dvdGI_mull. Qed.

Lemma dvdGIxx x : x %| x.
Proof. by rewrite /dvdGI modGIxx. Qed.

Lemma dvdGI_norm x y : x %| y -> ('N x %| 'N y)%N.
Proof. by move=> /dvdGIP[z ->]; rewrite normGIM dvdn_mull // dvdnn. Qed.

Lemma dvd1GI x : (1 %| x) .
Proof. by apply/dvdGIP; exists x; rewrite mulr1. Qed.

Lemma dvdGI1 x : (x %| 1) = ('N x == 1%N).
Proof.
apply/idP/idP => [H|].
  by have := dvdGI_norm H; rewrite normGI1 dvdn1.
rewrite normGI_unit => H; apply/dvdGIP; exists x^-1.
by apply/eqP; rewrite mulrC eq_sym -unitrE.
Qed.

Lemma divGIK (x y : GI) : x %| y -> (y %/ x)%GI * x = y.
Proof.
have [/eqP->|nZx /dvdGIP[q ->]] := boolP (x == 0).
  by rewrite dvd0GI mulr0 => /eqP->.
by rewrite divGIKl.
Qed.

Lemma dvdGI_add x y z:  (x %| y) -> (x %| z) -> (x %| y + z).
Proof.
move=> /dvdGIP[q1->] /dvdGIP[q2->]; apply/dvdGIP; exists (q1 + q2).
by rewrite mulrDl.
Qed.

Lemma dvdGI_nat_dvdz_Re n x :
  n%:R %| x -> (n %| `|floorC ('Re (algGI x))|)%N.
Proof.
case/dvdGIP=> q /val_eqP/eqP /(congr1 (fun x => Re x)) /=.
case: x => /= ax; rewrite qualifE => /andP[Rx Ix].
case: q => /= aq; rewrite qualifE => /andP[Rq Iq].
rewrite [aq]algCrect mulrDl algGI_nat -['i * _ * _]mulrA Re_rect; last 2 first.
  by rewrite rpredM // Creal_Cint // Cint_Cnat.
  by rewrite rpredM // Creal_Cint // Cint_Cnat.
move=> /(congr1 Num.norm) /eqP.
rewrite [`|_* _%:R|]normrM -{1}(floorCK Rx) -{1}(floorCK Rq).
rewrite normr_nat -!intr_norm -(intrM _ _ (Posz n)) eqr_int.
rewrite -2![`|_|]abszE -PoszM => /eqP[H].
by apply/dvdnP; exists (`|floorC ('Re aq)|)%N.
Qed.

Lemma dvdGI_nat_dvdz_Im n x :
  n%:R %| x -> (n %| `|floorC ('Im (algGI x))|)%N.
Proof.
case/dvdGIP=> q /val_eqP/eqP/(congr1 (fun x => Im x)) /=.
case: x => /= ax; rewrite qualifE => /andP[Rx Ix].
case: q => /= aq; rewrite qualifE => /andP[Rq Iq].
rewrite [aq]algCrect mulrDl algGI_nat -['i * _ * _]mulrA Im_rect; last 2 first.
  by rewrite rpredM // Creal_Cint // Cint_Cnat.
  by rewrite rpredM // Creal_Cint // Cint_Cnat.
move=> /(congr1 Num.norm) /eqP.
rewrite [`|_* _%:R|]normrM -{1}(floorCK Ix) -{1}(floorCK Iq).
rewrite normr_nat -!intr_norm -(intrM _ _ (Posz n)) eqr_int.
rewrite -2![`|_|]abszE -PoszM => /eqP[H].
by apply/dvdnP; exists (`|floorC ('Im aq)|)%N.
Qed.

Lemma conjGI_dvd x y : x %| y -> (conjGI x) %| (conjGI y).
Proof.
case/dvdGIP=> q ->; apply/dvdGIP; exists (conjGI q).
by rewrite rmorphM.
Qed.

Fact iGI_proof : 'i \is a gaussInteger.
Proof. by rewrite qualifE Re_i Im_i Cint0 Cint1. Qed.

Definition iGI := GIof iGI_proof.

Lemma dvdGI_norm_even x :  ~~ odd ('N x) = ((1 + iGI) %| x).
Proof.
apply/idP/idP => [Ex|/dvdGIP[u ->]]; last first.
  rewrite normGIM {2}/normGI gaussNormE normC2_Re_Im.
  rewrite !raddfD /= Re_i Im_i (Creal_ReP _ _) // (Creal_ImP _ _) //.
  by rewrite add0r addr0 expr1n (natCK 2) odd_mul negb_and orbT.
apply/dvdGIP.
have := algGIP x; rewrite qualifE => / andP[].
have := Ex; rewrite normGIE odd_add !odd_exp /= negb_add.
set m := 'Re _; set n := 'Im _ => /eqP Omn Cm Cn.
suff FF : (n + m)/2%:R + 'i * ((n - m)/2%:R) \is a gaussInteger.
  exists (GIof FF); apply/val_eqP => /=.
  rewrite -{2}['i]mulr1 mulC_rect !mulr1 mul1r -mulrBl -mulrDl.
  rewrite opprB [_  + (m - n)]addrC addrA subrK.
  rewrite -addrA [_ + (_ - _)]addrC subrK.
  have F u : (u * 2%:R = u + u) by rewrite mulrDr mulr1.
  by rewrite -!F !mulfK 1?[algGI x]algCrect ?(eqC_nat _ 0).
rewrite qualifE Re_rect ?Im_rect; last 4 first.
- by rewrite !(rpredM, rpredV) 1? rpredD ?Creal_Cint.
- by rewrite !(rpredM, rpredV) 1? rpredB ?rpredD ?Creal_Cint.
- by rewrite !(rpredM, rpredV) 1? rpredD ?Creal_Cint.
- by rewrite !(rpredM, rpredV) 1? rpredB ?rpredD ?Creal_Cint.
rewrite (CintEsign Cm) (CintEsign Cn).
rewrite -(truncCK (Cnat_norm_Cint Cm)) -(truncCK (Cnat_norm_Cint Cn)).
rewrite -[truncC `|m|]odd_double_half -[truncC `|n|]odd_double_half.
rewrite Omn !natrD !mulrDr ![(-1) ^+ _]signrE.
set u := nat_of_bool _; set v := nat_of_bool _; set w := nat_of_bool _.
set x1 := _./2; set y1 := _./2.
have F : 2%:R != 0 :> algC by rewrite (eqC_nat 2 0).
apply/andP; split.
  rewrite addrAC addrA -mulrDl -addrA.
  rewrite addrAC !addrA -[1 + 1](natrD _ 1 1) addnn.
  rewrite -!muln2 !natrM !mul1r [_ * v%:R]mulrC.
  rewrite ![v%:R * _]mulrBr !mulrA !(mulrBl, mulrDl) !mulfK //.
  by rewrite !mul1r !(rpredB, rpredD, rpredN, rpredM) // Cint_Cnat // Cnat_nat.
rewrite addrAC opprD addrA -mulrBl opprB [(_ - _) + (_ - _)]addrC !addrA subrK.
rewrite -!muln2 !natrM [_ * v%:R]mulrC.
rewrite ![v%:R * _]mulrBr !mulrA !(mulrBl, mulrDl) !mulfK //.
by rewrite !mul1r !(rpredB, rpredD, rpredN, rpredM) // Cint_Cnat // Cnat_nat.
Qed.

Fixpoint gcdGI_rec (n : nat) (xx  yy : GI) {struct n} :=
   let rr := modGI xx yy in
   if rr == 0 then yy else
   if n is n1.+1 then gcdGI_rec n1 yy rr else rr.

Definition gcdGI x y :=
  let: (x1, y1) := if ('N x < 'N y)%N then (y, x) else (x, y) in
  if x1 == 0 then y1 else
  gcdGI_rec ('N x1) x1 y1.

Lemma gcd0GI : left_id 0 gcdGI.
Proof.
move=> x; rewrite /gcdGI.
have [/eqP->|xNz]:= boolP (x == 0).
  by rewrite ltnn eqxx.
rewrite normGI0 normGI_gt0 xNz (negPf xNz).
have : 'N x != 0%N by rewrite normGI_eq0.
by case: ('N _) => [|[|v]]; rewrite //= !(mod0GI, modGI0) (negPf xNz) eqxx.
Qed.

Lemma gcdGI0 : right_id 0 gcdGI.
Proof.
move=> x; rewrite /gcdGI.
have [/eqP->|xNz]:= boolP (x == 0).
  by rewrite ltnn eqxx.
rewrite normGI0 /= (negPf xNz).
by case: ('N _) => [|[|v]] //=  ; rewrite !(modGI0,mod0GI) (negPf xNz) ?eqxx.
Qed.

Lemma gcdGI_recE m n x y : ('N y <= m)%N -> ('N y <= n)%N
      -> ('N y < 'N x)%N -> gcdGI_rec m x y = gcdGI_rec n x y.
Proof.
elim: m n x y => [|m Hrec] [|n] //= x1 y1.
 - rewrite leqn0 normGI_eq0 => /eqP=> -> _.
   rewrite normGI0 normGI_gt0 modGI0 => /negPf-> /=.
   by case: n => [|n]; rewrite /= mod0GI eqxx.
 - rewrite leqn0 normGI_eq0 => _ /eqP=> -> _.
   rewrite modGI0; case: (boolP (x1 == 0)) => // x1Nz.
   by case: m {Hrec} =>[|m]; rewrite /= mod0GI eqxx.
case: ifP => Epq Sm Sn Sq //; rewrite ?Epq //.
case: (eqVneq y1 0) => [->|y1Nz].
  by case: n m {Sm Sn Hrec} => [|m] [|n] //=; rewrite mod0GI eqxx.
apply: Hrec; last by rewrite ltn_modGI.
  by rewrite -ltnS (leq_trans _ Sm) // ltn_modGI.
by rewrite -ltnS (leq_trans _ Sn) // ltn_modGI.
Qed.

Lemma gcdGIE x y :
  gcdGI x y = if ('N x < 'N y)%N
    then gcdGI (y %% x) x else gcdGI (x %% y) y.
Proof.
case: (eqVneq x 0) => [-> | xNz].
  by rewrite mod0GI modGI0 gcd0GI gcdGI0 if_same.
case: (eqVneq y 0) => [-> | yNz].
  by rewrite mod0GI modGI0 gcd0GI gcdGI0 if_same.
rewrite /gcdGI.
case: ltnP; rewrite (negPf xNz, negPf yNz) //=.
  move=> ltxy; rewrite ltn_modGI (negPf xNz) //=.
  rewrite -(ltn_predK ltxy) /=; case: eqP => [->|].
    by case: ('N x) => [|[|s]]; rewrite /= modGI0 (negPf xNz) // mod0GI eqxx.
  move/eqP=> yxNz; rewrite (negPf xNz).
  apply: gcdGI_recE => //; last by rewrite ltn_modGI.
    by rewrite -ltnS (ltn_predK ltxy) (leq_trans _ ltxy) ?leqW // ltn_modGI.
  by rewrite ltnW // ltn_modGI.
move=> leyx; rewrite ltn_modGI (negPf yNz) //=.
have x_gt0: ('N x > 0)%N by rewrite normGI_gt0.
rewrite -(prednK x_gt0) /=; case: eqP => [->|].
  by case: ('N y)%N => [|[|s]]; rewrite /= modGI0 (negPf yNz) // mod0GI eqxx.
move/eqP=> xyNz; rewrite (negPf yNz).
apply: gcdGI_recE => //; last by rewrite ltn_modGI.
  by rewrite -ltnS (prednK x_gt0) (leq_trans _ leyx) // ltn_modGI.
by rewrite ltnW // ltn_modGI.
Qed.

Lemma gcd1GIE y :
  gcdGI 1 y = if ('N y == 1)%N then y else 1.
Proof.
rewrite gcdGIE normGI1; case: leqP => [|H].
  rewrite leq_eqVlt; case: eqP => [/eqP|/= _].
    by rewrite -dvdGI1 => /eqP->; rewrite gcd0GI.
  rewrite ltnS leqn0 normGI_eq0 => /eqP->.
  by rewrite modGI0 gcdGI0.
rewrite modGI1 gcd0GI.
by move: H; rewrite ltnNge leq_eqVlt negb_or => /andP[/negPf->].
Qed.

Lemma gcd1GI_norm y : 'N(gcdGI 1 y) = 1%N.
Proof. by rewrite gcd1GIE; case: eqP; rewrite ?normGI1. Qed.

Lemma gcdGI1 y : gcdGI y 1 = 1.
Proof.
rewrite gcdGIE normGI1; case: leqP => [_|].
  by rewrite modGI1 gcd0GI.
rewrite ltnS leqn0 normGI_eq0 => /eqP->.
by rewrite modGI0 gcdGI0.
Qed.

Lemma gcdGIxx : idempotent gcdGI.
Proof. by move=> x; rewrite gcdGIE ltnn modGIxx gcd0GI. Qed.

Lemma dvdGI_mod d x y : d %| x -> (d %| y) = (d %| y %% x).
Proof.
case: (altP (x =P 0)) => [-> | nZx]; first by rewrite modGI0.
case: (altP (d =P 0)) => [-> | nZd /dvdGIP[q1 ->]].
  by rewrite dvd0GI => /eqP->; rewrite modGI0.
apply/dvdGIP/dvdGIP=> [] [q2 Hq2].
  rewrite /modGI Hq2 !mulrA -mulrBl.
  by set u := _ - _; exists u.
rewrite (divGI_eq y (q1 * d)) Hq2 mulrA -mulrDl.
by set u := _ + _; exists u.
Qed.

Lemma dvdGI_gcdlr x y : (gcdGI x y %| x) && (gcdGI x y %| y).
Proof.
elim: {x y}minn {-2}x {-2}y (leqnn (minn ('N y) ('N x))) => [x y|r IH x y].
  rewrite geq_min !leqn0 !normGI_eq0.
  by case/pred2P=>->; 
     rewrite (gcd0GI, gcdGI0) dvdGIxx ?andbT dvdGI0.
case: (eqVneq x 0) => [-> _|nZx].
  by rewrite gcd0GI dvdGIxx andbT dvdGI0.
case: (eqVneq y 0) => [->|nZy].
  by rewrite gcdGI0 dvdGIxx /= dvdGI0.
rewrite gcdGIE minnC /minn; case: ltnP => [lt_xy | le_xy] le_yr.
  suffices /IH/andP[E1 E2]: (minn ('N x) ('N (y %% x)%GI) <= r)%N.
    by rewrite E2 (dvdGI_mod _ E2).
  by rewrite geq_min orbC -ltnS (leq_trans _ le_yr) ?ltn_modGI.
suffices /IH/andP[E1 E2] : (minn ('N y) ('N (x %% y)%GI) <= r)%N.
  by rewrite E2 andbT (dvdGI_mod _ E2).
by rewrite geq_min orbC -ltnS (leq_trans _ le_yr) ?ltn_modGI.
Qed.

Lemma dvdGI_gcdl x y : gcdGI x y %| x.
Proof. by case/andP: (dvdGI_gcdlr x y). Qed.

Lemma dvdGI_gcdr x y : gcdGI x y %| y.
Proof. by case/andP: (dvdGI_gcdlr x y). Qed.

Lemma gcdGI_eq0 x y : (gcdGI x y == 0) = ((x == 0) && (y == 0)).
Proof.
have [/eqP->|/eqP nZx] := boolP (x == 0).
  by rewrite gcd0GI.
have := dvdGI_gcdl x y.
by case:eqP => //->; rewrite dvd0GI => /eqP.
Qed.

Lemma dvdGI_leq x y : y != 0 -> x %| y -> ('N x <= 'N y)%N.
Proof.
move=> nZy /dvdGIP[q qE]; have := nZy.
rewrite qE -normGI_eq0 normGIM muln_eq0 negb_or => /andP[H1 H2].
by rewrite -[X in (X <= _)%N] mul1n leq_pmul2r lt0n.
Qed.

Lemma leq_gcdGIl (x y : GI) : x != 0 -> ('N (gcdGI x y) <= 'N x)%N.
Proof. by move=> nZx;  apply: dvdGI_leq => //; exact: dvdGI_gcdl. Qed.

Lemma leq_gcdGIr (x y : GI) : y != 0 -> ('N (gcdGI x y) <= 'N y)%N.
Proof. by move=> nZy; move: (dvdGI_gcdr x y); apply: dvdGI_leq. Qed.

Lemma dvdGI_trans : transitive dvdGI.
Proof.
move=> x y z /dvdGIP[qx -> /dvdGIP[qy ->]].
by apply/dvdGIP; exists (qy * qx); rewrite mulrA.
Qed.

Lemma dvdGI_gcd x y z : x %| gcdGI y z = (x %| y) && (x %| z).
Proof.
apply/idP/andP=> [dv_xyz | [dv_xy dv_xz]].
  by rewrite ?(dvdGI_trans dv_xyz) ?dvdGI_gcdl ?dvdGI_gcdr.
move: (leqnn (minn ('N z) ('N y))) dv_xy dv_xz.
elim: {y z}minn {-2}y {-2}z => [|r IH] y z.
  rewrite geq_min !leqn0 !normGI_eq0.
  by case/pred2P=> ->; rewrite ?(gcd0GI, gcdGI0).
case: (eqVneq y 0) => [-> _|nZy]; first by rewrite gcd0GI.
case: (eqVneq z 0) => [->|nZz]; first by rewrite gcdGI0.
rewrite gcdGIE minnC /minn; case: ltnP => Czy le_r dv_y dv_z.
  apply: IH => //; last by rewrite -(dvdGI_mod _ dv_y).
  by rewrite geq_min orbC -ltnS (leq_trans _ le_r) ?ltn_modGI.
apply: IH => //; last by rewrite -(dvdGI_mod _ dv_z).
by rewrite geq_min orbC -ltnS (leq_trans _ le_r) ?ltn_modGI.
Qed.

Lemma dvdGI_mul2r (p d x : GI) :  p != 0 ->  (d * p %| x * p) = (d %| x).
Proof.
move=> nZp; apply/dvdGIP/dvdGIP=> [] [q Hq]; exists q.
  by apply: (mulIf nZp); rewrite -mulrA.
by rewrite Hq mulrA.
Qed.

Lemma dvdGI_mul2l (p d x : GI) :  p != 0 ->  (p * d %| p * x) = (d %| x).
Proof. by rewrite ![p *_]mulrC; exact: dvdGI_mul2r. Qed.

Definition lcmGI x y := (x * y) %/ gcdGI x y.

Lemma mulGI_lcm_gcd x y : lcmGI x y * gcdGI x y = x * y.
Proof. by apply/eqP; rewrite divGIK // dvdGI_mull // dvdGI_gcdr. Qed.

Lemma lcm0GI y : lcmGI 0 y = 0.
Proof. by rewrite /lcmGI mul0r div0GI. Qed.

Lemma lcmGI0 x : lcmGI x 0 = 0.
Proof. by rewrite /lcmGI mulr0 div0GI. Qed.

Lemma lcmGI_eq0 x y : (lcmGI x y == 0) = ((x == 0) || (y == 0)).
Proof.
have [/eqP->|nZx] := boolP (x == 0).
  by rewrite lcm0GI eqxx.
have [/eqP->|nZy] := boolP (y == 0).
  by rewrite lcmGI0 eqxx.
rewrite /lcmGI.
have /dvdGIP[q Hq]: gcdGI x y %| x * y by rewrite dvdGI_mulr // dvdGI_gcdl.
rewrite Hq divGIKl ?gcdGI_eq0 ?negb_and ?nZx //.
case: eqP Hq => // -> /eqP.
by rewrite mul0r mulf_eq0 (negPf nZx) (negPf nZy).
Qed.

Definition eqGI x y :=  (dvdGI x y) && (dvdGI y x).

Lemma eqGIxx : reflexive eqGI.
Proof. by move=> x; rewrite /eqGI dvdGIxx. Qed.

Lemma eqGI_sym : symmetric eqGI.
Proof. by move=> x y; rewrite /eqGI andbC. Qed.

Lemma eqGI_trans : transitive eqGI.
Proof. 
move=> x y z /andP[U1 V1] /andP[U2 V2].
by rewrite /eqGI (dvdGI_trans U1) // (dvdGI_trans V2).
Qed.

Infix "%=" := eqGI : GI_scope.

Lemma eqGI0 (x : GI) : (x %= 0) = (x == 0).
Proof.
apply/andP/eqP=>[[]|->]; last by rewrite dvdGIxx.
by rewrite dvd0GI => _ /eqP.
Qed.

Lemma eqGI_eq0  x y : x %= y -> (x == 0) = (y == 0).
Proof.
have [/eqP->|] := boolP (x == 0).
  by rewrite eqGI_sym eqGI0.
have [/eqP->|//] := boolP (y == 0).
by rewrite eqGI0 => /negP.
Qed.

Lemma eqGI_norm  x y : x %= y -> 'N x = 'N y.
Proof.
have [/eqP->|nZx] := boolP (x == 0).
  by rewrite eqGI_sym eqGI0 => /eqP->.
have [/eqP->|nZy] := boolP (y == 0).
  by rewrite eqGI0 => /eqP->.
case/andP => /(dvdGI_leq nZy) H1 /(dvdGI_leq nZx) H2.
by apply/eqP; rewrite eqn_leq H1.
Qed.

Lemma dvdGI_eq_norm x y : 'N x = 'N y -> x %| y -> x %= y.
Proof.
have [/eqP->|nZx] := boolP (x == 0).
  by rewrite dvd0GI => _ /eqP->; exact: eqGIxx.
move=> xNy xDy; rewrite /eqGI xDy /=.
case/dvdGIP: xDy => q Hq.
apply/dvdGIP; exists q^-1.
rewrite Hq mulrA mulVr ?mul1r // -normGI_unit.
have /eqn_pmul2r<- : (0 < 'N x)%N.
  by move: nZx; rewrite -normGI_eq0; case: ('N x).
by rewrite -normGIM -Hq xNy mul1n.
Qed.

Lemma eqGI_nat m n : m%:R %= n%:R -> m = n.
Proof.
move=> /andP[H1 H2]; apply/eqP.
by rewrite -(eqn_exp2r _ _ (isT : 0 < 2)%N) -!normGI_nat eqn_dvd !dvdGI_norm.
Qed.

Lemma conjGI_gcd x y : conjGI (gcdGI x y) %= gcdGI (conjGI x) (conjGI y).
Proof.
rewrite /eqGI dvdGI_gcd !conjGI_dvd //= ?(dvdGI_gcdr,dvdGI_gcdl) //.
rewrite -[X in X %|_]conjGIK.
by rewrite conjGI_dvd // dvdGI_gcd -{2}[x]conjGIK -{3}[y]conjGIK !conjGI_dvd //
          ?(dvdGI_gcdr,dvdGI_gcdl).
Qed. 

Lemma conjGIM_norm x : x * conjGI x = ('N x)%:R.
Proof.
by apply/val_eqP; rewrite /= -normCK -gaussNormE algGI_nat truncCK.
Qed.

Lemma eqGIP (x y : GI) :
  reflect (exists2 u, normGI u = 1%N & x = u * y)
          (x %= y).
Proof.
apply: (iffP andP)=> [[xDy yDx]|[u Nu->]]; last first.
  split; apply/dvdGIP; last by exists u.
  exists (conjGI u); rewrite mulrA [conjGI _ * _]mulrC.
  by rewrite conjGIM_norm Nu mul1r.
have: 'N x = 'N y by rewrite (@eqGI_norm x y) ///eqGI xDy.
case/dvdGIP: yDx => u -> /eqP.
rewrite normGIM -{2}['N y]mul1n eqn_mul2r normGI_eq0 => /orP[/eqP->|/eqP Nu].
  by exists 1; rewrite ?mulr0 // normGI1.
by exists u.
Qed.

Lemma gcdGIC x y : gcdGI x y %= gcdGI y x.
Proof. by rewrite /eqGI !(dvdGI_gcd, dvdGI_gcdl, dvdGI_gcdr). Qed.

Lemma gcd1GI y : gcdGI 1 y %= 1.
Proof.
rewrite /eqGI dvd1GI dvdGI1 gcd1GIE.
by case: (@eqP _ ('N y) 1%N) => [->|]; rewrite ?normGI1.
Qed.

Lemma eqGI_dvdr x y1 y2 : y1 %= y2 -> (x %| y1) = (x %| y2).
Proof.
move=> /andP[y1Dy2 y2Dy1]; apply/idP/idP.
  by move=> /dvdGI_trans /(_ y1Dy2).
by move=> /dvdGI_trans /(_ y2Dy1).
Qed.

Lemma eqGI_dvdl y x1 x2 : x1 %= x2 -> (x1 %| y) = (x2 %| y).
Proof.
move=> /andP[x1Dx2 x2Dx1]; apply/idP/idP.
  by move=> /(dvdGI_trans x2Dx1).
by move=> /(dvdGI_trans x1Dx2).
Qed.

Lemma eqGI_gcdr x y1 y2 : y1 %= y2 -> gcdGI x y1 %= gcdGI x y2.
Proof.
move=> y1Ey2; rewrite /eqGI !(dvdGI_gcd, dvdGI_gcdl, dvdGI_gcdr).
by rewrite -(eqGI_dvdr _ y1Ey2) dvdGI_gcdr (eqGI_dvdr _ y1Ey2) dvdGI_gcdr.
Qed.

Lemma eqGI_gcdl y x1 x2 : x1 %= x2 -> gcdGI x1 y %= gcdGI x2 y.
Proof.
move=> x1Ex2; apply: eqGI_trans (gcdGIC _ _).
by apply: eqGI_trans (gcdGIC _ _) _; exact: eqGI_gcdr.
Qed.

Lemma eqGI_mul2r (r p q : GI) : r != 0 -> (p * r %= q * r) = (p %= q).
Proof. by move => nZr; rewrite /eqGI !dvdGI_mul2r. Qed.

Lemma eqGI_mul2l (r p q : GI): r != 0 -> (r * p %= r * q) = (p %= q).
Proof. by move => nZr; rewrite /eqGI !dvdGI_mul2l. Qed.

Lemma eqGI_mul (p1 p2  q1 q2 : GI) : 
 p1 %= q1 ->  p2 %= q2 ->  p1 * p2 %= q1 * q2.
Proof.
move=> /andP[E1 E2] /andP[F1 F2]; apply/andP; split.
  have /dvdGIP[u1->] := E1; have /dvdGIP[v1->] := F1.
  by apply/dvdGIP; exists (u1 * v1); rewrite mulrAC [p1 * _]mulrC !mulrA.
have /dvdGIP[u1->] := E2; have /dvdGIP[v1->] := F2.
by apply/dvdGIP; exists (u1 * v1); rewrite mulrAC [q1 * _]mulrC !mulrA.
Qed.

Fixpoint egcdGI_rec n (x y : GI) := 
  if y == 0 then (1, 0) else
  if n is n1.+1 then
    let: (u, v) := egcdGI_rec n1 y (modGI x y) in
     (v, u - v * (x %/ y)%GI)
  else (1, 0).

Definition egcdGI (x y : GI) :=
  if ('N y <= 'N x)%N then 
    egcdGI_rec ('N x) x y else
  let e := egcdGI_rec ('N y) y x in (e.2, e.1).

Lemma egcdGI_rec0r n x : egcdGI_rec n x 0 = (1, 0).
Proof. by case: n => /= [|n]; rewrite eqxx. Qed.

Lemma egcdGI0 x : egcdGI x 0 = (1, 0).
Proof.  by rewrite /egcdGI normGI0 egcdGI_rec0r. Qed.

Lemma egcd0GI y : y != 0 -> egcdGI 0 y = (0, 1).
Proof.
by rewrite /egcdGI normGI0 -normGI_eq0 leqn0  egcdGI_rec0r => /negPf->/=.
Qed.

Lemma egcdGI_recP : 
  forall n x y,  y != 0 -> ('N y <= n)%N -> ('N y <= 'N x)%N ->
  forall (e := egcdGI_rec n x y), gcdGI_rec n x y = e.1 * x + e.2 * y.
Proof.
elim => [x y nZy|n /= IH x y nZy NyLn NyLNx].
  by rewrite leqn0 normGI_eq0 (negPf nZy).
have NxP : (0 < 'N x)%N.
  by apply: leq_trans NyLNx; rewrite ltnNge leqn0 normGI_eq0.
rewrite (negPf nZy).
have [r0|nZr0] := eqVneq (x %% y) 0.
  by rewrite r0 egcdGI_rec0r !mul0r subr0 add0r mul1r eqxx.
have NxyLn : ('N(x %% y)%GI <= n)%N.
  by rewrite -ltnS (leq_trans _ NyLn) // ltn_modGI.
have NxyLNy : ('N (x %% y)%GI <= 'N y)%N by rewrite ltnW // ltn_modGI.
have := IH _ _ nZr0 NxyLn NxyLNy.
case: (egcdGI_rec _ _) => u v ->.
by rewrite (negPf nZr0) /= /modGI mulrBr mulrBl addrCA mulrA.
Qed.

Lemma egcdGIP (x y : GI) : gcdGI x y = (egcdGI x y).1 * x + (egcdGI x y).2 * y.
Proof.
have [->|nZy] := eqVneq y 0.
  by rewrite egcdGI0 gcdGI0 mul1r mulr0 addr0.
have [->|nZx] := eqVneq x 0.
  by rewrite mulr0 add0r gcd0GI egcd0GI // mul1r.
rewrite /egcdGI /gcdGI.
case: leqP => [H|H] /=; last first.
  rewrite (negPf nZy) addrC.
  by apply: egcdGI_recP; rewrite // ltnW.
rewrite (negPf nZx).
apply: egcdGI_recP => //.
Qed.

Lemma mulGI_gcdr x y z : x * gcdGI y z %= gcdGI (x * y) (x * z).
Proof.
have [/eqP->|nZx] := boolP (x == 0); first by rewrite !mul0r gcd0GI eqGIxx.
rewrite /eqGI dvdGI_gcd !dvdGI_mul2l // dvdGI_gcdl dvdGI_gcdr /=.
rewrite [X in _%|_ * X]egcdGIP mulrDr dvdGI_add // mulrCA dvdGI_mull //.
  by rewrite dvdGI_gcdl.
by rewrite dvdGI_gcdr.
Qed.

Lemma mulGI_gcdl x y z : gcdGI y z * x %= gcdGI (y * x) (z * x).
Proof. by rewrite ![_ * x]mulrC mulGI_gcdr. Qed.

Lemma dvdGI_lcm d1 d2 x : lcmGI d1 d2 %| x = (d1 %| x) && (d2 %| x).
Proof.
have [/eqP->|nZd1] := boolP (d1 == 0).
  by rewrite lcm0GI dvd0GI; case: eqP => //->; rewrite dvdGI0.
have [/eqP->|nZd2] := boolP (d2 == 0).
  by rewrite lcmGI0 dvd0GI andbC; case: eqP=> //->; rewrite dvdGI0.
have /dvdGI_mul2r<- : gcdGI d1 d2 != 0 by rewrite gcdGI_eq0 negb_and nZd1.
rewrite mulGI_lcm_gcd (eqGI_dvdr _ (mulGI_gcdr _ _ _)) dvdGI_gcd.
by rewrite {1}mulrC !dvdGI_mul2r // andbC.
Qed.

Section OrdinalGI.

Variable n : nat.

Inductive ordinalGI : predArgType := OrdinalGI x of ('N x < n)%N.

Coercion GI_of_ord i := let: OrdinalGI m _ := i in m.

Canonical ordinalGI_subType := [subType for GI_of_ord].
Definition ordinalGI_eqMixin := Eval hnf in [eqMixin of ordinalGI by <:].
Canonical ordinalGI_eqType := Eval hnf in EqType ordinalGI ordinalGI_eqMixin.
Definition ordinalGI_choiceMixin := [choiceMixin of ordinalGI by <:].
Canonical ordinalGI_choiceType :=
  Eval hnf in ChoiceType ordinalGI ordinalGI_choiceMixin.
Definition ordinalGI_countMixin := [countMixin of ordinalGI by <:].
Canonical ordinalGI_countType :=
  Eval hnf in CountType ordinalGI ordinalGI_countMixin.
Canonical ordinalGI_subCountType := [subCountType of ordinalGI].

Lemma ltn_ordGI (i : ordinalGI) : ('N i < n)%N.
Proof. exact: valP i. Qed.

Lemma ordGI_inj : injective GI_of_ord. Proof. exact: val_inj. Qed.

Definition  ordGI_enum : seq ordinalGI :=
 pmap insub
  [seq (let: (n1, n2) := i in 
        (((nat_of_ord n1))%:R - n%:R) + 
              iGI * ((nat_of_ord n2)%:R - n%:R)) |
      i <-  (enum [finType of ('I_n.*2 * 'I_n.*2)%type])].


Lemma ordGI_enum_uniq : uniq ordGI_enum.
Proof. 
rewrite pmap_sub_uniq // map_inj_in_uniq ?enum_uniq //.
move=> /= [x1 x2] [y1 y2] _ _  /val_eqP /eqP /= H.
congr (_ , _); apply/eqP.
  have /eqP := congr1 (fun x => Re x) H.
  rewrite !Re_rect ?rpredB ?Creal_Cnat ?algGI_nat //.
  by rewrite - subr_eq0 opprB addrA subrK subr_eq0 eqC_nat.
have /eqP := congr1 (fun x => Im x) H.
rewrite !Im_rect ?rpredB ?Creal_Cnat ?algGI_nat //.
by rewrite - subr_eq0 opprB addrA subrK subr_eq0 eqC_nat.
Qed.

Fact int_norm_nat x y m : 
  x \in Cint ->  y \in Cint -> 
  `|x| ^+ 2 + `|y| ^+ 2 < m%:R -> (x + m%:R \in Cnat) && (x + m%:R < m.*2%:R).
Proof.
move=> xCint yCint xyLem.
rewrite CnatEint rpredD // ?Cint_Cnat //=.
have : `|x| ^+ 2 < (Posz m)%:~R ^+ 2.
  apply: ltr_le_trans (_ : m%:R <= _).
    apply: ler_lt_trans xyLem.
    by rewrite ler_addl -realEsqr Creal_Cnat // Cnat_norm_Cint.
  rewrite -natrX ler_nat.
  by case: (m) => // m1; rewrite (leq_pexp2l _ (isT : (0 < 2)%N)).
rewrite -{1}(floorCK xCint) -intr_norm -!rmorphX /= ltr_int.
pose nD := [numDomainType of algC].
case: m{xyLem} => [|m] //.
rewrite -subr_gt0 subr_sqr pmulr_lgt0; last first.
  apply: ltr_le_trans (_ : Posz m.+1 + 0 <= _) => //.
  by apply: ler_add.
rewrite subr_gt0 lter_norml -!(ltr_int nD) floorCK //.
rewrite -subr_gt0 rmorphN opprK => /andP[/ltrW].
by rewrite -[x < _](ltr_add2r m.+1%:R) -natrD addnn => ->.
Qed.

Lemma mem_ordGI_enum x : x \in ordGI_enum.
Proof.
rewrite mem_pmap.
apply/mapP; exists (GI_of_ord x); last by rewrite valK.
apply/mapP.
pose xr := truncC ('Re (algGI (GI_of_ord x)) + n%:R).
pose yr := truncC ('Im (algGI (GI_of_ord x)) + n%:R).
pose nD := [numDomainType of algC].
have := ltn_ordGI x.
rewrite normGIE -(ltr_nat nD) natrD !natrX !truncCK ?Cnat_norm_Cint //.
move => HH.
have /andP[Hrx1 Lx1] := int_norm_nat (GIRe _) (GIIm _) HH.
have F1 : (truncC ('Re (val (GI_of_ord x)) + n%:R) < n.*2)%N.
  by rewrite -(ltr_nat nD) truncCK.
rewrite addrC in HH.
have /andP[Hrx2 Lx2] := int_norm_nat (GIIm _) (GIRe _) HH.
have F2 : (truncC ('Im (val (GI_of_ord x)) + n%:R) < n.*2)%N.
  by rewrite -(ltr_nat nD) truncCK.
exists (Ordinal F1, Ordinal F2); rewrite ?mem_enum //=.
apply/val_eqP=> /=.
by rewrite !algGI_nat !truncCK // !addrK -algCrect.
Qed.

Definition ordinalGI_finMixin :=
  Eval hnf in UniqFinMixin ordGI_enum_uniq mem_ordGI_enum.
Canonical ordinalGI_finType := Eval hnf in FinType ordinalGI ordinalGI_finMixin.
Canonical ordinalGI_subFinType := Eval hnf in [subFinType of ordinalGI].

End OrdinalGI.

Definition primeGI (x : GI) :=
  (1 < 'N x)%N && [forall y : ordinalGI ('N x), (y %| x) ==> ('N y == 1%N)]. 

Lemma nprimeGI0 : ~ primeGI 0.
Proof. by case/andP; rewrite normGI0. Qed.

Lemma primeGIP x :
  reflect ((1 < 'N x)%N /\ 
           forall y, ('N y < 'N x)%N -> (y %| x) -> 'N y = 1%N) (primeGI x).
Proof.
apply: (iffP andP) => [[H1 /forallP H2]|[H1 H2]].
  split => // y yLx yDx.
  by have /implyP/(_ yDx)/eqP := H2 (OrdinalGI yLx).
split => //; apply/forallP => y; apply/implyP => yDx; apply/eqP.
by apply: H2 => //; apply: ltn_ordGI.
Qed.

Lemma primeGIPn x :
  reflect (('N x < 2)%N \/ 
           exists2 y, (1 < 'N y < 'N x)%N & (y %| x)) 
           (~~ primeGI x).
Proof.
apply: (iffP idP)=> [|[H|[y /andP[H1 H2] H3]]]; last 2 first.
- by apply/negP=> /primeGIP[]; rewrite leqNgt H.
- apply/negP=> /primeGIP[H4 /(_ y H2 H3) H5].
  by have := H1; rewrite H5.
case: leqP => [H|H _]; last by left.
case: (boolP [exists z : ordinalGI ('N x), (1 < 'N z)%N && (z %| x)]).
move=> /existsP[z /andP[H1z H2z]]; right; exists z => //.
  by rewrite H1z ltn_ordGI.
rewrite negb_exists => /forallP HH /negP[].
rewrite /primeGI H; apply/forallP => z.
have := HH z; case: (boolP (_ %| _)) => //.
rewrite andbT -leqNgt leq_eqVlt ltnS leqn0 normGI_eq0.
have [/eqP->|] := boolP (GI_of_ord z == 0); last by rewrite orbF.
by rewrite dvd0GI => /eqP HH1; have := H; rewrite HH1 normGI0.
Qed.

Definition primesGI (x : GI) :=
 [seq i <- [seq GI_of_ord i| i : ordinalGI ('N x).+1] |
      primeGI i && (i %| x)].


Lemma mem_primesGI  (p x : GI) :
   (p \in primesGI x) = [&& primeGI p, x != 0 & p %| x].
Proof.
apply/idP/idP.
  rewrite mem_filter => /andP[/andP[H1 H2]] /mapP[[y yL _ /= HH]].
  rewrite H1 H2 andbT /=.
  have /primeGIP[] := H1.
  rewrite HH => HH1 _.
  by rewrite -normGI_eq0 -leqn0 -ltnNge -ltnS (leq_trans HH1) // ltnW.
move=> /andP[H1 /andP[H2 H3]].
have HH : ('N p < ('N x).+1)%N.
  by rewrite ltnS dvdGI_leq // -normGI_eq0; case: ('N _) H2.
rewrite mem_filter H1 H3; apply/mapP; exists (OrdinalGI HH) => //.
by rewrite mem_enum.
Qed.

Lemma eqGI_prime x y : x %= y -> primeGI x -> primeGI y.
Proof.
move=> xEy /primeGIP[H1 H2]; apply/primeGIP; split=> [|y1 Hy1 H1y1].
  by rewrite -(eqGI_norm xEy).
by apply: H2; rewrite ?(eqGI_norm xEy, eqGI_dvdr _ xEy).
Qed.


Definition pdivGI x : GI := head 1 (primesGI x).

Lemma pdivGI_prime x : (1 < 'N x)%N -> primeGI (pdivGI x).
Proof.
move=> Nx.
have [y Py yDz] : exists2 y, primeGI y & (y %| x).
  elim: {x}S {-2}x (ltnSn ('N x)) Nx => // n IH x NxL ONx.
  have [Px|/primeGIPn] := boolP (primeGI x).
    by exists x; rewrite ?dvdGIxx //.
  rewrite ltnNge ONx => [] [//|[y /andP[H1y H2y] H3y]].
    case: (IH _ _ H1y) => [|z Pz zDy]; first by apply: (leq_trans H2y _).
    exists z; rewrite ?(dvdGI_trans zDy) //.
have yIp : y \in primesGI x.
  by rewrite mem_primesGI Py yDz -normGI_eq0; case: ('N _) Nx.
suff: pdivGI x \in primesGI x by rewrite mem_primesGI => /andP[].
by rewrite /pdivGI; case: primesGI yIp => //= a l _; rewrite in_cons eqxx.
Qed.

Lemma pdivGI_dvd x : pdivGI x %| x.
Proof.
have := sym_equal (mem_primesGI (pdivGI x) x).
rewrite /pdivGI; case: primesGI => [|a l]; first by rewrite dvd1GI.
by rewrite /= in_cons eqxx /= => /and3P[].
Qed.

Lemma pdivGI_leq x : x != 0 -> ('N (pdivGI x) <= 'N x)%N.
Proof. by move=> /dvdGI_leq /(_ (pdivGI_dvd _)). Qed.

Lemma pdivGI_neq0 x : pdivGI x != 0.
Proof.
apply/eqP=> H.
have := pdivGI_dvd x.
rewrite H dvd0GI => /eqP Zx.
have := fun x => mem_primesGI x 0; rewrite eqxx /=.
have := H; rewrite Zx /pdivGI; case: primesGI => [/eqP/=| a l _ /(_ a)].
  by rewrite oner_eq0.
by rewrite in_cons eqxx andbF.
Qed.

Fixpoint logGI_rec p x n := 
  if (p %| x) then 
    if n is n1.+1 then (logGI_rec p (x %/ p) n1).+1 else 0%N
  else 0%N.

Definition logGI p x :=
  if primeGI p then logGI_rec p x ('N x) else 0%N.

Lemma logGI_recE p x m1 m2 :
  primeGI p -> ('N x <= m1)%N -> ('N x <= m2)%N -> x != 0 ->
  logGI_rec p x m1 = logGI_rec p x m2.
Proof.
move=> Pp.
elim: m1 m2 x => [m2 x|m1 IH [|m2 /=] x].
- by rewrite leqn0 normGI_eq0 => /eqP->; rewrite eqxx.
- by rewrite leqn0 normGI_eq0 => _ /eqP->; rewrite eqxx.
move=> NxLm1 NxLm2 nZx.
have [/dvdGIP[q Hq]|//] := boolP (_ %| _).
have nZp : p != 0.
  by apply: contra nZx => /eqP HH; rewrite Hq HH mulr0.
have nZq : q != 0.
  by apply: contra nZx => /eqP HH; rewrite Hq HH mul0r.
have F : ('N (x %/ p)%GI < 'N x)%N.
  rewrite Hq divGIKl // normGIM -{1}['N q]muln1.
  by rewrite ltn_mul2l ltnNge leqn0 normGI_eq0 nZq; case/andP: Pp.
congr (_.+1); apply: IH.
- by rewrite -ltnS (leq_trans F).
- by rewrite -ltnS (leq_trans F).
by rewrite Hq divGIKl.
Qed.

Lemma logGIE p x :
  logGI p x = if [&& primeGI p, x != 0 & p %| x] then (logGI p (x %/ p)).+1 else 0%N.
Proof.
rewrite /logGI.
have [Pp|//] := boolP (primeGI p).
rewrite -normGI_eq0.
case E : ('N x) => /= [|k].
  by rewrite if_same.
have [/dvdGIP[q Hq]|//] := boolP (_ %| _).
have nZx : x != 0 by rewrite -normGI_eq0 E.
have nZp : p != 0.
  by apply: contra nZx => /eqP HH; rewrite Hq HH mulr0.
have nZq : q != 0.
  by apply: contra nZx => /eqP HH; rewrite Hq HH mul0r.
congr (_).+1.
apply: logGI_recE => //.
  rewrite -ltnS -E Hq divGIKl // normGIM -{1}['N q]muln1.
  by rewrite ltn_mul2l ltnNge leqn0 normGI_eq0 nZq; case/andP: Pp.
by rewrite Hq divGIKl.
Qed.

Lemma logGI_gt0 p x : (0 < logGI p x)%N = (p \in primesGI x).
Proof. by rewrite logGIE -mem_primesGI; case: (p \in _). Qed.

Lemma ltn_log0 p x : ('N x < 'N p)%N -> logGI p x = 0%N.
Proof.
rewrite logGIE ltnNge.
have [|nZx] := boolP (x == 0); first by rewrite andbF.
by have [/(dvdGI_leq nZx)->|] /= := boolP (p %| x); last by rewrite andbF.
Qed.

Lemma logGI0 p : logGI p 0 = 0%N.
Proof. by rewrite /logGI normGI0 /= !if_same. Qed.

Lemma logGI1 p : logGI p 1 = 0%N.
Proof. 
rewrite logGIE dvdGI1 /primeGI ltnNge leq_eqVlt negb_or.
by case: ('N p == 1%N); rewrite ?andbF.
Qed.

Lemma pfactor_dvdGI p (n : nat) (x : GI) : primeGI p -> x != 0 -> (p ^+ n %| x) = (n <= logGI p x)%N.
Proof.
move=> Pp; elim: n x => [|n IHn] x nZx; first  by rewrite dvd1GI.
rewrite logGIE Pp nZx.
have [/dvdGIP[q Hq]/=|nD] := boolP (p %| x); last first.
  apply/dvdGIP=> [] [/= q qE].
  by case/negP: nD; rewrite qE exprS mulrCA dvdGI_mulr // dvdGIxx.
have nZp : p != 0.
  by apply: contra nZx => /eqP HH; rewrite Hq HH mulr0.
have nZq : q != 0.
  by apply: contra nZx => /eqP HH; rewrite Hq HH mul0r.
by rewrite Hq exprSr dvdGI_mul2r // divGIKl // IHn.
Qed.

Definition coprimeGI (x y : GI) := 'N(gcdGI x y) == 1%N.

Lemma coprimeGI1 x : coprimeGI x 1.
Proof. by rewrite /coprimeGI gcdGI1 normGI1. Qed.


Lemma coprime1GI x : coprimeGI 1 x.
Proof.
rewrite /coprimeGI gcd1GIE.
by have [//|] := boolP ('N x == 1%N); rewrite normGI1.
Qed.

Lemma coprimeGIE x y : coprimeGI x y = (gcdGI x y %= 1).
Proof. by rewrite /coprimeGI /eqGI dvdGI1 dvd1GI andbT. Qed.

Lemma coprimeGI_sym: commutative coprimeGI.
Proof.
move=> x y.
by rewrite !coprimeGIE; apply/idP/idP=> /(eqGI_trans _)->//; exact: gcdGIC.
Qed.

Lemma Gauss_dvdGI (x y z : GI) : coprimeGI x y -> (x * y %| z) = (x %| z) && (y %| z).
Proof.
have [/eqP-> _|nZx] := boolP (x == 0).
  by rewrite mul0r dvd0GI; case: eqP => //->; rewrite dvdGI0.
have [/eqP-> _|nZy] := boolP (y == 0).
  by rewrite mulr0 dvd0GI andbC; case: eqP => //->; rewrite dvdGI0.
rewrite coprimeGIE.
have /eqGI_mul2l<-: lcmGI x y != 0 by rewrite lcmGI_eq0 negb_or nZx.
rewrite mulr1 mulGI_lcm_gcd => /eqGI_dvdl->.
by rewrite dvdGI_lcm.
Qed.

Lemma coprimeGI_nat m n :
  coprime m n -> coprimeGI (m%:R) (n%:R).
Proof.
move=> Cmn.
rewrite coprimeGIE /eqGI dvd1GI andbT dvdGI1 -dvdn1.
have/eqP<-: coprime (m ^ 2) (n ^ 2).
  by rewrite coprime_expl // coprime_expr.
by rewrite dvdn_gcd -!normGI_nat !dvdGI_norm // ?(dvdGI_gcdr,dvdGI_gcdl).
Qed.

Lemma Gauss_dvdGIr (x y z : GI) :
   coprimeGI x y -> (x %| y * z) = (x %| z).
Proof.
have [/eqP->|/dvdGI_mul2r H Cxy] := boolP (y == 0). 
 rewrite /coprimeGI gcdGI0 mul0r dvdGI0 normGI_unit => H.
 apply/sym_equal/idP/dvdGIP; exists (z * x^-1).
 by rewrite -mulrA mulVr // mulr1.
rewrite -[in RHS]H Gauss_dvdGI // mulrC.
by rewrite [y %|_]dvdGI_mull ?dvdGIxx // andbT.
Qed.

Lemma Gauss_dvdGIl (x y z : GI) :
   coprimeGI x y -> (x %| z * y) = (x %| z).
Proof. by rewrite mulrC; exact: Gauss_dvdGIr. Qed.

Lemma coprimeGI_dvdl x y z : x %| y ->  coprimeGI y z -> coprimeGI x z.
Proof.
move=> /dvdGIP[q ->].
rewrite !coprimeGIE  egcdGIP => /eqGI_dvdr H.
by rewrite /eqGI dvd1GI andbT -H mulrA dvdGI_add // !dvdGI_mull ?(dvdGI_gcdl, dvdGI_gcdr).
Qed.

Lemma coprimeGI_dvdr x y z : x %| y ->  coprimeGI z y -> coprimeGI z x.
Proof.
move=> /dvdGIP[q ->].
rewrite !coprimeGIE  egcdGIP => /eqGI_dvdr H.
by rewrite /eqGI dvd1GI andbT -H mulrA dvdGI_add // !dvdGI_mull ?(dvdGI_gcdl, dvdGI_gcdr).
Qed.

Lemma Gauss_gcdGIr (x y z : GI) :
   coprimeGI z x -> gcdGI z (x * y) %= gcdGI z y.
Proof.
move=> Cxy; rewrite /eqGI !dvdGI_gcd dvdGI_mull ?(dvdGI_gcdl, dvdGI_gcdr) //.
by rewrite -(@Gauss_dvdGIr _ x) ?dvdGI_gcdr // (coprimeGI_dvdl _ Cxy) // dvdGI_gcdl.
Qed.

Lemma Gauss_gcdGIl x y z :
   coprimeGI z y -> gcdGI z (x * y) %= gcdGI z x.
Proof. by move=> u; rewrite mulrC; exact: Gauss_gcdGIr. Qed.

Lemma coprimeGI_mulr (x y z : GI) :
  coprimeGI x (y * z) = coprimeGI x y && coprimeGI x z.
Proof.
have [H|/= H] := boolP (coprimeGI x y).
  by rewrite !coprimeGIE /eqGI !dvd1GI !andbT (eqGI_dvdl _ (Gauss_gcdGIr _ _)).
apply/idP=> H1; case/negP: H; apply: coprimeGI_dvdr H1.
by apply: dvdGI_mulr (dvdGIxx _).
Qed.

Lemma coprimeGI_mull (x y z : GI) :
  coprimeGI (y * z) x = coprimeGI y x && coprimeGI z x.
Proof. by rewrite ![coprimeGI _ x]coprimeGI_sym -coprimeGI_mulr. Qed.

Lemma primeGI_neq0 p : primeGI p -> p != 0.
Proof. by case/primeGIP; case: eqP => //->; rewrite normGI0. Qed.

Lemma coprimeGI_pexpl k (x y : GI) : 
  (0 < k)%N -> coprimeGI (x ^+ k) y = coprimeGI x y.
Proof.
case: k => // k _; elim: k => [|k IHk]; first by rewrite expr1.
by rewrite exprS coprimeGI_mull -IHk andbb.
Qed.

Lemma coprimeGI_pexpr k (x y : GI) : 
  (0 < k)%N -> coprimeGI x (y ^+ k) = coprimeGI x y.
Proof. by move=> nZk; rewrite !(coprimeGI_sym x) coprimeGI_pexpl. Qed.

Lemma coprimeGI_expl k (x y : GI) : coprimeGI x y -> coprimeGI (x ^+ k) y.
Proof.
by case: k => [|k] Cxy; rewrite ?coprime1GI // coprimeGI_pexpl.
Qed.

Lemma coprimeGI_expr k x y : coprimeGI x y -> coprimeGI x (y ^+ k).
Proof. rewrite !(coprimeGI_sym x); exact: coprimeGI_expl. Qed.

Lemma primeGI_dvd p x : primeGI p -> (x %| p) = (x %= 1) || (x %= p).
Proof.
move=> Pp.
apply/idP/orP=> [xDp|[|]/eqGI_dvdl->]; rewrite ?dvdGIxx ?dvd1GI //.
have nZp := primeGI_neq0 Pp.
have := dvdGI_leq nZp xDp.
rewrite leq_eqVlt => /orP[]; last first.
  case/primeGIP: Pp => _ HH /HH /(_ xDp) /eqP.
  by rewrite -dvdGI1 /eqGI dvd1GI => ->; left.
case/dvdGIP: xDp => q ->.
rewrite /eqGI dvdGI_mull ?dvdGIxx // normGIM.
have [/eqP->|nZx]:= boolP (x == 0).
  by rewrite mulr0 dvdGIxx; right.
rewrite -{1}['N x]mul1n eqn_mul2r normGI_eq0 (negPf nZx) eq_sym /=.
rewrite normGI_unit => HH; right.
by apply/dvdGIP; exists q^-1; rewrite mulrA mulVr // mul1r.
Qed.

Lemma primeGI_coprime p x : primeGI p -> coprimeGI p x = ~~ (p %| x).
Proof.
move=> Pp.
have nZp := primeGI_neq0 Pp.
have Np_neq1 : ('N p == 1)%N = false.
  by case/primeGIP: Pp; case: ('N _) =>  // [[]].
have: gcdGI p x %| p by exact: dvdGI_gcdl.
rewrite primeGI_dvd // => /orP[H|].
  rewrite coprimeGIE H; apply/sym_equal/negP => H1.
  have: p %|gcdGI p x by rewrite dvdGI_gcd dvdGIxx H1.
  by rewrite (eqGI_dvdr _ H) dvdGI1 Np_neq1.
rewrite eqGI_sym => H.
rewrite (eqGI_dvdl _ H) dvdGI_gcdr /= coprimeGIE.
apply/negP => /(eqGI_trans H).
by rewrite /eqGI dvd1GI dvdGI1 Np_neq1.
Qed.

Lemma pfactor_coprimeGI (p x : GI) :
  primeGI p -> x != 0 -> {y | coprimeGI p y & x = y * p ^+ logGI p x}.
Proof.
move=> Pp nZx; set k := logGI p x.
have Dk : p ^+ k %| x by rewrite pfactor_dvdGI.
exists (x %/ p ^+ k); last by rewrite divGIK.
rewrite primeGI_coprime // -(@dvdGI_mul2r (p ^+ k)); last first.
  by apply: expf_neq0 (primeGI_neq0 Pp).
by rewrite -exprS divGIK // pfactor_dvdGI // ltnn.
Qed.

Lemma dvdGI_leq_log (x y z : GI) : 
  z != 0 -> y %| z -> (logGI x y <= logGI x z)%N.
Proof.
move=> nZz yDz.
have [/eqP Zy|nZy] := boolP (y == 0).
  by move: yDz; rewrite Zy dvd0GI (negPf nZz).
have [Px|nPx] := boolP (primeGI x); last first.
  by rewrite /logGI (negPf nPx).
by rewrite -pfactor_dvdGI // (dvdGI_trans _ yDz) // pfactor_dvdGI.
Qed.

Lemma pfactorGIK p n : primeGI p -> logGI p (p ^+ n) = n.
Proof.
move=> Pp.
have nZpn : p ^+ n != 0 by apply: expf_neq0 (primeGI_neq0 _).
have [y Cyp pnE]:= pfactor_coprimeGI Pp nZpn.
have yDpn : y %| p ^+ n by rewrite pnE dvdGI_mulr ?dvdGIxx.
suff: y %= 1.
  rewrite /eqGI dvd1GI dvdGI1 andbT => /eqP Ny.
  have /eqP := congr1 normGI pnE; rewrite normGIM Ny mul1n.
  rewrite !normGIX eqn_exp2l; last by case/primeGIP: Pp.
  by move/eqP<-.
elim: (n) yDpn => [|n1 IH]; first by rewrite expr0 /eqGI dvd1GI andbT.
by rewrite exprS Gauss_dvdGIr // coprimeGI_sym.
Qed.

Lemma pdivGI_pfactor p k : primeGI p -> pdivGI (p ^+ k.+1) %= p.
Proof. 
move=> Pp.
have nZpn : p ^+ k.+1 != 0 by apply: expf_neq0 (primeGI_neq0 _).
have: p \in primesGI (p ^+ k.+1).
  rewrite mem_primesGI Pp nZpn.
  by apply/dvdGIP; exists (p ^+ k); rewrite -exprSr.
rewrite /pdivGI.
case: primesGI (fun x => mem_primesGI x (p ^+ k.+1)) => /= [|a l /(_ a)].
  by rewrite in_nil.
rewrite in_cons eqxx => /= /(@sym_equal _ _ _) /and3P[Pa _ aDp] _.
have [Cap|NCap]:= boolP (coprimeGI a p).
  elim: (k) aDp => [|k1 IHk1].
    by move: Cap; rewrite expr1 primeGI_coprime=> // /negP.
  by rewrite exprS Gauss_dvdGIr.
have : ~~ coprimeGI p a.
   by apply: contra NCap; rewrite coprimeGI_sym.
by move: NCap; rewrite /eqGI !primeGI_coprime // !negbK => ->.
Qed.

Lemma logGI_Gauss x y z : 
   coprimeGI x y -> logGI x (y * z) = logGI x z.
Proof.
move=> Cxy; have [Pp|PnP] := boolP (primeGI x); last first.
  by rewrite /logGI (negPf PnP).
have [/eqP-> | nZz] := boolP (z == 0); first by rewrite mulr0.
have [/eqP Zy | nZy] := boolP (y == 0).
  by move: Cxy; rewrite Zy primeGI_coprime // dvdGI0.
have nZyz: y * z != 0 by  rewrite mulf_eq0 (negPf nZy) (negPf nZz).
apply/eqP; rewrite eqn_leq andbC dvdGI_leq_log ?dvdGI_mull ?dvdGIxx //.
set k := logGI x _; have: x ^+ k %| y * z by rewrite pfactor_dvdGI.
by rewrite Gauss_dvdGIr ?coprimeGI_expl // -pfactor_dvdGI.
Qed.

Lemma logGIM x y z : 
  y != 0 -> z != 0 -> logGI x (y * z) = (logGI x y + logGI x z)%N.
Proof.
move=> nZy nZz.
have [Pp|/negPf PnP] := boolP (primeGI x); last by rewrite /logGI PnP.
have xlp := pfactor_coprimeGI Pp.
case/xlp : nZy => y1 Cxy1 yE.
case/xlp : nZz => z1 Cxz1 zE.
by rewrite {1}yE {1}zE mulrCA -mulrA -exprD !logGI_Gauss // pfactorGIK.
Qed.

Lemma logGIX p x n : logGI p (x ^+ n) = (n * logGI p x)%N.
Proof.
have [Pp|/negPf PnP] := boolP (primeGI p); last by rewrite /logGI PnP.
elim: n => [|n IHn]; first by rewrite logGI1.
have [/eqP->|nZx] := boolP (x == 0); first by rewrite expr0n logGI0 muln0.
by rewrite exprS logGIM  ?IHn // expf_eq0 // negb_and nZx orbT.
Qed.

Lemma gcdGI_mull_equiv (m n p q : GI) :
  coprimeGI m n -> m * n  = p * q -> m %= gcdGI m p * gcdGI m q.
Proof.
elim: {m}_.+1 {-2}m (ltnSn ('N m)) p q => // k IH m.
case: (leqP ('N m) 1%N).
  rewrite leq_eqVlt ltnS leqn0 normGI_eq0 => /orP[|/eqP-> _ p q _]; last first.
    by rewrite mul0r !gcd0GI=> <-; exact: eqGIxx.
  move=> H _ p q _ _.
  have G : m %= 1 by rewrite /eqGI dvd1GI dvdGI1 H.
  have G1 :  gcdGI m p %= 1.
    by rewrite (eqGI_trans (gcdGIC _ _)) // -(gcdGI1 p) eqGI_gcdr.
  have G2 : gcdGI m q %= 1.
    by rewrite (eqGI_trans (gcdGIC _ _)) // -(gcdGI1 q) eqGI_gcdr.
  apply: eqGI_trans (G) _; rewrite eqGI_sym.
  rewrite (eqGI_trans _ G1) // -[X in _ %= X]mulr1 eqGI_mul2l //.
  by apply/eqP=> HH; move/eqGI_norm : G1; rewrite normGI1 HH normGI0.
have [/eqP-> Nx _ p q|nZn] := boolP (n == 0).
  by rewrite /coprimeGI gcdGI0; case: ('N _) Nx => // [[]].
move=> OLNm MnL1 p q Cmn.
have nZm : m != 0 by rewrite -normGI_eq0; case: ('N _) OLNm.
have [/eqP->/eqP|nZp] := boolP (p == 0).
  by rewrite mul0r mulf_eq0 (negPf nZm) (negPf nZn).
have [/eqP->/eqP|nZq] := boolP (q == 0).
  by rewrite mulr0 mulf_eq0 (negPf nZm) (negPf nZn).
pose v := pdivGI m.
have Pv : primeGI v := pdivGI_prime OLNm.
move=> mnE.
have logE : logGI v m = (logGI v p + logGI v q)%N.
  rewrite -logGIM // -mnE mulrC logGI_Gauss //.
  by rewrite coprimeGI_sym (coprimeGI_dvdr (pdivGI_dvd _)) // coprimeGI_sym.
move: mnE MnL1.
have [p1 Cp1dm1 ->] := pfactor_coprimeGI Pv nZp.
have [q1 Cq1dm1 ->] := pfactor_coprimeGI Pv nZq.
rewrite mulrAC !mulrA -mulrA -exprD addnC.
move/eqP; move: OLNm Cmn.
have [m1 Cpdm1 -> OLNm Cmn] :=  pfactor_coprimeGI Pv nZm.
rewrite -logE [_ * n]mulrAC -subr_eq0 -mulrBl mulf_eq0 subr_eq0.
rewrite expf_eq0 (negPf (primeGI_neq0 Pv)) andbF orbF => /eqP mnE mL.
rewrite logE !exprD  {2}[_ ^+ _ * _]mulrC !mulrA.
set u1 := _ ^+ _; set u2 := _ ^+ _.
have F1 : m1 %= gcdGI m1 p1 * gcdGI m1 q1.
  apply: IH => //; last first.
    by move: Cmn; rewrite coprimeGI_mull => /andP[].
  rewrite -ltnS (leq_trans _ mL) // ltnS normGIM normGIX.
  rewrite -{1}['N m1]muln1 ltn_mul2l -{2}(expn0 ('N v)) ltn_exp2l //.
    rewrite logGI_gt0 mem_primesGI Pv nZm pdivGI_dvd.
    by move: OLNm; rewrite normGIM; case: ('N _).
  by case/primeGIP: Pv.
have F2 : gcdGI (m1 * u2) p1 %= gcdGI m1 p1.
  apply: eqGI_trans (gcdGIC _ _) _.
  apply: eqGI_trans (Gauss_gcdGIl _ _) _ => //.
    by rewrite coprimeGI_expr // coprimeGI_sym.
  by apply: gcdGIC.
have F3 : gcdGI (m1 * u1) q1 %= gcdGI m1 q1.
  apply: eqGI_trans (gcdGIC _ _) _.
  apply: eqGI_trans (Gauss_gcdGIl _ _) _ => //.
    by rewrite coprimeGI_expr  // coprimeGI_sym.
  by apply: gcdGIC.
rewrite -mulrA.
apply: eqGI_trans (eqGI_mul F1 (eqGIxx _)) _.
rewrite mulrCA !mulrA [u1 * _]mulrC -mulrA.
apply: eqGI_mul.
  rewrite eqGI_sym.
  apply: eqGI_trans (eqGI_mul F2 (eqGIxx _)).
  by rewrite eqGI_sym mulGI_gcdl.
rewrite eqGI_sym.
apply: eqGI_trans (eqGI_mul F3 (eqGIxx _)).
by rewrite eqGI_sym mulGI_gcdl.
Qed.


End GaussIntegers.

Delimit Scope GI_scope with GI.

Notation "'N x" := (normGI x%R) (at level 10) : GI_scope.
Notation " x %| y " := (dvdGI x y) : GI_scope.
Notation " x %/ y " := (divGI x y) : GI_scope.
Notation " x %% y " := (modGI x y) : GI_scope.
Notation " x %= y " := (eqGI x y) : GI_scope.



(* End of exercices *)

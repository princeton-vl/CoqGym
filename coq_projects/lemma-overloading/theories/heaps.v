(*
    Copyright (C) 2012  G. Gonthier, B. Ziliani, A. Nanevski, D. Dreyer

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

From mathcomp
Require Import ssreflect ssrfun ssrnat div ssrbool seq.
From LemmaOverloading
Require Import prelude finmap ordtype.
From mathcomp
Require Import path eqtype.
Require Import Eqdep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* uncomment for ssreflect trunk *)
Notation eqn_addl := eqn_add2l.
Notation modn_addl := modnDl.
Notation modn_mulr := modnMr.
Notation modn_add2m := modnDm.
Notation modn_addr := modnDr.


(*************)
(* Locations *)
(*************)

Inductive ptr := ptr_nat of nat.

Definition null := ptr_nat 0.

Definition nat_ptr (x : ptr) := let: ptr_nat y := x in y.

Definition eq_ptr (x y : ptr) :=
  match x, y with ptr_nat m, ptr_nat n => m == n end.

Lemma eq_ptrP : Equality.axiom eq_ptr.
Proof. by case=>x [y] /=; case: eqP=>[->|*]; constructor=>//; case. Qed.

Definition ptr_eqMixin := EqMixin eq_ptrP.
Canonical Structure ptr_eqType := EqType ptr ptr_eqMixin.

(* some pointer arithmetic: offsetting from a base *)

Definition ptr_offset x i := ptr_nat (nat_ptr x + i).

Notation "x .+ i" := (ptr_offset x i)
  (at level 3, format "x .+ i").

Lemma ptrE x y : (x == y) = (nat_ptr x == nat_ptr y).
Proof. by move: x y=>[x][y]. Qed.

Lemma ptr0 x : x.+0 = x.
Proof. by case: x=>x; rewrite /ptr_offset addn0. Qed.

Lemma ptrA x i j : x.+i.+j = x.+(i+j).
Proof. by case: x=>x; rewrite /ptr_offset addnA. Qed.

Lemma ptrK x i j : (x.+i == x.+j) = (i == j).
Proof.
by case: x=>x; rewrite ptrE eqn_addl.
Qed.

Lemma ptr_null x m : (x.+m == null) = (x == null) && (m == 0).
Proof. by case: x=>x; rewrite !ptrE addn_eq0. Qed.

Lemma ptrT x y : {m : nat | (x == y.+m) || (y == x.+m)}.
Proof.
case: x y=>x [y]; exists (if x <= y then (y - x) else (x - y)).
rewrite !ptrE leq_eqVlt /=.
by case: (ltngtP x y)=>/= E; rewrite subnKC ?(ltnW E) ?eq_refl ?orbT // E.
Qed.

Definition ltn_ptr (x y : ptr) :=
  match x, y with ptr_nat m, ptr_nat n => m < n end.

Lemma ltn_ptr_irr : irreflexive ltn_ptr.
Proof. by case=>x /=; rewrite ltnn. Qed.

Lemma ltn_ptr_trans : transitive ltn_ptr.
Proof. by case=>x [y][z]; apply: ltn_trans. Qed.

Lemma ltn_ptr_total : forall x y : ptr, [|| ltn_ptr x y, x == y | ltn_ptr y x].
Proof. by case=>x [y]; rewrite ptrE /=; case: ltngtP. Qed.

Definition ptr_ordMixin := OrdMixin ltn_ptr_irr ltn_ptr_trans ltn_ptr_total.
Canonical Structure ptr_ordType := OrdType ptr ptr_ordMixin.

(*********)
(* Heaps *)
(*********)

Inductive heap :=
  Undef | Def (finmap : {finMap ptr -> dynamic}) of
               null \notin supp finmap.

Section NullLemmas.
Variables (f g : {finMap ptr -> dynamic}) (x : ptr) (d : dynamic).

Lemma upd_nullP :
        x != null -> null \notin supp f -> null \notin supp (ins x d f).
Proof. by move=>H1 H2; rewrite supp_ins negb_or /= eq_sym H1. Qed.

Lemma free_nullP : null \notin supp f -> null \notin supp (rem x f).
Proof. by move=>H; rewrite supp_rem negb_and /= H orbT. Qed.

Lemma un_nullP :
        null \notin supp f -> null \notin supp g ->
          null \notin supp (fcat f g).
Proof. by move=>H1 H2; rewrite supp_fcat negb_or H1 H2. Qed.

Lemma heapE pf pg : f = g <-> @Def f pf = @Def g pg.
Proof.
split=>[E|[//]]; move: pf pg.
by rewrite E=>pf pg; congr Def; apply: bool_irrelevance.
Qed.

End NullLemmas.

(****************)
(* main methods *)
(****************)

Definition def h := if h is Def _ _ then true else false.

Definition empty := @Def (finmap.nil _ _) is_true_true.

Definition upd h x d := nosimpl
  (if h is Def hs ns then
    if decP (@idP (x != null)) is left pf then
      Def (@upd_nullP _ _ d pf ns)
    else Undef
  else Undef).

Definition dom h : pred ptr := nosimpl
  (if h is Def f _ then mem (supp f) else pred0).

Definition free x h : heap :=
  (if h is Def hs ns then Def (free_nullP x ns) else Undef).

Definition look (x : ptr) h :=
  (if h is Def hs _ then
    if fnd x hs is Some d then d else dyn tt
  else dyn tt).

Definition union2 h1 h2 := nosimpl
  (if (h1, h2) is (Def hs1 ns1, Def hs2 ns2) then
     if disj hs1 hs2 then
        Def (@un_nullP _ _ ns1 ns2)
     else Undef
  else Undef).

Definition empb h :=
  if h is Def hs _ then supp hs == [::] else false.

Definition fresh h :=
  (if h is Def hs _ then last null (supp hs) else null) .+ 1.

Definition subdom h1 h2 :=
  if (h1, h2) is (Def hs1 _, Def hs2 _) then
    all (fun x => x \in supp hs2) (supp hs1)
  else false.

Definition subheap h1 h2 :=
  subdom h1 h2 /\ forall x, x \in dom h1 -> look x h1 = look x h2.

(* Definition subheap h1 h2 p :=  *)
(*   if (h1, h2) is (Def hs1 _, Def hs2 _) then  *)
(*     all (fun x => p (look x h1) (look x h2)) (supp hs1) *)
(*   else false. *)

Definition subtract h1 h2 :=
  if h1 is (Def hs1 _) then
    foldl (fun h x => free x h) h2 (supp hs1)
  else Undef.

Definition pick h :=
  if h is Def hs _ then head null (supp hs) else null.

Definition pts A (x : ptr) (v : A) := upd empty x (dyn v).

Notation "h1 :+ h2" := (union2 h1 h2) (at level 43, left associativity).
Notation "h2 :- h1" := (subtract h1 h2) (at level 43, left associativity).
Notation "x :-> v" := (pts x v) (at level 30).

(***********************)
(* monoidal properties *)
(***********************)

Lemma unC : forall h1 h2, h1 :+ h2 = h2 :+ h1.
Proof.
case=>[|h1 H1]; case=>[|h2 H2] //; rewrite /union2.
by case: ifP=>E; rewrite disjC E // -heapE fcatC.
Qed.

Lemma unA : forall h1 h2 h3, h1 :+ (h2 :+ h3) = h1 :+ h2 :+ h3.
Proof.
case=>[|h1 H1]; case=>[|h2 H2]; case=>[|h3 H3] //; rewrite /union2;
case: ifP=>//; case: ifP=>//; last first.
- by move=>E1 E2; rewrite disjC disj_fcat andbC disjC E2.
- by case: ifP=>E1 //; rewrite disj_fcat E1 /= -!(disjC h3) disj_fcat=>->->.
rewrite disj_fcat; case/andP=>->.
rewrite -!(disjC h3) disj_fcat=>E2 E3.
by rewrite E2 E3 -heapE fcatA // disjC.
Qed.

Lemma unCA h1 h2 h3 : h1 :+ (h2 :+ h3) = h2 :+ (h1 :+ h3).
Proof. by rewrite unC (unC h1) unA. Qed.

Lemma unAC h1 h2 h3 : h1 :+ h2 :+ h3 = h1 :+ h3 :+ h2.
Proof. by rewrite (unC h1) -unA unC. Qed.

Lemma un0h h : empty :+ h = h.
Proof. by case: h=>[|h H] //; apply/heapE; rewrite fcat0s. Qed.

Lemma unh0 h : h :+ empty = h.
Proof. by rewrite unC un0h. Qed.

(* cancelativity *)

Lemma unKhl h h1 h2 : def (h1 :+ h) -> h1 :+ h = h2 :+ h -> h1 = h2.
Proof.
case: h h1 h2=>[|h H]; case=>[|h1 H1]; case=>[|h2 H2] //=; rewrite /union2;
case: ifP=>//; case: ifP=>// D1 D2 _ [E]; apply/heapE.
by apply: fcatsK E; rewrite D1 D2.
Qed.

Lemma unhKl h h1 h2 : def (h :+ h1) -> h :+ h1 = h :+ h2 -> h1 = h2.
Proof. by rewrite !(unC h); apply: unKhl. Qed.

Lemma unKhr h h1 h2 : def (h2 :+ h) -> h1 :+ h = h2 :+ h -> h1 = h2.
Proof. by move=>H1 H2; symmetry in H2; rewrite (unKhl H1 H2). Qed.

Lemma unhKr h h1 h2 : def (h :+ h2) -> h :+ h1 = h :+ h2 -> h1 = h2.
Proof. by rewrite !(unC h); apply: unKhr. Qed.

(*******)
(* dom *)
(*******)

Lemma dom0 : dom empty = pred0.
Proof. by []. Qed.

Lemma domU h y d :
        dom (upd h y d) =i
        [pred x | (y != null) && if x == y then def h else x \in dom h].
Proof.
case: h=>[|h T] /= x; rewrite inE /upd /=.
- rewrite ?inE. case: ifP=>//; rewrite andbF; reflexivity.
case: ifP=>E; case: decP=>H1; rewrite /dom /=.
- by rewrite (eqP E) H1 supp_ins inE /= eq_refl.
- by case: eqP H1.
- by rewrite supp_ins inE /= E H1.
by case: eqP H1.
Qed.

Lemma domPt A x (v : A) : dom (x :-> v) =i [pred y | (x == y) && (x != null)].
Proof.
move=>y; rewrite domU dom0 !inE /=.
by case: ifP=>E; rewrite -(eq_sym y) E andbC.
Qed.

Lemma domF h x :
        dom (free x h) =i [pred y | if x == y then false else y \in dom h].
Proof.
case: h=>[|h H] y /=; rewrite ?inE /=; case: ifP=>// E;
by rewrite supp_rem inE /= eq_sym E.
Qed.

Lemma domUn h1 h2 :
        dom (h1 :+ h2) =i
        [pred x | def (h1 :+ h2) && (x \in [predU dom h1 & dom h2])].
Proof.
case: h1 h2 =>[|h1 H1] // [|h2 H2] // x; rewrite /dom /union2.
by case: ifP=>// E; rewrite supp_fcat.
Qed.

Lemma dom_null h x : x \in dom h -> x != null.
Proof. by case: h=>[|h H1] //; case: eqP=>// ->; rewrite (negbTE H1). Qed.

Lemma dom_def h x : x \in dom h -> def h.
Proof. by case: h. Qed.

Lemma dom_free h x : x \notin dom h -> free x h = h.
Proof. by case: h=>[|h H] // E; apply/heapE; apply: rem_supp. Qed.

Lemma dom_look h x : x \notin dom h -> look x h = dyn tt.
Proof.
by case: h=>[|h H] //; rewrite /look /dom -topredE /=; case: (suppP x)=>// ->.
Qed.

(*******)
(* def *)
(*******)

Lemma def0 : def empty.
Proof. by []. Qed.

Hint Resolve def0 : core.

Lemma defU h x d : def (upd h x d) = (x != null) && (def h).
Proof.
case: h=>[|h H] /=; first by rewrite andbF.
by rewrite /upd; case: decP=>/= [->//|]; case: eqP.
Qed.

Lemma defPt A x (v : A) : def (x :-> v) = (x != null).
Proof. by rewrite defU andbT. Qed.

Lemma defF h x : def (free x h) = def h.
Proof. by case: h. Qed.

CoInductive defUn_spec h1 h2 : bool -> Type :=
| def_false1 of ~~ def h1 : defUn_spec h1 h2 false
| def_false2 of ~~ def h2 : defUn_spec h1 h2 false
| def_false3 x of x \in dom h1 & x \in dom h2 : defUn_spec h1 h2 false
| def_true of def h1 & def h2 &
    (forall x, x \in dom h1 -> x \notin dom h2) : defUn_spec h1 h2 true.

Lemma defUn : forall h1 h2, defUn_spec h1 h2 (def (h1 :+ h2)).
Proof.
case=>[|h1 H1][|h2 H2] /=; try by [apply: def_false1 | apply: def_false2].
rewrite /union2; case: ifP=>E.
- by apply: def_true=>// x H; case: disjP E=>//; move/( _ _ H).
by case: disjP E=>// x T1 T2 _; apply: (def_false3 (x:=x)).
Qed.

Lemma defUnl h1 h2 : def (h1 :+ h2) -> def h1.
Proof. by case: h1. Qed.

Lemma defUnr h1 h2 : def (h1 :+ h2) -> def h2.
Proof. by case: h1=>h1 // H; case: h2. Qed.

Lemma defFUn h1 h2 x : def (h1 :+ h2) -> def (free x h1 :+ h2).
Proof.
case: defUn=>// H1 H2 H _.
case: defUn=>//; [by rewrite defF H1|by rewrite H2|].
move=>k; rewrite domF inE /=.
by case: ifP=>_ //; move/H; move/negbTE=>->.
Qed.

Lemma defUnF h1 h2 x : def (h1 :+ h2) -> def (h1 :+ free x h2).
Proof. by rewrite unC; move/(defFUn x); rewrite unC. Qed.

Lemma undefE x : ~~ def x <-> x = Undef.
Proof. by case: x; split. Qed.

(**********)
(* update *)
(**********)

Lemma upd_inj h x d1 d2 :
        def h -> x != null -> upd h x d1 = upd h x d2 -> d1 = d2.
Proof.
case: h=>[|h H] // _ H1; rewrite /upd; case: decP=>// H2 [E].
have: fnd x (ins x d1 h) = fnd x (ins x d2 h) by rewrite E.
by rewrite !fnd_ins eq_refl; case.
Qed.

Lemma heap_eta h x : x \in dom h -> h = upd (free x h) x (look x h).
Proof.
case: h=>[|h H] //; rewrite /upd /look /dom /free.
case: decP; rewrite -topredE => /= H1 H2; last first.
- by case: eqP H1 H H2=>// -> _ H; rewrite (negbTE H).
apply/heapE; apply: fmapP=>k; rewrite fnd_ins.
case: ifP=>[|E]; last by rewrite fnd_rem E.
move/eqP=>->; case E1: (fnd x h)=>//.
by case: (suppP _ h) H2 E1=>// v ->.
Qed.

Lemma updU h x y d1 d2 :
        upd (upd h x d1) y d2 =
        if x == y then upd h x d2 else upd (upd h y d2) x d1.
Proof.
case: h =>[|h T]; rewrite /upd; case: ifP=>// H;
case: decP=>H1 //; case: decP=>// H2; last 2 first.
- by rewrite -(eqP H) H1 in H2.
- by apply/heapE; rewrite ins_ins eq_sym H.
by apply/heapE; rewrite ins_ins (eqP H) eq_refl.
Qed.

Lemma updF h x y d :
        upd (free x h) y d =
        if x == y then upd h x d else free x (upd h y d).
Proof.
case: h=>[|h H] /=; case: ifP=>E //; rewrite /upd; last first.
- case: decP=>// H1.
  by apply/heapE; rewrite ins_rem eq_sym E.
case: decP=>// H1; case: decP=>// H2.
- by apply/heapE; rewrite ins_rem (eqP E) eq_refl.
- by rewrite (eqP E) H1 in H2.
by rewrite -(eqP E) H2 in H1.
Qed.

Lemma updUnl h1 h2 x d :
        upd (h1 :+ h2) x d =
        if x \in dom h1 then upd h1 x d :+ h2 else h1 :+ upd h2 x d.
Proof.
case: h1 h2=>[|h1 H1][|h2 H2] //; case: ifP=>H //;
rewrite /upd /union2; case: decP=>// H3; case: ifP=>D //.
- rewrite disjC disj_ins disjC D.
  case: disjP D=>//; move/(_ _ H)=>H4 _; rewrite H4.
  by apply/heapE; rewrite fcat_inss.
- by rewrite disjC disj_ins disjC D andbF.
- rewrite disj_ins D H /=; apply/heapE.
  rewrite (@fcatC _ _ h1) // (@fcatC _ _ h1).
  - by rewrite fcat_inss // H.
  by rewrite disj_ins H D.
by rewrite disj_ins D andbF.
Qed.

Lemma updUnr h1 h2 x d :
        upd (h1 :+ h2) x d =
        if x \in dom h2 then h1 :+ upd h2 x d else upd h1 x d :+ h2.
Proof. by rewrite unC updUnl (unC h1) (unC h2). Qed.

Lemma pts_injP A1 A2 x1 x2 (v1 : A1) (v2 : A2) :
        def (x1 :-> v1) -> x1 :-> v1 = x2 :-> v2 -> x1 = x2 /\ A1 = A2.
Proof.
rewrite /pts /upd /=.
by case: decP=>H1; case: decP=>H2 // _; case.
Qed.

Lemma pts_injT A1 A2 x (v1 : A1) (v2 : A2) :
        def (x :-> v1) -> x :-> v1 = x :-> v2 -> A1 = A2.
Proof. by move=>D; case/(pts_injP D). Qed.

Lemma pts_inj A x (v1 v2 : A) :
        def (x :-> v1) -> x :-> v1 = x :-> v2 -> v1 = v2.
Proof.
move=>D; rewrite /pts /upd.
case: decP; last by rewrite -(defPt _ v1) D.
by move=>H []; apply: inj_pairT2.
Qed.

(********)
(* free *)
(********)

Lemma free0 x : free x empty = empty.
Proof. by apply/heapE; rewrite rem_empty. Qed.

Lemma freeU h x y d :
        free x (upd h y d) = if x == y then
          if y == null then Undef else free x h
        else upd (free x h) y d.
Proof.
case: h=>[|h H] /=; first by case: ifP=>// E; case: ifP.
rewrite /upd; case: ifP=>E1; case: decP=>H1 //.
- by rewrite (negbTE H1); apply/heapE; rewrite rem_ins E1.
- by case: ifP H1=>// ->.
by apply/heapE; rewrite rem_ins E1.
Qed.

Lemma freeF h x y :
        free x (free y h) = if x == y then free x h else free y (free x h).
Proof. by case: h=>*; case: ifP=>E //; apply/heapE; rewrite rem_rem E. Qed.

Lemma freeUn h1 h2 x :
        free x (h1 :+ h2) =
        if x \in dom (h1 :+ h2) then free x h1 :+ free x h2
        else h1 :+ h2.
Proof.
case: h1 h2=>[|h1 H1] [|h2 H2] //; rewrite /union2 /free /dom /=.
case: ifP=>E1 //; rewrite supp_fcat inE /=.
case: ifP=>E2; last by apply/heapE; rewrite rem_supp // supp_fcat inE /= E2.
rewrite disj_rem; last by rewrite disjC disj_rem // disjC.
apply/heapE; case/orP: E2=>E2.
- suff E3: x \notin supp h2 by rewrite -fcat_rems // (rem_supp E3).
  by case: disjP E1 E2=>// H _; move/H.
suff E3: x \notin supp h1 by rewrite -fcat_srem // (rem_supp E3).
by case: disjP E1 E2=>// H _; move/contra: (H x); rewrite negbK.
Qed.

Lemma freeUnD h1 h2 x :
        def (h1 :+ h2) -> free x (h1 :+ h2) = free x h1 :+ free x h2.
Proof.
move=>D; rewrite freeUn domUn D !inE /=; case: ifP=>//.
by move/negbT; rewrite negb_or; case/andP=>H1 H2; rewrite !dom_free.
Qed.

Lemma freeUnl h1 h2 x : x \notin dom h1 -> free x (h1 :+ h2) = h1 :+ free x h2.
Proof.
move=>D1; rewrite freeUn domUn !inE (negbTE D1) /=.
case: ifP; first by case/andP; rewrite dom_free.
move/negbT; rewrite negb_and; case/orP=>D2; last by rewrite dom_free.
suff: ~~ def (h1 :+ free x h2).
- by case: (h1 :+ free x h2)=>// _; case: (h1 :+ h2) D2.
apply: contra D2; case: defUn=>// H1 H2 H _.
case: defUn=>//; first by [rewrite H1]; first by move: H2; rewrite defF=>->.
move=>k H3; move: (H _ H3); rewrite domF inE /=.
by case: ifP H3 D1=>[|_ _ _]; [move/eqP=><- -> | move/negbTE=>->].
Qed.

Lemma freeUnr h1 h2 x : x \notin dom h2 -> free x (h1 :+ h2) = free x h1 :+ h2.
Proof. by move=>H; rewrite unC freeUnl // unC. Qed.

(**********)
(* lookup *)
(**********)

Lemma lookU h x y d :
        look x (upd h y d) = if x == y then
          if def h && (y != null) then d else dyn tt
        else if y != null then look x h else dyn tt.
Proof.
case: h=>[|h H] /=; case: ifP=>E //; case: ifP=>H1 //; rewrite /upd;
by case: decP=>// H2; rewrite /look fnd_ins E //; rewrite H1 in H2.
Qed.

Lemma lookF h x y :
        look x (free y h) = if x == y then dyn tt else look x h.
Proof. by case: h=>[|h H]; case: ifP=>E //; rewrite /look /free fnd_rem E. Qed.

Lemma lookUnl h1 h2 x :
        def (h1 :+ h2) ->
        look x (h1 :+ h2) = if x \in dom h1 then look x h1 else look x h2.
Proof.
case: h1 h2=>[|h1 H1] // [|h2 H2] //; rewrite /look /dom /union2.
case: ifP=>D //= _; case: ifP=>E1; last first.
- by rewrite fnd_fcat; case: ifP=>// E2; rewrite fnd_supp ?E1 // fnd_supp ?E2.
suff E2: x \notin supp h2 by rewrite fnd_fcat (negbTE E2).
by case: disjP D E1=>// H _; apply: H.
Qed.

Lemma lookUnr h1 h2 x :
        def (h1 :+ h2) ->
        look x (h1 :+ h2) = if x \in dom h2 then look x h2 else look x h1.
Proof. by rewrite unC=>D; rewrite lookUnl. Qed.

(********)
(* empb *)
(********)

Lemma empP h : reflect (h = empty) (empb h).
Proof.
case: h=>[|h] /=; first by right.
case: eqP=>E H; first by apply: ReflectT; apply/heapE; apply/supp_nilE.
by apply: ReflectF; move/heapE=>S; rewrite S supp_nil in E.
Qed.

Lemma empU h x d : empb (upd h x d) = false.
Proof.
case: h=>[|h H] //; rewrite /upd /empb; case: decP=>// H1.
suff: x \in supp (ins x d h) by case: (supp _).
by rewrite supp_ins inE /= eq_refl.
Qed.

Lemma empPt A x (v : A) : empb (x :-> v) = false.
Proof. by rewrite empU. Qed.

Lemma empUn h1 h2 : empb (h1 :+ h2) = empb h1 && empb h2.
Proof.
case: h1 h2=>[|h1 H1] // [|h2 H2] /=; first by rewrite andbC.
rewrite /empb /union2; case: ifP=>E;
case: eqP=>E1; case: eqP=>E2 //=; last 2 first.
- by move: E2 E1; move/supp_nilE=>->; rewrite fcat0s; case: eqP.
- by move: E1 E2 E; do 2![move/supp_nilE=>->]; case: disjP.
- by move/supp_nilE: E2 E1=>-> <-; rewrite fcat0s eq_refl.
have [k H3]: exists k, k \in supp h1.
- case: (supp h1) {E1 H1 E} E2=>[|x s _] //.
  by exists x; rewrite inE eq_refl.
suff: k \in supp (fcat h1 h2) by rewrite E1.
by rewrite supp_fcat inE /= H3.
Qed.

(* some transformation lemmas *)

Lemma empbE h : h = empty <-> empb h.
Proof. by split=>[-> //|]; case: empP. Qed.

Lemma un0E h1 h2 : h1 :+ h2 = empty <-> h1 = empty /\ h2 = empty.
Proof. by rewrite !empbE empUn; case: andP. Qed.

Lemma defE h : reflect (def h /\ forall x, x \notin dom h)(empb h).
Proof.
case: empP=>T; constructor; first by rewrite T.
case=>D E; case: T; case: h D E=>// f H _; rewrite /dom => E.
apply/heapE; apply/supp_nilE.
by case: (supp f) E=>// x s; move/(_ x); rewrite inE eq_refl.
Qed.

Lemma defUnhh h : def (h :+ h) = empb h.
Proof.
case E: (empb h); first by move/empbE: E=>->.
case: defUn=>// D _ L.
case: defE E=>//; case; split=>// x.
case E: (x \in dom h)=>//.
by move: (L x E); rewrite E.
Qed.

(*********)
(* fresh *)
(*********)

Lemma path_last n s x : path ord x s -> ord x (last x s).+(n+1).
Proof.
move: n s x.
suff L: forall s x, path ord x s -> ord x (last x s).+(1).
- elim=>[|n IH] // s x; move/IH=>E; apply: trans E _.
  by case: (last x s)=>m; rewrite /ord /= addSn (addnS m).
elim=>[|y s IH x] /=; first by case=>x; rewrite /ord /= addn1.
by case/andP=>H1; move/IH; apply: trans H1.
Qed.

Lemma path_filter (A : ordType) (s : seq A) (p : pred A) x :
        path ord x s -> path ord x (filter p s).
Proof.
elim: s x=>[|y s IH] x //=.
case/andP=>H1 H2.
case: ifP=>E; first by rewrite /= H1 IH.
apply: IH; elim: s H2=>[|z s IH] //=.
by case/andP=>H2 H3; rewrite (@trans _ y).
Qed.

Lemma dom_fresh h n : (fresh h).+n \notin dom h.
Proof.
suff L2: forall h x, x \in dom h -> ord x (fresh h).
- by apply: (contra (L2 _ _)); rewrite -leqNgt leq_addr.
case=>[|[s H1]] //; rewrite /supp => /= H2 x.
rewrite /dom /fresh /supp -topredE /=.
elim: s H1 null H2 x=>[|[y d] s IH] //= H1 x.
rewrite inE negb_or; case/andP=>H3 H4 z; rewrite inE.
case/orP; first by move/eqP=>->{z}; apply: (path_last 0).
by apply: IH; [apply: path_sorted H1 | apply: notin_path H1].
Qed.

Lemma fresh_null h : fresh h != null.
Proof. by rewrite -lt0n addn1. Qed.

Opaque fresh.

Hint Resolve dom_fresh fresh_null : core.

(********)
(* pick *)
(********)

Lemma emp_pick h : (pick h == null) = (~~ def h || empb h).
Proof.
case: h=>[|h] //=; case: (supp h)=>[|x xs] //=.
by rewrite inE negb_or eq_sym; case/andP; move/negbTE=>->.
Qed.

Lemma pickP h : def h && ~~ empb h = (pick h \in dom h).
Proof.
by rewrite /dom; case: h=>[|h] //=; case: (supp h)=>// *; rewrite inE eq_refl.
Qed.

(**********)
(* subdom *)
(**********)

Lemma subdom_def h1 h2 : subdom h1 h2 -> def h1 && def h2.
Proof. by case: h1 h2=>[|h1 H1] // [|h2 H2]. Qed.

Lemma subdomP h1 h2 :
        def h1 -> ~~ empb h1 ->
        reflect (forall x, x \in dom h1 -> x \in dom h2)
                (subdom h1 h2).
Proof.
case: h1 h2=>[|h1 H1] // [|h2 H2] //= _ H3; last by apply: allP.
apply: ReflectF.
suff H: head null (supp h1) \in supp h1 by move/(_ _ H).
by case: (supp h1) H1 H3=>[|x xs] //=; rewrite !inE eq_refl.
Qed.

Lemma subdomQ x h1 h2 : subdom h1 h2 -> x \in dom h1 -> x \in dom h2.
Proof.
move=>S H; case: subdomP S=>//.
- by apply: dom_def H.
- by case: empP=>// E; rewrite E dom0 in H.
by move=>H2 _; apply: H2.
Qed.

Lemma subdom_refl h : def h -> subdom h h.
Proof. by case: h=>[//|h H _]; apply/allP. Qed.

Lemma subdomD h1 h2 h : subdom h1 h2 -> def (h2 :+ h) -> def (h1 :+ h).
Proof.
case: h1 h2 h=>[|h1 H1]; case=>[|h2 H2]; case=>[|h H] //=.
rewrite /subdom /def /union2 /=; case: ifP=>E1 //; case: ifP=>E2 // E _.
case: disjP E2=>// x H3 H4 _; case: disjP E1=>// X1 _.
by case: (allP (s := supp h1)) E=>//; move/(_ _ H3); move/X1; rewrite H4.
Qed.

Lemma subdomE h1 h2 h :
        def (h2 :+ h) -> subdom h1 h2 -> subdom (h1 :+ h) (h2 :+ h).
Proof.
case: h1 h2 h=>[|h1 H1]; case=>[|h2 H2]; case=>[|h H] //=.
rewrite /union2 /subdom /def /=; case: ifP=>E1 // _; case: ifP=>E2;
case: (allP (s:=supp h1))=>// E _; last first.
- case: disjP E2=>// x H3 H4; move/E: H3.
  by case: disjP E1=>// X _; move/X; rewrite H4.
case: (allP (s:=supp (fcat h1 h)))=>//; case=>x.
rewrite !supp_fcat !inE /=.
by case/orP; rewrite ?inE; [move/E=>->| move=>->; rewrite orbT].
Qed.

Lemma subdomUE h1 h2 h1' h2' :
        def (h2 :+ h2') -> subdom h1 h2 -> subdom h1' h2' ->
          subdom (h1 :+ h1') (h2 :+ h2').
Proof.
case: h1 h2 h1' h2'=>[|h1 H1]; case=>[|h2 H2];
case=>[|h1' H1']; case=>[|h2' H2'] //.
rewrite /subdom /def /union2.
case: ifP=>E1 // _; case: ifP=>E2 // T1 T2; last first.
- case: disjP E2=>// x; case: allP T1=>// X _; move/X=>{X}.
  case: disjP E1=>// X _; move/X=>{X}.
  by case: allP T2=>// X _ H3 H4; move/X: H4 H3=>->.
case: allP=>//; case=>x.
rewrite !supp_fcat !inE; case/orP=>E.
- by case: allP T1=>//; move/(_ _ E)=>->.
by case: allP T2=>//; move/(_ _ E)=>->; rewrite orbT.
Qed.

Lemma subdom_emp h : def h -> subdom empty h.
Proof. by case: h. Qed.

Lemma subdom_emp_inv h : subdom h empty -> h = empty.
Proof.
case: h=>[|h H] //; rewrite /subdom /=.
case: (allP (s:=supp h))=>// E _; apply/heapE; apply: fmapP=>x.
case: suppP (E x)=>// v E2; move/(_ (erefl _)).
by rewrite supp_nil.
Qed.

Lemma subdomPE A B x (v1 : A) (v2 : B) :
        x != null -> subdom (x :-> v1) (x :-> v2).
Proof.
move=>H; rewrite /subdom /pts /upd /=; case: decP=>//= _.
rewrite (_ : FinMap _ = ins x (dyn v2) (finmap.nil _ _)) //.
by rewrite supp_ins inE /= eq_refl.
Qed.

Lemma subdom_trans h2 h1 h3 : subdom h1 h2 -> subdom h2 h3 -> subdom h1 h3.
Proof.
move=>H1 H2; move: (subdom_def H1) (subdom_def H2).
case/andP=>D1 _; case/andP=>_ D2.
case E: (empb h1).
- by move/empP: E =>->; rewrite subdom_emp.
apply/subdomP=>[//||x in1]; first by apply negbT.
by apply: (subdomQ H2) (subdomQ H1 in1).
Qed.

Hint Resolve subdom_emp subdomPE : core.

(***********)
(* subheap *)
(***********)

Lemma subheap_refl h : def h -> subheap h h.
Proof. by move=>D; split=>//; apply: subdom_refl. Qed.

Lemma subheapE h : def h -> subheap empty h.
Proof. by split; [apply subdom_emp | rewrite dom0]. Qed.

Lemma subheapUn h1 h2 h1' h2' :
        def (h2 :+ h2') -> subheap h1 h2 -> subheap h1' h2' ->
        subheap (h1 :+ h1') (h2 :+ h2').
Proof.
move=>defs [Sd1 Sl1] [Sd2 Sl2].
split=>[|x]; first by apply: subdomUE.
rewrite domUn inE /= inE /=; case/andP=>D; case/orP=>H.
- by rewrite !lookUnl // H Sl1 // (subdomQ Sd1 H).
by rewrite !lookUnr // H Sl2 // (subdomQ Sd2 H).
Qed.

Lemma subheapUnl h1 h2 : def (h1 :+ h2) -> subheap h1 (h1 :+ h2).
Proof.
move=>D; rewrite -{1}[h1]unh0; apply: subheapUn=>//.
- by apply: subheap_refl; apply: defUnl D.
by apply: subheapE; apply: defUnr D.
Qed.

Lemma subheapUnr h1 h2 : def (h1 :+ h2) -> subheap h2 (h1 :+ h2).
Proof. by rewrite unC; apply: subheapUnl. Qed.

Lemma subheap_def h1 h2 : subheap h1 h2 -> def h1 /\ def h2.
Proof. by case=>[subdm _]; move/andP: (subdom_def subdm). Qed.

Lemma subheap_trans h2 h1 h3 : subheap h1 h2 -> subheap h2 h3 -> subheap h1 h3.
Proof.
move=>[S12 E12] [S23 E23].
split=> [|x in1]; first by apply: (subdom_trans S12 S23).
by rewrite (E12 x in1); apply: (E23 x (subdomQ S12 in1)).
Qed.

Lemma subheap_id hp1 hp2: subheap hp1 hp2 -> subheap hp2 hp1 -> hp1 = hp2.
Proof.
move=>S12; move: (S12) => [D12 _].
move/andP: (subdom_def D12) S12=>{D12} [D1 D2].
case: hp1 D1=>[//=|fm1 pf1].
case: hp2 D2=>[//=|fm2 pf2] _ _ [S12 L12] [S21 L21].
rewrite -heapE; apply: fmapP => k.
move: (@subdomQ k _ _ S12) (@subdomQ k _ _ S21) => S'12 S'21.
move: (L12 k) (L21 k).
case H1: (k \in dom (Def pf1)).
- move: (S'12 H1)=> H2.
  case F1: (fnd k fm1)=> [d1|]; case F2: (fnd k fm2)=> [d2|] //=; rewrite F1 F2.
  - by move=>H; rewrite (H is_true_true).
  - by move: (fnd_supp_in H2); rewrite F2=> [[v]].
  - by move: (fnd_supp_in H1); rewrite F1=> [[v]].
case H2 : (k \in dom (Def pf2)).
- by rewrite (S'21 H2) in H1.
move => _ _; rewrite /dom -topredE in H2.
by rewrite (fnd_supp (negbT H1)) (fnd_supp (negbT H2)).
Qed.

(***********************)
(* Some derived lemmas *)
(***********************)

Lemma noalias h1 h2 x1 x2 :
        x1 \in dom h1 -> x2 \in dom h2 -> def (h1 :+ h2) -> x1 != x2.
Proof.
by case: defUn=>// H1 H2 H; move/H; case: eqP=>// ->; move/negbTE=>->.
Qed.

Lemma defPtUn A h x (v : A) :
        def (x :-> v :+ h) = [&& x != null, def h & x \notin dom h].
Proof.
case: defUn; last 1 first.
- by rewrite defPt=>H1 -> H2; rewrite H1 (H2 x) // domPt inE /= eq_refl.
- by rewrite defPt; move/negbTE=>->.
- by move/negbTE=>->; rewrite andbF.
by move=>y; rewrite domPt inE /=; case/andP; move/eqP=><-->->; rewrite andbF.
Qed.

(* the three projections from defPtUn are often useful *)

Lemma defPt_null A h x (v : A) : def (x :-> v :+ h) -> x != null.
Proof. by rewrite defPtUn; case/and3P. Qed.

Lemma defPt_def A h x (v : A) : def (x :-> v :+ h) -> def h.
Proof. by rewrite defPtUn; case/and3P. Qed.

Lemma defPt_dom A h x (v : A) : def (x :-> v :+ h) -> x \notin dom h.
Proof. by rewrite defPtUn; case/and3P. Qed.

(* now dom *)

Lemma domPtUn A h x (v : A) :
        dom (x :-> v :+ h) =i
        [pred y | def (x :-> v :+ h) && ((x == y) || (y \in dom h))].
Proof.
move=>y; rewrite domUn !inE !defPtUn domPt inE /=.
by case: (x =P null)=>//= _; rewrite andbT.
Qed.

(* look and free *)
Lemma lookPtUn A h x (v : A) :
        def (x :-> v :+ h) -> look x (x :-> v :+ h) = dyn v.
Proof.
by move=>D; rewrite lookUnl // lookU domPt !inE eq_refl (defPt_null D).
Qed.

Lemma freePtUn A h x (v : A) :
        def (x :-> v :+ h) -> free x (x :-> v :+ h) = h.
Proof.
move=>D; rewrite freeUnr; last by rewrite (defPt_dom D).
by rewrite freeU eqxx (negbTE (defPt_null D)) free0 un0h.
Qed.

Lemma updPtUn A1 A2 x i (v1 : A1) (v2 : A2) :
        upd (x :-> v1 :+ i) x (dyn v2) = x :-> v2 :+ i.
Proof.
case E1: (def (x :-> v1 :+ i)).
- by rewrite updUnl domPt inE /= eqxx (defPt_null E1) /= updU eqxx.
have E2: def (x :-> v2 :+ i) = false by rewrite !defPtUn in E1 *.
by case: (_ :+ _) E1=>// _; case: (_ :+ _) E2.
Qed.

Lemma heap_etaP h x : x \in dom h -> h = x :-> Dyn.val (look x h) :+ free x h.
Proof.
move=>H; rewrite {1}(heap_eta H) /pts -dyn_eta.
by rewrite -{1}[free x h]un0h updUnr domF inE /= eq_refl.
Qed.

Lemma cancelT A1 A2 h1 h2 x (v1 : A1) (v2 : A2) :
        def (x :-> v1 :+ h1) ->
          x :-> v1 :+ h1 = x :-> v2 :+ h2 -> A1 = A2.
Proof.
move=>D E.
have: look x (x :-> v1 :+ h1) = look x (x :-> v2 :+ h2) by rewrite E.
by rewrite !lookPtUn -?E //; apply: dyn_injT.
Qed.

Lemma cancel A h1 h2 x (v1 v2 : A) :
        def (x :-> v1 :+ h1) ->
        x :-> v1 :+ h1 = x :-> v2 :+ h2 -> [/\ v1 = v2, def h1 & h1 = h2].
Proof.
move=>D E.
have: look x (x :-> v1 :+ h1) = look x (x :-> v2 :+ h2) by rewrite E.
rewrite !lookPtUn -?E // => X; move: (dyn_inj X)=>{X} X.
by rewrite -{}X in E *; rewrite -(unhKl D E) (defUnr D).
Qed.

Lemma domPtUnX A (v : A) x i : def (x :-> v :+ i) -> x \in dom (x :-> v :+ i).
Proof. by move=>D; rewrite domPtUn inE /= D eq_refl. Qed.

Lemma domPtX A (v : A) x : def (x :-> v) -> x \in dom (x :-> v).
Proof. by move=>D; rewrite -(unh0 (x :-> v)) domPtUnX // unh0. Qed.

Lemma dom_notin_notin h1 h2 x :
        def (h1 :+ h2) -> x \notin dom (h1 :+ h2) -> x \notin dom h1.
Proof. by move=>D; rewrite domUn inE /= negb_and negb_or /= D; case/andP. Qed.

Lemma dom_in_notin h1 h2 x : def (h1 :+ h2) -> x \in dom h1 -> x \notin dom h2.
Proof. by case: defUn=>// D1 D2 H _; apply: H. Qed.

(******************************)
(* Properties of block update *)
(******************************)

Section BlockUpdate.
Variable (A : Type).

Fixpoint updi x (vs : seq A) {struct vs} : heap :=
  if vs is v'::vs' then (x :-> v') :+ updi (x .+ 1) vs' else empty.

Lemma updiS x v vs : updi x (v :: vs) = x :-> v :+ updi (x .+ 1) vs.
Proof. by []. Qed.

Lemma updi_last x v vs :
        updi x (rcons vs v) = updi x vs :+ x.+(size vs) :-> v.
Proof.
elim: vs x v=>[|w vs IH] x v /=.
- by rewrite ptr0 unh0 un0h.
by rewrite -(addn1 (size vs)) addnC -ptrA IH unA.
Qed.

Lemma updi_cat x vs1 vs2 :
        updi x (vs1 ++ vs2) = updi x vs1 :+ updi x.+(size vs1) vs2.
Proof.
elim: vs1 x vs2=>[|v vs1 IH] x vs2 /=.
- by rewrite ptr0 un0h.
by rewrite -(addn1 (size vs1)) addnC -ptrA IH unA.
Qed.

Lemma updi_catI x y vs1 vs2 :
        y = x.+(size vs1) -> updi x vs1 :+ updi y vs2 = updi x (vs1 ++ vs2).
Proof. by move=>->; rewrite updi_cat. Qed.

(* helper lemma *)
Lemma updiVm' x m xs : m > 0 -> x \notin dom (updi x.+m xs).
Proof.
elim: xs x m=>[|v vs IH] x m //= H.
rewrite ptrA domPtUn inE /= negb_and negb_or -{4}(ptr0 x) ptrK -lt0n H /=.
by rewrite orbC IH // addn1.
Qed.

Lemma updiD x xs : def (updi x xs) = (x != null) || (size xs == 0).
Proof.
elim: xs x=>[|v xs IH] x //=; first by rewrite orbC.
by rewrite defPtUn updiVm' // orbF IH ptr_null andbF andbC.
Qed.

Lemma updiVm x m xs :
        x \in dom (updi x.+m xs) = [&& x != null, m == 0 & size xs > 0].
Proof.
case: m=>[|m] /=; last first.
- by rewrite andbF; apply: negbTE; apply: updiVm'.
case: xs=>[|v xs]; rewrite ptr0 ?andbF ?andbT //=.
by rewrite domPtUn inE /= eq_refl -updiS updiD orbF andbT /=.
Qed.

Lemma updimV x m xs :
        x.+m \in dom (updi x xs) = (x != null) && (m < size xs).
Proof.
case H: (x == null)=>/=.
- by case: xs=>// a s; rewrite (eqP H).
elim: xs x m H=>[|v vs IH] x m H //; case: m=>[|m].
- by rewrite ptr0 /= domPtUn inE /= eq_refl andbT -updiS updiD H.
rewrite -addn1 addnC -ptrA updiS domPtUn inE /= IH; last first.
- by rewrite ptrE /= addn1.
by rewrite -updiS updiD H /= -{1}(ptr0 x) ptrA ptrK.
Qed.

Lemma updiP x y xs :
        reflect (y != null /\ exists m, x = y.+m /\ m < size xs)
                (x \in dom (updi y xs)).
Proof.
case H: (y == null)=>/=.
- by rewrite (eqP H); elim: xs=>[|z xs IH] //=; constructor; case.
case E: (x \in _); constructor; last first.
- by move=>[_][m][H1] H2; rewrite H1 updimV H2 H in E.
case: (ptrT x y) E=>m; case/orP; move/eqP=>->.
- by rewrite updimV H /= => H1; split=>//; exists m.
rewrite updiVm; case/and3P=>H1; move/eqP=>-> H2.
by split=>//; exists 0; rewrite ptrA addn0 ptr0.
Qed.

(* Invertibility *)
Lemma updi_inv x xs1 xs2 :
        def (updi x xs1) -> updi x xs1 = updi x xs2 -> xs1 = xs2.
Proof.
elim: xs1 x xs2 =>[|v1 xs1 IH] x /=; case=>[|v2 xs2] //= D;
[move/esym| | ]; try by rewrite empbE empUn empPt.
by case/(cancel D)=><- {D} D; move/(IH _ _ D)=><-.
Qed.

Lemma updi_iinv x xs1 xs2 h1 h2 :
        size xs1 = size xs2 -> def (updi x xs1 :+ h1) ->
        updi x xs1 :+ h1 = updi x xs2 :+ h2 -> xs1 = xs2 /\ h1 = h2.
Proof.
elim: xs1 x xs2 h1 h2=>[|v1 xs1 IH] x /=; case=>[|v2 xs2] //= h1 h2.
- by rewrite !un0h.
move=>[E]; rewrite -!unA=>D; case/(cancel D)=><- {D} D.
by case/(IH _ _ _ _ E D)=>->->.
Qed.

End BlockUpdate.

(*********************************************************************)
(* Freshness for even and odd locations -- used in information flow, *)
(* where heaps are split into low (even) and high (odd) parts.       *)
(*********************************************************************)

Definition low : pred ptr := fun x => 0 == nat_ptr x %[mod 2].
Definition high : pred ptr := fun x => 1 == nat_ptr x %[mod 2].

Definition get_lows h :=
  if h is Def hs _ then filter low (supp hs) else [::].

Definition get_highs h :=
  if h is Def hs _ then filter high (supp hs) else [::].

Definition ldom h : pred ptr := fun x => x \in get_lows h.
Definition hdom h : pred ptr := fun x => x \in get_highs h.

Lemma ldomP h x : x \in ldom h = (x \in dom h) && low x.
Proof.
case: h=>[//|[h S]]; rewrite /ldom /= /dom /supp /= =>H.
rewrite -!topredE /=.
elim: (map key h)=>[|y s IH] //=.
case: ifP=>E; rewrite !inE IH; case: eqP=>// -> //=.
by rewrite E andbF.
Qed.

Lemma hdomP h x : x \in hdom h = (x \in dom h) && high x.
Proof.
case: h=>[//|[h S]]; rewrite /hdom /= /dom /supp /= =>H.
rewrite -!topredE /=.
elim: (map key h)=>[|y s IH] //=.
case: ifP=>E; rewrite !inE IH; case: eqP=>// -> //=.
by rewrite E andbF.
Qed.

Lemma ldomK h1 h2 t1 t2 :
        def (h1 :+ t1) -> def (h2 :+ t2) ->
        ldom h1 =i ldom h2 ->
        ldom (h1 :+ t1) =i ldom (h2 :+ t2) -> ldom t1 =i ldom t2.
Proof.
move=>D1 D2 H1 H2 x; move: {H1 H2} (H1 x) (H2 x).
rewrite !ldomP !domUn !inE.
case: defUn D1=>// H1 H2 L1 _; case: defUn D2=>// H3 H4 L2 _.
case E1: (x \in dom t1); case E2: (x \in dom t2)=>//; rewrite orbF orbT /=;
case E3: (x \in dom h1); case E4: (x \in dom h2)=>//= _ _;
by [move/L1: E3; rewrite E1 | move/L2: E4; rewrite E2].
Qed.

Definition lfresh h := (last null (get_lows h)) .+ 2.
Definition hfresh h := (last (null .+ 1) (get_highs h)) .+ 2.

Lemma last_inv A B (f : A -> B) (x1 x2 : A) (h : seq A) :
        f x1 = f x2 -> f (last x1 h) = f (last x2 h).
Proof. by elim: h. Qed.


Lemma lfresh_low h n : low (lfresh h) .+ (2*n).
Proof.
rewrite /lfresh /low /get_lows.
case: h; first by rewrite modn_addl modn_mulr.
case; rewrite /supp /low /=.
elim=>[|[[x] v] h IH] /=; first by rewrite modn_addl modn_mulr.
rewrite inE negb_or ptrE /=; move/path_sorted=>H1; case/andP=>H2 H3.
case: ifP=>E /=; last by apply: IH.
set f := fun x => (nat_ptr x + 2 + 2 * n) %% 2.
have F: f (ptr_nat x) = f null.
- by rewrite /f -modn_mod -addnA -modn_add2m -(eqP E) !modn_mod.
move: (last_inv (f := f) (x1 := (ptr_nat x)) (x2 := null))=>L.
by rewrite /f /= in L; rewrite {}L //; apply: IH.
Qed.

Lemma hfresh_high h n : high (hfresh h) .+ (2*n).
Proof.
rewrite /hfresh /high /get_highs.
case: h n=>[n|].
- by rewrite /null /= add0n -addnA -modn_add2m modn_addl modn_mulr addn0.
case; rewrite /supp /high /=.
elim=>[|[[x] v] h IH] /=.
- by move=>_ _ n; rewrite add0n -addnA -modn_add2m modn_addl modn_mulr addn0.
rewrite inE negb_or ptrE /=; move/path_sorted=>H1; case/andP=>H2 H3.
case: ifP=>E n /=; last by apply: IH.
set f := fun x => (nat_ptr x + 2 + 2 * n) %% 2.
have F: f (ptr_nat x) = f (null .+ 1).
- rewrite /f -modn_mod /= add0n -addnA.
   rewrite -modn_add2m -(eqP E) modn_mod.
   by rewrite modn_add2m addnA.
move: (last_inv (f := f) (x1 := (ptr_nat x)) (x2 := null .+ 1))=>L.
by rewrite /f /= in L; rewrite {}L //; apply: IH.
Qed.

Lemma dom_lfresh h n : (lfresh h) .+ (2*n) \notin dom h.
Proof.
suff L2: forall h x, low x -> x \in dom h -> ord x (lfresh h).
- apply: (contra (L2 _ _ (lfresh_low h n))).
  by rewrite -leqNgt leq_addr.
case=>[|[s H1]] //; rewrite /supp => /= H2 x.
rewrite /dom /lfresh /get_lows /low /supp -topredE /=.
elim: s H1 null H2 x=>[|[y d] s IH] //= H1 x.
rewrite inE negb_or; case/andP=>H3 H4 z /= E; rewrite inE.
case/orP=>H5.
- rewrite -!{H5 y}(eqP H5) E in H1 H3 *.
  by apply: (path_last 1); apply: path_filter.
by case: ifP=>E2; apply: IH=>//; move: H1;
[apply: path_sorted | apply: notin_path | apply: path_sorted].
Qed.

Lemma dom_hfresh h n : (hfresh h) .+ (2*n) \notin dom h.
Proof.
suff L2: forall h x, high x -> x \in dom h -> ord x (hfresh h).
- apply: (contra (L2 _ _ (hfresh_high h n))).
  by rewrite -leqNgt leq_addr.
case=>[|[s H1]] //; rewrite /supp => /= H2 x.
rewrite /dom /hfresh /get_highs /high /supp -topredE /=.
elim: s H1 null H2 x=>[|[y d] s IH] //= H1 x.
rewrite inE negb_or; case/andP=>H3 H4 z /= E; rewrite inE.
case/orP=>H5.
- rewrite -!{H5 y}(eqP H5) E in H1 H3 *.
  by apply: (path_last 1); apply: path_filter.
case: ifP=>E2; last by apply: IH=>//; apply: path_sorted H1.
move: H1.
have [t -> H1]: exists t, y = t .+ 1.
- case: y {H3} E2; case=>[|m] //.
  by exists (ptr_nat m); rewrite /ptr_offset /= addn1.
apply: IH=>//; first by apply: path_sorted H1.
apply: notin_path; apply: ord_path H1.
by case: t=>m; rewrite /ord /= addn1.
Qed.

Lemma lfresh_null h : lfresh h != null.
Proof. by case: h=>[//|[h H] F]; rewrite /lfresh ptrE -lt0n /= addnS. Qed.

Lemma hfresh_null h : hfresh h != null.
Proof. by case: h=>[//|[h H] F]; rewrite /lfresh ptrE -lt0n /= addnS. Qed.

Lemma high_lowD : [predI low & high] =i pred0.
Proof.
case=>x; rewrite inE /low /high /= -!topredE /=.
by case: x=>// n; case E: (0 %% 2 == _)=>//=; rewrite -(eqP E).
Qed.


Lemma modnS x1 x2 : (x1 == x2 %[mod 2]) = (x1.+1 == x2.+1 %[mod 2]).
Proof.
case E: (x1 %% 2 == _).
- by rewrite -addn1 -modn_add2m (eqP E) modn_add2m addn1 eq_refl.
suff L: ((x1.+1) %% 2 == (x2.+1) %% 2) -> (x1 %% 2 == x2 %% 2).
- by rewrite E in L; case: eqP L=>// _; apply.
move=>{E} E; rewrite -(modn_addr x1) -(modn_addr x2).
by rewrite -addSnnS -modn_add2m (eqP E) modn_add2m addSnnS.
Qed.

Lemma hlE x : high x = ~~ low x.
Proof.
case: x=>n; rewrite /high /low /=.
elim: n=>[//|m IH]; apply: negb_inj.
by rewrite negbK -modnS -IH modnS modnn.
Qed.

Lemma lhE x : low x = ~~ high x.
Proof. by apply: negb_inj; rewrite negbK hlE. Qed.

Lemma ldomUn h1 h2 :
        ldom (h1 :+ h2) =i
        [pred x | def (h1 :+ h2) && (x \in [predU ldom h1 & ldom h2])].
Proof. by move=>x; rewrite !inE !ldomP domUn !inE /= -andbA andb_orl. Qed.

Definition loweq h1 h2 := get_lows h1 == get_lows h2.

Notation "h1 =~ h2" := (loweq h1 h2) (at level 80).

Lemma low_refl h : h =~ h.
Proof. by rewrite /loweq. Qed.

Hint Resolve low_refl : core.

Lemma low_sym h1 h2 : (h1 =~ h2) = (h2 =~ h1).
Proof. by rewrite /loweq eq_sym. Qed.

Lemma low_trans h2 h1 h3 : h1 =~ h2 -> h2 =~ h3 -> h1 =~ h3.
Proof. by rewrite /loweq; move/eqP=>->. Qed.

Lemma loweqP h1 h2 : reflect (ldom h1 =i ldom h2) (h1 =~ h2).
Proof.
case E: (loweq h1 h2); constructor; rewrite /loweq in E.
- by move=>x; rewrite /ldom (eqP E).
move=>F.
suff {E} : get_lows h1 = get_lows h2 by move/eqP; rewrite E.
apply: (eq_sorted_irr (leT := ord)); last by apply: F.
- by apply: trans.
- by apply: irr.
- case: h1 {F}=>// [[h S] H].
  by rewrite sorted_filter //; apply: trans.
case: h2 {F}=>// [[h S] H].
by rewrite sorted_filter //; apply: trans.
Qed.

Lemma loweqK h1 h2 t1 t2 :
        def (h1 :+ t1) -> def (h2 :+ t2) ->
        h1 =~ h2 -> h1 :+ t1 =~ h2 :+ t2 -> t1 =~ t2.
Proof.
move=>D1 D2.
case: loweqP=>// E1 _; case: loweqP=>// E2 _; apply/loweqP.
by apply: ldomK E2.
Qed.

Lemma loweqE h1 h2 : h1 =~ h2 -> lfresh h1 = lfresh h2.
Proof. by rewrite /loweq /lfresh; move/eqP=>->. Qed.

Lemma lowUn h1 h2 t1 t2 :
        def (h1 :+ t1) ->
        def (h2 :+ t2) ->
        h1 =~ h2 -> t1 =~ t2 -> h1 :+ t1 =~ h2 :+ t2.
Proof.
move=>D1 D2; do 2![case: loweqP=>//]=>H1 H2 _ _.
apply/loweqP=>x; move: (H1 x) (H2 x).
by rewrite !ldomP !domUn !inE D1 D2 /= !andb_orl=>-> ->.
Qed.

Lemma lowPn A1 A2 (x : ptr) (v1 : A1) (v2 : A2) : x :-> v1 =~ x :-> v2.
Proof. by apply/loweqP=>y; rewrite !ldomP !domPt. Qed.

Hint Resolve lowPn : core.

Lemma highPn A1 A2 (x1 x2 : ptr) (v1 : A1) (v2 : A2) :
        high x1 -> high x2 -> x1 :-> v1 =~ x2 :-> v2.
Proof.
move=>H1 H2.
apply/loweqP=>y; rewrite !ldomP !domPt !inE.
case E1: (x1 == y); first by rewrite -(eqP E1) lhE H1 !andbF.
case E2: (x2 == y)=>//=.
by rewrite -(eqP E2) lhE H2 andbF.
Qed.

Lemma lowPtUn A1 A2 h1 h2 (x : ptr) (v1 : A1) (v2 : A2) :
        def (x :-> v1 :+ h1) ->
        def (x :-> v2 :+ h2) ->
        (x :-> v1 :+ h1 =~ x :-> v2 :+ h2) = (h1 =~ h2).
Proof.
move=>D1 D2.
case E: (h1 =~ h2); first by apply: lowUn.
move/(elimF idP): E=>E; apply: (introF idP)=>F; case: E.
by apply: loweqK F.
Qed.

Lemma highPtUn A h1 h2 (x : ptr) (v : A) :
        def (x :-> v :+ h1) -> high x ->
        (x :-> v :+ h1 =~ h2) = (h1 =~ h2).
Proof.
move=>D H.
case E: (h1 =~ h2); case: loweqP E=>// L1 _; apply/loweqP.
- move=>y; rewrite !ldomP domPtUn !inE D.
  case: eqP=>[<-|]; last by rewrite -!ldomP L1.
  by rewrite lhE H /= andbF.
move=>L2; case: L1 => y; move: {L2} (L2 y).
rewrite !ldomP !domPtUn !inE D /=.
by case: eqP=>//= <-; rewrite lhE H andbF -[x \in dom h1]negbK (defPt_dom D).
Qed.

Lemma highPtUn2 A1 A2 h1 h2 (x1 x2 : ptr) (v1 : A1) (v2 : A2) :
        def (x1 :-> v1 :+ h1) ->
        def (x2 :-> v2 :+ h2) ->
        high x1 -> high x2 ->
        h1 =~ h2 -> x1 :-> v1 :+ h1 =~ x2 :-> v2 :+ h2.
Proof. by move=>D1 D2 H1 H2 L; apply: lowUn=>//; apply: highPn. Qed.

(**********************************************)
(* several basic operations on pairs of heaps *)
(**********************************************)

Definition plus2 (h1 h2 : heap * heap) : heap * heap :=
  (h1.1 :+ h2.1, h1.2 :+ h2.2).

Definition def2 (h : heap * heap) := def h.1 && def h.2.

Notation "h1 :++ h2" := (plus2 h1 h2) (at level 50).

Lemma unA2 h1 h2 h3 : h1 :++ (h2 :++ h3) = h1 :++ h2 :++ h3.
Proof. by congr (_, _); rewrite /= unA. Qed.

Lemma unC2 h1 h2 : h1 :++ h2 = h2 :++ h1.
Proof. by congr (_, _); rewrite unC. Qed.

Lemma unKhl2 h h1 h2 : def2 (h1 :++ h) -> h1 :++ h = h2 :++ h -> h1 = h2.
Proof.
move: h h1 h2=>[h1 h2][h11 h12][h21 h22]; case/andP=>/= [D1 D2] [E1 E2].
by rewrite (unKhl D1 E1) (unKhl D2 E2).
Qed.

Lemma unKhr2 h h1 h2 : def2 (h2 :++ h) -> h1 :++ h = h2 :++ h -> h1 = h2.
Proof.
move: h h1 h2=>[h1 h2][h11 h12][h21 h22]; case/andP=>/= [D1 D2] [E1 E2].
by rewrite (unKhr D1 E1) (unKhr D2 E2).
Qed.

Lemma unDl2 h1 h2 : def2 (h1 :++ h2) -> def2 h1.
Proof. by case/andP=>/= D1 D2; rewrite /def2 (defUnl D1) (defUnl D2). Qed.

Lemma unDr2 h1 h2 : def2 (h1 :++ h2) -> def2 h2.
Proof. by case/andP=>/= D1 D2; rewrite /def2 (defUnr D1) (defUnr D2). Qed.

Lemma un0h2 h : (empty, empty) :++ h = h.
Proof. by case: h=>h1 h2; rewrite /plus2 /= !un0h. Qed.

Lemma unh02 h : h :++ (empty, empty) = h.
Proof. by case: h=>h1 h2; rewrite /plus2 /= !unh0. Qed.

(**************************************************************************)
(* Several tactics for canceling common terms in disjoint unions          *)
(* Currently, they don't deal with weak pointers. I.e.  they only if they *)
(* see iterms like x :-> v1 and x :-> v2, they will reduce to v1 = v2     *)
(* only if v1, v2 are of the same type A more general tactic would emit   *)
(* obligation dyn v1 = dyn v2, but I don't bother with this now.          *)
(**************************************************************************)

(* First cancelation in hypotheses *)

Lemma injUh A h1 h2 x (v1 v2 : A) :
        def (h1 :+ (x :-> v1)) ->
        h1 :+ (x :-> v1) = h2 :+ (x :-> v2) ->
          def h1 /\ h1 = h2 /\ v1 = v2.
Proof. by rewrite -!(unC (x :-> _))=>D; case/(cancel D)=><- -> ->. Qed.

Lemma eqUh h1 h2 h : def (h1 :+ h) -> h1 :+ h = h2 :+ h -> def h1 /\ h1 = h2.
Proof. by move=>D E; rewrite {2}(unKhl D E) (defUnl D). Qed.

Lemma exit1 h1 h2 h : def (h1 :+ h) -> h1 :+ h = h :+ h2 -> def h1 /\ h1 = h2.
Proof. by move=>D; rewrite (unC h); apply: eqUh. Qed.

Lemma exit2 h1 h : def (h1 :+ h) -> h1 :+ h = h -> def h1 /\ h1 = empty.
Proof. by move=>H1; rewrite -{2}(unh0 h)=>H2; apply: exit1 H2. Qed.

Lemma exit3 h1 h : def h -> h = h :+ h1 -> def empty /\ empty = h1.
Proof.
move=>H1 H2; split=>//; rewrite -{1}(unh0 h) in H2.
by apply: unhKl H2; rewrite unh0.
Qed.

Lemma exit4 h : def h -> h = h -> def empty /\ empty = empty.
Proof. by []. Qed.

Ltac cancelator t H :=
  match goal with
  (* we exit when we hit the terminator on the left *)
  | |- ?h1 :+ t = ?h2 -> _ =>
     let j := fresh "j" in
     set j := {1}(h1 :+ t);
     rewrite -1?unA /j {j};
     (move/(exit1 H)=>{H} [H] || move/(exit2 H)=>{H} [H])
  | |- t = ?h2 -> _ =>
     rewrite -?unA;
     (move/(exit3 H)=>{H} [H] || move/(exit4 H)=>{H} [H])
  | |- (?h1 :+ (?x :-> ?v) = ?h2) -> _ =>
    let j := fresh "j" in
    set j := {1}(h1 :+ (x :-> v));
    (* if x appears in the second union, first bring it to the back *)
    rewrite 1?(unC (x :-> _)) -?(unAC _ _ (x :-> _)) /j {j};
    (* then one of the following must apply *)
    (* if x is in the second union then cancel *)
    (move/(injUh H)=>{H} [H []] ||
    (* if not, rotate x in the first union *)
     rewrite (unC h1) ?unA in H * );
    (* and proceed *)
    cancelator t H
  (* if the heap is not a points-to relation, also try to cancel *)
  | |- (?h1 :+ ?h = ?h2) -> _ =>
    let j := fresh "j" in
    set j := {1}(h1 :+ h);
    (* if h appears in the second union, first bring it to the back *)
    rewrite 1?(unC h) -?(unAC _ _ h) /j {j};
    (* then one of the following must apply *)
    (* if h is in the second union then cancel *)
    (move/(eqUh H)=>{H} [H []] ||
    (* if not, rotate h in the first union *)
    rewrite (unC h1) ?unA in H * );
    (* and proceed *)
    cancelator t H
  | |- _ => idtac
  end.

Ltac heap_cancel :=
  match goal with
  | |- ?h1 = ?h2 -> ?GG =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let t := fresh "t" in
    let H := fresh "H" in
    let G := fresh "hidden_goal"
    in
      (* generate the obligation to prove that the left heap is defined *)
      suff : def h1; first (
       (* make sure no sharing of expressions in the goal *)
       set t1 := {1 2}h1; set t2 := {1}h2; set G := GG;
       (* introduce terminators *)
       rewrite -(un0h t1) -(un0h t2) [empty]lock;
       set t := locked empty; rewrite /t1 /t2 {t1 t2};
       move=>H;
       (* flatten the goal *)
       rewrite ?unA in H *;
       (* call the cancelation routine *)
       cancelator t H;
       (* remove the terminator and push H onto the goal *)
       move: H {t}; rewrite /G {G})
  | |- _ => idtac
  end.

(* Then cancelation in conclusions *)

Lemma cexit1 h1 h2 h : h1 = h2 -> h1 :+ h = h :+ h2.
Proof. by move=>->; rewrite unC. Qed.

Lemma cexit2 h1 h : h1 = empty -> h1 :+ h = h.
Proof. by move=>->; rewrite un0h. Qed.

Lemma cexit3 h1 h : empty = h1 -> h = h :+ h1.
Proof. by move=><-; rewrite unh0. Qed.

Lemma congUh A h1 h2 x (v1 v2 : A) :
        h1 = h2 -> v1 = v2 -> h1 :+ (x :-> v1) = h2 :+ (x :-> v2).
Proof. by move=>-> ->. Qed.

Lemma congeqUh h1 h2 h : h1 = h2 -> h1 :+ h = h2 :+ h.
Proof. by move=>->. Qed.

Ltac congruencer t :=
  match goal with
  | |- ?h1 :+ t = ?h2 =>
     let j := fresh "j" in
     set j := {1}(h1 :+ t);
     rewrite -1?unA /j {j};
     (apply: cexit1 || apply: cexit2)
  | |- t = ?h2 =>
     rewrite -1?unA;
     (apply: cexit3 || apply: refl_equal)
  | |- (?h1 :+ (?x :-> ?v) = ?h2) =>
    let j := fresh "j" in
    set j := {1}(h1 :+ (x :-> v));
    (* if x appears in the second union, first bring it to the back *)
    rewrite 1?(unC (x :-> _)) -?(unAC _ _ (x :-> _)) /j {j};
    (* then one of the following must apply *)
    (* if x is in the second union then cancel *)
    ((apply: congUh; [congruencer t | idtac]) ||
    (* if not, rotate x in the first union *)
     (rewrite (unC h1) ?unA; congruencer t))
  (* if the heap is not a points-to relation, also try to cancel *)
  | |- (?h1 :+ ?h = ?h2) =>
    let j := fresh "j" in
    set j := {1}(h1 :+ h);
    (* if h appears in the second union, first bring it to the back *)
    rewrite 1?(unC h) -?(unAC _ _ h) /j {j};
    (* then one of the following must apply *)
    (* if h is in the second union then cancel *)
    (apply: congeqUh ||
    (* if not, rotate h in the first union *)
    rewrite (unC h1) ?unA);
    (* and proceed *)
    congruencer t
  | |- _ => idtac
  end.

Ltac heap_congr :=
  match goal with
  | |- ?h1 = ?h2 =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let t := fresh "t" in
      set t1 := {1}h1; set t2 := {1}h2;
      (* introduce terminators *)
      rewrite -(un0h t1) -(un0h t2) [empty]lock;
      set t := locked empty; rewrite /t1 /t2 {t1 t2};
      (* flatten the goal *)
      rewrite ?unA;
      (* call the congruence routine and remove the terminator *)
      congruencer t=>{t}
  | |- _ => idtac
  end.

Lemma test h1 h2 h3 x (v1 v2 : nat) :
        h3 = h2 -> v1 = v2 ->
        h1 :+ (x :-> v1) :+ h3= h2 :+ h1 :+ (x :-> v2).
Proof. by move=>H1 H2; heap_congr. Qed.

(* and a tactic for computing the subdom relation *)

Definition supdom h2 h1 := subdom h1 h2.

Lemma sexit1 h1 h2 h :
        def (h2 :+ h) ->
          (def h2 -> supdom h2 h1) -> supdom (h2 :+ h) (h :+ h1).
Proof.
move=>H1 H2; rewrite (unC h); apply: subdomE=>//.
by apply: H2; apply: defUnl H1.
Qed.

Lemma sexit2 h1 h :
        def (h1 :+ h) -> (def h1 -> supdom h1 empty) ->
          supdom (h1 :+ h) h.
Proof.
move=>H1 H2; rewrite -{2}(un0h h); apply: subdomE=>//.
by apply: H2; apply: defUnl H1.
Qed.

Lemma sexit3 h1 h :
        def h -> (def empty -> supdom empty h1) ->
          supdom h (h :+ h1).
Proof.
move=>H1 H2; rewrite unC -{1}(un0h h).
by apply: subdomE; [rewrite un0h | apply: H2].
Qed.

Lemma sexit4 h : def h -> (def empty -> empty = empty) -> supdom h h.
Proof. by move=>*; rewrite -(un0h h); apply: subdomE=>//; rewrite un0h. Qed.

Lemma supdomUh A B h1 h2 x (v1 : A) (v2 : B) :
        def (h2 :+ (x :-> v2)) ->
          (def h2 -> supdom h2 h1) ->
            supdom (h2 :+ (x :-> v2)) (h1 :+ (x :-> v1)).
Proof.
move=>H1 H2.
apply: subdomUE=>//; first by apply: H2; apply: defUnl H1.
by apply: subdomPE; apply: (@defPt_null _ h2 x v2); rewrite unC.
Qed.

Lemma supdomeqUh h1 h2 h :
        def (h2 :+ h) -> (def h2 -> supdom h2 h1) -> supdom (h2 :+ h) (h1 :+ h).
Proof. by rewrite (unC h1); apply: sexit1. Qed.

Lemma sup_defdef h1 h2 : def h2 -> supdom h2 h1 -> def h1.
Proof. by move=>H1; rewrite /supdom; move/subdom_def; rewrite H1 andbT. Qed.

Ltac supdom_checker t H :=
  match goal with
  | |- is_true (supdom (?h1 :+ t) ?h2) =>
     let j := fresh "j" in
     set j := {1}(h1 :+ t);
     rewrite -1?unA /j {j};
     (apply: (sexit1 H)=>{H} H || apply: (sexit2 H)=>{H} H)
  | |- is_true (supdom t ?h1) =>
     rewrite -1?unA;
     (apply: (sexit3 H)=>{H} H || apply: (sexit4 H)=>{H} H)
  | |- is_true (supdom (?h1 :+ (?x :-> ?v)) ?h2) =>
    let j := fresh "j" in
    set j := {1}(h1 :+ (x :-> v));
    (* if x appears in the second union, first bring it to the back *)
    rewrite 1?(unC (x :-> _)) -?(unAC _ _ (x :-> _)) /j {j};
    (* then one of the following must apply *)
    (* if x is in the second union then cancel *)
    (apply: (supdomUh _ H)=>{H} H ||
    (* if not, rotate x in the first union *)
     (rewrite (unC h1) ?unA in H * )); supdom_checker t H
  (* if the heap is not a points-to relation, also try to cancel *)
  | |- is_true (supdom (?h1 :+ ?h) ?h2) =>
    let j := fresh "j" in
    set j := {1}(h1 :+ h);
    (* if h appears in the second union, first bring it to the back *)
    rewrite 1?(unC h) -?(unAC _ _ h) /j {j};
    (* then one of the following must apply *)
    (* if h is in the second union then cancel *)
    (apply: (supdomeqUh H)=>{H} H ||
    (* if not, rotate h in the first union *)
    (rewrite (unC h1) ?unA in H * ));
    (* and proceed *)
    supdom_checker t H
  | |- _ => idtac
  end.

Ltac defcheck :=
  match goal with
  | |- is_true (def ?h2) -> is_true (def ?h1) =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let t := fresh "t" in
    let H := fresh "H" in
      set t2 := {1}h2; set t1 := {1}h1;
      (* introduce terminators *)
      rewrite -(un0h t1) -(un0h t2) [empty]lock;
      set t := locked empty; rewrite /t1 /t2 {t1 t2};
      (* flatten the goal *)
      rewrite ?unA;
      move=>H;
      apply: (sup_defdef H);
      (* call the subdom_cheker routine and remove the terminator *)
      supdom_checker t H; move: H {t}; rewrite /supdom
  | |- _ => idtac
  end.

(* this diverges in coq 8.3
Lemma test2 h1 h2 x (v1 v2 : nat) : subdom h1 h2 ->
        def (h2 :+ (x :-> v2)) -> def (h1 :+ (x :-> v1)).
Proof. by move=>H; defcheck. Qed.
*)

Ltac hhauto := (do ?econstructor=>//; try by [heap_congr])=>//.

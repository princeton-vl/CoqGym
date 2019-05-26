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
Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
From LemmaOverloading
Require Import heaps rels hprop stmod.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope stsep_scope with stsep.
Open Scope stsep_scope.

Definition lolli (p : _ -> Prop) q i m :=
  forall i1 h, i = i1 :+ h -> def i -> p i1 ->
    exists m1, m = m1 :+ h /\ def m /\ q i1 m1.

Notation "p '--o' q"   := (lolli p q) (at level 75) : stsep_scope.

Lemma antiframe p q i m h :
        def (i :+ h) -> (p --o q) (i :+ h) (m :+ h) -> (p --o q) i m.
Proof.
move=>D1 H i2 m2 E D2 H1; rewrite {i}E in H D1 D2 *.
move: (H i2 (m2 :+ h)); rewrite unA; case/(_ (erefl _) D1 H1)=>h2 [E][D3].
rewrite unA in E; exists h2; rewrite (unKhl D3 E).
by rewrite E in D3; rewrite (defUnl D3).
Qed.

(* p --o q is local *)
Lemma locality p q i1 m h :
        def (i1 :+ h) -> (p # top) i1 -> (p --o q) (i1 :+ h) m ->
          exists m1, m = m1 :+ h /\ def m /\ (p --o q) i1 m1.
Proof.
move=>D [h1][h2][E][H1] _ H2; rewrite {i1}E in D H2 *.
move: (H2 h1 (h2 :+ h)); rewrite unA; case/(_ (erefl _) D H1)=>m1 [E][D2].
rewrite {m}E unA in H2 D2 *; exists (m1 :+ h2); do !split=>//.
by apply: antiframe D H2.
Qed.

Lemma fr_pre p i j : (p # top) i -> (p # top) (i :+ j).
Proof.
by case=>i1 [i2][->][H] _; rewrite -unA; exists i1; exists (i2 :+ j).
Qed.

(********************)
(* Separation monad *)
(********************)

Definition fr A (s : spec A) : spec A :=
  (s.1 # top, fun x => s.1 --o s.2 x).

Prenex Implicits fr.

Notation "[ s ]" := (fr s).

Definition STsep A (s : spec A) := ST [s].

Section SepReturn.
Variable (A : Type) (x : A).

Definition ret_s : spec A := (emp, fun y i m => m = i /\ y = Val x).

Lemma retP : Model.conseq (Model.ret_s x) [ret_s].
Proof.
move=>i /= H1 D1; split=>// y m [->] -> _ i1 i2 -> D ->.
by exists empty; rewrite un0h (defUnr D).
Qed.

Definition ret := Model.Do (Model.ret x) retP.

End SepReturn.

Section SepBind.
Variables (A B : Type) (s1 : spec A) (s2 : A -> spec B).
Variables (e1 : STsep s1) (e2 : forall x, STsep (s2 x)).

Definition bind_s : spec B :=
  (Model.bind_pre [s1] (fr \o s2), Model.bind_post [s1] (fr \o s2)).

Lemma bindP : Model.conseq (Model.bind_s [s1] (fr \o s2)) [bind_s].
Proof.
move=>i H D; split=>[|{H D}].
- case: H D=>i1 [i2][->][[H S]] _ D.
  split=>[|y m]; first by apply: fr_pre.
  by case/(locality D H)=>m1 [->][_]; move/S; apply: fr_pre.
move=>y m H _ i1 i2 E D1 [H1 S1]; rewrite {i}E in H D1 *.
case: H=>[[x][h][]|[e][->]]; case/(locality D1 H1)=>h1 [->][D2] T2.
- move/S1: (T2)=>H2; case/(locality D2 H2)=>m1 [->][D3] T3.
  by exists m1; do !split=>//; left; exists x; exists h1.
by exists h1; do !split=>//; right; exists e.
Qed.

Definition bind : STsep bind_s := Model.Do (Model.bind e1 e2) bindP.

End SepBind.

Definition verify' A (s : spec A) i (r : ans A -> heap -> Prop) :=
  def i -> s.1 i /\ forall y m, s.2 y i m -> def m -> r y m.

Notation verify s i r := (@verify' _ [s] i r).

Section SepFrame.
Variables (A : Type) (s : spec A).

Lemma frame i j (r : ans A -> heap -> Prop) :
        verify s i (fun y m => def (m :+ j) -> r y (m :+ j)) ->
        verify s (i :+ j) r.
Proof.
move=>H D; case: (H (defUnl D))=>H1 H2.
split=>[|y m]; first by apply: fr_pre.
case/(locality D H1)=>m1 [->][D1]; move/H2.
by apply; apply: defUnl D1.
Qed.

Lemma frame0 i r : verify' s i r -> verify s i r.
Proof.
move=>H D; case: (H D)=>H1 H2.
split=>[|y m]; first by exists i; exists empty; rewrite unh0.
move/(_ i empty); rewrite unh0; case/(_ (erefl _) D H1)=>m1.
by rewrite unh0=>[[<-]][_]; apply: H2.
Qed.

Lemma frame1 i (r : ans A -> heap -> Prop) :
        verify' s empty (fun y m => def (m :+ i) -> r y (m :+ i)) ->
        verify s i r.
Proof. by move=>H; rewrite -[i]un0h; apply: frame; apply: frame0. Qed.

End SepFrame.

Definition conseq A (s : spec A) (p : pre) (q : post A) :=
  forall i, p i -> verify s i (fun y m => q y i m).

Local Notation conseq1 :=
  (fun A (s1 s2 : spec A) =>
     conseq s1 (let 'pair x _ := s2 in x)
               (let 'pair _ x := s2 in x)).

Lemma conseq_refl A (s : spec A) : conseq1 A s s.
Proof. by case: s=>s1 s2 i H; apply: frame0. Qed.

Hint Resolve conseq_refl : core.

Section SepConseq.
Variables (A : Type) (s1 s2 : spec A) (e : STsep s1).
Variables (pf : conseq1 A s1 s2).

Lemma doP : Model.conseq [s1] [s2].
Proof.
move=>i H D; split=>[|y m {H D} /=].
- case: H D=>i1 [i2][->][H] _ D.
  by case: (@pf i1 H (defUnl D))=>H1 _; apply: fr_pre.
move=>S D i1 i2 E D2 H2; rewrite {i}E in D S D2 H2.
case: (@pf i1 H2 (defUnl D2))=>H1 T1.
case: (locality D2 H1 S)=>m1 [->][D3] {S}.
by move/T1; move/(_ (defUnl D3))=>T2; exists m1.
Qed.

Definition do' : STsep s2 := Model.Do e doP.

End SepConseq.

Notation "'Do' e" := (do' e _) (at level 80).

Section SepRead.
Variables (A : Type) (x : ptr).

Definition read_s : spec A :=
  (fun i => exists v : A, i = x :-> v,
   fun y i m => i = m /\ forall v, i = x :-> v -> y = Val v).

Lemma readP : Model.conseq (Model.read_s A x) [read_s].
Proof.
move=>i H D; split=>[|{H D} y _ [->] H _ i1 h E1 D E2].
- case: H D=>i1 [i2][->][[v]] -> _ D /=.
  rewrite domPtUn inE /= D eq_refl; split=>//.
  by exists v; rewrite lookPtUn.
move: E1 E2 H D=>-> [v ->] H D; exists (x :-> v); do 3!split=>//.
move=>w; move/(pts_inj (defUnl D))=><-; apply: H.
by rewrite lookPtUn.
Qed.

Definition read : STsep read_s := Model.Do (Model.read A x) readP.

End SepRead.

Section SepWrite.
Variables (A : Type) (x : ptr) (v : A).

Definition write_s : spec unit :=
  (fun i => exists B : Type, exists y : B, i = x :-> y,
   fun y i m => y = Val tt /\ m = x :-> v).

Lemma writeP : Model.conseq (Model.write_s x v) [write_s].
Proof.
move=>i H D; split=>[|{H D} y m [->] <- D1 i1 h E1 D2 [B][w] E2].
- case: H D=>i1 [i2][->][[B]][y] -> _ D /=.
  by rewrite domPtUn inE /= D eq_refl.
move: E1 E2 D1 D2=>->->-> D; exists (x :-> v).
by rewrite updUnl domPt inE /= eq_refl (defPt_null D) /= updU eq_refl.
Qed.

Definition write : STsep write_s := Model.Do (Model.write x v) writeP.

End SepWrite.

Section SepAlloc.
Variables (A : Type) (v : A).

Definition alloc_s : spec ptr :=
  (emp, fun y i m => exists x, y = Val x /\ m = x :-> v).

Lemma allocP : Model.conseq (Model.alloc_s v) [alloc_s].
Proof.
move=>i H D; split=>[|{H D} y m [x][H1][->][H2] <- D1 i1 h E1 D E2].
- by case: H D=>i1 [i2][->][->].
move: E1 E2 H2 D D1=>-> ->; rewrite {1 2}un0h=>H2 D D1.
exists (x :-> v); rewrite updUnr (negbTE H2) defPtUn H1 H2 D.
by do !split=>//; exists x.
Qed.

Definition alloc : STsep alloc_s := Model.Do (Model.alloc v) allocP.

End SepAlloc.

Section SepBlockAlloc.
Variables (A : Type) (v : A) (n : nat).

Definition allocb_s : spec ptr :=
  (emp, fun y i m => exists x:ptr, y = Val x /\ m = updi x (nseq n v)).

Lemma allocbP : Model.conseq (Model.allocb_s v n) [allocb_s].
Proof.
move=>i H D; split=>[|y m].
  by case: H D=>i1 [i2][->][->][]; rewrite unC.
case=>x [->] -> D1 i1 h E1 D2 E2.
move: E1 E2 D1 D2=>->->; rewrite un0h {2}unC=>D1 D2.
by exists (updi x (nseq n v)); do !split=>//; exists x.
Qed.

Definition allocb : STsep allocb_s := Model.Do (Model.allocb v n) allocbP.

End SepBlockAlloc.

Section SepDealloc.
Variable x : ptr.

Definition dealloc_s : spec unit :=
  (fun i => exists A : Type, exists v:A, i = x :-> v,
   fun y i m => y = Val tt /\ m = empty).

Lemma deallocP : Model.conseq (Model.dealloc_s x) [dealloc_s].
Proof.
move=>i H D; split=>[|{H D} y m [->] <- D1 i1 h E1 D2 [A][v] E2].
- case: H D=>i1 [i2][->][[A]][v]-> _ D /=.
  by rewrite domPtUn inE /= D eq_refl.
move: E1 E2 D1 D2=>->->->; rewrite defPtUn; case/and3P=>H1 _ H2.
by exists empty; rewrite freeUnr // freeU eq_refl (negbTE H1) free0.
Qed.

Definition dealloc : STsep dealloc_s := Model.Do (Model.dealloc x) deallocP.

End SepDealloc.

Section SepThrow.
Variables (A : Type) (e : exn).

Definition throw_s : spec A :=
  (emp, fun y i m => m = i /\ y = Exn e).

Lemma throwP : Model.conseq (Model.throw_s A e) [throw_s].
Proof.
move=>i H D; split=>{H D} // y m [->] -> _ i1 h -> D ->.
by exists empty; rewrite un0h; do !split=>//; apply: defUnr D.
Qed.

Definition throw : STsep throw_s := Model.Do (Model.throw A e) throwP.

End SepThrow.

Section SepTry.
Variables (A B : Type) (s : spec A) (s1 : A -> spec B) (s2 : exn -> spec B).
Variables (e : STsep s) (e1 : forall x, STsep (s1 x)).
Variables (e2 : forall e, STsep (s2 e)).

Definition try_s : spec B :=
  (Model.try_pre [s] (fr \o s1) (fr \o s2),
   Model.try_post [s] (fr \o s1) (fr \o s2)).

Lemma tryP : Model.conseq (Model.try_s [s] (fr \o s1) (fr \o s2)) [try_s].
Proof.
move=>i H D; split=>[|{H D} y m H1 D1 i1 h E1 D2 /= [H2][H3] H4].
- case: H D=>i1 [i2][->][[H [S1 S2]]] _ D.
  split; first by apply: fr_pre.
  split=>y m; case/(locality D H)=>m1 [->][_]; [move/S1 | move/S2];
  by apply: fr_pre.
rewrite {i}E1 /= in H1 D2.
case: H1=>[[x]|[x]][h1][];
case/(locality D2 H2)=>m1 [->][D3] T1; move: (T1);
[move/H3 | move/H4]=>T'; case/(locality D3 T')=>m2 [->][D4] T2;
exists m2; do 2!split=>//; [left | right];
by exists x; exists m1.
Qed.

Definition try : STsep try_s := Model.Do (Model.try e e1 e2) tryP.

End SepTry.

Section SepFix.
Variables (A : Type) (B : A -> Type) (s : forall x, spec (B x)).
Notation tp := (forall x, STsep (s x)).

Definition Fix (f : tp -> tp) : tp := Model.ffix f.

End SepFix.

(* Conditionals for various types *)

Section CondBool.
Variables (A : Type) (b : bool) (s1 s2 : spec A).

Program
Definition If (e1 : STsep s1) (e2 : STsep s2) : STsep (if b then s1 else s2) :=
  match b with true => Do e1 | false => Do e2 end.

End CondBool.

Section CondOption.
Variable (A B : Type) (x : option A) (s1 : spec B) (s2 : A -> spec B).

Program
Definition Match_opt (e1 : STsep s1) (e2 : forall v, STsep (s2 v)) :
             STsep (match x with Some v => s2 v | None => s1 end) :=
  match x with Some v => Do (e2 v) | None => Do e1 end.

End CondOption.

Section CondDecide.
Variable (A : Type) (p1 p2 : Prop) (b : {p1} + {p2})
         (s1 : p1 -> spec A) (s2 : p2 -> spec A).

Program
Definition Match_dec (e1 : forall x, STsep (s1 x))
                     (e2 : forall x, STsep (s2 x)) :
             STsep (match b with left x => s1 x | right x => s2 x end) :=
  match b with left x => Do (e1 x) | right x => Do (e2 x) end.

End CondDecide.

Section CondNat.
Variable (A : Type) (n : nat) (s1 : spec A) (s2 : nat -> spec A).

Program
Definition Match_nat (e1 : STsep s1) (e2 : forall n, STsep (s2 n)) :
             STsep (match n with 0 => s1 | m.+1 => s2 m end) :=
  match n with 0 => Do e1 | m.+1 => Do (e2 m) end.

End CondNat.

Section CondSeq.
Variable (A B : Type) (s : seq A) (s1 : spec B) (s2 : A -> seq A -> spec B).

Program
Definition Match_seq (e1 : STsep s1) (e2 : forall hd tl, STsep (s2 hd tl)) :
             STsep (match s with [::] => s1 | hd::tl => s2 hd tl end) :=
  match s with [::] => Do e1 | hd::tl => Do (e2 hd tl) end.

End CondSeq.

(******************************************)
(* Lemmas for pulling out ghost variables *)
(******************************************)

Section Ghosts.
Variables (A : Type) (s : spec A) (p : pre).

Lemma allC (B1 B2 : Type) (q : B1 -> B2 -> post A) :
       conseq s p (fun y i m => forall x1 x2, q x1 x2 y i m) <->
       conseq s p (fun y i m => forall x, q x.1 x.2 y i m).
Proof.
split=>H1 i H2 D1; case: (H1 i H2 D1)=>S1 S2.
- by split=>// y m H D [x1 x2]; apply: S2.
by split=>// y m H D x1 x2; apply: (S2 y m H D (x1, x2)).
Qed.

Lemma impC (B : Type) (q1 q2 : heap -> B -> Prop) (r : B -> post A) :
        conseq s p (fun y i m => forall x, q1 i x -> q2 i x -> r x y i m) <->
        conseq s p (fun y i m => forall x, q1 i x /\ q2 i x -> r x y i m).
Proof.
split=>H1 i H2 D1; case: (H1 i H2 D1)=>S1 S2.
- by split=>// y m H D x []; apply: S2.
by split=>// *; apply: S2.
Qed.

Lemma ghE (B : Type) (q : heap -> B -> Prop) (r : B -> post A) :
        (forall i, p i -> def i -> exists x, q i x) ->
        (forall i x, q i x -> p i -> def i ->
           verify s i (fun y m => r x y i m)) ->
        conseq s p (fun y i m => forall x, q i x -> r x y i m).
Proof.
move=>H1 H2 i H3 D1; case: (H1 i H3 D1)=>x H4.
case: (H2 i x H4 H3 D1 D1)=>H5 _; split=>// y m H6 D2 z H7.
by case: (H2 i z H7 H3 D1 D1)=>_; apply.
Qed.

End Ghosts.

Definition gh := (allC, impC).

Notation "x '<--' c1 ';' c2" := (bind c1 (fun x => c2))
  (at level 78, right associativity) : stsep_scope.
Notation "c1 ';;' c2" := (bind c1 (fun _ => c2))
  (at level 78, right associativity) : stsep_scope.
Notation "'!' x" := (read _ x) (at level 50) : stsep_scope.
Notation "e1 '::=' e2" := (write e1 e2) (at level 60) : stsep_scope.
Notation "'throw' [ t ] E" := (throw t E)
  (at level 70, no associativity) : stsep_scope.
Notation "'ttry' E 'then' [ r ] E1 'else' [ x ] E2" :=
  (try E (fun r => E1) (fun x => E2)) (at level 80) : stsep_scope.
Notation "'ttry' E 'then' [ r ] E1 'else' E2" :=
  (try E (fun r => E1) (fun _ => E2)) (at level 80) : stsep_scope.
Notation "'ttry' E 'then' E1 'else' [ x ] E2" :=
  (try E (fun _ => E1) (fun x => E2)) (at level 80) : stsep_scope.
Notation "'ttry' E 'then' E1 'else' E2" :=
  (try E (fun _ => E1) (fun _ => E2)) (at level 80) : stsep_scope.
Notation "'match_opt' E 'then' E1 'else' [ x ] E2" :=
  (Match_opt E E1 (fun x => E2)) (at level 80) : stsep_scope.
Notation "'match_opt' E 'then' E1 'else' [ x ] E2" :=
  (Match_opt E E1 (fun x => E2)) (at level 80) : stsep_scope.
Notation "'If' E 'then' E1 'else' E2" :=
  (If E E1 E2) (at level 80) : stsep_scope.

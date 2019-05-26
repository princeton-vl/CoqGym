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
Require Import ssreflect ssrbool seq ssrfun.
From LemmaOverloading
Require Import heaps rels hprop stmod stsep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma bnd_is_try (A B : Type) (s1 : spec A) (s2 : A -> spec B) i r :
        verify (try_s s1 s2 (fun y => fr (throw_s B y))) i r ->
        verify (bind_s s1 s2) i r.
Proof.
move=>H; apply: frame0=>D.
case: {H D} (H D) (D)=>[[i1]][i2][->][[H1 [H2 H3]]] _ T D.
split=>[|y m].
- split=>[|x m]; first by apply: fr_pre H1.
  by case/(locality D H1)=>m1 [->][_]; move/H2; apply: fr_pre.
move=>{D} H; apply: T=>h1 h2 E.
rewrite {i1 i2 H1 H2 H3}E in H * => D1 [H1][H2] H3.
case: H=>[[x][h][]|[e][->]]; move/(locality D1 H1);
case=>[m1][->][D2] T1; move: (T1); [move/H2 | move/H3]=>H4.
- move=>T2; case/(locality D2 H4): (T2)=>m3 [->][D3].
  by exists m3; do !split=>//; left; exists x; exists m1.
exists m1; do !split=>//; right; exists e; exists m1; split=>//.
move=>j1 j2 E D _; rewrite {m1 D2}E in T1 D H4 *.
exists j1; do !split=>//; move=>k1 k2 -> D2 ->.
by exists empty; rewrite un0h; do !split=>//; apply: defUnr D2.
Qed.

Local Notation cont A := (ans A -> heap -> Prop).

Section EvalDo.
Variables (A B : Type).

Lemma val_do (s : spec A) i j (r : cont A) :
         s.1 i ->
         (forall x m, s.2 (Val x) i m -> def (m :+ j) -> r (Val x) (m :+ j)) ->
         (forall e m, s.2 (Exn e) i m -> def (m :+ j) -> r (Exn e) (m :+ j)) ->
         verify s (i :+ j) r.
Proof.
move=>H1 H2 H3; apply: frame; apply: frame0; split=>//.
by case=>x m H4 D1 D2; [apply: H2 | apply: H3].
Qed.

Lemma try_do (s : spec A) s1 s2 i j (r : cont B) :
        s.1 i ->
        (forall x m, s.2 (Val x) i m -> verify (s1 x) (m :+ j) r) ->
        (forall e m, s.2 (Exn e) i m -> verify (s2 e) (m :+ j) r) ->
        verify (try_s s s1 s2) (i :+ j) r.
Proof.
move=>H1 H2 H3; apply: frame0=>D; split=>[|y m].
- split; first by apply: fr_pre; exists i; exists empty; rewrite unh0.
  by split=>y m; case/(_ i j (erefl _) D H1)=>m1 [->][D2]; [case/H2 | case/H3].
by case=>[[x]|[e]][h][]; case/(_ i j (erefl _) D H1)=>m1 [->][D2];
   [case/H2 | case/H3]=>// _; apply.
Qed.

Lemma bnd_do (s : spec A) s2 i j (r : cont B) :
        s.1 i ->
        (forall x m, s.2 (Val x) i m -> verify (s2 x) (m :+ j) r) ->
        (forall e m, s.2 (Exn e) i m -> def (m :+ j) -> r (Exn e) (m :+ j)) ->
        verify (bind_s s s2) (i :+ j) r.
Proof.
move=>H1 H2 H3; apply: bnd_is_try.
apply: try_do=>// e m H4; apply: frame0; apply: frame1=>_.
by split=>// y m1 [->] -> _; rewrite un0h; apply: H3.
Qed.

End EvalDo.

Section EvalReturn.
Variables (A B : Type).

Lemma val_ret v i (r : cont A) :
       (def i -> r (Val v) i) -> verify (ret_s v) i r.
Proof.
by rewrite -[i]un0h=>H; apply: val_do=>// x m [->] // [->].
Qed.

Lemma try_ret s1 s2 (v : A) i (r : cont B) :
        verify (s1 v) i r -> verify (try_s (ret_s v) s1 s2) i r.
Proof.
by rewrite -[i]un0h=>H; apply: try_do=>// x m [->] // [->].
Qed.

Lemma bnd_ret s (v : A) i (r : cont B) :
        verify (s v) i r -> verify (bind_s (ret_s v) s) i r.
Proof. by move=>H; apply: bnd_is_try; apply: try_ret. Qed.

End EvalReturn.

Section EvalRead.
Variables (A B : Type).

Lemma val_read v x i (r : cont A) :
        (def (x :-> v :+ i) -> r (Val v) (x :-> v :+ i)) ->
        verify (read_s A x) (x :-> v :+ i) r.
Proof.
move=>*; apply: val_do; first by [exists v];
by move=>y m [<-]; move/(_ v (erefl _))=>// [->].
Qed.

Lemma try_read s1 s2 v x i (r : cont B) :
        verify (s1 v) (x :-> v :+ i) r ->
        verify (try_s (read_s A x) s1 s2) (x :-> v :+ i) r.
Proof.
move=>*; apply: try_do; first by [exists v];
by move=>y m [<-]; move/(_ v (erefl _))=>// [->].
Qed.

Lemma bnd_read s v x i (r : cont B) :
        verify (s v) (x :-> v :+ i) r ->
        verify (bind_s (read_s A x) s) (x :-> v :+ i) r.
Proof. by move=>*; apply: bnd_is_try; apply: try_read. Qed.

End EvalRead.

Section EvalWrite.
Variables (A B C : Type).

Lemma val_write (v : A) (w : B) x i (r : cont unit) :
        (def (x :-> v :+ i) -> r (Val tt) (x :-> v :+ i)) ->
        verify (write_s x v) (x :-> w :+ i) r.
Proof.
move=>*; apply: val_do; first by [exists B; exists w];
by move=>y m [// [->] ->].
Qed.

Lemma try_write s1 s2 (v: A) (w : C) x i (r : cont B) :
        verify (s1 tt) (x :-> v :+ i) r ->
        verify (try_s (write_s x v) s1 s2) (x :-> w :+ i) r.
Proof.
move=>*; apply: try_do; first by [exists C; exists w];
by move=>y m [// [->] ->].
Qed.

Lemma bnd_write s (v : A) (w : C) x i (r : cont B) :
        verify (s tt) (x :-> v :+ i) r ->
        verify (bind_s (write_s x v) s) (x :-> w :+ i) r.
Proof. by move=>*; apply: bnd_is_try; apply: try_write. Qed.

End EvalWrite.

Section EvalAlloc.
Variables (A B : Type).

Lemma val_alloc (v : A) i (r : cont ptr) :
        (forall x, def (x :-> v :+ i) -> r (Val x) (x :-> v :+ i)) ->
        verify (alloc_s v) i r.
Proof.
move=>H; rewrite -[i]un0h; apply: val_do=>//;
by move=>y m [x][//][-> ->]; apply: H.
Qed.

Lemma try_alloc s1 s2 (v : A) i (r : cont B) :
        (forall x, verify (s1 x) (x :-> v :+ i) r) ->
        verify (try_s (alloc_s v) s1 s2) i r.
Proof.
move=>H; rewrite -[i]un0h; apply: try_do=>//;
by move=>y m [x][//][-> ->]; apply: H.
Qed.

Lemma bnd_alloc s (v : A) i (r : cont B) :
        (forall x, verify (s x) (x :-> v :+ i) r) ->
        verify (bind_s (alloc_s v) s) i r.
Proof. by move=>*; apply: bnd_is_try; apply: try_alloc. Qed.

End EvalAlloc.

Section EvalBlockAlloc.
Variables (A B : Type).

Lemma val_allocb (v : A) n i (r : cont ptr) :
        (forall x, def (updi x (nseq n v) :+ i) ->
           r (Val x) (updi x (nseq n v) :+ i)) ->
        verify (allocb_s v n) i r.
Proof.
move=>H; rewrite -[i]un0h; apply: val_do=>//;
by move=>y m [x][//][->]->; apply: H.
Qed.

Lemma try_allocb s1 s2 (v : A) n i (r : cont B) :
        (forall x, verify (s1 x) (updi x (nseq n v) :+ i) r) ->
        verify (try_s (allocb_s v n) s1 s2) i r.
Proof.
move=>H; rewrite -[i]un0h; apply: try_do=>//;
by move=>y m [x][//][->]->; apply: H.
Qed.

Lemma bnd_allocb s (v : A) n i (r : cont B) :
        (forall x, verify (s x) (updi x (nseq n v) :+ i) r) ->
        verify (bind_s (allocb_s v n) s) i r.
Proof. by move=>*; apply: bnd_is_try; apply: try_allocb. Qed.

End EvalBlockAlloc.

Section EvalDealloc.
Variables (A B : Type).

Lemma val_dealloc (v : A) x i (r : cont unit) :
        (def i -> r (Val tt) i) ->
        verify (dealloc_s x) (x :-> v :+ i) r.
Proof.
move=>H; apply: val_do; first by [exists A; exists v];
by move=>y m [//][->] ->; rewrite un0h.
Qed.

Lemma try_dealloc s1 s2 (v : B) x i (r : cont A) :
        verify (s1 tt) i r ->
        verify (try_s (dealloc_s x) s1 s2) (x :-> v :+ i) r.
Proof.
move=>H; apply: try_do; first by [exists B; exists v];
by move=>y m [//][->] ->; rewrite un0h.
Qed.

Lemma bnd_dealloc s (v : B) x i (r : cont A) :
        verify (s tt) i r ->
        verify (bind_s (dealloc_s x) s) (x :-> v :+ i) r.
Proof. by move=>*; apply: bnd_is_try; apply: try_dealloc. Qed.

End EvalDealloc.

Section EvalThrow.
Variables (A B : Type).

Lemma val_throw e i (r : cont A) :
        (def i -> r (Exn e) i) -> verify (throw_s A e) i r.
Proof.
move=>H; rewrite -[i]un0h; apply: val_do=>//;
by move=>y m [->] // [->]; rewrite un0h.
Qed.

Lemma try_throw s1 s2 e i (r : cont B) :
        verify (s2 e) i r ->
        verify (try_s (throw_s A e) s1 s2) i r.
Proof.
move=>H; rewrite -[i]un0h; apply: try_do=>//;
by move=>y m [->] // [->]; rewrite un0h.
Qed.

Lemma bnd_throw s e i (r : cont B) :
        (def i -> r (Exn e) i) ->
        verify (bind_s (throw_s A e) s) i r.
Proof.
move=>H; apply: bnd_is_try; apply: try_throw; apply: frame0.
by rewrite -[i]un0h; apply: val_do=>// y m [->] // [->]; rewrite un0h.
Qed.

End EvalThrow.

(* specialized versions of do lemmas, to handle ghost variables. *)

Section EvalGhost.
Variables (A B C : Type) (t : C) (p : C -> Pred heap) (q : C -> post A).
Variables (s1 : A -> spec B) (s2 : exn -> spec B) (i j : heap) (P : Pred heap).

Lemma val_gh (r : cont A) :
        let: s := (fun i => exists x, i \In p x,
                   fun y i m => forall x, i \In p x -> q x y i m) in
        (forall x m, q t (Val x) i m -> def (m :+ j) -> r (Val x) (m :+ j)) ->
        (forall e m, q t (Exn e) i m -> def (m :+ j) -> r (Exn e) (m :+ j)) ->
        i \In p t ->
        verify s (i :+ j) r.
Proof. by move=>*; apply: val_do=>/=; eauto. Qed.

Lemma val_gh1 (r : cont A) :
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in
        (i \In p t -> P i) ->
        (forall x m, q t (Val x) i m -> def (m :+ j) -> r (Val x) (m :+ j)) ->
        (forall e m, q t (Exn e) i m -> def (m :+ j) -> r (Exn e) (m :+ j)) ->
        i \In p t ->
        verify (P, Q) (i :+ j) r.
Proof. by move=>*; apply: val_do=>/=; eauto. Qed.

Lemma try_gh (r : cont B) :
        let: s := (fun i => exists x, i \In p x,
                   fun y i m => forall x, i \In p x -> q x y i m) in
        (forall x m, q t (Val x) i m -> verify (s1 x) (m :+ j) r) ->
        (forall e m, q t (Exn e) i m -> verify (s2 e) (m :+ j) r) ->
        i \In p t ->
        verify (try_s s s1 s2) (i :+ j) r.
Proof. by move=>*; apply: try_do=>/=; eauto. Qed.

Lemma try_gh1 (r : cont B) :
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in
        (i \In p t -> P i) ->
        (forall x m, q t (Val x) i m -> verify (s1 x) (m :+ j) r) ->
        (forall e m, q t (Exn e) i m -> verify (s2 e) (m :+ j) r) ->
        i \In p t ->
        verify (try_s (P, Q) s1 s2) (i :+ j) r.
Proof. by move=>*; apply: try_do=>/=; eauto. Qed.

Lemma bnd_gh (r : cont B) :
        let: s := (fun i => exists x, i \In p x,
                   fun y i m => forall x, i \In p x -> q x y i m) in
        (forall x m, q t (Val x) i m -> verify (s1 x) (m :+ j) r) ->
        (forall e m, q t (Exn e) i m -> def (m :+ j) -> r (Exn e) (m :+ j)) ->
        i \In p t ->
        verify (bind_s s s1) (i :+ j) r.
Proof. by move=>*; apply: bnd_do=>/=; eauto. Qed.

Lemma bnd_gh1 (r : cont B) :
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in
        (i \In p t -> P i) ->
        (forall x m, q t (Val x) i m -> verify (s1 x) (m :+ j) r) ->
        (forall e m, q t (Exn e) i m -> def (m :+ j) -> r (Exn e) (m :+ j)) ->
        i \In p t ->
        verify (bind_s (P, Q) s1) (i :+ j) r.
Proof. by move=>*; apply: bnd_do=>/=; eauto. Qed.

End EvalGhost.

(*****************************************************************************)
(* associativity lemmas should go here, but I don't want to bother right now *)
(*****************************************************************************)

(* packaging up the lemmas into a tactic that selects them appropriately *)

Definition pull (A : Type) x (v:A) := (unC (x :-> v), unCA (x :-> v)).
Definition push (A : Type) x (v:A) := (unCA (x :-> v), unC (x :-> v)).

Ltac hstep :=
  match goal with
    | |- verify ?h (ret_s _) _ =>
      apply: val_ret
    | |- verify ?h (try_s (ret_s _) _ _) _ =>
      apply: try_ret
    | |- verify ?h (bind_s (ret_s _) _) _ =>
      apply: bnd_ret

    | |- verify ?h (read_s _ ?l) _ =>
      rewrite -?(pull l); apply: val_read
    | |- verify ?h (try_s (read_s _ ?l) _ _) _ =>
      rewrite -?(pull l); apply: try_read
    | |- verify (?h) (bind_s (read_s _ ?l) _) _ =>
      rewrite -?(pull l); apply: bnd_read

    | |- verify (?h) (write_s ?l _) _ =>
      rewrite -?(pull l); apply: val_write
    | |- verify (?h) (try_s (write_s ?l _) _ _) _ =>
      rewrite -?(pull l); apply: try_write
    | |- verify (?h) (bind_s (write_s ?l _) _) _ =>
      rewrite -?(pull l); apply: bnd_write

    | |- verify ?h (alloc_s _) _ =>
      apply: val_alloc
    | |- verify ?h (try_s (alloc_s _) _ _) _ =>
      apply: try_alloc
    | |- verify ?h (bind_s (alloc_s _) _) _ =>
      apply: bnd_alloc

    | |- verify ?h (allocb_s _ _) _ =>
      apply: val_allocb
    | |- verify ?h (try_s (allocb_s _ _) _ _) _ =>
      apply: try_allocb
    | |- verify ?h (bind_s (allocb_s _ _) _) _ =>
      apply: bnd_allocb

    | |- verify ?h (dealloc_s ?l) _ =>
      rewrite -?(pull l); apply: val_dealloc
    | |- verify ?h (try_s (dealloc_s ?l) _ _) _ =>
      rewrite -?(pull l); apply: try_dealloc
    | |- verify ?h (bind_s (dealloc_s ?l) _) _ =>
      rewrite -?(pull l); apply: bnd_dealloc

    | |- verify ?h (throw_s _ _) _ =>
      apply: val_throw
    | |- verify ?h (try_s (throw_s _ _) _ _) _ =>
      apply: try_throw
    | |- verify ?h (bind_s (throw_s _ _) _) _ =>
      apply: bnd_throw
  end.

Lemma swp : forall (A : Type) (v : A) x h, h \In x :--> v <-> h = x :-> v.
Proof. by move=>A v x h; split; rewrite InE /pts /=; unlock. Qed.

Lemma opn : forall (A : Type) (v : A) x h, h \In x :--> v <-> x :-> v = h.
Proof. by move=>A v x h; split=>[|H]; rewrite InE /= /pts; unlock. Qed.

Prenex Implicits swp opn.


Lemma blah (A : Type) (p : ptr) (l : A) : def (p :-> l) -> (p :-> l) \In p :--> l.
Proof. by move=>H; apply/swp. Qed.

Hint Immediate blah : core.

Lemma blah2 (A : Type) (v1 v2 : A) q :
        def (q :-> v1) -> v1 = v2 -> q :-> v1 \In q :--> v2.
Proof. by move=>D E; apply/swp; rewrite E. Qed.

Hint Immediate blah2 : core.

Ltac hauto := (do ?econstructor=>//;
                try by [defcheck; auto |
                       eapply blah2; defcheck; auto])=>//.

Ltac hhauto := (do ?econstructor=>//; try by [heap_congr])=>//.
Ltac hdone := repeat progress hhauto=>//=.
Ltac heval := do ![hstep | by hhauto].

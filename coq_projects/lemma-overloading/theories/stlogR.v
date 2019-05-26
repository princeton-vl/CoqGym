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
Require Import ssreflect ssrbool ssrfun.
From LemmaOverloading
Require Import heaps rels stmod stsep stlog.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* This file contains several lemmas automated with canonical structures to   *)
(* verify programs with HTT                                                   *)
(******************************************************************************)


(*************************************************************************)
(* First, the mechanism for search-and-replace for the overloaded lemas, *)
(* pattern-matching on heap expressions.                                 *)
(*************************************************************************)

Structure tagged_heap := Tag {untag :> heap}.

Definition right_tag := Tag.
Definition left_tag := right_tag.
Canonical Structure found_tag i := left_tag i.

Definition update_axiom k r (h : tagged_heap) := untag h = k :+ r.

Structure update (k r : heap) :=
  Update {heap_of :> tagged_heap;
        _ : update_axiom k r heap_of}.

Lemma updateE r k (f : update k r) : untag f = k :+ r.
Proof. by case: f=>[[j]] /=; rewrite /update_axiom /= => ->. Qed.

Lemma found_pf k : update_axiom k empty (found_tag k).
Proof. by rewrite /update_axiom unh0. Qed.

Canonical Structure found_struct k := Update (found_pf k).

Lemma left_pf h r (f : forall k, update k r) k :
        update_axiom k (r :+ h) (left_tag (f k :+ h)).
Proof. by rewrite updateE /update_axiom /= unA. Qed.

Canonical Structure left_struct h r (f : forall k, update k r) k :=
  Update (left_pf h f k).

Lemma right_pf h r (f : forall k, update k r) k :
        update_axiom k (h :+ r) (right_tag (h :+ f k)).
Proof. by rewrite updateE /update_axiom /= unCA. Qed.

Canonical Structure right_struct h r (f : forall k, update k r) k :=
  Update (right_pf h f k).

(*********************)
(* Overloaded lemmas *)
(*********************)

Notation cont A := (ans A -> heap -> Prop).

Section EvalDoR.
Variables (A B : Type).

Lemma val_doR (s : spec A) i j (f : forall k, update k j) (r : cont A) :
         s.1 i ->
         (forall x m, s.2 (Val x) i m -> def (f m) -> r (Val x) (f m)) ->
         (forall e m, s.2 (Exn e) i m -> def (f m) -> r (Exn e) (f m)) ->
         verify s (f i) r.
Proof.
move=>H1 H2 H3; rewrite updateE; apply: (val_do H1).
- by move=>x m; move: (H2 x m); rewrite updateE.
by move=>x m; move: (H3 x m); rewrite updateE.
Qed.

Lemma try_doR (s : spec A) s1 s2 i j (f : forall k, update k j) (r : cont B) :
        s.1 i ->
        (forall x m, s.2 (Val x) i m -> verify (s1 x) (f m) r) ->
        (forall e m, s.2 (Exn e) i m -> verify (s2 e) (f m) r) ->
        verify (try_s s s1 s2) (f i) r.
Proof.
move=>H1 H2 H3; rewrite updateE; apply: (try_do H1).
- by move=>x m; move: (H2 x m); rewrite updateE.
by move=>x m; move: (H3 x m); rewrite updateE.
Qed.

Lemma bnd_doR (s : spec A) s2 i j (f : forall k, update k j) (r : cont B) :
        s.1 i ->
        (forall x m, s.2 (Val x) i m -> verify (s2 x) (f m) r) ->
        (forall e m, s.2 (Exn e) i m -> def (f m) -> r (Exn e) (f m)) ->
        verify (bind_s s s2) (f i) r.
Proof.
move=>H1 H2 H3; rewrite updateE; apply: (bnd_do H1).
- by move=>x m; move: (H2 x m); rewrite updateE.
by move=>x m; move: (H3 x m); rewrite updateE.
Qed.

End EvalDoR.

(* ret lemmas need no reflection, as they operate on any heap; still *)
(* rename them for uniformity *)

Definition val_retR := val_ret.
Definition try_retR := try_ret.
Definition bnd_retR := bnd_ret.

Section EvalReadR.
Variables (A B : Type).

Lemma val_readR v x i (f : update (x :-> v) i) (r : cont A) :
        (def f -> r (Val v) f) ->
        verify (read_s A x) f r.
Proof. by rewrite updateE; apply: val_read. Qed.

Lemma try_readR s1 s2 v x i (f : update (x :-> v) i) (r : cont B) :
        verify (s1 v) f r ->
        verify (try_s (read_s A x) s1 s2) f r.
Proof. by rewrite updateE; apply: try_read. Qed.

Lemma bnd_readR s v x i (f : update (x :-> v) i) (r : cont B) :
        verify (s v) f r ->
        verify (bind_s (read_s A x) s) f r.
Proof. by rewrite updateE; apply: bnd_read. Qed.

End EvalReadR.

Section EvalWriteR.
Variables (A B C : Type).

Lemma val_writeR (v : A) (w : B) x i (f : forall k, update k i) (r : cont unit) :
        (def (f (x :-> v)) -> r (Val tt) (f (x :-> v))) ->
        verify (write_s x v) (f (x :-> w)) r.
Proof. by rewrite !updateE; apply: val_write. Qed.

Lemma try_writeR s1 s2 (v : A) (w : C) x i
                 (f : forall k, update k i) (r : cont B) :
        verify (s1 tt) (f (x :-> v)) r ->
        verify (try_s (write_s x v) s1 s2) (f (x :-> w)) r.
Proof. rewrite !updateE; apply: try_write. Qed.

Lemma bnd_writeR s (v : A) (w : C) x i (f : forall k, update k i) (r : cont B) :
        verify (s tt) (f (x :-> v)) r ->
        verify (bind_s (write_s x v) s) (f (x :-> w)) r.
Proof. by rewrite !updateE; apply: bnd_write. Qed.

End EvalWriteR.

Definition val_allocR := val_alloc.
Definition try_allocR := try_alloc.
Definition bnd_allocR := bnd_alloc.
Definition val_allocbR := val_allocb.
Definition try_allocbR := try_allocb.
Definition bnd_allocbR := bnd_allocb.

Section EvalDeallocR.
Variables (A B : Type).

Lemma val_deallocR (v : A) x i (f : forall k, update k i) (r : cont unit) :
        (def (f empty) -> r (Val tt) (f empty)) ->
        verify (dealloc_s x) (f (x :-> v)) r.
Proof. by rewrite !updateE un0h; apply: val_dealloc. Qed.

Lemma try_deallocR s1 s2 (v : B) x i (f : forall k, update k i) (r : cont A) :
        verify (s1 tt) (f empty) r ->
        verify (try_s (dealloc_s x) s1 s2) (f (x :-> v)) r.
Proof. by rewrite !updateE un0h; apply: try_dealloc. Qed.

Lemma bnd_deallocR s (v : B) x i (f : forall k, update k i) (r : cont A) :
        verify (s tt) (f empty) r ->
        verify (bind_s (dealloc_s x) s) (f (x :-> v)) r.
Proof. by rewrite !updateE un0h; apply: bnd_dealloc. Qed.

End EvalDeallocR.

Definition val_throwR := val_throw.
Definition try_throwR := try_throw.
Definition bnd_throwR := bnd_throw.

(* specialized versions of do lemmas, to handle ghost variables. *)

Section EvalGhostR.
Variables (A B C : Type) (t : C) (p : C -> Pred heap) (q : C -> post A).
Variables (s1 : A -> spec B) (s2 : exn -> spec B) (i j : heap).
Variables (f : forall k, update k j) (P : Pred heap).

Lemma val_ghR (r : cont A) :
        let: s := (fun i => exists x, i \In p x,
                   fun y i m => forall x, i \In p x -> q x y i m) in
        (forall x m, q t (Val x) i m -> def (f m) -> r (Val x) (f m)) ->
        (forall e m, q t (Exn e) i m -> def (f m) -> r (Exn e) (f m)) ->
        i \In p t ->
        verify s (f i) r.
Proof.
move=>H1 H2; rewrite updateE; apply: val_gh.
- by move=>x m; move: (H1 x m); rewrite updateE.
by move=>x m; move: (H2 x m); rewrite updateE.
Qed.

Lemma val_gh1R (r : cont A) :
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in
        (i \In p t -> P i) ->
        (forall x m, q t (Val x) i m -> def (f m) -> r (Val x) (f m)) ->
        (forall e m, q t (Exn e) i m -> def (f m) -> r (Exn e) (f m)) ->
        i \In p t ->
        verify (P, Q) (f i) r.
Proof.
move=>H1 H2 H3; rewrite updateE; apply: (val_gh1 H1).
- by move=>x m; move: (H2 x m); rewrite updateE.
by move=>x m; move: (H3 x m); rewrite updateE.
Qed.

Lemma try_ghR (r : cont B) :
        let: s := (fun i => exists x, i \In p x,
                   fun y i m => forall x, i \In p x -> q x y i m) in
        (forall x m, q t (Val x) i m -> verify (s1 x) (f m) r) ->
        (forall e m, q t (Exn e) i m -> verify (s2 e) (f m) r) ->
        i \In p t ->
        verify (try_s s s1 s2) (f i) r.
Proof.
move=>H1 H2; rewrite updateE; apply: try_gh.
- by move=>x m; move: (H1 x m); rewrite updateE.
by move=>x m; move: (H2 x m); rewrite updateE.
Qed.

Lemma try_gh1R (r : cont B) :
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in
        (i \In p t -> P i) ->
        (forall x m, q t (Val x) i m -> verify (s1 x) (f m) r) ->
        (forall e m, q t (Exn e) i m -> verify (s2 e) (f m) r) ->
        i \In p t ->
        verify (try_s (P, Q) s1 s2) (f i) r.
Proof.
move=>H1 H2 H3; rewrite updateE; apply: (try_gh1 H1).
- by move=>x m; move: (H2 x m); rewrite updateE.
by move=>x m; move: (H3 x m); rewrite updateE.
Qed.

Lemma bnd_ghR (r : cont B) :
        let: s := (fun i => exists x, i \In p x,
                   fun y i m => forall x, i \In p x -> q x y i m) in
        (forall x m, q t (Val x) i m -> verify (s1 x) (f m) r) ->
        (forall e m, q t (Exn e) i m -> def (f m) -> r (Exn e) (f m)) ->
        i \In p t ->
        verify (bind_s s s1) (f i) r.
Proof.
move=>H1 H2; rewrite updateE; apply: bnd_gh.
- by move=>x m; move: (H1 x m); rewrite updateE.
by move=>x m; move: (H2 x m); rewrite updateE.
Qed.

Lemma bnd_gh1R (r : cont B) :
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in
        (i \In p t -> P i) ->
        (forall x m, q t (Val x) i m -> verify (s1 x) (f m) r) ->
        (forall e m, q t (Exn e) i m -> def (f m) -> r (Exn e) (f m)) ->
        i \In p t ->
        verify (bind_s (P, Q) s1) (f i) r.
Proof.
move=>H1 H2 H3; rewrite updateE; apply: (bnd_gh1 H1).
- by move=>x m; move: (H2 x m); rewrite updateE.
by move=>x m; move: (H3 x m); rewrite updateE.
Qed.

End EvalGhostR.

(****************************************************)
(* Automating the selection of which lemma to apply *)
(* (the hstep tactic made as an overloaded lemma    *)
(****************************************************)

(* Need to case-split on bnd_, try_, or a val_ lemma. *)
(* Hence, three classes of canonical structures.      *)

Structure val_form A i r (p : Prop):=
  ValForm {val_pivot :> spec A;
           _ : p -> verify val_pivot i r}.

Structure bnd_form A B i (s : A -> spec B) r (p : Prop) :=
  BndForm {bnd_pivot :> spec A;
           _ : p -> verify (bind_s bnd_pivot s) i r}.

Structure try_form A B i (s1 : A -> spec B)
                         (s2 : exn -> spec B) r (p : Prop) :=
  TryForm {try_pivot :> spec A;
           _ : p -> verify (try_s try_pivot s1 s2) i r}.

(* The main lemma which triggers the selection. *)
Definition hstep A i (r : cont A) p (e : val_form i r p) : p -> verify e i r :=
  let: ValForm _ pf := e in pf.

(* First check if matching on bnd_ or try_. If so, switch to searching *)
(* for bnd_ or try_form, respectively. Otherwise, fall through, and    *)
(* continue searching for a val_form. *)
Definition hstep_bnd A B i (s : A -> spec B) r p (e : bnd_form i s r p)
  : p -> verify (bind_s e s) i r
  := let: BndForm _ pf := e in pf.

Canonical Structure
  bnd_case_form A B i (s : A -> spec B) r p (e : bnd_form i s r p) :=
  ValForm (hstep_bnd e).

Lemma try_case_pf A B i (s1 : A -> spec B) (s2 : exn -> spec B) r p
                        (e : try_form i s1 s2 r p) :
        p -> verify (try_s e s1 s2) i r.
Proof. by case:e=>[?]; apply. Qed.

(* After that, find the form in the following list.  Notice that the list *)
(* can be extended arbitrarily in the future. There is no centralized     *)
(* tactic to maintain. *)

Canonical Structure val_ret_form A v i r :=
  ValForm (@val_retR A v i r).
Canonical Structure bnd_ret_form A B s v i r :=
  BndForm (@bnd_retR A B s v i r).
Canonical Structure try_ret_form A B s1 s2 v i r :=
  TryForm (@try_retR A B s1 s2 v i r).

Canonical Structure val_read_form A v x r j f :=
  ValForm (@val_readR A v x j f r).
Canonical Structure bnd_read_form A B s v x r j f :=
  BndForm (@bnd_readR A B s v x j f r).
Canonical Structure try_read_form A B s1 s2 v x r j f :=
  TryForm (@try_readR A B s1 s2 v x j f r).

Canonical Structure val_write_form A B v w x r j f :=
  ValForm (@val_writeR A B v w x j f r).
Canonical Structure bnd_write_form A B C s v w x r j f :=
  BndForm (@bnd_writeR A B C s v w x j f r).

Canonical Structure try_write_form A B C s1 s2 v w x r j f :=
  TryForm (@try_writeR A B C s1 s2 v w x j f r).

Canonical Structure val_alloc_form A v i r :=
  ValForm (@val_allocR A v i r).
Canonical Structure bnd_alloc_form A B s v i r :=
  BndForm (@bnd_allocR A B s v i r).
Canonical Structure try_alloc_form A B s1 s2 v i r :=
  TryForm (@try_allocR A B s1 s2 v i r).

Canonical Structure val_allocb_form A v n i r :=
  ValForm (@val_allocbR A v n i r).
Canonical Structure bnd_allocb_form A B s v n i r :=
  BndForm (@bnd_allocbR A B s v n i r).
Canonical Structure try_allocb_form A B s1 s2 v n i r :=
  TryForm (@try_allocbR A B s1 s2 v n i r).

Canonical Structure val_dealloc_form A v x r j f :=
  ValForm (@val_deallocR A v x j f r).
Canonical Structure bnd_dealloc_form A B s v x r j f :=
  BndForm (@bnd_deallocR A B s v x j f r).
Canonical Structure try_dealloc_form A B s1 s2 v x r j f :=
  TryForm (@try_deallocR A B s1 s2 v x j f r).

(* we still keep one tactic to kill final goals, which *)
(* are usually full of existentials *)
Ltac vauto := (do ?econstructor=>//).

Example ex_read x :
  verify (bind_s (write_s x 4) (fun _=> read_s _ x))
         (x :-> 0) (fun r _ => r = Val 4).
by do 2! [apply: hstep].
Abort.

Example ex_val_do (s : spec nat) (r : cont nat) (x y : ptr) :
         s.1 (y:->2) ->
         (forall x' m,
               s.2 (Val x') (y:->2) m -> def (x:->1:+m) -> r (Val x') (x:->1:+m)) ->
         (forall e m,
               s.2 (Exn e) (y:->2) m -> def (x:->1:+m) -> r (Exn e) (x:->1:+m)) ->
         verify s (x:->1 :+ y:->2) r.
move=>H1 H2 H3.
apply: (val_doR _ (i:=y:->2))=>//=.
Abort.

Example ex_bwd i x1 x2 (e : unit -> spec nat) q:
          verify (e tt) (i :+ (x1 :-> 1 :+ x2 :-> 4)) q ->
          verify (bind_s (write_s x2 4) e) (i :+ (x1 :-> 1 :+ x2 :-> 2)) q.
by move=>H; apply: bnd_writeR.
Abort.


Example ex_fwd i x1 x2 (e : unit -> spec nat) q:
          verify (e tt) (i :+ (x1 :-> 1 :+ x2 :-> 4)) q ->
          verify (bind_s (write_s x2 4) e) (i :+ (x1 :-> 1 :+ x2 :-> 2)) q.
move=>H.
apply: (bnd_writeR (x:=x2) H).
Abort.


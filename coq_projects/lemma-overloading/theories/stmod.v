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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From LemmaOverloading
Require Import prelude heaps rels hprop domains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Exceptions are an equality type *)
Inductive exn : Type := exn_from_nat : nat -> exn.

Definition exn_to_nat (e : exn) : nat :=
  let: exn_from_nat y := e in y.

Definition eqexn (e1 e2 : exn) : bool :=
  match e1, e2 with exn_from_nat m, exn_from_nat n => m == n end.

Lemma eqexnP : Equality.axiom eqexn.
Proof.
move=>[x][y]//=; case: eqP=>[->|*];constructor=>//.
by move=>[*].
Qed.

Canonical Structure exn_eqMixin := EqMixin eqexnP.
Canonical Structure exn_eqType := EqType exn exn_eqMixin.

(* Answer type *)
Inductive ans (A : Type) : Type := Val of A | Exn of exn.
Arguments Exn [A].

Notation pre := (Pred heap).
Notation post A := (ans A -> heap -> heap -> Prop).
Definition spec B := pre * post B : Type.

(********************************)
(* Definition of the Hoare type *)
(********************************)

Definition defed (P : Pred heap) : Pred heap :=
  fun i => i \In P /\ def i.

Notation ideald P := (ideal (defed P)).

Section BasePrograms.
Variables (A : Type) (P : Pred heap).

Lemma singleP i : i \In defed P -> this i <== defed P.
Proof. by move=>[pf1 pf2] h <-; split. Qed.

Definition single i (pf : i \In defed P) := Ideal (singleP pf).

Lemma bound (p : ideald P) i : i \In id_val p -> i \In defed P.
Proof. by case: p=>p H; case/H. Qed.

(* we carve out the model out of the following base type *)
Definition prog := ideald P -> ans A -> Pred heap.

(* we take progs with only special properties *)
(* which we defined next *)

(* coherence is continuity stated with *)
(* directed sets instead of chains *)
Definition coherent (e : prog) :=
  forall p x m,
    m \In e p x <-> exists i, exists pf : i \In id_val p,
                    m \In e (single (bound pf)) x.

(* defined heaps map to defined heaps *)
Definition def_strict (e : prog) := forall p x, Undef \Notin e p x.

(* set of program runs *)
Definition runs_of (e : prog) : Pred (heap * ans A * heap) :=
  fun r => exists pf : r.1.1 \In defed P, r.2 \In e (single pf) r.1.2.

End BasePrograms.

Definition has_spec A (s : spec A) :=
  [Pred c : prog A s.1 |
     forall i y m, (i, y, m) \In runs_of c -> s.2 y i m].

Section STDef.
Variables (A : Type) (s : spec A).

Structure ST := STprog {
  model : prog A s.1;
  _ : coherent model;
  _ : def_strict model;
  _ : model \In has_spec s}.

Lemma modelE (e1 e2 : ST) : e1 = e2 <-> model e1 = model e2.
Proof.
move: e1 e2=>[e1 M1 S1 H1][e2 M2 S2 H2] /=; split=>[[//]|E].
rewrite E in M1 S1 H1 *.
by congr STprog; apply: proof_irrelevance.
Qed.

(* poset structure on ST *)

Definition st_leq e1 e2 := model e1 <== model e2.

Lemma st_refl e : st_leq e e.
Proof. by []. Qed.

Lemma st_asym e1 e2 : st_leq e1 e2 -> st_leq e2 e1 -> e1 = e2.
Proof.
move: e1 e2=>[e1 M1 S1 H1][e2 M2 S2 H2]; rewrite /st_leq /= => E1 E2.
rewrite (poset_asym E1 E2) in M1 M2 S1 S2 H1 H2 *; congr STprog;
by apply: proof_irrelevance.
Qed.

Lemma st_trans e1 e2 e3 : st_leq e1 e2 -> st_leq e2 e3 -> st_leq e1 e3.
Proof.
move: e1 e2 e3=>[e1 M1 S1 H1][e2 M2 S2 H2][e3 M3 S3 H3].
by apply: poset_trans.
Qed.

Definition st_bot' := bot : [poset of prog A s.1].

Lemma st_bot_coherent : coherent st_bot'.
Proof. by move=>r x m; split=>//; case=>i []. Qed.

Lemma st_bot_dstrict : def_strict st_bot'.
Proof. by move=>r x. Qed.

Lemma st_bot_has_spec : st_bot' \In has_spec s.
Proof. by move=>i y m [/= H][]. Qed.

Definition st_bot := STprog st_bot_coherent st_bot_dstrict st_bot_has_spec.

Lemma st_botP e : st_leq st_bot e.
Proof. by case: e=>*; apply: botP. Qed.

Definition stPosetMixin := PosetMixin st_botP st_refl st_asym st_trans.
Canonical stPoset := Eval hnf in Poset ST stPosetMixin.

(* lattice structure on ST *)

Definition st_sup' (u : Pred ST) :=
  sup [Pred p | exists e, p = model e /\ e \In u].

Lemma st_sup_coherent u : coherent (st_sup' u).
Proof.
move=>r x m; split.
- case=>_ [[_]][[_]][[_]][[]][p] M S H [->] P -> -> -> /=.
  case/M=>i [pf] H1.
  exists i; exists pf; exists (p (single (bound pf)) x m).
  split=>//; do 3![eexists _; split=>//].
  by exists (STprog M S H).
case=>i [pf][_][[_]][[_]][[_]][[]][p] M D H [->] P -> -> -> /= E.
have: exists i, exists pf : i \In id_val r, m \In p (single (bound pf)) x.
- by exists i; exists pf.
move/M=>H3; exists (p r x m); split=>//; do 3![eexists _; split=>//].
by exists (STprog M D H).
Qed.

Lemma st_sup_dstrict u : def_strict (st_sup' u).
Proof.
by move=>p x [_][[_]][[_]][[_]][[]][r] M D H [->] P -> -> -> /=; move/D.
Qed.

Lemma st_sup_has_spec u : st_sup' u \In has_spec s.
Proof.
move=>i y m [/= D].
case=>_ [[_]][[_]][[_]][[]][p] M S H [->] P -> -> -> /= R.
by apply: (H); exists D.
Qed.

Definition st_sup u :=
  STprog (@st_sup_coherent u) (@st_sup_dstrict u) (@st_sup_has_spec u).

Lemma st_supP (u : Pred ST) e : e \In u -> st_leq e (st_sup u).
Proof. by case: e=>p M S H R; apply: supP; exists (STprog M S H). Qed.

Lemma st_supM (u : Pred ST) e :
        (forall e1, e1 \In u -> st_leq e1 e) -> st_leq (st_sup u) e.
Proof. by case: e=>p M S H R; apply: supM=>y [q][->]; apply: R. Qed.

Definition stLatticeMixin := LatticeMixin st_supP st_supM.
Canonical stLattice := Lattice ST stLatticeMixin.

(* In proofs, we keep goals in form (i, x, m) \In runs_of (model e). *)
(* We need a couple of lemmas about this form. *)

Lemma bot_runs : runs_of (model st_bot) =p Pred0.
Proof. by move=>r; split=>//; case. Qed.

Lemma model_runs p y m (e : ST) :
        m \In model e p y <->
        exists i, i \In id_val p /\ (i, y, m) \In runs_of (model e).
Proof.
case: e=>mod M S H; rewrite M; split; case=>i [H1] H2.
- by exists i; split=>//; exists (bound H1).
exists i; exists H1; case: H2 =>/= H2.
by rewrite (proof_irrelevance H2 (bound H1)).
Qed.

Lemma def_runs i y m (e : ST) :
        (i, y, m) \In runs_of (model e) -> [/\ def i, i \In s.1 & def m].
Proof.
case=>[[/= P D]] R; split=>//.
by case: e R=>p M S H; case: m=>//; move/S.
Qed.

Lemma spec_runs i y m (e : ST) :
        (i, y, m) \In runs_of (model e) -> s.2 y i m.
Proof. by case: e=>p M S; apply. Qed.

End STDef.

Arguments spec_runs {A s i y m}.
Prenex Implicits bot_runs model_runs def_runs.

(************************************)
(* modeling the language primitives *)
(************************************)

Module Model.

(* recursion *)
Section Fix.
Variables (A : Type) (B : A -> Type) (s : forall x, spec (B x)).
Notation tp := (forall x, ST (s x)).
Notation lat := (dfunLattice (fun x => [lattice of ST (s x)])).
Variable (f : tp -> tp).

(* we take a fixpoint not of f, but of its monotone completion f' *)
(* should eventually prove that f' is monotone *)

Definition f' (e : lat) :=
  sup [Pred t : lat | exists e', e' <== e /\ t = f e'].

Definition ffix : tp := tarski_lfp f'.

End Fix.

Section Return.
Variables (A : Type) (x : A).

Definition ret_s : spec A :=
  (fun i => True, fun y i m => m = i /\ y = Val x).

Definition ret_sp (p : ideald ret_s.1) y m :=
  m \In id_val p /\ y = Val x.

Lemma ret_coherent : coherent ret_sp.
Proof.
move=>p y m; split; first by case=>H ->{y}; exists m; exists H.
by case=>i [H1] [<-{m}] ->{y}.
Qed.

Lemma ret_dstrict : def_strict ret_sp.
Proof. by case=>p H y /= []; case/H. Qed.

Lemma ret_has_spec : ret_sp \In has_spec ret_s.
Proof. by move=>i y m; case=>/= T [-> ->]. Qed.

Definition ret := STprog ret_coherent ret_dstrict ret_has_spec.

End Return.


Section Throw.
Variables (A : Type) (e : exn).

Definition throw_s : spec A :=
  (fun i => True, fun y i m => m = i /\ y = Exn e).

Definition throw_sp (p : ideald throw_s.1) y m :=
  m \In id_val p /\ y = @Exn A e.

Lemma throw_coherent : coherent throw_sp.
Proof.
move=>p y m; split; first by case=>H ->{y}; exists m; exists H.
by case=>i [H1] [<-{m}] ->{y}.
Qed.

Lemma throw_dstrict : def_strict throw_sp.
Proof. by case=>p H y /= []; case/H. Qed.

Lemma throw_has_spec : throw_sp \In has_spec throw_s.
Proof. by move=>i y m; case=>/= T [-> ->]. Qed.

Definition throw := STprog throw_coherent throw_dstrict throw_has_spec.

End Throw.


Section Bind.
Variables (A B : Type).
Variables (s1 : spec A) (s2 : A -> spec B).
Variables (e1 : ST s1) (e2 : forall x, ST (s2 x)).

Definition bind_pre : pre :=
  fun i => s1.1 i /\ forall x m, s1.2 (Val x) i m -> (s2 x).1 m.
Definition bind_post : post B :=
  fun y i m => (exists x, exists h, s1.2 (Val x) i h /\ (s2 x).2 y h m) \/
               (exists e, y = Exn e /\ s1.2 (Exn e) i m).
Definition bind_s := (bind_pre, bind_post).

Definition bind_sp (p : ideald bind_s.1) y m :=
   exists i, exists x, exists h, i \In id_val p /\
     (i, x, h) \In runs_of (model e1) /\
     match x with
       Val x' => (h, y, m) \In runs_of (model (e2 x'))
     | Exn e => y = Exn e /\ m = h
     end.

Lemma bind_coherent : coherent bind_sp.
Proof.
case=>p H y m; split.
- case=>i [x][h][/= H1][H2] H3.
  by exists i; exists H1; exists i; exists x; exists h.
case=>i [/= H1][_][x][h][<-][T1 T2].
by exists i; exists x; exists h.
Qed.

Lemma bind_dstrict : def_strict bind_sp.
Proof.
move=>p y [i][x][h][H1][].
case: x=>[x'|e] H2; first by case/def_runs.
by case=>_ E; case/def_runs: H2; rewrite -E.
Qed.

Lemma bind_has_spec : bind_sp \In has_spec bind_s.
Proof.
move=>i y m.
case=>[[[/= S1 S2]]] D [h][x][j][<-][].
case: x=>[x|e] T1; last first.
- case=>->->; right; exists e; split=>//.
  by apply: spec_runs T1.
move=>T2; left; exists x; exists j.
by split; [apply: spec_runs T1 | apply: spec_runs T2].
Qed.

Definition bind := STprog bind_coherent bind_dstrict bind_has_spec.

End Bind.


Section Try.
Variables (A B : Type) (s : spec A) (s1 : A -> spec B) (s2 : exn -> spec B).
Variables (e : ST s) (e1 : forall x, ST (s1 x)) (e2 : forall x, ST (s2 x)).

Definition try_pre : pre :=
  fun i => s.1 i /\ (forall y m, s.2 (Val y) i m -> (s1 y).1 m) /\
                     forall e m, s.2 (Exn e) i m -> (s2 e).1 m.
Definition try_post : post B :=
  fun y i m => (exists x, exists h, s.2 (Val x) i h /\ (s1 x).2 y h m) \/
               (exists e, exists h, s.2 (Exn e) i h /\ (s2 e).2 y h m).
Definition try_s := (try_pre, try_post).

Definition try_sp (p : ideald try_s.1) y m :=
   exists i, exists x, exists h, i \In id_val p /\
     (i, x, h) \In runs_of (model e) /\
     match x with
       Val x' => (h, y, m) \In runs_of (model (e1 x'))
     | Exn e => (h, y, m) \In runs_of (model (e2 e))
     end.

Lemma try_coherent : coherent try_sp.
Proof.
case=>p H y m; split.
- case=>i [x][h][/= H1][H2] H3.
  by exists i; exists H1; exists i; exists x; exists h.
case=>i [/= H1][_][x][h][<-][T1 T2].
by exists i; exists x; exists h.
Qed.

Lemma try_dstrict : def_strict try_sp.
Proof.
move=>p y [i][x][h][H1][].
by case: x=>[x'|e'] H2; case/def_runs.
Qed.

Lemma try_has_spec : try_sp \In has_spec try_s.
Proof.
move=>i y m; case=>[[[/= S1 [S2 S3]]]] D [h][x][j][<-][].
case: x=>[x'|e'] T1 T2; [left; exists x' | right; exists e'];
exists j; by split; [apply: spec_runs T1 | apply: spec_runs T2].
Qed.

Definition try := STprog try_coherent try_dstrict try_has_spec.

End Try.


Definition conseq A (s1 s2 : spec A) :=
  forall i, s2.1 i -> def i ->
    s1.1 i /\ forall y m, s1.2 y i m -> def m -> s2.2 y i m.

Lemma conseq_refl (A : Type) (s : spec A) : conseq s s.
Proof. by []. Qed.

Hint Resolve conseq_refl : core.

Section Consequence.
Variables (A : Type) (s1 s2 : spec A) (e : ST s1) (pf : conseq s1 s2).

Definition do_sp (p : ideald s2.1) y m :=
  exists i, i \In id_val p /\ (i, y, m) \In runs_of (model e).

Lemma do_coherent : coherent do_sp.
Proof.
case=>q H y m; split.
- by case=>i [/= H1 T1]; exists i; exists H1; exists i.
by case=>i [/= H1][_][<-] T1; exists i.
Qed.

Lemma do_dstrict : def_strict do_sp.
Proof. by move=>q y [h][/= H]; case/def_runs. Qed.

Lemma do_has_spec : do_sp \In has_spec s2.
Proof.
move=>i y m [[/= S1 D1]][_][<-] T; case/def_runs: (T)=>_ S2 D2.
by apply: (proj2 (pf S1 D1)) D2; apply: spec_runs T.
Qed.

Definition Do := STprog do_coherent do_dstrict do_has_spec.

End Consequence.


Section Read.
Variable (A : Type) (x : ptr).

Definition read_s : spec A :=
  (fun i => x \in dom i /\ exists v:A, look x i = dyn v,
   fun y i m => m = i /\ forall v, look x i = dyn v -> y = Val v).

Definition read_sp (p : ideald read_s.1) (v : ans A) m :=
  m \In id_val p /\ exists w, v = Val w /\ look x m = dyn w.

Lemma read_coherent : coherent read_sp.
Proof.
move=>p v m; split; last first.
- by case=>i [H1][<-][w][->]; split=>//; exists w.
case=>H1 [w][->] H2.
by exists m; exists H1; split=>//; exists w.
Qed.

Lemma read_dstrict : def_strict read_sp.
Proof. by case=>p H y []; case/H. Qed.

Lemma read_has_spec : read_sp \In has_spec read_s.
Proof.
move=>i y m [[[/= H1]]][v] H2 D [<-][w][->] H3.
by split=>// b1; rewrite H3=>H; move:(dyn_inj H)=>->.
Qed.

Definition read := STprog read_coherent read_dstrict read_has_spec.

End Read.


Section Write.
Variable (A : Type) (x : ptr) (v : A).

Definition write_s : spec unit :=
  (fun i => x \in dom i : Prop,
   fun y i m => y = Val tt /\ upd i x (dyn v) = m).

Definition write_sp (p : ideald write_s.1) (y : ans unit) m :=
  exists i, i \In id_val p /\ x \in dom i /\
            y = Val tt /\ m = upd i x (dyn v).

Lemma write_coherent : coherent write_sp.
Proof.
move=>p y m; split; case=>i [H1].
- by case=>H2 [->->]; exists i; exists H1; exists i.
by case=>_ [<-][H2][->] ->; exists i.
Qed.

Lemma write_dstrict : def_strict write_sp.
Proof.
case=>p H y [i] /= [H1][H2][H3].
suff L: def (upd i x (dyn v)) by move=>H4; rewrite -H4 in L.
by rewrite defU (dom_null H2) (dom_def H2).
Qed.

Lemma write_has_spec : write_sp \In has_spec write_s.
Proof. by move=>i y m [[/= H1 D1]][_][<-][H2][->] ->. Qed.

Definition write := STprog write_coherent write_dstrict write_has_spec.

End Write.


Section Allocation.
Variables (A : Type) (v : A).

Definition alloc_s : spec ptr :=
  (fun i => def i : Prop,
   fun y i m => exists x, x != null /\ y = Val x /\ x \notin dom i /\
                          upd i x (dyn v) = m).

Definition alloc_sp (p : ideald alloc_s.1) y m :=
  exists i, i \In id_val p /\ exists l : ptr, y = Val l /\
    m = i :+ l :-> v /\ l != null /\ l \notin dom i.

Lemma alloc_coherent : coherent alloc_sp.
Proof.
move=>p x m; split.
- case=>i [H1][l][->][->][H2] H3.
  by exists i; exists H1; exists i; split=>//; exists l.
case=>i [H1][_][<-][l][->][->][H2] H3.
by exists i; split=>//; exists l.
Qed.

Lemma alloc_dstrict : def_strict alloc_sp.
Proof.
case=>p H y [m][/= H1][l][H2][H3][H4] H5; case/H: H1=>_ D.
suff {H3}: def (m :+ l :-> v) by rewrite -H3.
by rewrite unC defPtUn H4 D H5.
Qed.

Lemma alloc_has_spec : alloc_sp \In has_spec alloc_s.
Proof.
move=>i y m [[/= H D]][_][<-][l][->][->][H1] H2.
exists l; do !split=>//.
rewrite (_ : i = i :+ empty); last by rewrite unh0.
by rewrite updUnl (negbTE H2) unh0.
Qed.

Definition alloc := STprog alloc_coherent alloc_dstrict alloc_has_spec.

End Allocation.


Section BlockAllocation.
Variables (A : Type) (v : A) (n : nat).

Definition allocb_s : spec ptr :=
  (fun i => def i : Prop,
   fun y i m => exists r, y = Val r /\ m = i :+ updi r (nseq n v)).

Definition allocb_sp (p : ideald allocb_s.1) y m :=
  exists i, i \In id_val p /\ y = Val (fresh i) /\
            m = i :+ updi (fresh i) (nseq n v).

Lemma allocb_coherent : coherent allocb_sp.
Proof.
move=>p x m; split.
- by case=>i [H1][->] ->; exists i; exists H1; exists i.
by case=>i [H1][_][<-][->] ->; exists i.
Qed.

Lemma allocb_dstrict : def_strict allocb_sp.
Proof.
case=>p H y [m][/= H1][_] H2; case/H: H1=>_ D.
suff {H2}: def (m :+ updi (fresh m) (nseq n v)) by rewrite -H2.
elim: n =>[|k IH]; first by rewrite /= unh0.
rewrite (_ : nseq k.+1 v = rcons (nseq k v) v); last first.
- by elim: {IH} k=>[|k IH] //=; rewrite -IH.
rewrite updi_last unA unC defPtUn IH /=.
rewrite ptr_null negb_and fresh_null /=.
rewrite domUn !inE /= negb_and IH negb_or /=.
by rewrite dom_fresh updimV negb_and fresh_null ltnn.
Qed.

Lemma allocb_has_spec : allocb_sp \In has_spec allocb_s.
Proof. by move=>i y m [[/= H D]][_][<-][->] ->; exists (fresh i). Qed.

Definition allocb := STprog allocb_coherent allocb_dstrict allocb_has_spec.

End BlockAllocation.


Section Deallocation.
Variable x : ptr.

Definition dealloc_s : spec unit :=
  (fun i => x \in dom i : Prop,
   fun y i m => y = Val tt /\ free x i = m).

Definition dealloc_sp (p : ideald dealloc_s.1) (y : ans unit) m :=
  exists i, i \In id_val p /\ y = Val tt /\ x \in dom i /\ m = free x i.

Lemma dealloc_coherent : coherent dealloc_sp.
Proof.
move=>p y m; split.
- by case=>i [H1][->][H2] ->; exists i; exists H1; exists i.
by case=>i [H1][_][<-][->][H2] ->; exists i.
Qed.

Lemma dealloc_dstrict : def_strict dealloc_sp.
Proof.
case=>p H y [h][/=]; case/H=>_ H1 [H2][H3] H4.
suff: def (free x h) by rewrite -H4.
by rewrite defF.
Qed.

Lemma dealloc_has_spec : dealloc_sp \In has_spec dealloc_s.
Proof. by move=>i y m [[/= H1 D1]][_][<-][->][H2] ->. Qed.

Definition dealloc :=
  STprog dealloc_coherent dealloc_dstrict dealloc_has_spec.

End Deallocation.

End Model.

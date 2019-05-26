(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(** %\subsection*{ support :  mult\_by\_scalars.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.

(** - mult_by_scalars is just an abbreviation for the special case of pointwise, where
 the operation is scalar multiplication. *)

(* That is to say: it takes two sequences of length N: one sequence v1...vN of *)
(* vectors and one sequence a1...aN of scalars. It returns the sequence of each vector *)
(* multiplied by its respective scalar; ie. a1*v1...aN*vN *)

Require Export pointwise.
Require Export modify_seq.
Require Export vecspaces_verybasic.

(** %\label{multbyscalars}% *)
Definition mult_by_scalars (R : ring) (V : module R) 
  (N : Nat) (a : Map (fin N) R) (v : Map (fin N) V) : 
  MAP (fin N) V := pointwise (uncurry (MODULE_comp (Mod:=V))) a v.

Lemma mult_by_scalars_comp :
 forall (R : ring) (V : module R) (N : Nat) (a b : MAP (fin N) R)
   (v w : MAP (fin N) V),
 a =' b in _ ->
 v =' w in _ -> mult_by_scalars a v =' mult_by_scalars b w in _.
intros.
unfold mult_by_scalars in |- *.
apply (pointwise_comp_general (A:=fin N) (B:=R) (C:=V) (D:=V));
 auto with algebra.
Qed.

Lemma mult_by_scalars_fun2_compatible :
 forall (R : ring) (V : module R) (N : Nat),
 fun2_compatible
   (mult_by_scalars (V:=V) (N:=N):MAP _ _ -> MAP _ _ -> MAP _ _).
exact mult_by_scalars_comp.
Qed.

Hint Resolve mult_by_scalars_fun2_compatible mult_by_scalars_comp: algebra.

Lemma mult_by_scalars_Seqtl :
 forall (R : ring) (V : module R) (N : Nat) (a : Map (fin N) R)
   (v : Map (fin N) V),
 mult_by_scalars (Seqtl a) (Seqtl v) =' Seqtl (mult_by_scalars a v) in _.
intros.
unfold mult_by_scalars in |- *.
apply Sym; auto with algebra.
Qed.

Hint Resolve mult_by_scalars_Seqtl: algebra.

Lemma mult_by_scalars_concat :
 forall (R : ring) (V : module R) (N M : Nat) (a : Map (fin N) R)
   (b : Map (fin M) R) (v : Map (fin N) V) (w : Map (fin M) V),
 mult_by_scalars (a ++ b) (v ++ w) ='
 mult_by_scalars a v ++ mult_by_scalars b w in _.
intros.
unfold mult_by_scalars in |- *.
auto with algebra.
Qed.

Hint Resolve mult_by_scalars_concat: algebra.

Lemma mult_by_scalars_modify_seq :
 forall (F : field) (V : vectorspace F) (n : Nat) (p : seq n F) 
   (k : seq n V) (i : fin n) (q : F),
 mult_by_scalars (modify_seq p i q) k ='
 modify_seq (mult_by_scalars p k) i (q mX k i) in seq _ _.
simple induction n.
intros; inversion i; inversion in_range_prf.
intros.
case i.
intro; case index.
intros.
apply Trans with (mult_by_scalars (q;; Seqtl p) k); auto with algebra.
apply Trans with (mult_by_scalars (q;; Seqtl p) (head k;; Seqtl k)).
unfold mult_by_scalars in |- *.
apply toMap; apply pointwise_comp; auto with algebra.
apply Trans with (q mX head k;; mult_by_scalars (Seqtl p) (Seqtl k)).
unfold mult_by_scalars in |- *.
apply
 Trans
  with
    (uncurry (MODULE_comp (Mod:=V)) (couple q (head k));;
     pointwise (uncurry (MODULE_comp (R:=F) (Mod:=V))) (Seqtl p) (Seqtl k));
 auto with algebra.
apply Trans with (q mX head k;; Seqtl (mult_by_scalars p k)).
apply cons_comp; auto with algebra.
unfold mult_by_scalars in |- *.
apply
 Trans
  with (q mX k (Build_finiteT in_range_prf);; Seqtl (mult_by_scalars p k));
 auto with algebra.
apply cons_comp; auto with algebra.


intros m Hm.
set (Hm' := lt_S_n _ _ Hm) in *.
apply
 Trans with (hdtl (mult_by_scalars (modify_seq p (Build_finiteT Hm) q) k));
 auto with algebra.
apply
 Trans
  with
    (hdtl
       (modify_seq (mult_by_scalars p k) (Build_finiteT Hm)
          (q mX k (Build_finiteT Hm)))); auto with algebra.
unfold hdtl in |- *.
apply
 Trans
  with
    (head (mult_by_scalars p k);;
     Seqtl
       (modify_seq (mult_by_scalars p k) (Build_finiteT Hm)
          (q mX k (Build_finiteT Hm)))); auto with algebra.
apply
 Trans
  with
    (head (mult_by_scalars (modify_seq p (Build_finiteT Hm) q) k);;
     mult_by_scalars (Seqtl (modify_seq p (Build_finiteT Hm) q)) (Seqtl k)).
auto with algebra.
apply
 Trans
  with
    (head (mult_by_scalars (modify_seq p (Build_finiteT Hm) q) k);;
     mult_by_scalars (modify_seq (Seqtl p) (Build_finiteT Hm') q) (Seqtl k)).
apply cons_comp; auto with algebra.
apply cons_comp; auto with algebra.
apply
 Trans
  with
    (mult_by_scalars (Seqtl (modify_seq p (Build_finiteT Hm) q)) (Seqtl k));
 auto with algebra.
apply
 Trans
  with
    (modify_seq (Seqtl (mult_by_scalars p k)) (Build_finiteT Hm')
       (q mX k (Build_finiteT Hm))); auto with algebra.
apply
 Trans
  with
    (modify_seq (mult_by_scalars (Seqtl p) (Seqtl k)) 
       (Build_finiteT Hm') (q mX k (Build_finiteT Hm))); 
 auto with algebra.
apply
 Trans
  with
    (mult_by_scalars (modify_seq (Seqtl p) (Build_finiteT Hm') q) (Seqtl k)).
apply toMap; apply mult_by_scalars_comp; auto with algebra.
apply
 Trans
  with
    (modify_seq (mult_by_scalars (Seqtl p) (Seqtl k)) 
       (Build_finiteT Hm') (q mX Seqtl k (Build_finiteT Hm')));
 auto with algebra.
Qed.

Hint Resolve mult_by_scalars_modify_seq: algebra.
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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************)
(*           The Calculus of Inductive Constructions            *)
(*                       COQ v5.10                              *)
(*                                                              *)
(* Laurent Arditi.  Laboratoire I3S. CNRS ura 1376.             *)
(* Universite de Nice - Sophia Antipolis                        *)
(* arditi@unice.fr, http://wwwi3s.unice.fr/~arditi/lolo.html    *)
(*                                                              *)
(* date: november 1995                                          *)
(* file: Fill_spec.v                                            *)
(* contents: proof of a memory block instruction: Fills cx words*)
(* in memory starting at address di with value al.              *)
(* Implementation level                                         *)
(****************************************************************)

Require Export Fill_defs.

(* Implementation:

cx: register a_size
di: register a_size
al: register d_size
mem: memory of d_size bit words, addresses of a_size bits
ad: register a_size
da: register d_size

ad <- di
da <- al
while not(cx=0) do begin
  mem[ad] <- da
  ad <- ad+1
  cx <- cx-1
end
di <- ad
*)



(****************************************************************)
(* Implementation *)

(* seq1 *)

Definition di1 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := di0.
Definition cx1 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := cx0.
Definition al1 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := al0.
Definition mem1 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := mem0.
Definition ad1 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := di0.
Definition da1 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := al0.

(* seq2 *)

Fixpoint di2 (st : nat) : BV -> BV -> BV -> Memo -> BV -> BV -> BV :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) =>
  match st return BV with
  | O => di0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
      | true => di2 t di0 cx0 al0 mem0 ad0 da0
      | false => di2 t di0 cx0 al0 mem0 ad0 da0
      end
  end
 
 with cx2 (st : nat) : BV -> BV -> BV -> Memo -> BV -> BV -> BV :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) =>
  match st return BV with
  | O => cx0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
      | true => cx2 t di0 cx0 al0 mem0 ad0 da0
      | false => BV_decrement (cx2 t di0 cx0 al0 mem0 ad0 da0)
      end
  end
 
 with al2 (st : nat) : BV -> BV -> BV -> Memo -> BV -> BV -> BV :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) =>
  match st return BV with
  | O => al0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
      | true => al2 t di0 cx0 al0 mem0 ad0 da0
      | false => al2 t di0 cx0 al0 mem0 ad0 da0
      end
  end
 
 with mem2 (st : nat) : BV -> BV -> BV -> Memo -> BV -> BV -> Memo :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) =>
  match st return Memo with
  | O => mem0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return Memo with
      | true => mem2 t di0 cx0 al0 mem0 ad0 da0
      | false =>
          MemoWrite (mem2 t di0 cx0 al0 mem0 ad0 da0)
            (BV_to_nat (ad2 t di0 cx0 al0 mem0 ad0 da0))
            (da2 t di0 cx0 al0 mem0 ad0 da0)
      end
  end
 
 with ad2 (st : nat) : BV -> BV -> BV -> Memo -> BV -> BV -> BV :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) =>
  match st return BV with
  | O => ad0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
      | true => ad2 t di0 cx0 al0 mem0 ad0 da0
      | false => BV_increment (ad2 t di0 cx0 al0 mem0 ad0 da0)
      end
  end
 
 with da2 (st : nat) : BV -> BV -> BV -> Memo -> BV -> BV -> BV :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) =>
  match st return BV with
  | O => da0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
      | true => da2 t di0 cx0 al0 mem0 ad0 da0
      | false => da2 t di0 cx0 al0 mem0 ad0 da0
      end
  end.

Lemma di2_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 di2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
 | true => di2 t di0 cx0 al0 mem0 ad0 da0
 | false => di2 t di0 cx0 al0 mem0 ad0 da0
 end.
auto.
Qed.

Lemma di2_constant :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 di2 t di0 cx0 al0 mem0 ad0 da0 = di0.
simple induction t. simpl in |- *; trivial.
intros. rewrite di2_t. elim (IsNull (cx2 n di0 cx0 al0 mem0 ad0 da0)). apply H.
apply H.
Qed.

Lemma cx2_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 cx2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
 | true => cx2 t di0 cx0 al0 mem0 ad0 da0
 | false => BV_decrement (cx2 t di0 cx0 al0 mem0 ad0 da0)
 end.
auto.
Qed.

Lemma al2_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 al2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
 | true => al2 t di0 cx0 al0 mem0 ad0 da0
 | false => al2 t di0 cx0 al0 mem0 ad0 da0
 end.
auto.
Qed.

Lemma al2_constant :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 al2 t di0 cx0 al0 mem0 ad0 da0 = al0.
simple induction t. simpl in |- *; trivial.
intros. rewrite al2_t. elim (IsNull (cx2 n di0 cx0 al0 mem0 ad0 da0)). apply H.
apply H.
Qed.

Lemma mem2_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 mem2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return Memo with
 | true => mem2 t di0 cx0 al0 mem0 ad0 da0
 | false =>
     MemoWrite (mem2 t di0 cx0 al0 mem0 ad0 da0)
       (BV_to_nat (ad2 t di0 cx0 al0 mem0 ad0 da0))
       (da2 t di0 cx0 al0 mem0 ad0 da0)
 end.
auto.
Qed.

Lemma ad2_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 ad2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
 | true => ad2 t di0 cx0 al0 mem0 ad0 da0
 | false => BV_increment (ad2 t di0 cx0 al0 mem0 ad0 da0)
 end.
auto.
Qed.

Lemma da2_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 da2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BV with
 | true => da2 t di0 cx0 al0 mem0 ad0 da0
 | false => da2 t di0 cx0 al0 mem0 ad0 da0
 end.
auto.
Qed.

Lemma da2_constant :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV),
 da2 t di0 cx0 al0 mem0 ad0 da0 = da0.
simple induction t. simpl in |- *; trivial.
intros. rewrite da2_t. elim (IsNull (cx2 n di0 cx0 al0 mem0 ad0 da0)). apply H.
apply H.
Qed.

(* seq3 *)

Definition di3 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := ad0.
Definition cx3 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := cx0.
Definition al3 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := al0.
Definition mem3 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := mem0.
Definition ad3 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := ad0.
Definition da3 (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) := da0.

(****************************************************************)

(* seq2.seq1 *)

Definition compo_2_1 (X : Set)
  (f : nat -> BV -> BV -> BV -> Memo -> BV -> BV -> X) 
  (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) :=
  f t (di1 di0 cx0 al0 mem0 ad0 da0) (cx1 di0 cx0 al0 mem0 ad0 da0)
    (al1 di0 cx0 al0 mem0 ad0 da0) (mem1 di0 cx0 al0 mem0 ad0 da0)
    (ad1 di0 cx0 al0 mem0 ad0 da0) (da1 di0 cx0 al0 mem0 ad0 da0).

Definition di_2_1 := compo_2_1 BV di2.
Definition cx_2_1 := compo_2_1 BV cx2.
Definition al_2_1 := compo_2_1 BV al2.
Definition mem_2_1 := compo_2_1 Memo mem2.
Definition ad_2_1 := compo_2_1 BV ad2.
Definition da_2_1 := compo_2_1 BV da2.

(* seq3.seq2.seq1 *)

Definition compo' (X : Set) (f : BV -> BV -> BV -> Memo -> BV -> BV -> X)
  (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo) (ad0 da0 : BV) :=
  f (di_2_1 t di0 cx0 al0 mem0 ad0 da0) (cx_2_1 t di0 cx0 al0 mem0 ad0 da0)
    (al_2_1 t di0 cx0 al0 mem0 ad0 da0) (mem_2_1 t di0 cx0 al0 mem0 ad0 da0)
    (ad_2_1 t di0 cx0 al0 mem0 ad0 da0) (da_2_1 t di0 cx0 al0 mem0 ad0 da0).

Definition di' := compo' BV di3.
Definition cx' := compo' BV cx3.
Definition al' := compo' BV al3.
Definition mem' := compo' Memo mem3.
Definition ad' := compo' BV ad3.
Definition da' := compo' BV da3.

(****************************************************************)

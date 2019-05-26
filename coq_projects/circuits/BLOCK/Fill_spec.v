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
(* Specification level                                          *)
(****************************************************************)

Require Export Fill_defs.

(* Specification:

cx: register a_size
di: register a_size
al: register d_size
mem: memory of d_size bit words, addresses of a_size bits

while not(cx=0) do begin
  mem[di] <- al
  di <- di+1
  cx <- cx-1
end
*)

(****************************************************************)

Fixpoint di (st : nat) : BV -> BV -> BV -> Memo -> BV :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) =>
  match st return BV with
  | O => di0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return BV with
      | true => di t di0 cx0 al0 mem0
      | false => BV_increment (di t di0 cx0 al0 mem0)
      end
  end
 
 with cx (st : nat) : BV -> BV -> BV -> Memo -> BV :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) =>
  match st return BV with
  | O => cx0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return BV with
      | true => cx t di0 cx0 al0 mem0
      | false => BV_decrement (cx t di0 cx0 al0 mem0)
      end
  end
 
 with al (st : nat) : BV -> BV -> BV -> Memo -> BV :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) =>
  match st return BV with
  | O => al0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return BV with
      | true => al t di0 cx0 al0 mem0
      | false => al t di0 cx0 al0 mem0
      end
  end
 
 with mem (st : nat) : BV -> BV -> BV -> Memo -> Memo :=
  fun (di0 cx0 al0 : BV) (mem0 : Memo) =>
  match st return Memo with
  | O => mem0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return Memo with
      | true => mem t di0 cx0 al0 mem0
      | false =>
          MemoWrite (mem t di0 cx0 al0 mem0)
            (BV_to_nat (di t di0 cx0 al0 mem0)) (al t di0 cx0 al0 mem0)
      end
  end.

(****************************************************************)
(* Valeurs generales des registres *)

Lemma di_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo),
 di (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return BV with
 | true => di t di0 cx0 al0 mem0
 | false => BV_increment (di t di0 cx0 al0 mem0)
 end.
auto.
Qed.

Lemma cx_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo),
 cx (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return BV with
 | true => cx t di0 cx0 al0 mem0
 | false => BV_decrement (cx t di0 cx0 al0 mem0)
 end.
auto.
Qed.

Lemma al_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo),
 al (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return BV with
 | true => al t di0 cx0 al0 mem0
 | false => al t di0 cx0 al0 mem0
 end.
auto.
Qed.

Lemma al_constant :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo),
 al t di0 cx0 al0 mem0 = al0.
simple induction t. auto.
intros. rewrite al_t. elim (IsNull (cx n di0 cx0 al0 mem0)). apply H. apply H.
Qed.

Lemma mem_t :
 forall (t : nat) (di0 cx0 al0 : BV) (mem0 : Memo),
 mem (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return Memo with
 | true => mem t di0 cx0 al0 mem0
 | false =>
     MemoWrite (mem t di0 cx0 al0 mem0) (BV_to_nat (di t di0 cx0 al0 mem0))
       (al t di0 cx0 al0 mem0)
 end.
auto.
Qed.
(****************************************************************)
(* Longueurs des registres *)

Lemma length_di :
 forall t : nat, lengthbv (di t di_init cx_init al_init mem_init) = a_size.
simple induction t. simpl in |- *. exact di_initsize.
intros.
rewrite di_t. elim (IsNull (cx n di_init cx_init al_init mem_init)). exact H.
rewrite length_BV_increment. exact H.
Qed.

Lemma length_cx :
 forall t : nat, lengthbv (cx t di_init cx_init al_init mem_init) = a_size.
simple induction t. simpl in |- *. exact cx_initsize.
intros.
rewrite cx_t. elim (IsNull (cx n di_init cx_init al_init mem_init)). exact H.
rewrite length_BV_decrement. exact H.
Qed.

Lemma length_al :
 forall t : nat, lengthbv (al t di_init cx_init al_init mem_init) = d_size.
intro. rewrite al_constant. exact al_initsize.
Qed.
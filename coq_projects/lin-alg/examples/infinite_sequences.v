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


(** %\subsection*{ examples :  infinite\_sequences.v }%*)
(** - The vectorspaces $F^\infty$, done in the new-fangled way using
 alt_build_vecspace; the final interactive definition requires only 3 lines (9 tactics) *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export alt_build_vecsp.

Section MAIN.
Variable F : field.
Definition infseq : Setoid.
apply
 (Build_Setoid
    (Equal:=fun s s' : nat -> F => forall i : nat, s i =' s' i in _)).
split; try split; red in |- *; unfold app_rel in |- *; simpl in |- *;
 auto with algebra.
intros.
apply Trans with (y i); auto with algebra.
Defined.

Definition addinfseqs : Map2 infseq infseq infseq.
apply
 (Build_Map2 (Ap2:=fun s s' : infseq => (fun i : nat => s i +' s' i):infseq));
 auto with algebra.
red in |- *; simpl in |- *.
auto with algebra.
Defined.

Definition mltinfseqs : Map2 F infseq infseq.
apply
 (Build_Map2
    (Ap2:=fun (c : F) (s' : infseq) => (fun i : nat => c rX s' i):infseq)).
red in |- *; simpl in |- *.
auto with algebra.
Defined.

Definition zeroseq : infseq := fun n => zero F.

Definition minusseq : Map infseq infseq.
apply Build_Map with (fun (s : infseq) (n : nat) => min s n).
red in |- *.
intros.
simpl in |- *.
simpl in H.
intros.
apply GROUP_comp.
auto.
Defined.

Definition vecspace_infseq : vectorspace F.
apply
 (alt_Build_vectorspace (V:=infseq) (F:=F) (add:=addinfseqs)
    (mlt:=mltinfseqs) (zer:=zeroseq) (mns:=minusseq)); 
 red in |- *; simpl in |- *; intros; auto with algebra.
apply Trans with (x i +' (zero F)); auto with algebra.
apply Trans with (zero F); auto with algebra.
Defined.
End MAIN.
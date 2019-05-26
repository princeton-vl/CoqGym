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

(*                           --- while.v ---                                *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

Global Set Asymmetric Patterns.

Section while_do.
 Variable St : Set. (* states *)
 Variable postcond : St -> Prop.
 Variable precond : St -> Prop.
 Variable Invar : St -> Prop.
 Variable term_order : St -> St -> Prop.
 Variable LoopExit : St -> Prop.
 Hypothesis
   LoopExit_dec : forall s : St, Invar s -> {LoopExit s} + {~ LoopExit s}.
 Hypothesis
   Onestep :
     forall s : St,
     ~ LoopExit s -> Invar s -> {s' : St | Invar s' /\ term_order s' s}.
 Hypothesis LoopExit_ok : forall s : St, LoopExit s -> Invar s -> postcond s.
 Hypothesis loopstart : forall s : St, precond s -> Invar s.


 Hypothesis Termi : well_founded term_order.

 
  Remark loopexec :
   forall s : St, Invar s -> {s' : St | Invar s' /\ LoopExit s'}.
  Proof.
  refine
   (well_founded_induction Termi (fun s => _)
      (fun s hr i =>
       match LoopExit_dec s i with
       | left _ => exist _ s _
       | right _ =>
           match Onestep s _ _ with
           | exist s' h' =>
               match hr s' _ _ with
               | exist s'' _ => exist _ s'' _
               end
           end
       end)); auto; elim h'; auto.
  Qed.

  Lemma startloop :
   forall s : St, precond s -> {s' : St | Invar s' /\ LoopExit s'}.
  Proof.
  intros s p; apply loopexec with s; auto.
  Qed.

 Lemma while_not : forall s : St, precond s -> {s' : St | postcond s'}.
 (******************)
 Proof.
  refine
   (fun s p => match startloop s p with
               | exist s' h' => exist _ s' _
               end); elim h'; auto.

 Qed.
End while_do.

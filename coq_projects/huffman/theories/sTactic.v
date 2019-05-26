(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU Lesser General Public License for more details.                *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(**********************************************************************
    Proof of Huffman algorithm: sTactic.v                            
                                                                     
    Useful tactics                                                   
                                                                     
    Tactics: Contradict, CaseEq, ElimEq                              
                                    Laurent.Thery@inria.fr (2003)    
  **********************************************************************)
 
Theorem Contradict1 : forall a b : Prop, b -> (a -> ~ b) -> ~ a.
Proof.
intuition.
Qed.
 
Theorem Contradict2 : forall a b : Prop, b -> ~ b -> a.
Proof.
intuition.
Qed.
 
Theorem Contradict3 : forall a : Prop, a -> ~ ~ a.
Proof.
auto.
Qed.

(* 
   Contradict is used to contradict an hypothesis H
     if we have H:~A |- B the result is |- A
     if we have H:~A |- ~B the result is H:B |- A
   A tactic to deal with assumption that starts with a negation:
      ~H |- G gives |- H
*)
Ltac Contradict name :=
  (apply (fun a : Prop => Contradict1 a _ name); clear name; intros name) ||
    (apply (fun a : Prop => Contradict2 a _ name); clear name);
   try apply Contradict3.

(* Same as Case but keep the equality *)
Ltac CaseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

(* Same as Case but clear the variable *)
Ltac Casec name := case name; clear name.

(* Same as Elim but clear the variable *)
Ltac Elimc name := elim name; clear name.

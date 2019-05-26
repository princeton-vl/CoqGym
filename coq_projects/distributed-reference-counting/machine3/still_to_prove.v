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



Require Export DistributedReferenceCounting.machine3.machine.
Require Export DistributedReferenceCounting.machine3.cardinal.
Require Export DistributedReferenceCounting.machine3.comm.

Axiom
  todo1 :
    forall (s3 s4 : Site) (q0 q1 q2 : queue Message),
    ~
    In_queue Message (inc_dec s4)
      (append Message q0
         (input Message dec
            (append Message q1 (input Message (inc_dec s3) q2)))) ->
    ~
    In_queue Message (inc_dec s4) (append Message q0 (append Message q1 q2)).



Axiom
  todo2 :
    forall (s0 s2 : Site) (q0 q1 q2 : queue Message),
    In_queue Message (inc_dec s0) (append Message q0 (append Message q1 q2)) ->
    In_queue Message (inc_dec s0)
      (append Message q0
         (input Message dec
            (append Message q1 (input Message (inc_dec s2) q2)))).


Axiom
  todo3 :
    forall (s2 : Site) (q0 q1 q2 : queue Message),
    In_queue Message (inc_dec s2)
      (append Message q0
         (input Message dec
            (append Message q1 (input Message (inc_dec s2) q2)))).


Axiom
  sigma_weight_change_queue :
    forall (s1 s2 s3 : Site) (b : Bag_of_message) (q : queue Message),
    b s1 s2 = input Message dec (input Message (inc_dec s3) q) ->
    sigma_weight (change_queue (queue Message) b s1 s2 q) =
    (sigma_weight b - cardinal_count dec - cardinal_count (inc_dec s3))%Z.


(* Axiom sigma_rooted_change_queue appears in invariant2.v *)

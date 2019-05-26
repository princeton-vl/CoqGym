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


Require Export general_Q.

Infix "/" := make_Q : Q_scope. 

Notation "{ x }" := (decode_Q x) : Q_scope.

Open Scope Q_scope.

Infix "+" := Qplus : Q_scope.

Infix "*" := Qmult : Q_scope.

Infix "-" := Qminus : Q_scope.

Infix "/" := Qdiv : Q_scope.

Notation "- x" := (Qopp x) : Q_scope.

Notation "x1 ^" := (Qinv x1) (at level 2, left associativity) : Q_scope.

Delimit Scope Q_scope with Q.

Infix "<" := Qlt : Q_scope.
Infix "<=" := Qle : Q_scope.


(** Examples *)
(** 
Eval compute in (make_Q `9` `-7`).

Eval compute in (decode_Q (Qneg (nR (dL (dL (dL (nR One))))))).

Eval compute in (decode_Q (Qneg One)).

Eval compute in `9`/`14`.

Eval compute in {(`2`/`3`)^}.

Eval compute in (`1`/`-7`)+(`2`/`3`)^.

Eval compute in {(`1`/`-7`)+(`2`/`3`)^}.

Eval compute in {`1`/`-7`+`2`/`3`^}.

*)

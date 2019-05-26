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


(** %\subsection*{ support :  equal\_syntax.v }%*)
(** This file introduces the notation [='] for the [Equal] relation.
We separate this from the rest of the algebra syntax since many
definitions only require setoids and nothing more.
%\label{equalsyntax}% *)
From Algebra Require Export Sets.

Notation "a =' b 'in' c" := (Equal (s:=c) a b) (at level 70, b at next level).

Notation "a =' b" := (a =' b in _) (at level 70, only parsing).

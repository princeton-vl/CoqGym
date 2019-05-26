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


Load "imecaux".



            Section be1_def.



Definition be1_pD00P00 := Ands (Var (Npos 11) :: Var (Npos 10) :: nil).

Definition be1_pD00P01 := Ands (Var (Npos 11) :: Var (Npos 9) :: nil).

Definition be1_pD00P02 := Ands (Var (Npos 11) :: Var (Npos 8) :: nil).

Definition be1_pD00P03 := Ands (Var (Npos 11) :: Var (Npos 7) :: nil).

Definition be1_pD00P04 := Ands (Var (Npos 11) :: Var (Npos 6) :: nil).

Definition be1_pD00P05 := Ands (Var (Npos 11) :: Var (Npos 5) :: nil).

Definition be1_pD01P00 := Ands (Var (Npos 4) :: Var (Npos 10) :: nil).

Definition be1_pD01P01 := Ands (Var (Npos 4) :: Var (Npos 9) :: nil).

Definition be1_pD01P02 := Ands (Var (Npos 4) :: Var (Npos 8) :: nil).

Definition be1_pD01P03 := Ands (Var (Npos 4) :: Var (Npos 7) :: nil).

Definition be1_pD01P04 := Ands (Var (Npos 4) :: Var (Npos 6) :: nil).

Definition be1_pD01P05 := Ands (Var (Npos 4) :: Var (Npos 5) :: nil).

Definition be1_pD02P00 := Ands (Var (Npos 3) :: Var (Npos 10) :: nil).

Definition be1_pD02P01 := Ands (Var (Npos 3) :: Var (Npos 9) :: nil).

Definition be1_pD02P02 := Ands (Var (Npos 3) :: Var (Npos 8) :: nil).

Definition be1_pD02P03 := Ands (Var (Npos 3) :: Var (Npos 7) :: nil).

Definition be1_pD02P04 := Ands (Var (Npos 3) :: Var (Npos 6) :: nil).

Definition be1_pD02P05 := Ands (Var (Npos 3) :: Var (Npos 5) :: nil).

Definition be1_pD03P00 := Ands (Var (Npos 2) :: Var (Npos 10) :: nil).

Definition be1_pD03P01 := Ands (Var (Npos 2) :: Var (Npos 9) :: nil).

Definition be1_pD03P02 := Ands (Var (Npos 2) :: Var (Npos 8) :: nil).

Definition be1_pD03P03 := Ands (Var (Npos 2) :: Var (Npos 7) :: nil).

Definition be1_pD03P04 := Ands (Var (Npos 2) :: Var (Npos 6) :: nil).

Definition be1_pD03P05 := Ands (Var (Npos 2) :: Var (Npos 5) :: nil).

Definition be1_pD04P00 := Ands (Var (Npos 1) :: Var (Npos 10) :: nil).

Definition be1_pD04P01 := Ands (Var (Npos 1) :: Var (Npos 9) :: nil).

Definition be1_pD04P02 := Ands (Var (Npos 1) :: Var (Npos 8) :: nil).

Definition be1_pD04P03 := Ands (Var (Npos 1) :: Var (Npos 7) :: nil).

Definition be1_pD04P04 := Ands (Var (Npos 1) :: Var (Npos 6) :: nil).

Definition be1_pD04P05 := Ands (Var (Npos 1) :: Var (Npos 5) :: nil).

Definition be1_pD05P00 := Ands (Var N0 :: Var (Npos 10) :: nil).

Definition be1_pD05P01 := Ands (Var N0 :: Var (Npos 9) :: nil).

Definition be1_pD05P02 := Ands (Var N0 :: Var (Npos 8) :: nil).

Definition be1_pD05P03 := Ands (Var N0 :: Var (Npos 7) :: nil).

Definition be1_pD05P04 := Ands (Var N0 :: Var (Npos 6) :: nil).

Definition be1_pD05P05 := Ands (Var N0 :: Var (Npos 5) :: nil).

Definition be1_sD01P01 := Xors (be1_pD04P05 :: be1_pD05P04 :: nil).

Definition be1_cD01P01 := Ands (be1_pD04P05 :: be1_pD05P04 :: nil).

Definition be1_sD01P02 := Xors (be1_pD03P05 :: be1_pD05P03 :: nil).

Definition be1_cD01P02 := Ands (be1_pD03P05 :: be1_pD05P03 :: nil).

Definition be1_sD01P03 := Xors (be1_pD02P05 :: be1_pD05P02 :: nil).

Definition be1_cD01P03 := Ands (be1_pD02P05 :: be1_pD05P02 :: nil).

Definition be1_sD01P04 := Xors (be1_pD01P05 :: be1_pD05P01 :: nil).

Definition be1_cD01P04 := Ands (be1_pD01P05 :: be1_pD05P01 :: nil).

Definition be1_sD01P05 := Xors (be1_pD00P05 :: be1_pD05P00 :: nil).

Definition be1_cD01P05 := Ands (be1_pD00P05 :: be1_pD05P00 :: nil).

Definition be1_sD02P01 :=
  Xors (be1_cD01P01 :: be1_sD01P02 :: be1_pD04P04 :: nil).

Definition be1_sD02P02 :=
  Xors (be1_cD01P02 :: be1_sD01P03 :: be1_pD03P04 :: nil).

Definition be1_sD02P03 :=
  Xors (be1_cD01P03 :: be1_sD01P04 :: be1_pD02P04 :: nil).

Definition be1_sD02P04 :=
  Xors (be1_cD01P04 :: be1_sD01P05 :: be1_pD01P04 :: nil).

Definition be1_sD02P05 :=
  Xors (be1_cD01P05 :: be1_pD04P00 :: be1_pD00P04 :: nil).

Definition be1_cD02P01 :=
  Ors
    (Ands (be1_cD01P01 :: be1_sD01P02 :: nil)
     :: Ands (be1_cD01P01 :: be1_pD04P04 :: nil)
        :: Ands (be1_sD01P02 :: be1_pD04P04 :: nil) :: nil).

Definition be1_cD02P02 :=
  Ors
    (Ands (be1_cD01P02 :: be1_sD01P03 :: nil)
     :: Ands (be1_cD01P02 :: be1_pD03P04 :: nil)
        :: Ands (be1_sD01P03 :: be1_pD03P04 :: nil) :: nil).

Definition be1_cD02P03 :=
  Ors
    (Ands (be1_cD01P03 :: be1_sD01P04 :: nil)
     :: Ands (be1_cD01P03 :: be1_pD02P04 :: nil)
        :: Ands (be1_sD01P04 :: be1_pD02P04 :: nil) :: nil).

Definition be1_cD02P04 :=
  Ors
    (Ands (be1_cD01P04 :: be1_sD01P05 :: nil)
     :: Ands (be1_cD01P04 :: be1_pD01P04 :: nil)
        :: Ands (be1_sD01P05 :: be1_pD01P04 :: nil) :: nil).

Definition be1_cD02P05 :=
  Ors
    (Ands (be1_cD01P05 :: be1_pD04P00 :: nil)
     :: Ands (be1_cD01P05 :: be1_pD00P04 :: nil)
        :: Ands (be1_pD04P00 :: be1_pD00P04 :: nil) :: nil).

Definition be1_sD03P01 :=
  Xors (be1_cD02P01 :: be1_sD02P02 :: be1_pD04P03 :: nil).

Definition be1_sD03P02 :=
  Xors (be1_cD02P02 :: be1_sD02P03 :: be1_pD03P03 :: nil).

Definition be1_sD03P03 :=
  Xors (be1_cD02P03 :: be1_sD02P04 :: be1_pD02P03 :: nil).

Definition be1_sD03P04 :=
  Xors (be1_cD02P04 :: be1_sD02P05 :: be1_pD01P03 :: nil).

Definition be1_sD03P05 :=
  Xors (be1_cD02P05 :: be1_pD03P00 :: be1_pD00P03 :: nil).

Definition be1_cD03P01 :=
  Ors
    (Ands (be1_cD02P01 :: be1_sD02P02 :: nil)
     :: Ands (be1_cD02P01 :: be1_pD04P03 :: nil)
        :: Ands (be1_sD02P02 :: be1_pD04P03 :: nil) :: nil).

Definition be1_cD03P02 :=
  Ors
    (Ands (be1_cD02P02 :: be1_sD02P03 :: nil)
     :: Ands (be1_cD02P02 :: be1_pD03P03 :: nil)
        :: Ands (be1_sD02P03 :: be1_pD03P03 :: nil) :: nil).

Definition be1_cD03P03 :=
  Ors
    (Ands (be1_cD02P03 :: be1_sD02P04 :: nil)
     :: Ands (be1_cD02P03 :: be1_pD02P03 :: nil)
        :: Ands (be1_sD02P04 :: be1_pD02P03 :: nil) :: nil).

Definition be1_cD03P04 :=
  Ors
    (Ands (be1_cD02P04 :: be1_sD02P05 :: nil)
     :: Ands (be1_cD02P04 :: be1_pD01P03 :: nil)
        :: Ands (be1_sD02P05 :: be1_pD01P03 :: nil) :: nil).

Definition be1_cD03P05 :=
  Ors
    (Ands (be1_cD02P05 :: be1_pD03P00 :: nil)
     :: Ands (be1_cD02P05 :: be1_pD00P03 :: nil)
        :: Ands (be1_pD03P00 :: be1_pD00P03 :: nil) :: nil).

Definition be1_sD04P01 :=
  Xors (be1_cD03P01 :: be1_sD03P02 :: be1_pD04P02 :: nil).

Definition be1_sD04P02 :=
  Xors (be1_cD03P02 :: be1_sD03P03 :: be1_pD03P02 :: nil).

Definition be1_sD04P03 :=
  Xors (be1_cD03P03 :: be1_sD03P04 :: be1_pD02P02 :: nil).

Definition be1_sD04P04 :=
  Xors (be1_cD03P04 :: be1_sD03P05 :: be1_pD01P02 :: nil).

Definition be1_sD04P05 :=
  Xors (be1_cD03P05 :: be1_pD02P00 :: be1_pD00P02 :: nil).

Definition be1_cD04P01 :=
  Ors
    (Ands (be1_cD03P01 :: be1_sD03P02 :: nil)
     :: Ands (be1_cD03P01 :: be1_pD04P02 :: nil)
        :: Ands (be1_sD03P02 :: be1_pD04P02 :: nil) :: nil).

Definition be1_cD04P02 :=
  Ors
    (Ands (be1_cD03P02 :: be1_sD03P03 :: nil)
     :: Ands (be1_cD03P02 :: be1_pD03P02 :: nil)
        :: Ands (be1_sD03P03 :: be1_pD03P02 :: nil) :: nil).

Definition be1_cD04P03 :=
  Ors
    (Ands (be1_cD03P03 :: be1_sD03P04 :: nil)
     :: Ands (be1_cD03P03 :: be1_pD02P02 :: nil)
        :: Ands (be1_sD03P04 :: be1_pD02P02 :: nil) :: nil).

Definition be1_cD04P04 :=
  Ors
    (Ands (be1_cD03P04 :: be1_sD03P05 :: nil)
     :: Ands (be1_cD03P04 :: be1_pD01P02 :: nil)
        :: Ands (be1_sD03P05 :: be1_pD01P02 :: nil) :: nil).

Definition be1_cD04P05 :=
  Ors
    (Ands (be1_cD03P05 :: be1_pD02P00 :: nil)
     :: Ands (be1_cD03P05 :: be1_pD00P02 :: nil)
        :: Ands (be1_pD02P00 :: be1_pD00P02 :: nil) :: nil).

Definition be1_sD05P01 :=
  Xors (be1_cD04P01 :: be1_sD04P02 :: be1_pD04P01 :: nil).

Definition be1_sD05P02 :=
  Xors (be1_cD04P02 :: be1_sD04P03 :: be1_pD03P01 :: nil).

Definition be1_sD05P03 :=
  Xors (be1_cD04P03 :: be1_sD04P04 :: be1_pD02P01 :: nil).

Definition be1_sD05P04 :=
  Xors (be1_cD04P04 :: be1_sD04P05 :: be1_pD01P01 :: nil).

Definition be1_sD05P05 :=
  Xors (be1_cD04P05 :: be1_pD01P00 :: be1_pD00P01 :: nil).

Definition be1_cD05P01 :=
  Ors
    (Ands (be1_cD04P01 :: be1_sD04P02 :: nil)
     :: Ands (be1_cD04P01 :: be1_pD04P01 :: nil)
        :: Ands (be1_sD04P02 :: be1_pD04P01 :: nil) :: nil).

Definition be1_cD05P02 :=
  Ors
    (Ands (be1_cD04P02 :: be1_sD04P03 :: nil)
     :: Ands (be1_cD04P02 :: be1_pD03P01 :: nil)
        :: Ands (be1_sD04P03 :: be1_pD03P01 :: nil) :: nil).

Definition be1_cD05P03 :=
  Ors
    (Ands (be1_cD04P03 :: be1_sD04P04 :: nil)
     :: Ands (be1_cD04P03 :: be1_pD02P01 :: nil)
        :: Ands (be1_sD04P04 :: be1_pD02P01 :: nil) :: nil).

Definition be1_cD05P04 :=
  Ors
    (Ands (be1_cD04P04 :: be1_sD04P05 :: nil)
     :: Ands (be1_cD04P04 :: be1_pD01P01 :: nil)
        :: Ands (be1_sD04P05 :: be1_pD01P01 :: nil) :: nil).

Definition be1_cD05P05 :=
  Ors
    (Ands (be1_cD04P05 :: be1_pD01P00 :: nil)
     :: Ands (be1_cD04P05 :: be1_pD00P01 :: nil)
        :: Ands (be1_pD01P00 :: be1_pD00P01 :: nil) :: nil).

Definition be1_sD06P01 := Xors (be1_cD05P01 :: be1_sD05P02 :: nil).

Definition be1_cD06P01 := Ands (be1_cD05P01 :: be1_sD05P02 :: nil).

Definition be1_sD06P02 :=
  Xors (be1_cD05P02 :: be1_sD05P03 :: be1_cD06P01 :: nil).

Definition be1_cD06P02 :=
  Ors
    (Ands (be1_cD05P02 :: be1_sD05P03 :: nil)
     :: Ands (be1_cD05P02 :: be1_cD06P01 :: nil)
        :: Ands (be1_sD05P03 :: be1_cD06P01 :: nil) :: nil).

Definition be1_sD06P03 :=
  Xors (be1_cD05P03 :: be1_sD05P04 :: be1_cD06P02 :: nil).

Definition be1_cD06P03 :=
  Ors
    (Ands (be1_cD05P03 :: be1_sD05P04 :: nil)
     :: Ands (be1_cD05P03 :: be1_cD06P02 :: nil)
        :: Ands (be1_sD05P04 :: be1_cD06P02 :: nil) :: nil).

Definition be1_sD06P04 :=
  Xors (be1_cD05P04 :: be1_sD05P05 :: be1_cD06P03 :: nil).

Definition be1_cD06P04 :=
  Ors
    (Ands (be1_cD05P04 :: be1_sD05P05 :: nil)
     :: Ands (be1_cD05P04 :: be1_cD06P03 :: nil)
        :: Ands (be1_sD05P05 :: be1_cD06P03 :: nil) :: nil).

Definition be1_sD06P05 :=
  Xors (be1_cD05P05 :: be1_pD00P00 :: be1_cD06P04 :: nil).

Definition be1_cD06P05 :=
  Ors
    (Ands (be1_cD05P05 :: be1_pD00P00 :: nil)
     :: Ands (be1_cD05P05 :: be1_cD06P04 :: nil)
        :: Ands (be1_pD00P00 :: be1_cD06P04 :: nil) :: nil).



Definition be1_z00 := be1_cD06P05.
 
Definition be1_z01 := be1_sD06P05.
 
Definition be1_z02 := be1_sD06P04.
 
Definition be1_z03 := be1_sD06P03.
 
Definition be1_z04 := be1_sD06P02.
 
Definition be1_z05 := be1_sD06P01.
 
Definition be1_z06 := be1_sD05P01.
 
Definition be1_z07 := be1_sD04P01.
 
Definition be1_z08 := be1_sD03P01.
 
Definition be1_z09 := be1_sD02P01.
 
Definition be1_z10 := be1_sD01P01.
 
Definition be1_z11 := be1_pD05P05.
 
End be1_def.







            Section be2_def.



Definition be2_pE00P00 := Ands (Var (Npos 10) :: Var (Npos 11) :: nil).

Definition be2_pE00P01 := Ands (Var (Npos 10) :: Var (Npos 4) :: nil).

Definition be2_pE00P02 := Ands (Var (Npos 10) :: Var (Npos 3) :: nil).

Definition be2_pE00P03 := Ands (Var (Npos 10) :: Var (Npos 2) :: nil).

Definition be2_pE00P04 := Ands (Var (Npos 10) :: Var (Npos 1) :: nil).

Definition be2_pE00P05 := Ands (Var (Npos 10) :: Var N0 :: nil).

Definition be2_pE01P00 := Ands (Var (Npos 9) :: Var (Npos 11) :: nil).

Definition be2_pE01P01 := Ands (Var (Npos 9) :: Var (Npos 4) :: nil).

Definition be2_pE01P02 := Ands (Var (Npos 9) :: Var (Npos 3) :: nil).

Definition be2_pE01P03 := Ands (Var (Npos 9) :: Var (Npos 2) :: nil).

Definition be2_pE01P04 := Ands (Var (Npos 9) :: Var (Npos 1) :: nil).

Definition be2_pE01P05 := Ands (Var (Npos 9) :: Var N0 :: nil).

Definition be2_pE02P00 := Ands (Var (Npos 8) :: Var (Npos 11) :: nil).

Definition be2_pE02P01 := Ands (Var (Npos 8) :: Var (Npos 4) :: nil).

Definition be2_pE02P02 := Ands (Var (Npos 8) :: Var (Npos 3) :: nil).

Definition be2_pE02P03 := Ands (Var (Npos 8) :: Var (Npos 2) :: nil).

Definition be2_pE02P04 := Ands (Var (Npos 8) :: Var (Npos 1) :: nil).

Definition be2_pE02P05 := Ands (Var (Npos 8) :: Var N0 :: nil).

Definition be2_pE03P00 := Ands (Var (Npos 7) :: Var (Npos 11) :: nil).

Definition be2_pE03P01 := Ands (Var (Npos 7) :: Var (Npos 4) :: nil).

Definition be2_pE03P02 := Ands (Var (Npos 7) :: Var (Npos 3) :: nil).

Definition be2_pE03P03 := Ands (Var (Npos 7) :: Var (Npos 2) :: nil).

Definition be2_pE03P04 := Ands (Var (Npos 7) :: Var (Npos 1) :: nil).

Definition be2_pE03P05 := Ands (Var (Npos 7) :: Var N0 :: nil).

Definition be2_pE04P00 := Ands (Var (Npos 6) :: Var (Npos 11) :: nil).

Definition be2_pE04P01 := Ands (Var (Npos 6) :: Var (Npos 4) :: nil).

Definition be2_pE04P02 := Ands (Var (Npos 6) :: Var (Npos 3) :: nil).

Definition be2_pE04P03 := Ands (Var (Npos 6) :: Var (Npos 2) :: nil).

Definition be2_pE04P04 := Ands (Var (Npos 6) :: Var (Npos 1) :: nil).

Definition be2_pE04P05 := Ands (Var (Npos 6) :: Var N0 :: nil).

Definition be2_pE05P00 := Ands (Var (Npos 5) :: Var (Npos 11) :: nil).

Definition be2_pE05P01 := Ands (Var (Npos 5) :: Var (Npos 4) :: nil).

Definition be2_pE05P02 := Ands (Var (Npos 5) :: Var (Npos 3) :: nil).

Definition be2_pE05P03 := Ands (Var (Npos 5) :: Var (Npos 2) :: nil).

Definition be2_pE05P04 := Ands (Var (Npos 5) :: Var (Npos 1) :: nil).

Definition be2_pE05P05 := Ands (Var (Npos 5) :: Var N0 :: nil).

Definition be2_sE01P01 := Xors (be2_pE04P05 :: be2_pE05P04 :: nil).

Definition be2_cE01P01 := Ands (be2_pE04P05 :: be2_pE05P04 :: nil).

Definition be2_sE01P02 := Xors (be2_pE03P05 :: be2_pE05P03 :: nil).

Definition be2_cE01P02 := Ands (be2_pE03P05 :: be2_pE05P03 :: nil).

Definition be2_sE01P03 := Xors (be2_pE02P05 :: be2_pE05P02 :: nil).

Definition be2_cE01P03 := Ands (be2_pE02P05 :: be2_pE05P02 :: nil).

Definition be2_sE01P04 := Xors (be2_pE01P05 :: be2_pE05P01 :: nil).

Definition be2_cE01P04 := Ands (be2_pE01P05 :: be2_pE05P01 :: nil).

Definition be2_sE01P05 := Xors (be2_pE00P05 :: be2_pE05P00 :: nil).

Definition be2_cE01P05 := Ands (be2_pE00P05 :: be2_pE05P00 :: nil).

Definition be2_sE02P01 :=
  Xors (be2_cE01P01 :: be2_sE01P02 :: be2_pE04P04 :: nil).

Definition be2_sE02P02 :=
  Xors (be2_cE01P02 :: be2_sE01P03 :: be2_pE03P04 :: nil).

Definition be2_sE02P03 :=
  Xors (be2_cE01P03 :: be2_sE01P04 :: be2_pE02P04 :: nil).

Definition be2_sE02P04 :=
  Xors (be2_cE01P04 :: be2_sE01P05 :: be2_pE01P04 :: nil).

Definition be2_sE02P05 :=
  Xors (be2_cE01P05 :: be2_pE04P00 :: be2_pE00P04 :: nil).

Definition be2_cE02P01 :=
  Ors
    (Ands (be2_cE01P01 :: be2_sE01P02 :: nil)
     :: Ands (be2_cE01P01 :: be2_pE04P04 :: nil)
        :: Ands (be2_sE01P02 :: be2_pE04P04 :: nil) :: nil).

Definition be2_cE02P02 :=
  Ors
    (Ands (be2_cE01P02 :: be2_sE01P03 :: nil)
     :: Ands (be2_cE01P02 :: be2_pE03P04 :: nil)
        :: Ands (be2_sE01P03 :: be2_pE03P04 :: nil) :: nil).

Definition be2_cE02P03 :=
  Ors
    (Ands (be2_cE01P03 :: be2_sE01P04 :: nil)
     :: Ands (be2_cE01P03 :: be2_pE02P04 :: nil)
        :: Ands (be2_sE01P04 :: be2_pE02P04 :: nil) :: nil).

Definition be2_cE02P04 :=
  Ors
    (Ands (be2_cE01P04 :: be2_sE01P05 :: nil)
     :: Ands (be2_cE01P04 :: be2_pE01P04 :: nil)
        :: Ands (be2_sE01P05 :: be2_pE01P04 :: nil) :: nil).

Definition be2_cE02P05 :=
  Ors
    (Ands (be2_cE01P05 :: be2_pE04P00 :: nil)
     :: Ands (be2_cE01P05 :: be2_pE00P04 :: nil)
        :: Ands (be2_pE04P00 :: be2_pE00P04 :: nil) :: nil).

Definition be2_sE03P01 :=
  Xors (be2_cE02P01 :: be2_sE02P02 :: be2_pE04P03 :: nil).

Definition be2_sE03P02 :=
  Xors (be2_cE02P02 :: be2_sE02P03 :: be2_pE03P03 :: nil).

Definition be2_sE03P03 :=
  Xors (be2_cE02P03 :: be2_sE02P04 :: be2_pE02P03 :: nil).

Definition be2_sE03P04 :=
  Xors (be2_cE02P04 :: be2_sE02P05 :: be2_pE01P03 :: nil).

Definition be2_sE03P05 :=
  Xors (be2_cE02P05 :: be2_pE03P00 :: be2_pE00P03 :: nil).

Definition be2_cE03P01 :=
  Ors
    (Ands (be2_cE02P01 :: be2_sE02P02 :: nil)
     :: Ands (be2_cE02P01 :: be2_pE04P03 :: nil)
        :: Ands (be2_sE02P02 :: be2_pE04P03 :: nil) :: nil).

Definition be2_cE03P02 :=
  Ors
    (Ands (be2_cE02P02 :: be2_sE02P03 :: nil)
     :: Ands (be2_cE02P02 :: be2_pE03P03 :: nil)
        :: Ands (be2_sE02P03 :: be2_pE03P03 :: nil) :: nil).

Definition be2_cE03P03 :=
  Ors
    (Ands (be2_cE02P03 :: be2_sE02P04 :: nil)
     :: Ands (be2_cE02P03 :: be2_pE02P03 :: nil)
        :: Ands (be2_sE02P04 :: be2_pE02P03 :: nil) :: nil).

Definition be2_cE03P04 :=
  Ors
    (Ands (be2_cE02P04 :: be2_sE02P05 :: nil)
     :: Ands (be2_cE02P04 :: be2_pE01P03 :: nil)
        :: Ands (be2_sE02P05 :: be2_pE01P03 :: nil) :: nil).

Definition be2_cE03P05 :=
  Ors
    (Ands (be2_cE02P05 :: be2_pE03P00 :: nil)
     :: Ands (be2_cE02P05 :: be2_pE00P03 :: nil)
        :: Ands (be2_pE03P00 :: be2_pE00P03 :: nil) :: nil).

Definition be2_sE04P01 :=
  Xors (be2_cE03P01 :: be2_sE03P02 :: be2_pE04P02 :: nil).

Definition be2_sE04P02 :=
  Xors (be2_cE03P02 :: be2_sE03P03 :: be2_pE03P02 :: nil).

Definition be2_sE04P03 :=
  Xors (be2_cE03P03 :: be2_sE03P04 :: be2_pE02P02 :: nil).

Definition be2_sE04P04 :=
  Xors (be2_cE03P04 :: be2_sE03P05 :: be2_pE01P02 :: nil).

Definition be2_sE04P05 :=
  Xors (be2_cE03P05 :: be2_pE02P00 :: be2_pE00P02 :: nil).

Definition be2_cE04P01 :=
  Ors
    (Ands (be2_cE03P01 :: be2_sE03P02 :: nil)
     :: Ands (be2_cE03P01 :: be2_pE04P02 :: nil)
        :: Ands (be2_sE03P02 :: be2_pE04P02 :: nil) :: nil).

Definition be2_cE04P02 :=
  Ors
    (Ands (be2_cE03P02 :: be2_sE03P03 :: nil)
     :: Ands (be2_cE03P02 :: be2_pE03P02 :: nil)
        :: Ands (be2_sE03P03 :: be2_pE03P02 :: nil) :: nil).

Definition be2_cE04P03 :=
  Ors
    (Ands (be2_cE03P03 :: be2_sE03P04 :: nil)
     :: Ands (be2_cE03P03 :: be2_pE02P02 :: nil)
        :: Ands (be2_sE03P04 :: be2_pE02P02 :: nil) :: nil).

Definition be2_cE04P04 :=
  Ors
    (Ands (be2_cE03P04 :: be2_sE03P05 :: nil)
     :: Ands (be2_cE03P04 :: be2_pE01P02 :: nil)
        :: Ands (be2_sE03P05 :: be2_pE01P02 :: nil) :: nil).

Definition be2_cE04P05 :=
  Ors
    (Ands (be2_cE03P05 :: be2_pE02P00 :: nil)
     :: Ands (be2_cE03P05 :: be2_pE00P02 :: nil)
        :: Ands (be2_pE02P00 :: be2_pE00P02 :: nil) :: nil).

Definition be2_sE05P01 :=
  Xors (be2_cE04P01 :: be2_sE04P02 :: be2_pE04P01 :: nil).

Definition be2_sE05P02 :=
  Xors (be2_cE04P02 :: be2_sE04P03 :: be2_pE03P01 :: nil).

Definition be2_sE05P03 :=
  Xors (be2_cE04P03 :: be2_sE04P04 :: be2_pE02P01 :: nil).

Definition be2_sE05P04 :=
  Xors (be2_cE04P04 :: be2_sE04P05 :: be2_pE01P01 :: nil).

Definition be2_sE05P05 :=
  Xors (be2_cE04P05 :: be2_pE01P00 :: be2_pE00P01 :: nil).

Definition be2_cE05P01 :=
  Ors
    (Ands (be2_cE04P01 :: be2_sE04P02 :: nil)
     :: Ands (be2_cE04P01 :: be2_pE04P01 :: nil)
        :: Ands (be2_sE04P02 :: be2_pE04P01 :: nil) :: nil).

Definition be2_cE05P02 :=
  Ors
    (Ands (be2_cE04P02 :: be2_sE04P03 :: nil)
     :: Ands (be2_cE04P02 :: be2_pE03P01 :: nil)
        :: Ands (be2_sE04P03 :: be2_pE03P01 :: nil) :: nil).

Definition be2_cE05P03 :=
  Ors
    (Ands (be2_cE04P03 :: be2_sE04P04 :: nil)
     :: Ands (be2_cE04P03 :: be2_pE02P01 :: nil)
        :: Ands (be2_sE04P04 :: be2_pE02P01 :: nil) :: nil).

Definition be2_cE05P04 :=
  Ors
    (Ands (be2_cE04P04 :: be2_sE04P05 :: nil)
     :: Ands (be2_cE04P04 :: be2_pE01P01 :: nil)
        :: Ands (be2_sE04P05 :: be2_pE01P01 :: nil) :: nil).

Definition be2_cE05P05 :=
  Ors
    (Ands (be2_cE04P05 :: be2_pE01P00 :: nil)
     :: Ands (be2_cE04P05 :: be2_pE00P01 :: nil)
        :: Ands (be2_pE01P00 :: be2_pE00P01 :: nil) :: nil).

Definition be2_sE06P01 := Xors (be2_cE05P01 :: be2_sE05P02 :: nil).

Definition be2_cE06P01 := Ands (be2_cE05P01 :: be2_sE05P02 :: nil).

Definition be2_sE06P02 :=
  Xors (be2_cE05P02 :: be2_sE05P03 :: be2_cE06P01 :: nil).

Definition be2_cE06P02 :=
  Ors
    (Ands (be2_cE05P02 :: be2_sE05P03 :: nil)
     :: Ands (be2_cE05P02 :: be2_cE06P01 :: nil)
        :: Ands (be2_sE05P03 :: be2_cE06P01 :: nil) :: nil).

Definition be2_sE06P03 :=
  Xors (be2_cE05P03 :: be2_sE05P04 :: be2_cE06P02 :: nil).

Definition be2_cE06P03 :=
  Ors
    (Ands (be2_cE05P03 :: be2_sE05P04 :: nil)
     :: Ands (be2_cE05P03 :: be2_cE06P02 :: nil)
        :: Ands (be2_sE05P04 :: be2_cE06P02 :: nil) :: nil).

Definition be2_sE06P04 :=
  Xors (be2_cE05P04 :: be2_sE05P05 :: be2_cE06P03 :: nil).

Definition be2_cE06P04 :=
  Ors
    (Ands (be2_cE05P04 :: be2_sE05P05 :: nil)
     :: Ands (be2_cE05P04 :: be2_cE06P03 :: nil)
        :: Ands (be2_sE05P05 :: be2_cE06P03 :: nil) :: nil).

Definition be2_sE06P05 :=
  Xors (be2_cE05P05 :: be2_pE00P00 :: be2_cE06P04 :: nil).

Definition be2_cE06P05 :=
  Ors
    (Ands (be2_cE05P05 :: be2_pE00P00 :: nil)
     :: Ands (be2_cE05P05 :: be2_cE06P04 :: nil)
        :: Ands (be2_pE00P00 :: be2_cE06P04 :: nil) :: nil).



Definition be2_z00 := be2_cE06P05.

Definition be2_z01 := be2_sE06P05.

Definition be2_z02 := be2_sE06P04.

Definition be2_z03 := be2_sE06P03.

Definition be2_z04 := be2_sE06P02.

Definition be2_z05 := be2_sE06P01.

Definition be2_z06 := be2_sE05P01.

Definition be2_z07 := be2_sE04P01.

Definition be2_z08 := be2_sE03P01.

Definition be2_z09 := be2_sE02P01.

Definition be2_z10 := be2_sE01P01.

Definition be2_z11 := be2_pE05P05.

End be2_def.

Definition bench :=
  Ands
    (Iff be1_z06 be2_z06
     :: Iff be1_z07 be2_z07
        :: Iff be1_z08 be2_z08
           :: Iff be1_z09 be2_z09
              :: Iff be1_z10 be2_z10
                 :: Iff be1_z11 be2_z11
                    :: Iff be1_z00 be2_z00
                       :: Iff be1_z01 be2_z01
                          :: Iff be1_z02 be2_z02
                             :: Iff be1_z03 be2_z03
                                :: Iff be1_z04 be2_z04
                                   :: Iff be1_z05 be2_z05 :: nil).
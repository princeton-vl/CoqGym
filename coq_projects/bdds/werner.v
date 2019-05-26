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
Definition be1_cst2 := Var (Npos 5).
Definition be1_cas1 :=
  Ors
    (Ands (Var (Npos 4) :: Var (Npos 3) :: nil)
     :: Ands (Neg (Var (Npos 4)) :: Neg (Var (Npos 3)) :: nil) :: nil).
Definition be1_sqb :=
  Ors
    (Ands (Var (Npos 4) :: Neg (Var (Npos 3)) :: nil)
     :: Ands (Neg (Var (Npos 4)) :: Var (Npos 3) :: nil) :: nil).
Definition be1_cas :=
  Ors
    (Ands
       (Var (Npos 3)
        :: Neg (Var (Npos 2)) :: Neg (Var (Npos 5)) :: Var (Npos 1) :: nil)
     :: Ands
          (Var (Npos 3)
           :: Neg (Var (Npos 2)) :: Var (Npos 5) :: Neg (Var (Npos 1)) :: nil)
        :: Ands
             (Neg (Var (Npos 3))
              :: Var (Npos 2) :: Neg (Var (Npos 5)) :: Var (Npos 1) :: nil)
           :: Ands
                (Neg (Var (Npos 3))
                 :: Var (Npos 2) :: Var (Npos 5) :: Neg (Var (Npos 1)) :: nil)
              :: Ands
                   (Neg (Var (Npos 5))
                    :: Neg (Var (Npos 1)) :: Var N0 :: nil)
                 :: Ands (Var (Npos 5) :: Var (Npos 1) :: Var N0 :: nil)
                    :: nil).
Definition be1_csh := Neg (Var (Npos 5)).
Definition be1_cpos := Ands (Neg (Var (Npos 2)) :: Var (Npos 1) :: nil).
Definition be1_cneg := Ands (Var (Npos 2) :: Var (Npos 1) :: nil).
End be1_def.
Section be2_def.
Definition be2_cst2 := Neg (Var (Npos 5)).
Definition be2_cas1 :=
  Ors
    (Ands (Neg (Var (Npos 4)) :: Var (Npos 3) :: nil)
     :: Ands (Var (Npos 4) :: Neg (Var (Npos 3)) :: nil) :: nil).
Definition be2_sqb :=
  Ors
    (Ands (Neg (Var (Npos 4)) :: Var (Npos 3) :: nil)
     :: Ands (Var (Npos 4) :: Neg (Var (Npos 3)) :: nil) :: nil).
Definition be2_cas :=
  Ors
    (Ands (Var (Npos 5) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands (Neg (Var (Npos 5)) :: Neg (Var (Npos 1)) :: Var N0 :: nil)
        :: Ands
             (Neg (Var (Npos 3))
              :: Var (Npos 2) :: Neg (Var (Npos 5)) :: Var (Npos 1) :: nil)
           :: Ands
                (Var (Npos 3)
                 :: Neg (Var (Npos 2))
                    :: Neg (Var (Npos 5)) :: Var (Npos 1) :: nil)
              :: Ands
                   (Neg (Var (Npos 3))
                    :: Var (Npos 2)
                       :: Var (Npos 5) :: Neg (Var (Npos 1)) :: nil)
                 :: Ands
                      (Var (Npos 3)
                       :: Neg (Var (Npos 2))
                          :: Var (Npos 5) :: Neg (Var (Npos 1)) :: nil)
                    :: nil).
Definition be2_csh := Neg (Var (Npos 5)).
Definition be2_cpos := Ands (Neg (Var (Npos 2)) :: Var (Npos 1) :: nil).
Definition be2_cneg := Ands (Var (Npos 2) :: Var (Npos 1) :: nil).
End be2_def.
Definition bench :=
  Ands
    (Iff be1_cpos be2_cpos
     :: Iff be1_cst2 be2_cst2
        :: Iff be1_sqb be2_sqb
           :: Iff be1_cneg be2_cneg
              :: Iff be1_cas be2_cas
                 :: Iff be1_csh be2_csh :: Iff be1_cas1 be2_cas1 :: nil).
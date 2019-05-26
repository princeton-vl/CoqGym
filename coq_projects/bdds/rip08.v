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



Definition be1_car1 := Ands (Var (Npos 15) :: Var (Npos 14) :: nil).

Definition be1_car2 :=
  Ors
    (Ands (Ors (Var (Npos 13) :: Var (Npos 12) :: nil) :: be1_car1 :: nil)
     :: Ands (Var (Npos 13) :: Var (Npos 12) :: nil) :: nil).

Definition be1_car3 :=
  Ors
    (Ands (Ors (Var (Npos 11) :: Var (Npos 10) :: nil) :: be1_car2 :: nil)
     :: Ands (Var (Npos 11) :: Var (Npos 10) :: nil) :: nil).

Definition be1_car4 :=
  Ors
    (Ands (Ors (Var (Npos 9) :: Var (Npos 8) :: nil) :: be1_car3 :: nil)
     :: Ands (Var (Npos 9) :: Var (Npos 8) :: nil) :: nil).

Definition be1_car5 :=
  Ors
    (Ands (Ors (Var (Npos 7) :: Var (Npos 6) :: nil) :: be1_car4 :: nil)
     :: Ands (Var (Npos 7) :: Var (Npos 6) :: nil) :: nil).

Definition be1_car6 :=
  Ors
    (Ands (Ors (Var (Npos 5) :: Var (Npos 4) :: nil) :: be1_car5 :: nil)
     :: Ands (Var (Npos 5) :: Var (Npos 4) :: nil) :: nil).

Definition be1_car7 :=
  Ors
    (Ands (Ors (Var (Npos 3) :: Var (Npos 2) :: nil) :: be1_car6 :: nil)
     :: Ands (Var (Npos 3) :: Var (Npos 2) :: nil) :: nil).



Definition be1_som1 := Xors (Var (Npos 15) :: Var (Npos 14) :: nil).

Definition be1_som2 :=
  Xors (Var (Npos 13) :: Var (Npos 12) :: be1_car1 :: nil).

Definition be1_som3 :=
  Xors (Var (Npos 11) :: Var (Npos 10) :: be1_car2 :: nil).

Definition be1_som4 := Xors (Var (Npos 9) :: Var (Npos 8) :: be1_car3 :: nil).

Definition be1_som5 := Xors (Var (Npos 7) :: Var (Npos 6) :: be1_car4 :: nil).

Definition be1_som6 := Xors (Var (Npos 5) :: Var (Npos 4) :: be1_car5 :: nil).

Definition be1_som7 := Xors (Var (Npos 3) :: Var (Npos 2) :: be1_car6 :: nil).

Definition be1_som8 := Xors (Var (Npos 1) :: Var N0 :: be1_car7 :: nil).

Definition be1_cout :=
  Ors
    (Ands (Ors (Var (Npos 1) :: Var N0 :: nil) :: be1_car7 :: nil)
     :: Ands (Var (Npos 1) :: Var N0 :: nil) :: nil).


End be1_def.






                Section be2_def.



Definition be2_cout1 := Ands (Var (Npos 14) :: Var (Npos 15) :: nil).

Definition be2_cout2 :=
  Ors
    (Ands (be2_cout1 :: Var (Npos 12) :: nil)
     :: Ands (be2_cout1 :: Var (Npos 13) :: nil)
        :: Ands (Var (Npos 12) :: Var (Npos 13) :: nil) :: nil).

Definition be2_cout3 :=
  Ors
    (Ands (be2_cout2 :: Var (Npos 10) :: nil)
     :: Ands (be2_cout2 :: Var (Npos 11) :: nil)
        :: Ands (Var (Npos 10) :: Var (Npos 11) :: nil) :: nil).

Definition be2_cout4 :=
  Ors
    (Ands (be2_cout3 :: Var (Npos 8) :: nil)
     :: Ands (be2_cout3 :: Var (Npos 9) :: nil)
        :: Ands (Var (Npos 8) :: Var (Npos 9) :: nil) :: nil).

Definition be2_cout5 :=
  Ors
    (Ands (be2_cout4 :: Var (Npos 6) :: nil)
     :: Ands (be2_cout4 :: Var (Npos 7) :: nil)
        :: Ands (Var (Npos 6) :: Var (Npos 7) :: nil) :: nil).

Definition be2_cout6 :=
  Ors
    (Ands (be2_cout5 :: Var (Npos 4) :: nil)
     :: Ands (be2_cout5 :: Var (Npos 5) :: nil)
        :: Ands (Var (Npos 4) :: Var (Npos 5) :: nil) :: nil).

Definition be2_cout7 :=
  Ors
    (Ands (be2_cout6 :: Var (Npos 2) :: nil)
     :: Ands (be2_cout6 :: Var (Npos 3) :: nil)
        :: Ands (Var (Npos 2) :: Var (Npos 3) :: nil) :: nil).



Definition be2_som1 :=
  Neg
    (Ors
       (Ands (Neg (Var (Npos 15)) :: Neg (Var (Npos 14)) :: nil)
        :: Ands (Var (Npos 15) :: Var (Npos 14) :: nil) :: nil)).
 
Definition be2_som2 :=
  Neg
    (Ors
       (Ands
          (Ors
             (Ands (Neg (Var (Npos 13)) :: Neg (Var (Npos 12)) :: nil)
              :: Ands (Var (Npos 13) :: Var (Npos 12) :: nil) :: nil)
           :: Neg be2_cout1 :: nil)
        :: Ands
             (be2_cout1
              :: Neg
                   (Ors
                      (Ands
                         (Neg (Var (Npos 13)) :: Neg (Var (Npos 12)) :: nil)
                       :: Ands (Var (Npos 13) :: Var (Npos 12) :: nil) :: nil))
                 :: nil) :: nil)).
 
Definition be2_som3 :=
  Neg
    (Ors
       (Ands
          (Ors
             (Ands (Neg (Var (Npos 11)) :: Neg (Var (Npos 10)) :: nil)
              :: Ands (Var (Npos 11) :: Var (Npos 10) :: nil) :: nil)
           :: Neg be2_cout2 :: nil)
        :: Ands
             (be2_cout2
              :: Neg
                   (Ors
                      (Ands
                         (Neg (Var (Npos 11)) :: Neg (Var (Npos 10)) :: nil)
                       :: Ands (Var (Npos 11) :: Var (Npos 10) :: nil) :: nil))
                 :: nil) :: nil)).
 
Definition be2_som4 :=
  Neg
    (Ors
       (Ands
          (Ors
             (Ands (Neg (Var (Npos 9)) :: Neg (Var (Npos 8)) :: nil)
              :: Ands (Var (Npos 9) :: Var (Npos 8) :: nil) :: nil)
           :: Neg be2_cout3 :: nil)
        :: Ands
             (be2_cout3
              :: Neg
                   (Ors
                      (Ands (Neg (Var (Npos 9)) :: Neg (Var (Npos 8)) :: nil)
                       :: Ands (Var (Npos 9) :: Var (Npos 8) :: nil) :: nil))
                 :: nil) :: nil)).
 
Definition be2_som5 :=
  Neg
    (Ors
       (Ands
          (Ors
             (Ands (Neg (Var (Npos 7)) :: Neg (Var (Npos 6)) :: nil)
              :: Ands (Var (Npos 7) :: Var (Npos 6) :: nil) :: nil)
           :: Neg be2_cout4 :: nil)
        :: Ands
             (be2_cout4
              :: Neg
                   (Ors
                      (Ands (Neg (Var (Npos 7)) :: Neg (Var (Npos 6)) :: nil)
                       :: Ands (Var (Npos 7) :: Var (Npos 6) :: nil) :: nil))
                 :: nil) :: nil)).
 
Definition be2_som6 :=
  Neg
    (Ors
       (Ands
          (Ors
             (Ands (Neg (Var (Npos 5)) :: Neg (Var (Npos 4)) :: nil)
              :: Ands (Var (Npos 5) :: Var (Npos 4) :: nil) :: nil)
           :: Neg be2_cout5 :: nil)
        :: Ands
             (be2_cout5
              :: Neg
                   (Ors
                      (Ands (Neg (Var (Npos 5)) :: Neg (Var (Npos 4)) :: nil)
                       :: Ands (Var (Npos 5) :: Var (Npos 4) :: nil) :: nil))
                 :: nil) :: nil)).
 
Definition be2_som7 :=
  Neg
    (Ors
       (Ands
          (Ors
             (Ands (Neg (Var (Npos 3)) :: Neg (Var (Npos 2)) :: nil)
              :: Ands (Var (Npos 3) :: Var (Npos 2) :: nil) :: nil)
           :: Neg be2_cout6 :: nil)
        :: Ands
             (be2_cout6
              :: Neg
                   (Ors
                      (Ands (Neg (Var (Npos 3)) :: Neg (Var (Npos 2)) :: nil)
                       :: Ands (Var (Npos 3) :: Var (Npos 2) :: nil) :: nil))
                 :: nil) :: nil)).
 
Definition be2_som8 :=
  Neg
    (Ors
       (Ands
          (Ors
             (Ands (Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
              :: Ands (Var (Npos 1) :: Var N0 :: nil) :: nil)
           :: Neg be2_cout7 :: nil)
        :: Ands
             (be2_cout7
              :: Neg
                   (Ors
                      (Ands (Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
                       :: Ands (Var (Npos 1) :: Var N0 :: nil) :: nil))
                 :: nil) :: nil)).
 
Definition be2_cout :=
  Ors
    (Ands (Var (Npos 1) :: be2_cout7 :: nil)
     :: Ands (Var N0 :: be2_cout7 :: nil)
        :: Ands (Var (Npos 1) :: Var N0 :: nil) :: nil).
 

End be2_def.

Definition bench :=
  ANd (Iff be1_cout be2_cout)
    (ANd (Iff be1_som1 be2_som1)
       (ANd (Iff be1_som2 be2_som2)
          (ANd (Iff be1_som3 be2_som3)
             (ANd (Iff be1_som4 be2_som4)
                (ANd (Iff be1_som5 be2_som5)
                   (ANd (Iff be1_som6 be2_som6)
                      (ANd (Iff be1_som7 be2_som7) (Iff be1_som8 be2_som8)))))))).
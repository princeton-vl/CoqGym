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
Definition be1_h :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Neg (Var (Npos 4))
              :: Var (Npos 3)
                 :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Neg (Var (Npos 4))
                 :: Var (Npos 3)
                    :: Var (Npos 2) :: Var (Npos 1) :: Neg (Var N0) :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Neg (Var (Npos 4))
                    :: Var (Npos 3)
                       :: Var (Npos 2)
                          :: Neg (Var (Npos 1)) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Neg (Var (Npos 4))
                       :: Var (Npos 3)
                          :: Var (Npos 2)
                             :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Neg (Var (Npos 4))
                          :: Var (Npos 3)
                             :: Neg (Var (Npos 2))
                                :: Var (Npos 1) :: Var N0 :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Neg (Var (Npos 4))
                             :: Var (Npos 3)
                                :: Neg (Var (Npos 2))
                                   :: Var (Npos 1) :: Neg (Var N0) :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Neg (Var (Npos 4))
                                :: Var (Npos 3)
                                   :: Neg (Var (Npos 2))
                                      :: Neg (Var (Npos 1))
                                         :: Var N0 :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Neg (Var (Npos 4))
                                   :: Var (Npos 3)
                                      :: Neg (Var (Npos 2))
                                         :: Neg (Var (Npos 1))
                                            :: Neg (Var N0) :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Var (Npos 5)
                                   :: Neg (Var (Npos 4))
                                      :: Neg (Var (Npos 3))
                                         :: Var (Npos 2)
                                            :: Var (Npos 1)
                                               :: Var N0 :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Var (Npos 5)
                                      :: Neg (Var (Npos 4))
                                         :: Neg (Var (Npos 3))
                                            :: Var (Npos 2)
                                               :: Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Var (Npos 5)
                                         :: Neg (Var (Npos 4))
                                            :: Neg (Var (Npos 3))
                                               :: Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Var (Npos 5)
                                            :: Neg (Var (Npos 4))
                                               :: Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Var (Npos 5)
                                               :: Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                               :: Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: nil).
Definition be1_i :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Var (Npos 4)
              :: Var (Npos 3)
                 :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 3)
                    :: Var (Npos 2) :: Var (Npos 1) :: Neg (Var N0) :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Var (Npos 4)
                    :: Var (Npos 3)
                       :: Var (Npos 2)
                          :: Neg (Var (Npos 1)) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4)
                       :: Var (Npos 3)
                          :: Var (Npos 2)
                             :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Var (Npos 4)
                          :: Var (Npos 3)
                             :: Neg (Var (Npos 2))
                                :: Var (Npos 1) :: Var N0 :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Var (Npos 4)
                             :: Var (Npos 3)
                                :: Neg (Var (Npos 2))
                                   :: Var (Npos 1) :: Neg (Var N0) :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Var (Npos 4)
                                :: Var (Npos 3)
                                   :: Neg (Var (Npos 2))
                                      :: Neg (Var (Npos 1))
                                         :: Var N0 :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Var (Npos 4)
                                   :: Var (Npos 3)
                                      :: Neg (Var (Npos 2))
                                         :: Neg (Var (Npos 1))
                                            :: Neg (Var N0) :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Var (Npos 5)
                                   :: Var (Npos 4)
                                      :: Neg (Var (Npos 3))
                                         :: Var (Npos 2)
                                            :: Var (Npos 1)
                                               :: Var N0 :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Var (Npos 5)
                                      :: Var (Npos 4)
                                         :: Neg (Var (Npos 3))
                                            :: Var (Npos 2)
                                               :: Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Var (Npos 5)
                                         :: Var (Npos 4)
                                            :: Neg (Var (Npos 3))
                                               :: Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Var (Npos 5)
                                            :: Var (Npos 4)
                                               :: Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Var (Npos 5)
                                               :: Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                               :: Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: nil).
Definition be1_j :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Var (Npos 4)
              :: Var (Npos 3)
                 :: Neg (Var (Npos 2)) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 3)
                    :: Neg (Var (Npos 2))
                       :: Var (Npos 1) :: Neg (Var N0) :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Var (Npos 4)
                    :: Var (Npos 3)
                       :: Neg (Var (Npos 2))
                          :: Neg (Var (Npos 1)) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4)
                       :: Var (Npos 3)
                          :: Neg (Var (Npos 2))
                             :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Var (Npos 4)
                          :: Neg (Var (Npos 3))
                             :: Var (Npos 2)
                                :: Var (Npos 1) :: Var N0 :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Var (Npos 4)
                             :: Neg (Var (Npos 3))
                                :: Var (Npos 2)
                                   :: Var (Npos 1) :: Neg (Var N0) :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Var (Npos 4)
                                :: Neg (Var (Npos 3))
                                   :: Var (Npos 2)
                                      :: Neg (Var (Npos 1))
                                         :: Var N0 :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Var (Npos 4)
                                   :: Neg (Var (Npos 3))
                                      :: Var (Npos 2)
                                         :: Neg (Var (Npos 1))
                                            :: Neg (Var N0) :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Var (Npos 5)
                                   :: Var (Npos 4)
                                      :: Neg (Var (Npos 3))
                                         :: Neg (Var (Npos 2))
                                            :: Var (Npos 1)
                                               :: Var N0 :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Var (Npos 5)
                                      :: Var (Npos 4)
                                         :: Neg (Var (Npos 3))
                                            :: Neg (Var (Npos 2))
                                               :: Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Var (Npos 5)
                                         :: Var (Npos 4)
                                            :: Neg (Var (Npos 3))
                                               :: Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Var (Npos 5)
                                            :: Var (Npos 4)
                                               :: Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Neg (Var (Npos 5))
                                               :: Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                               :: Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: nil).
Definition be1_k :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Var (Npos 4)
              :: Var (Npos 3)
                 :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 3)
                    :: Var (Npos 2) :: Var (Npos 1) :: Neg (Var N0) :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Var (Npos 4)
                    :: Var (Npos 3)
                       :: Var (Npos 2)
                          :: Neg (Var (Npos 1)) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4)
                       :: Var (Npos 3)
                          :: Var (Npos 2)
                             :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Neg (Var (Npos 4))
                          :: Neg (Var (Npos 3))
                             :: Neg (Var (Npos 2))
                                :: Var (Npos 1) :: Neg (Var N0) :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Neg (Var (Npos 4))
                             :: Neg (Var (Npos 3))
                                :: Neg (Var (Npos 2))
                                   :: Neg (Var (Npos 1)) :: Var N0 :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Neg (Var (Npos 4))
                                :: Neg (Var (Npos 3))
                                   :: Neg (Var (Npos 2))
                                      :: Neg (Var (Npos 1))
                                         :: Neg (Var N0) :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Neg (Var (Npos 5))
                                :: Var (Npos 4)
                                   :: Var (Npos 3)
                                      :: Var (Npos 2)
                                         :: Var (Npos 1) :: Var N0 :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Neg (Var (Npos 5))
                                   :: Var (Npos 4)
                                      :: Var (Npos 3)
                                         :: Var (Npos 2)
                                            :: Var (Npos 1)
                                               :: Neg (Var N0) :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Neg (Var (Npos 5))
                                      :: Var (Npos 4)
                                         :: Var (Npos 3)
                                            :: Var (Npos 2)
                                               :: Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Neg (Var (Npos 5))
                                         :: Var (Npos 4)
                                            :: Var (Npos 3)
                                               :: Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Neg (Var (Npos 5))
                                            :: Neg (Var (Npos 4))
                                               :: Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Neg (Var (Npos 5))
                                               :: Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                               :: Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: nil).
Definition be1_m :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Neg (Var (Npos 4))
              :: Var (Npos 3)
                 :: Neg (Var (Npos 2)) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Neg (Var (Npos 4))
                 :: Var (Npos 3)
                    :: Neg (Var (Npos 2))
                       :: Var (Npos 1) :: Neg (Var N0) :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Neg (Var (Npos 4))
                    :: Var (Npos 3)
                       :: Neg (Var (Npos 2))
                          :: Neg (Var (Npos 1)) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Neg (Var (Npos 4))
                       :: Var (Npos 3)
                          :: Neg (Var (Npos 2))
                             :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Neg (Var (Npos 4))
                          :: Neg (Var (Npos 3))
                             :: Var (Npos 2)
                                :: Var (Npos 1) :: Var N0 :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Neg (Var (Npos 4))
                             :: Neg (Var (Npos 3))
                                :: Var (Npos 2)
                                   :: Var (Npos 1) :: Neg (Var N0) :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Neg (Var (Npos 4))
                                :: Neg (Var (Npos 3))
                                   :: Var (Npos 2)
                                      :: Neg (Var (Npos 1))
                                         :: Var N0 :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Neg (Var (Npos 4))
                                   :: Neg (Var (Npos 3))
                                      :: Var (Npos 2)
                                         :: Neg (Var (Npos 1))
                                            :: Neg (Var N0) :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Neg (Var (Npos 5))
                                   :: Var (Npos 4)
                                      :: Var (Npos 3)
                                         :: Neg (Var (Npos 2))
                                            :: Var (Npos 1)
                                               :: Var N0 :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Neg (Var (Npos 5))
                                      :: Var (Npos 4)
                                         :: Var (Npos 3)
                                            :: Neg (Var (Npos 2))
                                               :: Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Neg (Var (Npos 5))
                                         :: Var (Npos 4)
                                            :: Var (Npos 3)
                                               :: Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Neg (Var (Npos 5))
                                            :: Var (Npos 4)
                                               :: Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Neg (Var (Npos 5))
                                               :: Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                               :: Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: nil).
Definition be1_n :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Var (Npos 4)
              :: Var (Npos 3)
                 :: Neg (Var (Npos 2)) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 3)
                    :: Neg (Var (Npos 2))
                       :: Var (Npos 1) :: Neg (Var N0) :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Var (Npos 4)
                    :: Var (Npos 3)
                       :: Neg (Var (Npos 2))
                          :: Neg (Var (Npos 1)) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4)
                       :: Var (Npos 3)
                          :: Neg (Var (Npos 2))
                             :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Var (Npos 4)
                          :: Neg (Var (Npos 3))
                             :: Var (Npos 2)
                                :: Var (Npos 1) :: Var N0 :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Var (Npos 4)
                             :: Neg (Var (Npos 3))
                                :: Var (Npos 2)
                                   :: Var (Npos 1) :: Neg (Var N0) :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Var (Npos 4)
                                :: Neg (Var (Npos 3))
                                   :: Var (Npos 2)
                                      :: Neg (Var (Npos 1))
                                         :: Var N0 :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Var (Npos 4)
                                   :: Neg (Var (Npos 3))
                                      :: Var (Npos 2)
                                         :: Neg (Var (Npos 1))
                                            :: Neg (Var N0) :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Var (Npos 5)
                                   :: Neg (Var (Npos 4))
                                      :: Var (Npos 3)
                                         :: Var (Npos 2)
                                            :: Var (Npos 1)
                                               :: Var N0 :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Var (Npos 5)
                                      :: Neg (Var (Npos 4))
                                         :: Var (Npos 3)
                                            :: Var (Npos 2)
                                               :: Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Var (Npos 5)
                                         :: Neg (Var (Npos 4))
                                            :: Var (Npos 3)
                                               :: Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Var (Npos 5)
                                            :: Neg (Var (Npos 4))
                                               :: Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Var (Npos 5)
                                               :: Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                               :: Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: nil).
Definition be1_o :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Var (Npos 4)
              :: Var (Npos 3)
                 :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 3)
                    :: Neg (Var (Npos 2))
                       :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Var (Npos 4)
                    :: Neg (Var (Npos 3))
                       :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4)
                       :: Neg (Var (Npos 3))
                          :: Neg (Var (Npos 2))
                             :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Neg (Var (Npos 4))
                          :: Var (Npos 3)
                             :: Var (Npos 2)
                                :: Var (Npos 1) :: Var N0 :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Neg (Var (Npos 4))
                             :: Var (Npos 3)
                                :: Var (Npos 2)
                                   :: Var (Npos 1) :: Neg (Var N0) :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Neg (Var (Npos 4))
                                :: Var (Npos 3)
                                   :: Var (Npos 2)
                                      :: Neg (Var (Npos 1))
                                         :: Var N0 :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Neg (Var (Npos 4))
                                   :: Var (Npos 3)
                                      :: Neg (Var (Npos 2))
                                         :: Var (Npos 1)
                                            :: Neg (Var N0) :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Var (Npos 5)
                                   :: Neg (Var (Npos 4))
                                      :: Var (Npos 3)
                                         :: Neg (Var (Npos 2))
                                            :: Neg (Var (Npos 1))
                                               :: Var N0 :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Var (Npos 5)
                                      :: Neg (Var (Npos 4))
                                         :: Var (Npos 3)
                                            :: Neg (Var (Npos 2))
                                               :: Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Var (Npos 5)
                                         :: Neg (Var (Npos 4))
                                            :: Neg (Var (Npos 3))
                                               :: Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Var (Npos 5)
                                            :: Neg (Var (Npos 4))
                                               :: Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Var (Npos 5)
                                               :: Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                               :: Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: nil).
Definition be1_p :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Var (Npos 4)
              :: Var (Npos 3)
                 :: Var (Npos 2) :: Var (Npos 1) :: Neg (Var N0) :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 3)
                    :: Var (Npos 2) :: Neg (Var (Npos 1)) :: Var N0 :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Var (Npos 4)
                    :: Var (Npos 3)
                       :: Var (Npos 2)
                          :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4)
                       :: Var (Npos 3)
                          :: Neg (Var (Npos 2))
                             :: Var (Npos 1) :: Var N0 :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Var (Npos 4)
                          :: Var (Npos 3)
                             :: Neg (Var (Npos 2))
                                :: Var (Npos 1) :: Neg (Var N0) :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Var (Npos 4)
                             :: Var (Npos 3)
                                :: Neg (Var (Npos 2))
                                   :: Neg (Var (Npos 1)) :: Var N0 :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Var (Npos 4)
                                :: Neg (Var (Npos 3))
                                   :: Var (Npos 2)
                                      :: Var (Npos 1)
                                         :: Neg (Var N0) :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Var (Npos 4)
                                   :: Neg (Var (Npos 3))
                                      :: Var (Npos 2)
                                         :: Neg (Var (Npos 1))
                                            :: Var N0 :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Var (Npos 5)
                                   :: Var (Npos 4)
                                      :: Neg (Var (Npos 3))
                                         :: Var (Npos 2)
                                            :: Neg (Var (Npos 1))
                                               :: Neg (Var N0) :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Var (Npos 5)
                                      :: Var (Npos 4)
                                         :: Neg (Var (Npos 3))
                                            :: Neg (Var (Npos 2))
                                               :: Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Var (Npos 5)
                                         :: Var (Npos 4)
                                            :: Neg (Var (Npos 3))
                                               :: Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Var (Npos 5)
                                            :: Var (Npos 4)
                                               :: Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Var (Npos 5)
                                               :: Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                               :: Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil) :: nil).
Definition be1_q :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Var (Npos 4)
              :: Var (Npos 3)
                 :: Var (Npos 2) :: Var (Npos 1) :: Neg (Var N0) :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 3)
                    :: Var (Npos 2) :: Neg (Var (Npos 1)) :: Var N0 :: nil)
        :: Ands
             (Var (Npos 6)
              :: Var (Npos 5)
                 :: Var (Npos 4)
                    :: Var (Npos 3)
                       :: Neg (Var (Npos 2))
                          :: Var (Npos 1) :: Neg (Var N0) :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4)
                       :: Var (Npos 3)
                          :: Neg (Var (Npos 2))
                             :: Neg (Var (Npos 1)) :: Var N0 :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Var (Npos 4)
                          :: Neg (Var (Npos 3))
                             :: Var (Npos 2)
                                :: Var (Npos 1) :: Neg (Var N0) :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Var (Npos 4)
                             :: Neg (Var (Npos 3))
                                :: Var (Npos 2)
                                   :: Neg (Var (Npos 1)) :: Var N0 :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Var (Npos 4)
                                :: Neg (Var (Npos 3))
                                   :: Neg (Var (Npos 2))
                                      :: Var (Npos 1)
                                         :: Neg (Var N0) :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Var (Npos 4)
                                   :: Neg (Var (Npos 3))
                                      :: Neg (Var (Npos 2))
                                         :: Neg (Var (Npos 1))
                                            :: Var N0 :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Var (Npos 5)
                                   :: Neg (Var (Npos 4))
                                      :: Var (Npos 3)
                                         :: Var (Npos 2)
                                            :: Var (Npos 1)
                                               :: Var N0 :: nil)
                             :: Ands
                                  (Var (Npos 6)
                                   :: Var (Npos 5)
                                      :: Neg (Var (Npos 4))
                                         :: Var (Npos 3)
                                            :: Var (Npos 2)
                                               :: Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                :: Ands
                                     (Var (Npos 6)
                                      :: Var (Npos 5)
                                         :: Neg (Var (Npos 4))
                                            :: Var (Npos 3)
                                               :: Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Var (Npos 5)
                                            :: Neg (Var (Npos 4))
                                               :: Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                      :: Ands
                                           (Var (Npos 6)
                                            :: Var (Npos 5)
                                               :: Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                            :: Ands
                                                 (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                               :: Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Var (Npos 6)
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Var (Npos 5)
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 3)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Var (Npos 1)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                                  :: 
                                                  Ands
                                                  (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 3))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil) :: nil).
End be1_def.
Section be2_def.
Definition be2_h := Var (Npos 6).
Definition be2_i :=
  Ors
    (Ands
       (Neg (Var (Npos 6))
        :: Neg (Var (Npos 5))
           :: Neg (Var (Npos 4))
              :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
        :: Ands
             (Neg (Var (Npos 6))
              :: Neg (Var (Npos 5))
                 :: Neg (Var (Npos 4))
                    :: Neg (Var (Npos 1)) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4) :: Neg (Var (Npos 1)) :: Var N0 :: nil)
              :: Ands
                   (Neg (Var (Npos 6))
                    :: Neg (Var (Npos 5))
                       :: Neg (Var (Npos 4))
                          :: Neg (Var (Npos 2)) :: Var (Npos 1) :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Var (Npos 4)
                             :: Neg (Var (Npos 2)) :: Var (Npos 1) :: nil)
                    :: Ands
                         (Neg (Var (Npos 6))
                          :: Neg (Var (Npos 5))
                             :: Neg (Var (Npos 4))
                                :: Neg (Var (Npos 2))
                                   :: Neg (Var (Npos 1))
                                      :: Neg (Var N0) :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Var (Npos 4)
                                   :: Neg (Var (Npos 2))
                                      :: Neg (Var (Npos 1))
                                         :: Neg (Var N0) :: nil)
                          :: Ands
                               (Var (Npos 6)
                                :: Var (Npos 5)
                                   :: Var (Npos 4)
                                      :: Var (Npos 2)
                                         :: Neg (Var N0) :: nil)
                             :: Ands
                                  (Neg (Var (Npos 6))
                                   :: Neg (Var (Npos 5))
                                      :: Neg (Var (Npos 4))
                                         :: Var (Npos 2)
                                            :: Neg (Var N0) :: nil) :: nil).
Definition be2_j :=
  Ors
    (Ands
       (Var (Npos 6)
        :: Var (Npos 5)
           :: Var (Npos 4) :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands (Neg (Var (Npos 5)) :: Var (Npos 4) :: Var (Npos 2) :: nil)
        :: Ands (Neg (Var (Npos 6)) :: Var (Npos 5) :: Var (Npos 4) :: nil)
           :: Ands
                (Var (Npos 6)
                 :: Var (Npos 5)
                    :: Var (Npos 4) :: Neg (Var (Npos 1)) :: Var N0 :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Var (Npos 5)
                       :: Var (Npos 4)
                          :: Neg (Var (Npos 2)) :: Var (Npos 1) :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Var (Npos 4)
                             :: Neg (Var (Npos 2))
                                :: Neg (Var (Npos 1))
                                   :: Neg (Var N0) :: nil)
                    :: Ands
                         (Var (Npos 6)
                          :: Var (Npos 5)
                             :: Var (Npos 4)
                                :: Var (Npos 2) :: Neg (Var N0) :: nil)
                       :: Ands
                            (Neg (Var (Npos 5))
                             :: Var (Npos 4) :: Var (Npos 3) :: nil)
                          :: Ands
                               (Neg (Var (Npos 5))
                                :: Neg (Var (Npos 3))
                                   :: Neg (Var (Npos 2)) :: nil) :: nil).
Definition be2_k :=
  Ors
    (Ands (Var (Npos 4) :: Var (Npos 3) :: Var (Npos 2) :: nil)
     :: Ands
          (Neg (Var (Npos 4))
           :: Neg (Var (Npos 3)) :: Neg (Var (Npos 2)) :: nil) :: nil).
Definition be2_m :=
  Ors
    (Ands
       (Var (Npos 5)
        :: Neg (Var (Npos 4))
           :: Neg (Var (Npos 2)) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands (Neg (Var (Npos 5)) :: Var (Npos 4) :: Var (Npos 2) :: nil)
        :: Ands
             (Var (Npos 5)
              :: Neg (Var (Npos 4))
                 :: Neg (Var (Npos 3)) :: Var (Npos 2) :: Var N0 :: nil)
           :: Ands
                (Neg (Var (Npos 6)) :: Var (Npos 5) :: Var (Npos 4) :: nil)
              :: Ands
                   (Var (Npos 6)
                    :: Neg (Var (Npos 5)) :: Neg (Var (Npos 4)) :: nil)
                 :: Ands
                      (Var (Npos 5)
                       :: Neg (Var (Npos 4))
                          :: Neg (Var (Npos 3))
                             :: Var (Npos 2)
                                :: Neg (Var (Npos 1))
                                   :: Neg (Var N0) :: nil)
                    :: Ands
                         (Var (Npos 5)
                          :: Neg (Var (Npos 4))
                             :: Neg (Var (Npos 2)) :: Neg (Var N0) :: nil)
                       :: Ands
                            (Var (Npos 5)
                             :: Neg (Var (Npos 4))
                                :: Neg (Var (Npos 3))
                                   :: Var (Npos 2) :: Var (Npos 1) :: nil)
                          :: Ands
                               (Neg (Var (Npos 5))
                                :: Var (Npos 4) :: Var (Npos 3) :: nil)
                             :: Ands
                                  (Var (Npos 5)
                                   :: Neg (Var (Npos 4))
                                      :: Neg (Var (Npos 2))
                                         :: Neg (Var (Npos 1)) :: nil) :: nil).
Definition be2_n :=
  Ors
    (Ands
       (Var (Npos 5)
        :: Neg (Var (Npos 4))
           :: Var (Npos 3) :: Var (Npos 2) :: Var N0 :: nil)
     :: Ands
          (Neg (Var (Npos 5))
           :: Neg (Var (Npos 4)) :: Neg (Var (Npos 2)) :: nil)
        :: Ands
             (Var (Npos 5)
              :: Neg (Var (Npos 4))
                 :: Var (Npos 3)
                    :: Var (Npos 2)
                       :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
           :: Ands
                (Var (Npos 5)
                 :: Neg (Var (Npos 4))
                    :: Var (Npos 3) :: Var (Npos 2) :: Var (Npos 1) :: nil)
              :: Ands (Var (Npos 5) :: Var (Npos 4) :: Var (Npos 3) :: nil)
                 :: Ands
                      (Neg (Var (Npos 4))
                       :: Neg (Var (Npos 3)) :: Neg (Var (Npos 2)) :: nil)
                    :: Ands
                         (Var (Npos 5) :: Var (Npos 4) :: Var (Npos 2) :: nil)
                       :: Ands
                            (Neg (Var (Npos 5))
                             :: Neg (Var (Npos 4))
                                :: Neg (Var (Npos 3)) :: nil)
                          :: Ands
                               (Neg (Var (Npos 5))
                                :: Neg (Var (Npos 3))
                                   :: Neg (Var (Npos 2)) :: nil) :: nil).
Definition be2_o :=
  Ors
    (Ands
       (Neg (Var (Npos 6))
        :: Neg (Var (Npos 5))
           :: Neg (Var (Npos 4))
              :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Var (Npos 5)
              :: Var (Npos 4)
                 :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
        :: Ands
             (Var (Npos 5)
              :: Neg (Var (Npos 4))
                 :: Var (Npos 3) :: Var (Npos 2) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 5)
                 :: Neg (Var (Npos 4))
                    :: Neg (Var (Npos 3)) :: Var (Npos 2) :: Var N0 :: nil)
              :: Ands
                   (Neg (Var (Npos 6)) :: Var (Npos 5) :: Var (Npos 4) :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Neg (Var (Npos 5)) :: Neg (Var (Npos 4)) :: nil)
                    :: Ands
                         (Neg (Var (Npos 6))
                          :: Neg (Var (Npos 5))
                             :: Neg (Var (Npos 4))
                                :: Neg (Var (Npos 2))
                                   :: Neg (Var (Npos 1))
                                      :: Neg (Var N0) :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Var (Npos 4)
                                   :: Neg (Var (Npos 2))
                                      :: Neg (Var (Npos 1))
                                         :: Neg (Var N0) :: nil)
                          :: Ands
                               (Neg (Var (Npos 5))
                                :: Var (Npos 4)
                                   :: Var (Npos 2) :: Var (Npos 1) :: nil)
                             :: Ands
                                  (Var (Npos 5)
                                   :: Neg (Var (Npos 4))
                                      :: Neg (Var (Npos 2))
                                         :: Neg (Var N0) :: nil)
                                :: Ands
                                     (Neg (Var (Npos 5))
                                      :: Var (Npos 4)
                                         :: Neg (Var (Npos 2))
                                            :: Neg (Var N0) :: nil)
                                   :: Ands
                                        (Var (Npos 5)
                                         :: Neg (Var (Npos 4))
                                            :: Var (Npos 3)
                                               :: Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1) :: nil)
                                      :: Ands
                                           (Var (Npos 5)
                                            :: Neg (Var (Npos 4))
                                               :: Neg (Var (Npos 3))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Var (Npos 1) :: nil)
                                         :: Ands
                                              (Var (Npos 5)
                                               :: Neg (Var (Npos 4))
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1)) :: nil)
                                            :: Ands
                                                 (Neg (Var (Npos 5))
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Var N0 :: nil) :: nil).
Definition be2_p :=
  Ors
    (Ands
       (Neg (Var (Npos 6))
        :: Var (Npos 5)
           :: Var (Npos 4) :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 6)
           :: Neg (Var (Npos 5))
              :: Neg (Var (Npos 4))
                 :: Var (Npos 2) :: Var (Npos 1) :: Var N0 :: nil)
        :: Ands
             (Var (Npos 5)
              :: Neg (Var (Npos 4))
                 :: Neg (Var (Npos 2)) :: Var (Npos 1) :: Var N0 :: nil)
           :: Ands
                (Neg (Var (Npos 5))
                 :: Var (Npos 4)
                    :: Neg (Var (Npos 2)) :: Var (Npos 1) :: Var N0 :: nil)
              :: Ands
                   (Neg (Var (Npos 6))
                    :: Neg (Var (Npos 5))
                       :: Neg (Var (Npos 4))
                          :: Neg (Var (Npos 1)) :: Var N0 :: nil)
                 :: Ands
                      (Var (Npos 6)
                       :: Var (Npos 5)
                          :: Var (Npos 4)
                             :: Neg (Var (Npos 1)) :: Var N0 :: nil)
                    :: Ands
                         (Neg (Var (Npos 6))
                          :: Neg (Var (Npos 5))
                             :: Neg (Var (Npos 4))
                                :: Neg (Var (Npos 2)) :: Var (Npos 1) :: nil)
                       :: Ands
                            (Var (Npos 6)
                             :: Var (Npos 5)
                                :: Var (Npos 4)
                                   :: Neg (Var (Npos 2))
                                      :: Var (Npos 1) :: nil)
                          :: Ands
                               (Neg (Var (Npos 5))
                                :: Var (Npos 4)
                                   :: Var (Npos 2)
                                      :: Neg (Var (Npos 1))
                                         :: Neg (Var N0) :: nil)
                             :: Ands
                                  (Var (Npos 5)
                                   :: Neg (Var (Npos 4))
                                      :: Var (Npos 3)
                                         :: Var (Npos 2)
                                            :: Neg (Var (Npos 1))
                                               :: Neg (Var N0) :: nil)
                                :: Ands
                                     (Var (Npos 5)
                                      :: Neg (Var (Npos 4))
                                         :: Neg (Var (Npos 3))
                                            :: Var (Npos 2)
                                               :: Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                   :: Ands
                                        (Var (Npos 6)
                                         :: Neg (Var (Npos 5))
                                            :: Neg (Var (Npos 4))
                                               :: Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                      :: Ands
                                           (Neg (Var (Npos 6))
                                            :: Var (Npos 5)
                                               :: Var (Npos 4)
                                                  :: 
                                                  Neg (Var (Npos 2))
                                                  :: 
                                                  Neg (Var (Npos 1))
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                         :: Ands
                                              (Var (Npos 6)
                                               :: Var (Npos 5)
                                                  :: 
                                                  Var (Npos 4)
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                            :: Ands
                                                 (Neg (Var (Npos 6))
                                                  :: 
                                                  Neg (Var (Npos 5))
                                                  :: 
                                                  Neg (Var (Npos 4))
                                                  :: 
                                                  Var (Npos 2)
                                                  :: 
                                                  Neg (Var N0) :: nil)
                                               :: nil).
Definition be2_q :=
  Ors
    (Ands
       (Neg (Var (Npos 5)) :: Var (Npos 4) :: Var (Npos 1) :: Var N0 :: nil)
     :: Ands
          (Var (Npos 5)
           :: Neg (Var (Npos 4)) :: Var (Npos 1) :: Var N0 :: nil)
        :: Ands
             (Neg (Var (Npos 5))
              :: Neg (Var (Npos 4)) :: Neg (Var (Npos 1)) :: Var N0 :: nil)
           :: Ands
                (Var (Npos 5)
                 :: Var (Npos 4) :: Neg (Var (Npos 1)) :: Var N0 :: nil)
              :: Ands
                   (Neg (Var (Npos 5))
                    :: Neg (Var (Npos 4))
                       :: Var (Npos 1) :: Neg (Var N0) :: nil)
                 :: Ands
                      (Var (Npos 5)
                       :: Var (Npos 4)
                          :: Var (Npos 1) :: Neg (Var N0) :: nil)
                    :: Ands
                         (Neg (Var (Npos 5))
                          :: Var (Npos 4)
                             :: Neg (Var (Npos 1)) :: Neg (Var N0) :: nil)
                       :: Ands
                            (Var (Npos 5)
                             :: Neg (Var (Npos 4))
                                :: Neg (Var (Npos 1))
                                   :: Neg (Var N0) :: nil) :: nil).
End be2_def.
Definition bench :=
  Ands
    (Iff be1_h be2_h
     :: Iff be1_i be2_i
        :: Iff be1_j be2_j
           :: Iff be1_k be2_k
              :: Iff be1_m be2_m
                 :: Iff be1_n be2_n
                    :: Iff be1_o be2_o
                       :: Iff be1_p be2_p :: Iff be1_q be2_q :: nil).
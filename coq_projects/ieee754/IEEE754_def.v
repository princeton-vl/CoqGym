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


(********************************************************)
(* Une  axiomatisation en coq de la norme IEEE 754 	*)
(* Module IEEE754_def.v				   	*)
(* un plan d'ensemble se trouve dans le fichier README 	*)
(* Patrick Loiseleur, avril 1997			*)
(********************************************************)

Require Import Omega.
Require Import Bool.
Require Import Zcomplements.
Require Import Zpower.
Require Import Zlogarithm.

Require Import Diadic.
Require Import Registers.

Section constants.

Inductive float_type : Set :=
  | Single : float_type
  | Single_ext : float_type
  | Double : float_type
  | Double_ext : float_type
  | Quad : float_type.

(* number of bits to represent the dig *) 
Definition dig_length (t : float_type) :=
  match t with
  | Single => 23%Z
  | Single_ext => 32%Z
  | Double => 52%Z
  | Double_ext => 74%Z
  | Quad => 112%Z
  end.

(* number of bits to represent the exponent *)
Definition exp_length (t : float_type) :=
  match t with
  | Single => 8%Z
  | Single_ext => 11%Z
  | Double => 11%Z
  | Double_ext => 15%Z
  | Quad => 15%Z
  end.

Definition dig_l (t : float_type) := Zabs_nat (dig_length t).
Definition exp_l (t : float_type) := Zabs_nat (exp_length t).

(* The exposants in the machine representation (see section machine) 
   are between -2^N + 1 and 2^N where N=(exp_length t)-1. But
   the extremal values -2^N + 1 and 2^N are used to represent special
   numbers such as NaNs, denomalized and projective values (+0, -0, 
   +infty, -infty). So the exposants of "ordinary" normalized numbers
   run between Emin = -2^N + 2 and Emax = 2^N - 1. *)

Definition Emax (t : float_type) :=
  match t with
  | Single => 127%Z
  | Single_ext => 1023%Z
  | Double => 1023%Z
  | Double_ext => 16383%Z
  | Quad => 16383%Z
  end.

Definition Emin (t : float_type) :=
  match t with
  | Single => (-126)%Z
  | Single_ext => (-1022)%Z
  | Double => (-1022)%Z
  | Double_ext => (-16382)%Z
  | Quad => (-16382)%Z
  end.

(* Exponent bias *)
Definition Ebias := Emax.

(* Exponent bias adjust, used to report Overflow *)
(* Its' equal to 3 * 2 ^ (exp_length - 2)        *)
Definition Ebias_adjust (t : float_type) :=
  match t with
  | Single => 192%Z
  | Single_ext => 1536%Z
  | Double => 1536%Z
  | Double_ext => 24576%Z
  | Quad => 24576%Z
  end.

(* The comparison between two IEEE numbers may take four values : 
  less than, equal, greater than, unordered. That extends the 3-valued
  type relation of ZArith *)
Inductive extended_relation : Set :=
  | Ordered : Datatypes.comparison -> extended_relation
  | Unordered : extended_relation.

(* Now an inductive type to represent the five exceptions 
  specified in the norm. *)
Inductive exception : Set :=
  | Invalid_operation : exception
  | Division_by_zero : exception
  | Overflow : exception
  | Underflow : exception
  | Inexact : exception
  | Inexact_underflow : exception
  | Inexact_overflow : exception
  | Nothing : exception.

(* For NaNs *)
Definition quiet := 1%positive.
Definition signaling_IE := 2%positive.

(* A type to represent trap signal orders. For every operation, the user
  can specify which exception he wants to ignore. 
  (trap_signal_order e) is true iff the user asks to ignore exception e *)
Definition trap_signal_order := exception -> bool.
Definition trap (tso : trap_signal_order) (e : exception) : exception :=
  if tso e then Nothing else e.

(* by default, don't ignore any signal *) 
Definition tso_default (x : exception) := false.
Definition tso_max (x : exception) := true.

(***** INUTILE
(* Minimal and maximal positive diadic number that can be represented *)
Definition max_diadic := [t:float_type]
  (Diadic (Z_of_register (dig_l t) (register_max (dig_l t))) 
      	  (% (Emax t) - (dig_length t))).
Definition Min_pos_diadic := [t:float_type]
  (Diadic `1`(% (Emin t) -  (dig_length t))).
*********)

End constants.

Section definitions.

(* All definitions of this section are parametrized by a type t *)
Variable t : float_type.

(* Abstraclty, an IEEE number is or a normal number, 
  or a subnormal one, or +- 0, or +- infty, or a NaN. *)
Inductive abstract_IEEE : Set :=
  | Normal : bool -> Z -> positive -> abstract_IEEE
  | Subnormal : bool -> positive -> abstract_IEEE
  | Zero : bool -> abstract_IEEE
  | Infty : bool -> abstract_IEEE
  | NaN : positive -> abstract_IEEE.

(* concretely, it's a register of 32 or more bits *)
Record concrete_IEEE : Set := C_build
  {c_sign : bool; c_exp : register (exp_l t); c_dig : register (dig_l t)}.

(* Well_formedness of abstract IEEE numbers *)
(* The conditions of Well-formedness are separated from the definition
  of abstract_IEEE, in order to separate Logical part from Informative
  part. The functions defined on abtract_IEEE have a specified behavior
  only for well-formed numbers *)

(* Because of the implicit bit convention, the dig of a normal number is
  a positive with (dig_length t) + 1 digits. The first digit will be
  automatically "forgotten" during the convertion abstract -> concrete *)

Definition abstract_wf (x : abstract_IEEE) :=
  match x with
  | Normal b e m => (Emin t <= e <= Emax t)%Z /\ log_inf m = dig_length t
  | Subnormal b m => (Zpos m < two_p (dig_length t))%Z
  | _ => True
  end.

(* Max and Min number (in absolute value) *)
Definition max_abstract (b : bool) :=
  Normal b (Emax t) (iter (dig_length t) positive xI 1%positive).
Definition min_abstract (b : bool) := Subnormal b 1.

(*** Just for recall (This is defined in Diadic.v)
Inductive rounding_mode : Set :=
  Rounding_sup : rounding_mode
| Rounding_inf : rounding_mode
| Rounding_nearest : rounding_mode
| Rounding_zero : rounding_mode.

NEG_ROUND : rounding_mode->positive->positive->entier
POS_ROUND : rounding_mode->positive->positive->entier
ZROUND : rounding_mode->positive->Z->Z
ROUND : rounding_mode -> Z -> diadic -> diadic.
**  First argument : mode. 
**  Second argument : number of digits to forget (for POS_ROUND and ZROUND)
                     number of digits of the rounded number (for ROUND)

*********)

(**************************************************************************)
(*      Conversions between diadic, abstract_IEEE and concrete_IEEE       *)
(**************************************************************************)

Definition abstract_of_diadic (m : rounding_mode) (x : diadic) :=
  let (nx, e1) := ROUND m (dig_length t) x in
  let ex := (e1 + dig_length t)%Z in
  match nx return abstract_IEEE with
  | Z0 => Zero true
  | Zpos p =>
      if Zbool.Zgt_bool ex (Emax t)
      then Infty true
      else
       match (ex - Emin t)%Z with
       | Zneg e =>
           match POS_ROUND m e p with
           | N0 => Zero true
           | Npos q =>
               if Zbool.Zge_bool (Zpos q) (two_p (Zsucc (dig_length t)))
               then Normal true (Emin t) q
               else Subnormal true q
           end
       | _ => Normal true ex p
       end
  | Zneg p =>
      if Zbool.Zgt_bool ex (Emax t)
      then Infty false
      else
       match (ex - Emin t)%Z with
       | Zneg e =>
           match NEG_ROUND m e p with
           | N0 => Zero false
           | Npos q =>
               if Zbool.Zge_bool (Zpos q) (two_p (Zsucc (dig_length t)))
               then Normal false (Emin t) q
               else Subnormal false q
           end
       | _ => Normal false ex p
       end
  end.

(*** The same function raising appropriated signals ***)
Definition abstract_of_diadic_s (m : rounding_mode) 
  (x : diadic) :=
  let (nx, e1) := ROUND m (dig_length t) x in
  let ex := (e1 + dig_length t)%Z in
  match nx return (abstract_IEEE * exception) with
  | Z0 => (Zero true, Nothing)
  | Zpos p =>
      if Zbool.Zgt_bool ex (Emax t)
      then (Infty true, Overflow)
      else
       match (ex - Emin t)%Z with
       | Zneg e =>
           match POS_ROUND m e p with
           | N0 => (Zero true, Inexact_underflow)
           | Npos q =>
               if Zbool.Zge_bool (Zpos q) (two_p (Zsucc (dig_length t)))
               then (Normal true (Emin t) q, Nothing)
               else (Subnormal true q, Underflow)
           end
       | _ => (Normal true ex p, Nothing)
       end
  | Zneg p =>
      if Zbool.Zgt_bool ex (Emax t)
      then (Infty false, Overflow)
      else
       match (ex - Emin t)%Z with
       | Zneg e =>
           match NEG_ROUND m e p with
           | N0 => (Zero false, Inexact_underflow)
           | Npos q =>
               if Zbool.Zge_bool (Zpos q) (two_p (Zsucc (dig_length t)))
               then (Normal false (Emin t) q, Nothing)
               else (Subnormal false q, Underflow)
           end
       | _ => (Normal false ex p, Nothing)
       end
  end.

(****** Special values are reresented by : 

  Exponent (biased) | Dig    | Meaning 
 -------------------+--------+-------------
  Emax + 1  (N)     | 0      | + or - Infty
  Emax + 1  (N)     | >0     | NaN  
  Emin - 1  (0)     | >0     | Subnormal
  Emin - 1  (0)     | 0      | +0 or -0     

(where N is 2^(exp_length t) - 1)

Normal values are represented by their sign bit, their exponent (biased)
and their dig.

******************************************)
(* Since 2^((dig_l t)+1) <= m < 2^((dig_l t)+2), register_to_zero (dig_l t)
  forgets the first (most significative) digit and so the implicit bit
  convention is realized *)

Definition concrete_of_abstract (x : abstract_IEEE) :=
  match x with
  | Normal b e m =>
      C_build b (register_of_Z (exp_l t) (e + Ebias t))
        (register_of_pos (dig_l t) m)
  | Subnormal b m =>
      C_build b (register_zero (exp_l t)) (register_of_pos (dig_l t) m)
  | Zero b => C_build b (register_zero (exp_l t)) (register_zero (dig_l t))
  | Infty b => C_build b (register_max (exp_l t)) (register_zero (dig_l t))
  | NaN s =>
      C_build true (register_max (exp_l t)) (register_of_pos (dig_l t) s)
  end.

Definition concrete_of_diadic (m : rounding_mode) (x : diadic) :=
  concrete_of_abstract (abstract_of_diadic m x).

(* When passing to a concrete number encoding a normal IEEE number to the
  abtract number, 2^(dig_l t) is added to the dig (implicit bit convention)
*)

Definition abstract_of_concrete (x : concrete_IEEE) :=
  match x return abstract_IEEE with
  | C_build b e m =>
      match entier_of_register (dig_l t) m return abstract_IEEE with
      | N0 =>
          if is_register_zero (exp_l t) e
          then Zero b
          else
           if is_register_max (exp_l t) e
           then Infty b
           else
            Normal b (Z_of_register (exp_l t) e - Ebias t)
              (nat_rect _ 1%positive (fun _ => xO) (dig_l t) )
      | Npos p =>
          if is_register_zero (exp_l t) e
          then Subnormal b p
          else
           if is_register_max (exp_l t) e
           then NaN p
           else
            Normal b (Z_of_register (exp_l t) e - Ebias t)
              (nat_rect _ 1%positive (fun _ => xO) (dig_l t) + p)
      end
  end.

Definition diadic_of_abstract (x : abstract_IEEE) :=
  match x with
  | Normal b e m => Diadic (sign_of b * Zpos m) (e - dig_length t)
  | Subnormal b m => Diadic (sign_of b * Zpos m) (Emin t - dig_length t)
  | Zero b => Dzero 0
  | Infty b => Diadic (sign_of b) (Emax Quad + 1)
  | NaN s => Diadic (Zpos s) (Emax Quad + 2)
  end.

Definition diadic_of_concrete (x : concrete_IEEE) :=
  diadic_of_abstract (abstract_of_concrete x).

(**************************************************************************)
(*                              Comparisons                               *)
(**************************************************************************)

(* We have -infty < any normal of subnormal < +infty. This is simply
  realized by comparing abtract numbers via their diadic representation.*)
(* Since 0+ = 0- and (NaN s) = (NaN s'), equality on IEEE numbers is not
   structural equality, i.e. bit-to-bit equality in the concrete
   representation. *)
(* As specified in the norm, the comparison works even with differents
  formats : that is the reason why +Infty is transformed to 
  (max_diadic_number Quad)+1, even when working with single-precision.
  Elsewhere we could obtain +Infty<+Infty when comparing a single and
  a double float. *)

Definition abstract_compare (x y : abstract_IEEE)
  (tso : trap_signal_order) :=
  match x, y with
  | NaN _, NaN _ => (Ordered Datatypes.Eq, Nothing)
  | NaN _, _ => (Unordered, trap tso Invalid_operation)
  | _, NaN _ => (Unordered, trap tso Invalid_operation)
  | x1, y1 =>
      (Ordered (Dcompare (diadic_of_abstract x1) (diadic_of_abstract y1)),
      Nothing)
  end.

(**************************************************************************)
(*                     Derived comparison functions                       *)
(**************************************************************************)

(* plus tard ! *)

(**************************************************************************)
(*                              Addition				  *)
(**************************************************************************)

(* without trapping *)
Definition abstract_add (m : rounding_mode) (x y : abstract_IEEE) :=
  match x, y return (abstract_IEEE * exception) with
  | NaN s1, _ => (NaN s1, Nothing)
  | _, NaN s2 => (NaN s2, Nothing)
  | Infty true, Infty false => (NaN quiet, Invalid_operation)
  | Infty false, Infty true => (NaN quiet, Invalid_operation)
  | Infty b1, _ => (Infty b1, Nothing)
  | _, Infty b2 => (Infty b2, Nothing)
  | _, _ =>
      abstract_of_diadic_s m
        (Dadd (diadic_of_abstract x) (diadic_of_abstract y))
  end.

Definition abstract_opp (x : abstract_IEEE) :=
  match x with
  | NaN s => NaN s
  | Infty b => Infty (negb b)
  | Zero b => Zero (negb b)
  | Normal b e m => Normal (negb b) e m
  | Subnormal b m => Subnormal (negb b) m
  end.

Definition abstract_sub (m : rounding_mode) (x y : abstract_IEEE) :=
  abstract_add m x (abstract_opp y).

(**************************************************************************)
(*                             Multiplication                             *)
(**************************************************************************)
Definition sign_of_mult (b1 b2 : bool) :=
  ifb b1 (ifb b2 true false) (ifb b2 false true).

Definition abstract_mult (m : rounding_mode) (x y : abstract_IEEE) :=
  match x, y return (abstract_IEEE * exception) with
  | NaN s1, _ => (NaN s1, Nothing)
  | _, NaN s2 => (NaN s2, Nothing)
  | Infty b1, Infty b2 => (Infty (sign_of_mult b1 b2), Nothing)
  | Infty b1, _ => (Infty b1, Nothing)
  | _, Infty b2 => (Infty b2, Nothing)
  | _, _ =>
      abstract_of_diadic_s m
        (Dmult (diadic_of_abstract x) (diadic_of_abstract y))
  end.

(**************************************************************************)
(*                                Division                                *)
(**************************************************************************)

Definition abstract_div (m : rounding_mode) (x y : abstract_IEEE) :=
  match x, y return (abstract_IEEE * exception) with
  | NaN s1, _ => (NaN s1, Nothing)
  | _, NaN s2 => (NaN s2, Nothing)
  | Infty _, Infty _ => (NaN quiet, Invalid_operation)
  | Zero _, Zero _ => (NaN quiet, Invalid_operation)
  | Infty b1, Normal b2 _ _ => (Infty (sign_of_mult b1 b2), Nothing)
  | Infty b1, Subnormal b2 _ =>
      (Infty (sign_of_mult b1 b2), Nothing)
      (*  | (Infty b1) (Zero b2) => ((Infty (sign_of_mult b1 b2)), Nothing) *)
      
  | Zero b1, Infty b2 => (Zero (sign_of_mult b1 b2), Nothing)
  | Subnormal b1 _, Infty b2 => (Zero (sign_of_mult b1 b2), Nothing)
  | Normal b1 _ _, Infty b2 => (Zero (sign_of_mult b1 b2), Nothing)
  | Infty b1, Zero b2 => (Infty (sign_of_mult b1 b2), Division_by_zero)
  | Normal b1 _ _, Zero b2 => (Infty (sign_of_mult b1 b2), Division_by_zero)
  | Subnormal b1 _, Zero b2 => (Infty (sign_of_mult b1 b2), Division_by_zero)
  | _, _ =>
      abstract_of_diadic_s m
        (Ddiv m (dig_length t) (diadic_of_abstract x) (diadic_of_abstract y))
  end.

(**************************************************************************)
(*                              Square root                               *)
(**************************************************************************)
Definition sqrt_abstract (m : rounding_mode) (x : abstract_IEEE) :=
  match x return (abstract_IEEE * exception) with
  | NaN s => (NaN s, Nothing)
  | Infty b => (Infty b, Nothing)
  | _ =>
      match Dnum (diadic_of_abstract x) with
      | Z0 => (Zero true, Nothing)
      | Zpos p =>
          abstract_of_diadic_s m
            (Dsqrt m (dig_length t) p (Dexp (diadic_of_abstract x)))
      | Zneg _ => (NaN quiet, Invalid_operation)
      end
  end.

End definitions.

(**************************************************************************)
(*                    Pretty Printing of IEEE numbers                     *)
(**************************************************************************)

Notation "#+ m 'E' e" := (C_build _ true e m) (at level 25, only printing).
Notation "#- m 'E' e" := (C_build _ false e m) (at level 25, only printing).

(* One would need a specific printer *)
Notation "0" := regO (only printing).
Notation "r 1" := (regS _ true r)
  (at level 24, left associativity, only printing).
Notation "r 0" := (regS _ false r)
  (at level 24, left associativity, only printing).

Check (C_build Single false
         (regS _ true (regS _ true (regS _ true (regS _ true (regS _ true (regS _ true (regS _ true (regS _ true regO))))))))
         (regS _ false (regS _ true (regS _ true (regS _ false (regS _ true (regS _ true (regS _ true (regS _ false (regS _ true (regS _ true (regS _ true (regS _ true (regS _ false (regS _ true (regS _ true (regS _ true (regS _ true (regS _ false (regS _ true (regS _ true (regS _ true (regS _ false (regS _ true regO)))))))))))))))))))))))).

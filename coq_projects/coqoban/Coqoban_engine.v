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


Set Implicit Arguments.
Unset Strict Implicit.

(* The game of Sokoban, the Japanese warehouse keeper's game. The keeper must
   push the boxes to specified destination places. He can only push one box at
   a time, no more, and he can't pull. How to put the boxes in place? *)

(* The boards microban_1 and microban_2 kindly taken from KSokoban, the Sokoban
   game included in the games package of the KDE desktop environment. Visit www.kde.org! *)

Inductive fieldtype : Type :=
  | Empty : fieldtype
  | Wall : fieldtype
  | Keeper : fieldtype
  | Box : fieldtype
  | Dest : fieldtype (* fields to put a box on (destination fields) *)
  | Full : fieldtype (* a destination field with a box on it *)
  | KeepOD : fieldtype. (* a destination field with the keeper on top *)

Inductive Direction : Type :=
  | No : Direction
  | Ea : Direction
  | So : Direction
  | We : Direction.

(* A row is a list of fields: *)
Inductive Row : Type :=
  | Nil : Row
  | C : fieldtype -> Row -> Row.

(* A playing board is a list of rows. However we have an additional "cons"
   constructor K to keep track of the row where the keeper is to be found.
   This diminishes searching and pattern matching difficulties *)
Inductive Board : Type :=
  | Nothing : Board
  | R : Row -> Board -> Board
  | K : Row -> Board -> Board.


(* Some syntax to represent a playing board nicely *)
(* See below for examples *)

(* Printing *)


(* To define when the game is over. I use the simplest rule:
   A board isn't finished as long as there are still boxes 'on the loose'
   (ie. not on a destination field) *)
Definition fieldready (x : fieldtype) : Prop :=
  match x with
  | Box => False
  | _ => True
  end.

Fixpoint rowready (r : Row) : Prop :=
  match r with
  | Nil => True
  | C x xs => fieldready x /\ rowready xs
  end.

Fixpoint ready (b : Board) : Prop :=
  match b with
  | Nothing => True
  | R row b' => rowready row /\ ready b'
  | K row b' => rowready row /\ ready b'
  end.



(* Extra datatypes to facilitate in- and output of functions: *)
Record triple : Type := tri {t1 : fieldtype; t2 : fieldtype; t3 : fieldtype}.

Inductive Can : Type :=
  | CAN : triple -> Can
  | CANT : Can.

(* This datatype is for pushing over 3 rows. It only occurs as output of an
   (auxiliary) pushing function of type Row->Row->Row->Tri. Both constructors
   bind together 3 rows, so the function has, in practice, 3 rows as both in-
   and output. The constructor keeps track of we have in fact pushed something *)
Inductive Tri : Type :=
  | TrS : Row -> Row -> Row -> Tri (* S - pushing Succesfully *)
  | TrF : Row -> Row -> Row -> Tri. (* F - pushing Failed *)



(* Rules for pushing the keeper. Input is a triple of adjacent fields where we try
   to push 'from left to right' - so the keeper must be on the first field: *)
Definition move (tr : triple) : Can :=
  match tr with
  | tri Keeper Empty x => CAN (tri Empty Keeper x)
  | tri Keeper Dest x => CAN (tri Empty KeepOD x)
  | tri Keeper Box Empty => CAN (tri Empty Keeper Box)
  | tri Keeper Box Dest => CAN (tri Empty Keeper Full)
  | tri Keeper Full Empty => CAN (tri Empty KeepOD Box)
  | tri Keeper Full Dest => CAN (tri Empty KeepOD Full)
  | tri KeepOD Empty x => CAN (tri Dest Keeper x)
  | tri KeepOD Dest x => CAN (tri Dest KeepOD x)
  | tri KeepOD Box Empty => CAN (tri Dest Keeper Box)
  | tri KeepOD Box Dest => CAN (tri Dest Keeper Full)
  | tri KeepOD Full Empty => CAN (tri Dest KeepOD Box)
  | tri KeepOD Full Dest => CAN (tri Dest KeepOD Full)
  | _ => CANT
  end.


(* Three auxiliary functions *)

(* Takes a row (containing the keeper) and moves the keeper east *)
Fixpoint rowstepeast (r : Row) : Row :=
  match r with
  | C x rs =>
      match rs with
      | C y (C z rs') =>
          match move (tri x y z) with
          | CAN (tri x' y' z') => C x' (C y' (C z' rs'))
          | CANT => C x (rowstepeast rs)
          end
      | _ => r
      end
  | Nil => Nil
  end.

(* similarly west *)
Fixpoint rowstepwest (r : Row) : Row :=
  match r with
  | C x rs =>
      match rs with
      | C y (C z rs') =>
          match move (tri z y x) with
          | CAN (tri z' y' x') => C x' (C y' (C z' rs'))
          | CANT => C x (rowstepwest rs)
          end
      | _ => r
      end
  | Nil => Nil
  end.

(* North and South are more difficult because it uses 3 different rows. This
   auxiliary function takes 3 rows with the keeper on the 1st. We search through
   this 1st row until we encounter the keeper; from the 2nd and 3rd rows we take
   the same elements. With these we form a triple with which to move. The keeper
   and the elements of the 2nd and 3rd rows are replaced, and with that the
   output is constructed *)
Fixpoint Tristep' (r1 : Row) : Row -> Row -> Tri :=
  fun r2 r3 =>
  match r1 with
  | Nil => TrF r1 r2 r3
  | C Keeper r1s =>
      match r2, r3 with
      | C y r2s, C z r3s =>
          match move (tri Keeper y z) with
          | CAN (tri x' y' z') => TrS (C x' r1s) (C y' r2s) (C z' r3s)
          | CANT => TrF r1 r2 r3
          end
      | _, _ => TrF r1 r2 r3
      end
  | C KeepOD r1s =>
      match r2, r3 with
      | C y r2s, C z r3s =>
          match move (tri KeepOD y z) with
          | CAN (tri x' y' z') => TrS (C x' r1s) (C y' r2s) (C z' r3s)
          | CANT => TrF r1 r2 r3
          end
      | _, _ => TrF r1 r2 r3
      end
  | C x r1s =>
      match r2, r3 with
      | C y r2s, C z r3s =>
          match Tristep' r1s r2s r3s with
          | TrS r1' r2' r3' => TrS (C x r1') (C y r2') (C z r3')
          | TrF r1' r2' r3' => TrF (C x r1') (C y r2') (C z r3')
          end
      | _, _ => TrF r1 r2 r3
      end
  end.



(* The actual moving functions: we search the board row-by-row until we find
   a pattern of 1 (East/West) or 3 (North/South) rows with which to move *)
Fixpoint stepnorth (b : Board) : Board :=
  match b with
  | R l1 (R l2 (K l3 b')) =>
      match Tristep' l3 l2 l1 with
      | TrS l3' l2' l1' => R l1' (K l2' (R l3' b'))
      | TrF l3' l2' l1' => R l1' (R l2' (K l3' b'))
      end
  | R r b' => R r (stepnorth b')
  | _ => b
  end.

Fixpoint stepeast (b : Board) : Board :=
  match b with
  | K r b' => K (rowstepeast r) b'
  | R r b' => R r (stepeast b')
  | Nothing => Nothing
  end.

Fixpoint stepsouth (b : Board) : Board :=
  match b with
  | R r b' => R r (stepsouth b')
  | K l1 (R l2 (R l3 b')) =>
      match Tristep' l1 l2 l3 with
      | TrS l1' l2' l3' => R l1' (K l2' (R l3' b'))
      | TrF l1' l2' l3' => K l1' (R l2' (R l3' b'))
      end
  | _ => b
  end.

Fixpoint stepwest (b : Board) : Board :=
  match b with
  | K r b' => K (rowstepwest r) b'
  | R r b' => R r (stepwest b')
  | Nothing => Nothing
  end.


(* This one's obvious: *)
Definition dostep (r : Direction) (b : Board) : Board :=
  match r with
  | No => stepnorth b
  | Ea => stepeast b
  | So => stepsouth b
  | We => stepwest b
  end.



(* The game of Sokoban now boils down to: given a board, prove it's solvable.
   If it's ready (see above: no loose boxes) then it's solvable (constructor OK)
   and it is also solvable if it's solvable after one step (constructor STEP) *)
Inductive solvable : Board -> Prop :=
  | OK : forall b : Board, ready b -> solvable b
  | STEP :
      forall (b : Board) (d : Direction), solvable (dostep d b) -> solvable b.


(* Four tactics to play the game easier: *)
Ltac n :=
  apply STEP with No; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac e :=
  apply STEP with Ea; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac s :=
  apply STEP with So; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac w :=
  apply STEP with We; simpl in |- *; try (apply OK; simpl in |- *; tauto).

(* Notations *)
Notation "'_' a" := (C Empty a) (at level 0, right associativity).
Notation "#  a" := (C Wall a) (at level 0, right associativity).
Notation "+ a" := (C Keeper a) (at level 0, right associativity).
Notation "'X' a" := (C Box a) (at level 0, right associativity).
Notation "'O' a" := (C Dest a) (at level 0, right associativity).
Notation "*  a" := (C Full a) (at level 0, right associativity).
Notation "'o'  a" := (C KeepOD a) (at level 0, right associativity).
Notation "<|" := Nil (at level 0).

Notation "|> a b" := (R a b)
  (format "'[v' |>  a '/' b ']'", at level 0, a, b at level 0).
Notation "+> a b" := (K a b)
  (format "'[v' +>  a '/' b ']'", at level 0, a, b at level 0).
Notation "|><|" := Nothing (format "|><| '//'", at level 0).

(* A silly example *)

Definition b :=
  |> # # # # # # # <|
  |> # _ _ _ _ _ # <|
  +> #
     _ +
       X _ _ # <| (* Note: the row containing the keeper (+) must be indicated *)
  |> #
     _ _ _ _ _ # <| (*       by +> instead of |>  (constructor K instead of R)  *)
  |> # _ _ _ _ O # <|
  |> # # # # # # # <|
  |><|
  .

Goal solvable b.
unfold b in |- *.
(* Stepping east, the hard way *)
apply STEP with Ea.
unfold dostep in |- *.
unfold stepeast in |- *.
unfold rowstepeast in |- *.
unfold move in |- *.
(* Another step east, still hard *)
apply STEP with Ea.
simpl in |- *.
(* Or using simply the tactics: *)
n.
(* We can tell Coq to go north even if there's a wall *)
n.
e.
s.
s.
Save solution'_b.
Print solution'_b. (* Look at the start of this term! *)

Definition microban_1 :=
  |> # # # # <|
  |> # _ O # <|
  |> # _ _ # # # <|
  +> # *  + _ _ # <|
  |> # _ _ X _ # <|
  |> # _ _ # # # <|
  |> # # # # <|
  |><|
  .

Goal solvable microban_1.
unfold microban_1 in |- *.
s.
w.
n.
e.
e.
e.
s.
w.
n.
w.
w.
s.
s.
e.
n.
w.
n.
e.
n.
n.
w.
s.
e.
s.
s.
e.
e.
n.
w.
s.
w.
n.
n.
Save microban_1_solution.
Print microban_1_solution.

Definition microban_2 :=
  |> # # # # # # <|
  |> # _ _ _ _ # <|
  +> # _ # + _ # <|
  |> #
     _ X * 
          (* The amount of whitespace doesn't matter in creating the boards *)
         _  (* as long as it's there in the proper places *)
         # <|
  |> # _ O *  _ # <|
  |> # _ _ _ _ # <|
  |> # # # # # # <|
  |><|
  .
Print microban_2.

Goal solvable microban_2.
unfold microban_2 in |- *.
(* Try this yourself! *)
Abort.
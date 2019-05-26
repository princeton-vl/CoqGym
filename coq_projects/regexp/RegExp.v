(** * RegExp Library *)

(** The Library [RegExp] is a Coq library for regular expression.
The implementation is based on the Janusz Brzozowski's algorithm
("Derivatives of Regular Expressions", Journal of the ACM 1964). *)

(** [RegExp] is a Kleene Algebra.
The following are axioms of Kleene Algebra ("Axioms of Kleene Algebra", 
 http://www.cs.cornell.edu/courses/cs786/2004sp/Lectures/l02-axioms.pdf).

The Kleene Algebra is an idempotent semiring; therefore for any elements $x, y, z:$ #x,y,z:#
 - $ x + (y + z) = (x + y) + z $ # x + (y + z) = (x + y) + z # ([Or_assoc])
 - $ x + y = y + x $ # x + y = y + x # ([Or_comm])
 - $ x + 0 = 0 + x = x $ # x + 0 = 0 + x = x # ([Or_left_id], [Or_right_id])
 - $ x + x = x $ # x + x = x # ([Or_idem])
 - $ x (y z) = (x y) z $ # x(yz) = (xy)z # ([Cat_assoc])
 - $ 1 x = x 1 = 1 $ # 1x = x1 = 1 # ([Cat_left_id], [Cat_right_id])
 - $ x (y + z) = x y + x z $ # x (y + z) = xy + xz # ([Cat_distr_left])
 - $ (x + y) z = x z + x y $ # (x + y) z = xz + xy # ([Cat_distr_right])
 - $ 0 x = x 0 = 0 $ # 0x = x0 = 0 # ([Cat_left_zero], [Cat_right_zero]).

*)

(** Additionally, in terms of partial order $\leq$ #<=# defined as
$ x \leq y \Leftrightarrow x + y = y, $ # x <= y iff x + y = y, #
axioms for Kleene star are given as follows:
 - $ 1 + x x^{\ast} \leq x $ # 1 + x x* <= x # ([Star_right])
 - $ 1 + x^{\ast} x \leq x $ # 1 + x* x <= x # ([Star_left])
 - $ b + a x \leq x \Rightarrow a^{\ast} b \leq x $ # b + ax <= x -> a*b <= x # ([Star_eq_left])
 - $ b + x a \leq x \Rightarrow b a^{\ast} \leq x $ # b + xa <= x -> ba* <= x. # ([Star_eq_right])

These axioms are proved in this library. 

In order to transform [RegExp] using these axioms and setoid tactics, 
[RegExp] is defined as a Setoid with the equivalence relation [re_eq].
Elements of [RegExp] satisfy [re_eq] when they give the same matching result to any strings.
*) 

(** * Coq codes *)
(** ** Dependencies *)

Require Export RegExp.Utility.
Require Export RegExp.Definitions.
Require Export RegExp.Boolean.
Require Export RegExp.Concat.
Require Export RegExp.Star.
Require Export RegExp.Includes.
Require Export RegExp.Char.

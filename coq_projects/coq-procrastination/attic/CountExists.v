Module Implem1.

(* A set of tactics to count the number of exists in the goal. This requires
   crazy tricks, but surprisingly, works. *)
Local Ltac count_exists_loop H k :=
  let ty := type of H in
  match ty with
  | @ex _ _ => count_exists_loop_aux H k
  | @sig _ _ => count_exists_loop_aux H k
  | @sigT _ _ => count_exists_loop_aux H k
  | _ => k O
  end

with count_exists_loop_aux H k :=
  let x := fresh in
  destruct H as [x H];
  count_exists_loop H ltac:(fun res => k (S res)).

Local Lemma count_exists_helper :
  forall G, (G -> True) -> nat -> nat.
Proof. auto. Defined.

Local Ltac count_exists_aux ty :=
  let n := fresh in
  evar (n : nat);
  apply (count_exists_helper ty); [
    let H := fresh in
    intro H;
    count_exists_loop H ltac:(fun res => instantiate (n := res));
    exact I
  | exact n].

(* The [constr:(ltac:())] trick spawns a "ghost" goal of type [nat], in which
   [count_exists_aux] is run; it returns its result by providing the right
   number as proof of the goal.
*)
Ltac count_exists g cont :=
  let n := constr:(ltac:(count_exists_aux g) : nat) in
  let n := eval cbv in n in
  cont n.

(* Test for [count_exists] *)
Goal exists a b c, a + b = c.
  match goal with |- ?g =>
    count_exists g ltac:(fun n => assert (n = 3) by reflexivity)
  end.
Abort.

End Implem1.

(*************************)

Module Implem2.

(* This uses the neat trick provided in the comment section of
   http://gallium.inria.fr/blog/how-to-quantify-quantifiers-an-ltac-puzzle/ (!)
   which is apparently inspired by Adam Chlipala's book. *)

Ltac count_exists_loop G n :=
  lazymatch G with
  | (fun g => exists x, @?body g x) =>
    count_exists_loop
      ltac:(eval cbv beta in (fun g => body (fst g) (snd g))) (S n)
  | _ => constr:(n)
  end.

Ltac count_exists g :=
  count_exists_loop (fun (_:unit) => g) O.

End Implem2.
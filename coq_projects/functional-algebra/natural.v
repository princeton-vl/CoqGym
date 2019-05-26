(*
  This module defines the Natural record type which can be uses to
  represent and model the natural numbers.
*)

Require Import base.
Require Import group.
Require Import abelian_group.
Require Import ring.
Require Import commutative_ring.
Require Import field.

Inductive Natural_Number : Set
  := E_0  : Natural_Number
  |  succ : Natural_Number -> Natural_Number.

Structure Natural : Type := natural {
  E
    :  Set
    := Natural_Number;

  E_1
    :  E
    := succ E_0;

  E_rect 
    :  forall P : E -> Type, P E_0 -> (forall n : E, P n -> P (succ n)) -> forall n : E, P n
    := fun (P : E -> Type) (f : P E_0) (f0 : forall n : E, P n -> P (succ n))
         => fix F (n : E) : P n
              := match n as n0 return (P n0) with
                   | E_0 => f
                   | succ n0 => f0 n0 (F n0)
                 end;

  E_ind 
    : forall P : E -> Prop, P E_0 -> (forall x : E, P x -> P (succ x)) -> forall x : E, P x
    := fun P : E -> Prop
         => E_rect P;

  E_rec 
    :  forall F : E -> Set, F E_0 -> (forall x : E, F x -> F (succ x)) -> forall x : E, F x
    := fun P : E -> Set
         => E_rect P;
        
  sum
    :  E -> E -> E
    := fun x y => E_rec (fun _ => E) y (fun _ F => succ F) x;

  (* sum E_0 x = x
     sum (succ x) y = succ (sum x y) *)

  sum_is_id_l
    :  E -> Prop
    := fun x : E => is_id_l E sum x;

  sum_is_id_r
    :  E -> Prop
    := fun x : E => is_id_r E sum x;

  sum_is_id
    :  E -> Prop
    := fun x : E => is_id E sum x;

  sum_id_l
    :  sum_is_id_l E_0
    := fun x => eq_refl x;

  sum_id_r
    :  sum_is_id_r E_0
    := E_ind
         (fun x => sum x E_0 = x)
         (eq_refl E_0)
         (fun x (H : sum x E_0 = x)
           => eq_ind_r
                (fun a => succ a = succ x)
                (eq_refl (succ x))
                H);

  sum_comm
    :  is_comm E sum
    := E_rec
         (fun x => forall y : E, sum x y = sum y x)
         (fun y
            => let H : sum E_0 y = y
                 := eq_ind_r
                      (fun a => a = y)
                      (eq_refl y)
                      (sum_id_l y) in
               let H0 : sum E_0 y = sum y E_0
                 := eq_ind_r
                      (fun a => sum E_0 y = a)
                      H
                      (sum_id_r y) in
               H0)
         (fun x (H : forall y : E, sum x y = sum y x)
           => E_rec
                (fun y => sum (succ x) y = sum y (succ x))
                (let H0 :  sum (succ x) E_0 = succ x
                   := sum_id_r (succ x) in
                 let H1 :  sum (succ x) E_0 = sum E_0 (succ x)
                   := eq_ind_r
                        (fun a => sum (succ x) E_0 = a)
                        H0
                        (sum_id_l (succ x)) in
                 H1)
                (fun y (H0 : sum (succ x) y = sum y (succ x))
                  => let H1 : succ (succ (sum y x)) = succ (succ (sum x y))
                           (* succ (sum (succ y) x) = succ (sum (succ x) y) *)
                       := eq_ind
                            (sum x y)
                            (fun a => succ (succ a) = succ (succ (sum x y)))
                            (eq_refl (succ (succ (sum x y))))
                            (sum y x)
                            (H y) in
                     let H2 : succ (sum x (succ y)) = succ (sum (succ x) y) 
                       := eq_ind_r
                            (fun a => succ a = succ (sum (succ x) y))
                            H1
                            (H (succ y)) in
                     let H3 : succ (sum x (succ y)) = succ (sum y (succ x))
                           (* sum (succ x) (succ y) = sum (succ y) (succ x) *)
                       := eq_ind
                            (sum (succ x) y)
                            (fun a => succ (sum x (succ y)) = succ a)
                            H2
                            (sum y (succ x))
                            H0 in
                     H3));

  sum_assoc
    :  is_assoc E sum
    := fun x
         => E_ind
              (fun y => forall z : E, sum x (sum y z) = sum (sum x y) z)
              (fun z
                => let H  :  sum x (sum E_0 z) = sum x z
                          := eq_ind_r
                               (fun a => sum x a = sum x z)
                               (eq_refl (sum x z))
                               (sum_id_l z) in
                   let H0 :  sum x (sum E_0 z) = sum (sum x E_0) z
                          := eq_ind_r
                               (fun a => sum x (sum E_0 z) = sum a z)
                             H
                             (sum_id_r x) in
                   H0)
              (fun y (H : forall z : E, sum x (sum y z) = sum (sum x y) z) z
                => (* g : sum x (sum (succ y) z) = sum (sum x (succ y)) z
                          sum x (succ (sum y z)) = sum (sum x (succ y)) z *)
                   let H0 :  succ (sum x (sum y z)) = succ (sum (sum x y) z)
                          := eq_ind_r
                               (fun a => succ a = succ (sum (sum x y) z))
                               (eq_refl (succ (sum (sum x y) z)))
                               (H z) in
                   let H1 :  succ (sum (sum y z) x) = succ (sum (sum x y) z)
                          (* sum (succ (sum y z)) x = succ (sum (sum x y) z) *)
                          := eq_ind_r
                               (fun a => succ a = succ (sum (sum x y) z))
                               H0
                               (sum_comm (sum y z) x) in
                   let H2 :  sum x (succ (sum y z)) = succ (sum (sum x y) z)
                          (* sum x (succ (sum y z)) = sum (succ (sum x y) z) *)
                          := eq_ind_r
                               (fun a => a = succ (sum (sum x y) z))
                               H1
                               (sum_comm x (succ (sum y z))) in
                   let H3 :  sum x (succ (sum y z)) = sum (succ (sum y x)) z
                          (* sum x (succ (sum y z)) = sum (sum (succ y) x) z *)
                          := eq_ind_r
                               (fun a => sum x (succ (sum y z)) = sum (succ a) z)
                               H2
                               (sum_comm y x) in
                   let H4 :  sum x (sum (succ y) z) = sum (sum x (succ y)) z
                          := eq_ind_r
                               (fun a => sum x (sum (succ y) z) = sum a z)
                               H3
                               (sum_comm x (succ y)) in
                   H4);

  sum_1_succ_l
    :  forall x : E, sum E_1 x = succ x
    := fun x
         => eq_ind_r
              (fun a => succ a = succ x)
              (eq_refl (succ x))
              (sum_id_l x);

  sum_1_succ_r
    :  forall x : E, sum x E_1 = succ x
    := fun x
         => eq_ind_r
              (fun a => a = succ x)
              (sum_1_succ_l x)
              (sum_comm x E_1);

  sum_1_succ
    :  forall x : E, (sum E_1 x = succ x /\ sum x E_1 = succ x)
    := fun x
         => conj (sum_1_succ_l x) (sum_1_succ_r x);

  prod
    :  E -> E -> E
    := fun x y => E_rec (fun _ => E) E_0 (fun _ F => sum y F) x;

  (* prod E_0 y = E_0
     prod (succ x) y = sum y (prod x y) *)

  prod_0_l
    :  forall x : E, prod E_0 x = E_0
    := fun x
         => eq_refl E_0;

  prod_0_r
    :  forall x : E, prod x E_0 = E_0
    := E_ind
         (fun x => prod x E_0 = E_0)
         (eq_refl E_0)
         (fun x (H : prod x E_0 = E_0)
           => eq_ind_r
                (fun a => a = E_0)
                H
                (sum_id_l (prod x E_0)));

  prod_is_id_l
    :  E -> Prop
    := fun x : E => is_id_l E prod x;

  prod_is_id_r
    :  E -> Prop
    := fun x : E => is_id_r E prod x;

  prod_is_id
    :  E -> Prop
    := fun x : E => is_id E prod x;

  prod_id_l
    :  prod_is_id_l E_1
    := fun x
         => eq_ind_r
              (fun a => sum x a = x)
              (sum_id_r x)
              (prod_0_l x);

  prod_id_r
    :  prod_is_id_r E_1
    := E_ind
         (fun x => prod x E_1 = x)
         (prod_0_l E_1)
         (fun x (H : prod x E_1 = x)
           => (* g : prod (succ x) E_1 = succ x
                 - g : sum E_1 (prod x E_1) = succ x
                 - g : sum E_1 x = succ x *)
              eq_ind_r
                (fun a => sum E_1 a = succ x)
                (sum_1_succ_l x)
                (prod_id_l x));

  prod_comm
    :  is_comm E prod
    := E_ind
         (fun x => forall y : E, prod x y = prod y x)
         (E_ind
           (fun y => prod E_0 y = prod y E_0)
           (eq_refl E_0)
           (fun y (H : prod E_0 y = prod y E_0)
             => H
                =|= (fun a => a = prod y E_0) by (prod_0_l y)
                =|= (fun a => E_0 = a) by (sum_id_l (prod y E_0))
                =|= (fun a => a = prod (succ y) E_0) by (prod_0_l (succ y))))
         (fun x (H : forall y : E, prod x y = prod y x)
           => E_ind
                (fun y => prod (succ x) y = prod y (succ x))
                (prod_0_r (succ x))
                (fun y (H0 : prod (succ x) y = prod y (succ x))
                  => (eq_refl (sum (succ (sum x y)) (prod x y)))
                     =|= [[ (prod y x) | (prod x y) ]]
                         (fun a => sum (succ (sum x y)) a = sum (succ (sum x y)) (prod x y))
                         by (H y)
                     =|= (fun a => sum (succ a) (prod y x) = sum (succ (sum x y)) (prod x y))
                         by (sum_comm y x)
                     =|= (fun a => a = sum (sum (succ x) y) (prod x y))
                         by (sum_assoc (succ y) x (prod y x))
                     =|= (fun a => sum (succ y) (sum x (prod y x)) = a)
                         by (sum_assoc (succ x) y (prod x y))
                     =|= [[ (prod y (succ x)) | (prod (succ x) y) ]]
                         (fun a => sum (succ y) (sum x (prod y x)) = sum (succ x) a)
                         by H0
                     =|= (fun a => sum (succ y) a = sum (succ x) (prod y (succ x)))
                         by (H (succ y))));

  prod_succ_l
    :  forall x y : E, prod (succ x) y = sum y (prod x y)

  prod_succ_r
    :  forall x y : E, prod y (succ x) = sum (prod y x) y
    := fun x y
         => eq_refl (prod (succ x) y)
            =|= (fun a => a = sum y (prod x y))
                by (prod_comm y (succ x))
            =|= (fun a => prod y (succ x) = a)
                by (sum_comm (prod x y) y)
            =|= (fun a => prod y (succ x) = sum a y)
                by (prod_comm y x);

  prod_distrib_l
    :  is_distrib_l E prod sum
    := E_ind
         (fun x => forall y z : E, prod x (sum y z) = sum (prod x y) (prod x z))
         (fun y z => eq_refl E_0)
         (fun x (H : forall y z : E, prod x (sum y z) = sum (prod x y) (prod x z)) y z
           => (eq_refl (sum (sum y z) (sum (prod x y) (prod x z))))
              =|= [[ (sum (sum (sum y z) (prod x y)) (prod x z)) | (sum (sum y z) (sum (prod x y) (prod x z))) ]]
                  (fun a => sum (sum y z) (sum (prod x y) (prod x z)) = a)
                  by (sum_assoc (sum y z) (prod x y) (prod x z))
              =|= (fun a => sum (sum y z) (sum (prod x y) (prod x z)) = sum a (prod x z))
                  by (sum_assoc y z (prod x y))
              =|= (fun a => sum (sum y z) (sum (prod x y) (prod x z)) = sum (sum y a) (prod x z))
                  by (sum_comm (prod x y) z)
              =|= [[ (sum (sum y (prod x y)) z) | (sum y (sum (prod x y) z)) ]]
                  (fun a => sum (sum y z) (sum (prod x y) (prod x z)) = sum a (prod x z))
                  by (sum_assoc y (prod x y) z)
              =|= (fun a => sum (sum y z) (sum (prod x y) (prod x z)) = a)
                  by (sum_assoc (sum y (prod x y)) z (prod x z))
              =|= (fun a => sum (sum y z) a = sum (prod (succ x) y) (prod (succ x) z))
                  by (H y z));

  prod_distrib_r
    :  is_distrib_r E prod sum
    := fun x y z
         => (prod_distrib_l x y z)
            =|= (fun a => a = sum (prod x y) (prod x z)) by (prod_comm (sum y z) x)
            =|= (fun a => prod (sum y z) x = sum a (prod x z)) by (prod_comm y x)
            =|= (fun a => prod (sum y z) x = sum (prod y x) a) by (prod_comm z x);


  prod_assoc
    :  is_assoc E prod
(*
    := (* (x + 1)(y z) = ((x + 1) y) z
          x (y z) + y z = (x y + y) z
          x (y z) + y z = (x y) z + y z *)
       fun x y z
         => E_ind
              (fun x => prod x (prod y z) = prod (prod x y) z)
              (eq_refl E_0)
              (fun x (H : prod x (prod y z) = prod (prod x y) z)
                => (eq_refl (sum (prod (prod x y) z) (prod y z)))
                   =|= (fun a => a = sum (prod (prod x y) z) (prod y z))
                       by H
                   =|= (fun a => sum (prod x (prod y z)) (prod y z) = a)
                       by (prod_distrib_r z x y)
                   =|= (fun a => sum (prod x (prod y z)) (prod y z) = prod a z)
                       by (sum_comm (prod x y) y)
                   =|= 
*)
}.

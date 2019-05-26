(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                              inversionSL.v                               *)
(****************************************************************************)

(*****************************************************************************)
(*                                                                           *)
(*      Meta-theory of the explicit substitution calculus lambda-env         *)
(*      Amokrane Saibi                                                       *)
(*                                                                           *)
(*      September 1993                                                       *)
(*                                                                           *)
(*****************************************************************************)


                       (* Inversion de sigma_lift (relSL) *)
Require Import sur_les_relations.
Require Import TS.
Require Import sigma_lift.

(*****************
Definition e_invSL:=[b:wsort][M:(TS b)][N:(TS b)]
(<[b:wsort]Prop>Case M of
 (* var *) [n:nat] False
 (* app *) [M1,M2:terms]
           (<[b:wsort]Prop>Case N of
            (* var *) [n:nat]False
            (* app *) [N1,N2:terms]
                      ((relSL M1 N1) /\ (M2=N2)) 
                   \/ ((M1=N1) /\ (relSL M2 N2))
            (* lam *) [N1:terms]False 
            (* env *) [N1:terms][N2:sub_explicits]False
            (* id  *) False
            (*  |  *) False
            (*  .  *) [N1:terms][N2:sub_explicits]False
            (*  o  *) [N1,N2:sub_explicits]False
            (* ||  *) [N1:sub_explicits]False
            (*  X  *) [n:nat]False
            (*  x  *) [n:nat]False  end)
 (* lam *) [M1:terms]
           (<[b:wsort]Prop>Case N of
            (* var *) [n:nat]False
            (* app *) [N1,N2:terms]False 
            (* lam *) [N1:terms](relSL M1 N1)
            (* env *) [N1:terms][N2:sub_explicits]False
            (* id  *) False
            (*  |  *) False
            (*  .  *) [N1:terms][N2:sub_explicits]False
            (*  o  *) [N1,N2:sub_explicits]False
            (* ||  *) [N1:sub_explicits]False
            (*  X  *) [n:nat]False
            (*  x  *) [n:nat]False  end)
 (* env *) [M1:terms][M2:sub_explicits]
           (<[b:wsort]Prop>Case N of
            (* var *) [n:nat] 
                 (Ex( ([m:nat] (M1=(var m)) /\ (n=(S m)) /\ (M2=shift) )))
             \/  (Ex( ([s:sub_explicits] (M1=(var O)) /\
                                  (M2=(lift s)) /\ (n=O) )))
             \/  (Ex( ([s:sub_explicits] (M1=(var O)) /\
                            (M2=(cons (var n) s)) )))
             \/ ((M1=(var n)) /\ (M2=id))
            (* app *) [N1,N2:terms]
                (Ex( ([a:terms] (Ex( ([b:terms] (M1=(app a b))
                    /\ (N1=(env a M2)) /\ (N2=(env b M2)) ))) )))
             \/ (Ex( ([s:sub_explicits] (M1=(var O)) /\
                            (M2=(cons (app N1 N2) s)) )))
             \/ ((M1=(app N1 N2)) /\ (M2=id)) 
            (* lam *) [N1:terms]
                (Ex( ([a:terms] (M1=(lambda a))
                                 /\ (N1=(env a (lift M2))) )))
             \/ (Ex( ([s:sub_explicits] (M1=(var O)) /\
                            (M2=(cons (lambda N1) s)) )))
             \/ ((M1=(lambda N1)) /\ (M2=id) )
            (* env *) [N1:terms][N2:sub_explicits]
                (Ex( ([s:sub_explicits] (M1=(env N1 s)) /\
                            (N2=(comp s M2)) )))   
             \/ (Ex( ([n:nat] (M1=(var n)) /\
                       (M2=(comp shift N2)) /\ (N1=(var (S n))) )))
             \/ (Ex( ([s:sub_explicits] (M1=(var O)) /\
                               (M2=(cons (env N1 N2) s)) )))
             \/ (Ex( ([s:sub_explicits] (M1=(var O)) /\
                        (M2=(comp (lift s) N2)) /\ (N1=(var O)) )))
             \/ (Ex( ([n:nat] (Ex( ([a:terms] (M1=(var (S n))) /\
                        (M2=(cons a N2)) /\ (N1=(var n)) ))) )))
             \/ (Ex( ([n:nat] (Ex( ([s:sub_explicits]
                   (M1=(var (S n))) /\ (M2=(lift s)) /\
                   (N1=(var n)) /\ (N2=(comp s shift)) ))) )))
             \/ (Ex( ([n:nat] (Ex( ([s:sub_explicits]
                  (Ex( ([t:sub_explicits] (M1=(var (S n))) /\
                  (M2=(comp (lift s) t)) /\ (N1=(var n)) /\
                  (N2=(comp s (comp shift t))) ))) ))) )))
             \/ ((M1=(env N1 N2)) /\ (M2=id))                  
             \/ ((relSL M1 N1) /\ (M2=N2))
             \/ ((M1=N1) /\ (relSL M2 N2))
            (* id  *) False
            (*  |  *) False
            (*  .  *) [N1:terms][N2:sub_explicits]False
            (*  o  *) [N1,N2:sub_explicits]False
            (* ||  *) [N1:sub_explicits]False
            (*  X  *) [n:nat]
             (Ex( ([s:sub_explicits] (M1=(var O)) /\
                            (M2=(cons (meta_X n) s)) )))
             \/ ((M1=(meta_X n)) /\ (M2=id))
            (*  x  *) [n:nat]False  end)
 (* id  *) False
 (*  |  *) False 
 (*  .  *) [M1:terms][M2:sub_explicits]
           (<[b:wsort]Prop>Case N of
            (* var *) [n:nat]False
            (* app *) [N1,N2:terms]False 
            (* lam *) [N1:terms]False 
            (* env *) [N1:terms][N2:sub_explicits]False
            (* id  *) False
            (*  |  *) False
            (*  .  *) [N1:terms][N2:sub_explicits]
                      ((relSL M1 N1) /\ (M2=N2))
                      \/  ((M1=N1) /\ (relSL M2 N2))
            (*  o  *) [N1,N2:sub_explicits]False
            (* ||  *) [N1:sub_explicits]False
            (*  X  *) [n:nat]False
            (*  x  *) [n:nat]False  end)
 (*  o  *) [M1,M2:sub_explicits]
           (<[b:wsort]Prop>Case N of
            (* var *) [n:nat]False
            (* app *) [N1,N2:terms]False 
            (* lam *) [N1:terms]False
            (* env *) [N1:terms][N2:sub_explicits]False
            (* id  *) (Ex( ([a:terms] (M1=shift) /\
                           (M2=(cons a id)) )))
                   \/ ((M1=id) /\ (M2=id))
            (*  |  *) (Ex( ([a:terms] (M1=shift) /\
                        (M2=(cons a shift)) )))
                   \/ ((M1=id) /\ (M2=shift))
                   \/ ((M1=shift) /\ (M2=id))
            (*  .  *) [N1:terms][N2:sub_explicits]
                  (Ex( ([a:terms](Ex( ([s:sub_explicits]
                     (M1=(cons a s)) /\ (N1=(env a M2)) /\
                     (N2=(comp s M2)) ))) )))
               \/ (Ex( ([a:terms] (M1=shift) /\
                        (M2=(cons a (cons N1 N2))) )))
               \/ (Ex( ([s:sub_explicits]
                     (Ex( ([t:sub_explicits] (M1=(lift s)) /\ (M2=(cons N1 t)) 
                         /\ (N2=(comp s t)) ))) )))
               \/ ((M1=id) /\ (M2=(cons N1 N2)))
               \/ ((M1=(cons N1 N2)) /\ (M2=id))
            (*  o  *) [N1,N2:sub_explicits]
                 (Ex( ([t:sub_explicits]
                   (M1=(comp N1 t)) /\ (N2=(comp t M2)) )))
              \/ (Ex( ([a:terms] (M1=shift) /\ (M2=(cons a (comp N1 N2))) )))
              \/ ((M1=shift) /\ (M2=(lift N1)) /\ (N2=shift))
              \/ (Ex( ([t:sub_explicits] (M1=shift) /\
                   (M2=(comp (lift N1) t)) /\ (N2=(comp shift t)) )))
              \/ (Ex( ([s:sub_explicits] 
                 (Ex( ([t:sub_explicits] (M1=(lift s)) /\
                    (M2=(comp (lift t) N2)) /\ (N1=(lift (comp s t)))))))))
              \/ ((M1=id) /\ (M2=(comp N1 N2)))
              \/ ((M1=(comp N1 N2)) /\ (M2=id))
              \/ ((relSL M1 N1) /\ (M2=N2))
              \/ ((M1=N1) /\ (relSL M2 N2)) 
            (* ||  *) [N1:sub_explicits]
                 (Ex( ([a:terms] (M1=shift) /\ (M2=(cons a (lift N1))))))
              \/ (Ex( ([s:sub_explicits] 
                 (Ex( ([t:sub_explicits] (M1=(lift s)) /\
                 (M2=(lift t)) /\ (N1=(comp s t)) ))) )))
              \/ ((M1=id) /\ (M2=(lift N1)))
              \/ ((M1=(lift N1)) /\ (M2=id))
            (*  X  *) [n:nat]False
            (*  x  *) [n:nat] 
                 (Ex( ([a:terms] (M1=shift) /\ (M2=(cons a (meta_x n))))))
                   \/ ((M1=id) /\ (M2=(meta_x n)))
                   \/ ((M1=(meta_x n)) /\ (M2=id))  end)
 (* ||  *) [M1:sub_explicits]
           (<[b:wsort]Prop>Case N of
            (* var *) [n:nat]False
            (* app *) [N1,N2:terms]False 
            (* lam *) [N1:terms]False
            (* env *) [N1:terms][N2:sub_explicits]False
            (* id  *) (M1=id)
            (*  |  *) False
            (*  .  *) [N1:terms][N2:sub_explicits]False
            (*  o  *) [N1,N2:sub_explicits]False
            (* ||  *) [N1:sub_explicits](relSL M1 N1)
            (*  X  *) [n:nat]False
            (*  x  *) [n:nat]False end)
  (*  X  *) [n:nat]False
  (*  x  *) [n:nat]False  end). 

****************)

Definition e_invSL (b : wsort) (M N : TS b) :=
  match M, N with
  | lift M1, id => M1 = id
  | lift M1, lift N1 => e_relSL _ M1 N1
  | lambda M1, lambda N1 => e_relSL _ M1 N1
  | app M1 M2, app N1 N2 =>
      e_relSL _ M1 N1 /\ M2 = N2 \/ M1 = N1 /\ e_relSL _ M2 N2
  | env M1 M2, var n as V =>
      (exists m : nat, M1 = var m /\ n = S m /\ M2 = shift) \/
      (exists s : sub_explicits, M1 = var 0 /\ M2 = lift s /\ n = 0) \/
      (exists s : sub_explicits, M1 = var 0 /\ M2 = cons V s) \/
      M1 = V /\ M2 = id
  | env M1 M2, app N1 N2 as A =>
      (exists a : terms,
         (exists b : terms, M1 = app a b /\ N1 = env a M2 /\ N2 = env b M2)) \/
      (exists s : sub_explicits, M1 = var 0 /\ M2 = cons A s) \/
      M1 = A /\ M2 = id
  | env M1 M2, lambda N1 as L =>
      (exists a : terms, M1 = lambda a /\ N1 = env a (lift M2)) \/
      (exists s : sub_explicits, M1 = var 0 /\ M2 = cons L s) \/
      M1 = L /\ M2 = id
  | env M1 M2, env N1 N2 as E =>
      (exists s : sub_explicits, M1 = env N1 s /\ N2 = comp s M2) \/
      (exists n : nat, M1 = var n /\ M2 = comp shift N2 /\ N1 = var (S n)) \/
      (exists s : sub_explicits, M1 = var 0 /\ M2 = cons E s) \/
      (exists s : sub_explicits,
         M1 = var 0 /\ M2 = comp (lift s) N2 /\ N1 = var 0) \/
      (exists n : nat,
         (exists a : terms, M1 = var (S n) /\ M2 = cons a N2 /\ N1 = var n)) \/
      (exists n : nat,
         (exists s : sub_explicits,
            M1 = var (S n) /\ M2 = lift s /\ N1 = var n /\ N2 = comp s shift)) \/
      (exists n : nat,
         (exists s : sub_explicits,
            (exists t : sub_explicits,
               M1 = var (S n) /\
               M2 = comp (lift s) t /\
               N1 = var n /\ N2 = comp s (comp shift t)))) \/
      M1 = E /\ M2 = id \/
      e_relSL _ M1 N1 /\ M2 = N2 \/ M1 = N1 /\ e_relSL _ M2 N2
  | env M1 M2, meta_X n =>
      (exists s : sub_explicits, M1 = var 0 /\ M2 = cons (meta_X n) s) \/
      M1 = meta_X n /\ M2 = id
  | cons M1 M2, cons N1 N2 =>
      e_relSL _ M1 N1 /\ M2 = N2 \/ M1 = N1 /\ e_relSL _ M2 N2
  | comp M1 M2, id =>
      (exists a : terms, M1 = shift /\ M2 = cons a id) \/ M1 = id /\ M2 = id
  | comp M1 M2, shift =>
      (exists a : terms, M1 = shift /\ M2 = cons a shift) \/
      M1 = id /\ M2 = shift \/ M1 = shift /\ M2 = id
  | comp M1 M2, cons N1 N2 as C =>
      (exists a : terms,
         (exists s : sub_explicits,
            M1 = cons a s /\ N1 = env a M2 /\ N2 = comp s M2)) \/
      (exists a : terms, M1 = shift /\ M2 = cons a C) \/
      (exists s : sub_explicits,
         (exists t : sub_explicits,
            M1 = lift s /\ M2 = cons N1 t /\ N2 = comp s t)) \/
      M1 = id /\ M2 = C \/ M1 = C /\ M2 = id
  | comp M1 M2, comp N1 N2 =>
      (exists t : sub_explicits, M1 = comp N1 t /\ N2 = comp t M2) \/
      (exists a : terms, M1 = shift /\ M2 = cons a (comp N1 N2)) \/
      M1 = shift /\ M2 = lift N1 /\ N2 = shift \/
      (exists t : sub_explicits,
         M1 = shift /\ M2 = comp (lift N1) t /\ N2 = comp shift t) \/
      (exists s : sub_explicits,
         (exists t : sub_explicits,
            M1 = lift s /\ M2 = comp (lift t) N2 /\ N1 = lift (comp s t))) \/
      M1 = id /\ M2 = comp N1 N2 \/
      M1 = comp N1 N2 /\ M2 = id \/
      e_relSL _ M1 N1 /\ M2 = N2 \/ M1 = N1 /\ e_relSL _ M2 N2
  | comp M1 M2, lift N1 as L =>
      (exists a : terms, M1 = shift /\ M2 = cons a L) \/
      (exists s : sub_explicits,
         (exists t : sub_explicits,
            M1 = lift s /\ M2 = lift t /\ N1 = comp s t)) \/
      M1 = id /\ M2 = L \/ M1 = L /\ M2 = id
  | comp M1 M2, meta_x n as x =>
      (exists a : terms, M1 = shift /\ M2 = cons a x) \/
      M1 = id /\ M2 = x \/ M1 = x /\ M2 = id
  | _, _ => False
  end.
(***********)

Notation invSL := (e_invSL _) (only parsing).
(* <Warning> : Syntax is discontinued *)


Goal forall (b : wsort) (M N : TS b), e_systemSL _ M N -> e_invSL _ M N.
simple induction 1; simple induction 1; intros.
(* app *)
simpl in |- *; left; exists a0; exists b1; auto.
(* lambda *)
simpl in |- *; left; exists a0; auto.
(* clos *)
simpl in |- *; left; exists s; auto.
(* varshift1 *)
simpl in |- *; left; exists n; auto.
(* varshift2 *)
simpl in |- *; right; left; exists n; auto.
(* fvarcons *)
pattern a0 in |- *; apply terms_ind; intros; simpl in |- *.
 (* var *)
do 2 right; left; exists s; auto.
 (* app *)
right; left; exists s; auto.
 (* lam *)
right; left; exists s; auto.
 (* env *)
do 2 right; left; exists s; auto.
 (* X *)
left; exists s; auto.
(* fvarlift1 *)
simpl in |- *; right; left; exists s; auto.
(* fvarlift2 *)
simpl in |- *; do 3 right; left; exists s; auto.
(* rvarcons *)
simpl in |- *; do 4 right; left; exists n; exists a0; auto.
(* rvarlift1 *)
simpl in |- *; do 5 right; left; exists n; exists s; auto.
(* rvarlift2 *)
simpl in |- *; do 6 right; left; exists n; exists s; exists t; auto.
(* assenv *)
simpl in |- *; left; exists t0; auto.
(* mapenv *)
simpl in |- *; left; exists a; exists s0; auto.
(* shiftcons *)
pattern s0 in |- *; apply sub_explicits_ind; intros; simpl in |- *.
 (* id *)
left; exists a; auto.
 (*| *)
left; exists a; auto.
 (* . *)
right; left; exists a; auto.
 (* o *)
right; left; exists a; auto.
 (*|| *)
left; exists a; auto.
 (* x *)
left; exists a; auto.
(* shiftlift1 *)
simpl in |- *; do 2 right; left; auto.
(* shiftlift2 *)
simpl in |- *; do 3 right; left; exists t0; auto.
(* lift1 *)
simpl in |- *; right; left; exists s0; exists t0; auto.
(* lift2 *)
simpl in |- *; do 4 right; left; exists s0; exists t0; auto.
(* liftenv *)
simpl in |- *; right; right; left; exists s0; exists t0; auto.
(* idl *)
pattern s0 in |- *; apply sub_explicits_ind; intros; simpl in |- *.
 (* id *)
right; auto.
 (*| *)
right; left; auto.
 (* . *)
do 3 right; left; auto.
 (* o *)
do 5 right; left; auto.
 (*|| *)
do 2 right; left; auto.
 (* x *)
right; left; auto.
(* idr *)
pattern s0 in |- *; apply sub_explicits_ind; intros; simpl in |- *.
 (* id *)
right; auto.
 (*| *)
right; right; auto.
 (* . *)
do 4 right; auto.
 (* o *)
do 6 right; left; auto.
 (*|| *)
do 3 right; auto.
 (* x *)
right; right; auto.
(* liftid *)
simpl in |- *; auto.
(* id *)
pattern a0 in |- *; apply terms_ind; intros; simpl in |- *.
 (* var *)
do 3 right; auto.
 (* app *)
do 2 right; auto.
 (* lam *)
do 2 right; auto.
 (* env *)
do 7 right; left; auto.
 (* X *)
right; auto.
Save lemma1_inv_systemSL.
Hint Resolve lemma1_inv_systemSL.

Goal forall (b : wsort) (M N : TS b), e_relSL _ M N -> e_invSL _ M N.
simple induction 1; intros; simpl in |- *; auto 11.
Save lemma1_invSL.
Hint Resolve lemma1_invSL.











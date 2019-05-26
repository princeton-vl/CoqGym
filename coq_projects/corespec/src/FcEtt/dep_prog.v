(* Tools for dependent programming *)

(* This is the *total* version of these tools, not the fueled one *)

Require FcEtt.imports.


Notation "f >-> g" := (fun x => (g (f x))) (at level 70).

Inductive sig2el (A:Type) (B:Type) (P : A -> B -> Prop) : Type :=
    exist2el : forall (x : A) (y : B), P x y -> sig2el P.

Notation "{ x , y | P }" := (sig2el (fun x y => P)) (at level 0, x at level 99, y at level 99) : type_scope.

(*
Notation "< e , f >"      := (exist2el _ e f _).
*)

Notation "'yeah'"      := (left _ _).
Notation "'nope'"      := (right _ _).

(* Notation "[[ x ]]"     := (inleft _ [x]). *)
Notation "<< x >>"     := (inleft _ (exist _ x _)).
(*
Notation "<< x , y >>" := (inleft _ <x, y>).
*)
Notation "<< x , y >>" := (inleft _ (exist2el _ x y _)).
Notation "!!"          := (inright _ _).


(* Do not use constructors on this: eauto would be tempted to make it run out of fuel all the time (after all, why bother computing a result?) *)
Hint Resolve inleft inright left right.

(* Notations: _ <- _; _ is the notation for destructing a fueled sumor (sumorf), >--> for destructing a fueled sumbool (sumboolf).
   Rule: the arrows are 1 dash longer when the return (type) constructor is different, e.g. destructing a sumboolf to return a sumorf. *)
Notation "x <- e1 ; e2" :=
  (match e1 with
     | inright _ => !!
     | inleft (exist x _) => e2
   end)
(right associativity, at level 60).

(* TODO: this form should check the shape *)
Notation "x <~ e1 ; e2" :=
  (match e1 with
     | inright _ => !!
     | inleft (exist x _) => e2
   end)
(right associativity, at level 60).

Notation "x <-- e1 ; e2" :=
  (match e1 with
     | inright _ => nope
     | inleft (exist x _) => e2
   end)
(right associativity, at level 60).

Notation "x & y <- e1 ; e2" :=
  (match e1 with
     | inright _ => !!
     | inleft (exist2el x y _) => e2
   end)
(right associativity, at level 60, y at level 0).

Notation "x & y <-- e1 ; e2" :=
  (match e1 with
     | inright _ => nope
     | inleft (exist2el x y _) => e2
   end)
(right associativity, at level 60, y at level 0).

Notation "e1 >--> e2" :=
  (match e1 with
     | right _ => nope
     | left _ => e2
   end)
(right associativity, at level 60).

Notation "e1 >---> e2" :=
  (match e1 with
     | right _ => !!
     | left _ => e2
   end)
(right associativity, at level 60).

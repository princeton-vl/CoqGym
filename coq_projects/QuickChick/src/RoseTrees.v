(* Lazy Rose Trees *)

Require Import List mathcomp.ssreflect.ssreflect.
Set Implicit Arguments.

Record Lazy (T : Type) := lazy { force : T }.

Inductive Rose (A : Type) : Type :=
  MkRose : A -> Lazy (list (Rose A)) -> Rose A.

Definition returnRose {A : Type} (x : A) := MkRose x (lazy nil).

Fixpoint joinRose {A : Type} (r : Rose (Rose A)) : Rose A :=
  match r with
    | MkRose (MkRose a ts) tts =>
      MkRose a (lazy ((List.map joinRose (force tts)) ++ (force ts)))
  end.

Fixpoint repeatRose {A : Type} (n : nat) (r : Rose A) :=
  match r with
  | MkRose a ts => MkRose a (lazy (concat (repeat (force ts) n)))
  end.

Fixpoint fmapRose {A B : Type} (f : A -> B) (r : Rose A) : Rose B :=
  match r with
    | MkRose x rs => MkRose (f x) (lazy (List.map (fmapRose f) (force rs)))
  end.

Definition bindRose {A B : Type} (m : Rose A) (k : A -> Rose B) : Rose B :=
  joinRose (fmapRose k m).

(*
(* CH: these seem unused now *)
Lemma joinRoseFmapRose :
  forall {A B} (f: A -> B) (x : Rose A),
    fmapRose f x = joinRose (fmapRose (fun x0 : A => returnRose (f x0)) x).
Proof.
  fix 4.
  move=> A B f x.
  destruct x as [a l]. destruct l as [lst]. induction lst as [|x lst IHlst].
  - reflexivity.
  - inversion IHlst as [Heq]. simpl.
    rewrite Heq. repeat apply f_equal. apply f_equal2.
    apply joinRoseFmapRose. reflexivity.
Qed.

Lemma monadFunctorLaw :
  (forall A B (f : A -> B) a,
     fmapRose f a = bindRose a (fun x => returnRose (f x))).
Proof.
  move => A B f a.
  destruct a. destruct l as [lst]. induction lst as [|x lst Hlst].
  + reflexivity.
  + simpl in Hlst. rewrite /bindRose /= in Hlst.
    inversion Hlst as [Heq].
    simpl. rewrite Heq /bindRose /= app_nil_r.
    repeat apply f_equal. apply f_equal2. apply joinRoseFmapRose. reflexivity.
Qed.

(* CH: TODO: need a proper induction principle for rose trees *)
Lemma fmapRose_id : forall a (rose : Rose a) f,
  (forall x : a, f x = x) ->
  fmapRose f rose = rose.
Proof.
  fix 2. (* <-- nasty *)
  move => a [r [xs]] f H. induction xs as [|x xs]; simpl in *.
  - by rewrite H.
  - inversion IHxs. f_equal. by repeat apply H1. f_equal. f_equal.
    + by apply fmapRose_id.
    + by do 2 rewrite H2.
Qed.
*)
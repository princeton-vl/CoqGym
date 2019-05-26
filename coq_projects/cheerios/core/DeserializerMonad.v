Require Import Cheerios.Core.
Require Import Cheerios.Types.
Require Import List.
Import ListNotations.

Definition sequence {A B} (df : ByteListReader.t (A -> B))
           (da : ByteListReader.t A) : ByteListReader.t B :=
  ByteListReader.bind df
                      (fun f =>
                         (ByteListReader.bind da
                                              (fun a => ByteListReader.ret (f a)))).

Lemma sequence_rewrite : forall {A B : Type}
                                (df : ByteListReader.t (A -> B))
                                (da : ByteListReader.t A),
    sequence df da =
    ByteListReader.bind df
                        (fun f =>
                           (ByteListReader.bind da
                                                (fun a => ByteListReader.ret (f a)))).
Proof.
  reflexivity.
Qed.
Hint Rewrite @sequence_rewrite : cheerios.

Module DeserializerNotations.
  Notation "m >>= f" := (@ByteListReader.bind _ _ m f) (at level 42, left associativity).

  Notation "x <- c1 ;; c2" := (c1 >>= (fun x => c2))
                                (at level 100, c1 at next level, right associativity).
  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                           (at level 100, right associativity).

  Notation "f <$> x" := (@ByteListReader.map _ _ f x) (at level 42, left associativity).

  Notation "f <*> x" := (@sequence _ _ f x) (at level 42, left associativity).
End DeserializerNotations.


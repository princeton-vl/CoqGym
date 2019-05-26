Ltac forward_reason :=
  repeat match goal with
           | H : exists x, _ |- _ =>
             destruct H
           | H : _ /\ _ |- _ => destruct H
           | H' : ?X , H : ?X -> ?Y |- _ =>
             match type of X with
               | Prop => specialize (H H')
             end
           | H : ?X -> ?Y |- _ =>
             match type of X with
               | Prop =>
                 let H' := fresh in
                 assert (H' : X) by eauto ;
               specialize (H H') ;
               clear H'
             end
         end.

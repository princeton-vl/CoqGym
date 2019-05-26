Inductive Qpositive : Set :=
  | nR : Qpositive -> Qpositive
  | dL : Qpositive -> Qpositive
  | One : Qpositive.

Fixpoint Qpositive_le_bool (w w' : Qpositive) {struct w'} : bool :=
  match w with
  | One => match w' with
           | dL y => false
           | _ => true
           end
  | dL y => match w' with
            | dL y' => Qpositive_le_bool y y'
            | _ => true
            end
  | nR y => match w' with
            | nR y' => Qpositive_le_bool y y'
            | _ => false
            end
  end.

Definition Qpositive_le (w w' : Qpositive) := Qpositive_le_bool w w' = true.

Fixpoint Qpositive_i (w : Qpositive) : nat * nat :=
  match w with
  | One => (1, 1)
  | nR w' => match Qpositive_i w' with
             | (p, q) => (p + q, q)
             end
  | dL w' => match Qpositive_i w' with
             | (p, q) => (p, p + q)
             end
  end.

Fixpoint Qpositive_c (p q n : nat) {struct n} : Qpositive :=
  match n with
  | O => One
  | S n' =>
      match p - q with
      | O => match q - p with
             | O => One
             | v => dL (Qpositive_c p v n')
             end
      | v => nR (Qpositive_c v q n')
      end
  end.

Definition Qpositive_sub (w w' : Qpositive) :=
  let (p, q) := Qpositive_i w in
  let (p', q') := Qpositive_i w' in
  Qpositive_c (p * q' - p' * q) (q * q') (p * q' + p' * q + q * q').

Theorem interp_non_zero :
 forall w : Qpositive,
 exists p : nat, (exists q : nat, Qpositive_i w = (S p, S q)).
simple induction w; simpl in |- *;
 (repeat exists 0; auto; fail) ||
   (intros w' Hrec; elim Hrec; intros p' Hex; elim Hex; intros q' Heq;
     rewrite Heq).
exists (p' + S q'); exists q'; auto.
exists p'; exists (p' + S q'); auto.
Qed.

Ltac make_fraction w p q Heq := elim (interp_non_zero w); intros p (q, Heq).

Theorem Qpositive_le_sub_l :
 forall w w' w'' : Qpositive,
 w <> w'' ->
 w' <> w'' ->
 Qpositive_le w w'' ->
 Qpositive_le w' w'' ->
 Qpositive_le w w' ->
 Qpositive_le (Qpositive_sub w'' w') (Qpositive_sub w'' w).
Proof.
intros w w' w''; make_fraction w ipattern:(p) ipattern:(q) ipattern:(Heq);
 make_fraction w' ipattern:(p') ipattern:(q') ipattern:(Heq');
 make_fraction w'' ipattern:(p'') ipattern:(q'') ipattern:(Heq'');
 intros Hneq1 Hneq2.
Admitted.

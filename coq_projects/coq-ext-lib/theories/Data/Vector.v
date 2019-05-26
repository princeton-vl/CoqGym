Require Import ExtLib.Data.Fin.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Section parametric.
  Variable T : Type.

  Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, T -> vector n -> vector (S n).

  Definition vector_hd n (v : vector (S n)) : T :=
    match v in vector n' return match n' with
                                  | 0 => unit
                                  | S _ => T
                                end with
      | Vnil => tt
      | Vcons _ x _ => x
    end.

  Definition vector_tl n (v : vector (S n)) : vector n :=
    match v in vector n' return match n' with
                                  | 0 => unit
                                  | S n => vector n
                                end with
      | Vnil => tt
      | Vcons _ _ x => x
    end.

  Theorem vector_eta : forall n (v : vector n),
                         v = match n as n return vector n -> vector n with
                               | 0 => fun _ => Vnil
                               | S n => fun v => Vcons (vector_hd v) (vector_tl v)
                             end v.
  Proof.
    destruct v; auto.
  Qed.

  Fixpoint get {n : nat} (f : fin n) : vector n -> T :=
    match f in fin n return vector n -> T with
      | F0 n => @vector_hd _
      | FS n f => fun v => get f (vector_tl v)
    end.

  Fixpoint put {n : nat} (f : fin n) (t : T) : vector n -> vector n :=
    match f in fin n return vector n -> vector n with
      | F0 _ => fun v => Vcons t (vector_tl v)
      | FS _ f => fun v => Vcons (vector_hd v) (put f t (vector_tl v))
    end.


  Theorem get_put_eq : forall {n} (v : vector n) (f : fin n) val,
                         get f (put f val v) = val.
  Proof.
    induction n.
    { inversion f. }
    { remember (S n). destruct f.
      inversion Heqn0; subst; intros; reflexivity.
      inversion Heqn0; subst; simpl; auto. }
  Qed.

  Theorem get_put_neq : forall {n} (v : vector n) (f f' : fin n) val,
                          f <> f' ->
                          get f (put f' val v) = get f v.
  Proof.
    induction n.
    { inversion f. }
    { remember (S n); destruct f.
      { inversion Heqn0; clear Heqn0; subst; intros.
        destruct (fin_case f'); try congruence.
        destruct H0; subst. auto. }
      { inversion Heqn0; clear Heqn0; subst; intros.
        destruct (fin_case f').
        subst; auto.
        destruct H0; subst. simpl.
        eapply IHn. congruence. } }
  Qed.

  Section ForallV.
    Variable P : T -> Prop.

    Inductive ForallV  : forall n, vector n -> Prop :=
    | ForallV_nil : ForallV Vnil
    | ForallV_cons : forall n e es, P e -> @ForallV n es -> ForallV (Vcons e es).

    Definition ForallV_vector_hd n (v : vector (S n)) (f : ForallV v) : P (vector_hd v) :=
      match f in @ForallV n v return match n as n return vector n -> Prop with
                                       | 0 => fun _ => True
                                       | S _ => fun v => P (vector_hd v)
                                     end v
      with
        | ForallV_nil => I
        | ForallV_cons _ _ _ pf _ => pf
      end.

    Definition ForallV_vector_tl n (v : vector (S n)) (f : ForallV v) : ForallV (vector_tl v) :=
      match f in @ForallV n v return match n as n return vector n -> Prop with
                                       | 0 => fun _ => True
                                       | S _ => fun v => ForallV (vector_tl v)
                                     end v
      with
        | ForallV_nil => I
        | ForallV_cons _ _ _ _ pf => pf
      end.
  End ForallV.

  Section vector_dec.
    Variable Tdec : forall a b : T, {a = b} + {a <> b}.

    Fixpoint vector_dec {n} (a : vector n)
      : forall b : vector n, {a = b} + {a <> b} :=
      match a in vector n
            return forall b : vector n, {a = b} + {a <> b}
      with
      | Vnil => fun b => left match b in vector 0 with
                                | Vnil => eq_refl
                                end
      | Vcons _ a a' => fun b =>
        match b as b in vector (S n)
              return forall a',
                (forall a : vector n, {a' = a} + {a' <> a}) ->
                {Vcons a a' = b} + {Vcons a a' <> b}
        with
        | Vcons _ b b' => fun a' rec =>
                            match Tdec a b , rec b' with
                            | left pf , left pf' =>
                              left match pf , pf' with
                                   | eq_refl , eq_refl => eq_refl
                                   end
                            | right pf , _ =>
                              right (fun x : Vcons a a' = Vcons b b' =>
                                       pf match x in _ = z
                                                return a = vector_hd z
                                          with
                                          | eq_refl => eq_refl
                                          end)
                            | left _ , right pf =>
                              right (fun x : Vcons a a' = Vcons b b' =>
                                       pf match x in _ = z
                                                return a' = vector_tl z
                                          with
                                          | eq_refl => eq_refl
                                          end)
                            end
        end a' (@vector_dec _ a')
      end.
  End vector_dec.

  Section vector_in.
    Variable a : T.
    Inductive vector_In : forall {n}, vector n -> Prop :=
    | vHere : forall n rst, @vector_In (S n) (Vcons a rst)
    | vNext : forall n rst b, @vector_In n rst ->
                              @vector_In (S n) (Vcons b rst).
  End vector_in.

  Lemma ForallV_vector_In : forall {n} t (vs : vector n) P,
      ForallV P vs ->
      vector_In t vs -> P t.
  Proof.
    induction 2.
    - eapply (ForallV_vector_hd H).
    - eapply IHvector_In. eapply (ForallV_vector_tl H).
  Qed.

End parametric.

Section vector_map.
  Context {T U : Type}.
  Variable f : T -> U.
  Fixpoint vector_map {n} (v : vector T n) : vector U n :=
    match v with
    | Vnil => Vnil _
    | Vcons _ v vs => Vcons (f v) (vector_map vs)
    end.
End vector_map.

Arguments vector T n.
Arguments vector_hd {T n} _.
Arguments vector_tl {T n} _.

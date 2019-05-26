(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Export List.

(* Definition of types *)

Parameter N : Set.
Inductive K : Set :=
  | inv : K -> K
  | ka : securite.N -> K
  | ks : securite.N -> K.

Parameter D : Set.
Parameter Aid Bid : D.
Axiom
  D_dec :
    forall d1 d2 : D, {d1 = Aid /\ d2 = Bid} + {~ (d1 = Aid /\ d2 = Bid)}.

Inductive B : Set :=
  | K2B : K -> B
  | D2B : D -> B.

Inductive C : Set :=
  | Encrypt : C -> K -> C
  | Pair : C -> C -> C
  | B2C : B -> C.

Notation SS := (list C) (only parsing).
(* <Warning> : Syntax is discontinued *)

(* known_in and not_comp_of predicates, equivS equivalence, setofkeys *)

Inductive known_in : C -> list C -> Prop :=
  | E0 :
      forall (c1 c2 : C) (s : list C), known_in c1 s -> known_in c1 (c2 :: s)
  | EP0 :
      forall (c : C) (s1 s2 : list C), known_in c s1 -> known_in c (s1 ++ s2)
  | A1 :
      forall (c1 c2 : C) (s : list C),
      known_in c1 s -> known_in c2 s -> known_in (Pair c1 c2) s
  | A2A :
      forall (c1 c2 : C) (s : list C),
      known_in (Pair c1 c2) s -> known_in c1 s
  | A2B :
      forall (c1 c2 : C) (s : list C),
      known_in (Pair c1 c2) s -> known_in c2 s
  | A3 :
      forall (c1 : C) (k1 : K) (s : list C),
      known_in c1 s ->
      known_in (B2C (K2B k1)) s -> known_in (Encrypt c1 k1) s
  | A4 :
      forall (c1 : C) (k1 : K) (s : list C),
      known_in (Encrypt c1 k1) s ->
      known_in (B2C (K2B (inv k1))) s -> known_in c1 s.

Hint Resolve A1 A2A A2B A3 A4: otway_rees.

Inductive equivS : list C -> list C -> Prop :=
  | equivS1a : equivS nil nil
  | equivS1b :
      forall (s1 s2 : list C) (c : C),
      equivS s1 s2 -> equivS (c :: s1) (c :: s2)
  | equivS2 :
      forall (s : list C) (c1 c2 : C), equivS (c1 :: c2 :: s) (c2 :: c1 :: s)
  | equivS4 :
      forall s1 s2 s3 : list C, equivS s1 s2 -> equivS s2 s3 -> equivS s1 s3
  | AlreadyIn1 : forall (c1 : C) (s : list C), In c1 s -> equivS s (c1 :: s)
  | AlreadyIn1b : forall (c1 : C) (s : list C), In c1 s -> equivS (c1 :: s) s
  | AlreadyIn :
      forall (c1 : C) (s : list C), known_in c1 s -> equivS s (c1 :: s)
  | AlreadyInb :
      forall (c1 : C) (s : list C), known_in c1 s -> equivS (c1 :: s) s.

Hint Resolve equivS1a equivS1b equivS2 equivS4 AlreadyIn1 AlreadyIn1b
  AlreadyIn AlreadyInb: otway_rees.

Lemma equivS3 : forall s1 s2 : list C, equivS s1 s2 -> equivS s2 s1.

Proof.
intros s1 s2 equiv; elim equiv; eauto with otway_rees.
Qed.

Fixpoint setofkeys (s : list C) : Prop :=
  match s with
  | nil => True
  | B2C (K2B _) :: s1 => setofkeys s1
  | _ => False
  end.

Inductive not_comp_of : C -> list C -> Prop :=
  | C1 :
      forall (c1 c2 : C) (k : K) (s : list C),
      not_comp_of (B2C (K2B k)) s ->
      c1 <> Encrypt c2 k -> not_comp_of c1 (Encrypt c2 k :: s)
  | C2 :
      forall (c1 c2 : C) (k : K) (s : list C),
      not_comp_of c1 (c2 :: s) ->
      c1 <> Encrypt c2 k -> not_comp_of c1 (Encrypt c2 k :: s)
  | C3 :
      forall (c1 : C) (d : D) (s : list C),
      not_comp_of c1 s ->
      c1 <> B2C (D2B d) -> not_comp_of c1 (B2C (D2B d) :: s)
  | C4 :
      forall (c1 c2 c3 : C) (s : list C),
      not_comp_of c1 (c2 :: c3 :: s) ->
      c1 <> Pair c2 c3 -> not_comp_of c1 (Pair c2 c3 :: s)
  | C5 : forall c1 : C, not_comp_of c1 nil
  | C7 :
      forall (k : K) (s : list C),
      ~ In (B2C (K2B k)) s -> setofkeys s -> not_comp_of (B2C (K2B k)) s
  | D1 : forall (c1 : C) (s : list C), ~ known_in c1 s -> not_comp_of c1 s
  | UnionSnE1 :
      forall (c : C) (s1 s2 : list C),
      not_comp_of c (s1 ++ s2) -> not_comp_of c s1.

Axiom
  D2 :
    forall (b : B) (s : list C),
    not_comp_of (B2C b) s -> ~ known_in (B2C b) s.
Axiom
  E1 :
    forall (c1 c2 : C) (s : list C),
    ~ known_in c1 (c2 :: s) -> ~ known_in c1 s.
Axiom
  EP1 :
    forall (c : C) (s1 s2 : list C),
    ~ known_in c (s1 ++ s2) -> ~ known_in c s1.

Hint Resolve C1 C2 C3 C4 C5 C7 D1 UnionSnE1 D2 E1 EP1: otway_rees.

Axiom
  equivknown :
    forall (c : C) (s1 s2 : list C),
    equivS s1 s2 -> known_in c s1 -> known_in c s2.

Axiom
  equivncomp :
    forall (c : C) (s1 s2 : list C),
    equivS s1 s2 -> not_comp_of c s1 -> not_comp_of c s2.

Lemma equivnknown1 :
 forall (c1 c2 : C) (s1 s2 : list C),
 equivS s1 s2 -> c1 = c2 -> ~ known_in c1 s1 -> ~ known_in c2 s2.

Proof.
intros.
elim H0.
unfold not in |- *; intros.
apply H1.
apply (equivknown c1 s2 s1).
elim H; simpl in |- *; eauto with otway_rees.
exact H2.
Qed.

(* Keys *)
Parameter KeyAB : D -> D -> K.
Parameter KeyX : D -> K.
Parameter rngDDKKeyAB : list C.
Parameter rngDDKKeyABminusKab : list C.

Axiom rngs : equivS rngDDKKeyAB (rngDDKKeyABminusKab ++ rngDDKKeyAB).

Notation Kab := (KeyAB Aid Bid) (only parsing).
(* <Warning> : Syntax is discontinued *)
Notation Kas := (KeyX Aid) (only parsing).
(* <Warning> : Syntax is discontinued *)
Notation Kbs := (KeyX Bid) (only parsing).
(* <Warning> : Syntax is discontinued *)

Axiom disjKasKeyAB : forall d1 d2 : D, KeyAB d1 d2 <> KeyX Aid.

Axiom
  rngDDKKeyAB1 : forall d1 d2 : D, In (B2C (K2B (KeyAB d1 d2))) rngDDKKeyAB.

Axiom
  rngDDKKeyABminusKab1 :
    forall d1 d2 : D,
    KeyAB d1 d2 <> KeyAB Aid Bid ->
    In (B2C (K2B (KeyAB d1 d2))) rngDDKKeyABminusKab.

Axiom
  KeyAB1 :
    forall d1 d2 : D,
    ~ (d1 = Aid /\ d2 = Bid) -> KeyAB d1 d2 <> KeyAB Aid Bid.

(* Definition of GlobalState *)
Definition triple (c1 c2 c3 : C) := Pair c1 (Pair c2 c3).
Definition quad (c1 c2 c3 c4 : C) := Pair c1 (Pair c2 (Pair c3 c4)).
Definition quint (c1 c2 c3 c4 c5 : C) :=
  Pair c1 (Pair c2 (Pair c3 (Pair c4 c5))).
          
Definition new (n : D) (s : list C) :=
  forall s2 : list C, setofkeys s2 -> ~ known_in (B2C (D2B n)) (s ++ s2).

Inductive AState : Set :=
    MBNaKab : D -> D -> D -> K -> AState.

Inductive BState : Set :=
    MANbKabCaCb : D -> D -> D -> K -> C -> C -> BState.

Inductive SState : Set :=
    MABNaNbKeyK : D -> D -> D -> D -> D -> SState.

Inductive GlobalState : Set :=
    ABSI : AState -> BState -> SState -> list C -> GlobalState.

(* Definition of the invariant properties *)

Definition inv0 (st : GlobalState) :=
  match st with
  | ABSI _ (MANbKabCaCb _ _ _ _ ca cb) _ s => known_in ca s /\ known_in cb s
  end. 

Definition inv1 (st : GlobalState) :=
  match st with
  | ABSI _ _ _ s =>
      ~ known_in (B2C (K2B (KeyX Aid))) (s ++ rngDDKKeyAB) /\
      ~ known_in (B2C (K2B (KeyX Bid))) (s ++ rngDDKKeyAB)
  end.

Definition invP (st : GlobalState) :=
  match st with
  | ABSI _ _ _ s =>
      ~ known_in (B2C (K2B (KeyAB Aid Bid))) (s ++ rngDDKKeyABminusKab)
  end.

(* Definition of rel *)
Definition rel1 (st1 st2 : GlobalState) :=
  match st1, st2 with
  | ABSI sta1 stb1 sts1 s1, ABSI sta2 stb2 sts2 s2 =>
      match sta1, sta2 with
      | MBNaKab _ _ na1 kab1, MBNaKab m2 b2 na2 kab2 =>
          s2 =
          quad (B2C (D2B m2)) (B2C (D2B Aid)) (B2C (D2B b2))
            (Encrypt
               (quad (B2C (D2B na2)) (B2C (D2B m2)) 
                  (B2C (D2B Aid)) (B2C (D2B b2))) (KeyX Aid)) :: s1 /\
          new na2 s1 /\
          new m2 s1 /\ stb1 = stb2 /\ sts1 = sts2 /\ na1 = na2 /\ kab1 = kab2
      end
  end.
    
Definition rel2 (st1 st2 : GlobalState) :=
  match st1, st2 with
  | ABSI sta1 stb1 sts1 s1, ABSI sta2 stb2 sts2 s2 =>
      match stb1, stb2 with
      | MANbKabCaCb _ _ nb1 kab1 _ cb1, MANbKabCaCb m2 a2 nb2 kab2 ca2 cb2 =>
          known_in (quad (B2C (D2B m2)) (B2C (D2B a2)) (B2C (D2B Bid)) ca2)
            s1 /\
          sta1 = sta2 /\
          sts1 = sts2 /\ s1 = s2 /\ nb1 = nb2 /\ kab1 = kab2 /\ cb1 = cb2
      end
  end.

Definition rel3 (st1 st2 : GlobalState) :=
  match st1, st2 with
  | ABSI sta1 stb1 sts1 s1, ABSI sta2 stb2 sts2 s2 =>
      match stb1, stb2 with
      | MANbKabCaCb m1 a1 nb1 kab1 ca1 cb1, MANbKabCaCb m2 a2 nb2 kab2 ca2
        cb2 =>
          s2 =
          quint (B2C (D2B m1)) (B2C (D2B a1)) (B2C (D2B Bid)) ca1
            (Encrypt
               (quad (B2C (D2B nb2)) (B2C (D2B m1)) 
                  (B2C (D2B a2)) (B2C (D2B Bid))) (KeyX Bid)) :: s1 /\
          new nb2 s1 /\
          sta1 = sta2 /\
          sts1 = sts2 /\
          m1 = m2 /\ a1 = a2 /\ kab1 = kab2 /\ ca1 = ca2 /\ cb1 = cb2
      end
  end.

Definition rel4 (st1 st2 : GlobalState) :=
  match st1, st2 with
  | ABSI sta1 stb1 _ s1, ABSI sta2 stb2 sts2 s2 =>
      match sts2 with
      | MABNaNbKeyK m2 a2 b2 na2 nb2 =>
          known_in
            (quint (B2C (D2B m2)) (B2C (D2B a2)) (B2C (D2B b2))
               (Encrypt
                  (quad (B2C (D2B na2)) (B2C (D2B m2)) 
                     (B2C (D2B a2)) (B2C (D2B b2))) 
                  (KeyX a2))
               (Encrypt
                  (quad (B2C (D2B nb2)) (B2C (D2B m2)) 
                     (B2C (D2B a2)) (B2C (D2B b2))) 
                  (KeyX b2))) s1 /\ sta1 = sta2 /\ stb1 = stb2 /\ s1 = s2
      end
  end.

Definition rel5 (st1 st2 : GlobalState) :=
  match st1, st2 with
  | ABSI sta1 stb1 sts1 s1, ABSI sta2 stb2 sts2 s2 =>
      match sts1 with
      | MABNaNbKeyK m1 a1 b1 na1 nb1 =>
          s2 =
          triple (B2C (D2B m1))
            (Encrypt (Pair (B2C (D2B na1)) (B2C (K2B (KeyAB a1 b1))))
               (KeyX a1))
            (Encrypt (Pair (B2C (D2B nb1)) (B2C (K2B (KeyAB a1 b1))))
               (KeyX b1)) :: s1 /\ sta1 = sta2 /\ stb1 = stb2 /\ sts1 = sts2
      end
  end.

Definition rel6 (st1 st2 : GlobalState) :=
  match st1, st2 with
  | ABSI sta1 stb1 sts1 s1, ABSI sta2 stb2 sts2 s2 =>
      match stb1, stb2 with
      | MANbKabCaCb m1 a1 nb1 _ ca1 _, MANbKabCaCb m2 a2 nb2 kab2 ca2 cb2 =>
          known_in
            (triple (B2C (D2B m1)) cb2
               (Encrypt (Pair (B2C (D2B nb1)) (B2C (K2B kab2))) (KeyX Bid)))
            s1 /\
          sta1 = sta2 /\
          sts1 = sts2 /\
          s1 = s2 /\ m1 = m2 /\ a1 = a2 /\ nb1 = nb2 /\ ca1 = ca2
      end
  end.

Definition rel7 (st1 st2 : GlobalState) :=
  match st1, st2 with
  | ABSI sta1 stb1 sts1 s1, ABSI sta2 stb2 sts2 s2 =>
      match stb1 with
      | MANbKabCaCb m1 _ _ _ _ cb1 =>
          s2 = Pair (B2C (D2B m1)) cb1 :: s1 /\
          sta1 = sta2 /\ stb1 = stb2 /\ sts1 = sts2
      end
  end.

Definition rel8 (st1 st2 : GlobalState) :=
  match st1, st2 with
  | ABSI sta1 stb1 sts1 s1, ABSI sta2 stb2 sts2 s2 =>
      match sta1, sta2 with
      | MBNaKab m1 b1 na1 _, MBNaKab m2 b2 na2 kab2 =>
          known_in
            (Pair (B2C (D2B m1))
               (Encrypt (Pair (B2C (D2B na1)) (B2C (K2B kab2))) (KeyX Aid)))
            s1 /\
          stb1 = stb2 /\
          sts1 = sts2 /\ s1 = s2 /\ m1 = m2 /\ b1 = b2 /\ na1 = na2
      end
  end.

Definition rel (st1 st2 : GlobalState) :=
  rel1 st1 st2 \/
  rel2 st1 st2 \/
  rel3 st1 st2 \/
  rel4 st1 st2 \/
  rel5 st1 st2 \/ rel6 st1 st2 \/ rel7 st1 st2 \/ rel8 st1 st2.
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*      Coq V5.8                                                            *)
(*                                                                          *)
(*                                                                          *)
(*      Alternating Bit Protocol                                            *)
(*                                                                          *)
(*      Jan Friso Groote                                                    *)
(*      Utrecht University                                                  *)
(*                                                                          *)
(*      November 1992                                                       *)
(*                                                                          *)
(* From bezem@phil.ruu.nl Fri Apr  2 13:14:31 1993                          *)
(*                                                                          *)
(****************************************************************************)
(*                                abp_base.v                                *)
(****************************************************************************)

Global Set Asymmetric Patterns.

Inductive act : Set :=
  | r1 : act
  | r2 : act
  | r3 : act
  | r5 : act
  | r6 : act
  | s2 : act
  | s3 : act
  | s4 : act
  | s5 : act
  | s6 : act
  | c2 : act
  | c3 : act
  | c5 : act
  | c6 : act
  | int : act
  | delta : act
  | tau : act.

Parameter proc : Set.
Parameter ia : forall E : Set, act -> E -> proc.

Inductive one : Set :=
    i : one.

Definition Delta := ia one delta i.

Inductive list (A : Set) : Set :=
  | nil : list A
  | cons : A -> list A -> list A.

(* ehlist are the lists used in the hiding and the encapsulation operator *)

Inductive ehlist : Set :=
  | ehnil : ehlist
  | ehcons : act -> ehlist -> ehlist.

Definition In_list (N : Set) (n : N) (Y : list N) : Prop :=
  (fix F (l : list N) : Prop :=
     match l with
     | nil => False
     | cons y l0 => n = y :>N \/ F l0
     end) Y.

Definition In_ehlist (a : act) (H : ehlist) : Prop :=
  (fix F (e : ehlist) : Prop :=
     match e with
     | ehnil => False
     | ehcons a0 e0 => a = a0 :>act \/ F e0
     end) H.

(* Parameter lab  :act->name *)
Parameter alt : proc -> proc -> proc.
Parameter seq : proc -> proc -> proc.
Parameter mer : proc -> proc -> proc.
Parameter Lmer : proc -> proc -> proc.
Parameter comm : proc -> proc -> proc.
Parameter cond : proc -> bool -> proc -> proc.
Parameter sum : forall A : Set, (A -> proc) -> proc.
Parameter enc : ehlist -> proc -> proc.
Parameter hide : ehlist -> proc -> proc.
Parameter GRD : proc -> Prop.

Infix "+" := sum (left associativity, at level 50).

Definition gamma (a b : act) :=
  match a, b with
  | r2, s2 => c2
  | r3, s3 => c3
  | r5, s5 => c5
  | r6, s5 => c6
  | s2, r2 => c2
  | s3, r3 => c3
  | s5, r5 => c5
  | s6, r6 => c6
  | _, _ => delta
  end.




Parameter EQ : Set -> Set -> Prop.
Axiom EQ_refl : forall S1 : Set, EQ S1 S1.
Axiom EQ_sym : forall S1 S2 : Set, EQ S1 S2 -> EQ S2 S1.

Section COMMUNICATION_F.
Variable a b : act.
Variable E F : Set.
Variable e e1 e2 : E.
Variable f : F.
Axiom CF1 : ia E (gamma a b) e = comm (ia E a e) (ia E b e).
Axiom CF2 : gamma a b = delta -> Delta = comm (ia E a e1) (ia E b e2).
Axiom CF2' : e1 <> e2 -> Delta = comm (ia E a e1) (ia E b e2).
Axiom CF2'' : ~ EQ E F -> Delta = comm (ia E a e) (ia F b f).
End COMMUNICATION_F.


(* The following lemma also lives under the name KSI in other versions 
   of this proof *)

Axiom
  EXTE :
    forall (D : Set) (x y : D -> proc), (forall d : D, x d = y d) -> x = y.

Section BPA.
Variable x y z : proc.
Axiom A1 : alt x y = alt y x.
Axiom A2 : alt x (alt y z) = alt (alt x y) z.
Axiom A3 : x = alt x x.
Axiom A4 : alt (seq x z) (seq y z) = seq (alt x y) z.
Axiom A5 : seq x (seq y z) = seq (seq x y) z.
Axiom A6 : x = alt x Delta.
Axiom A7 : Delta = seq Delta x.
End BPA.

Goal forall x : proc, x = alt Delta x.
intro.
elim A1.
apply A6.
Save A6'.

Section GUARDED.
Variable D : Set.
Variable d : D.
Variable x y : proc.
Variable z : D -> proc.
Variable a : act.
Variable B : bool.
Variable L : ehlist.
Axiom G2 : GRD (ia D a d).
Axiom G5 : (forall d : D, GRD (z d)) -> GRD (D + z).
Axiom G6 : GRD x -> GRD (seq x y).
Axiom G7 : GRD x -> GRD (Lmer x y).
Axiom G8 : GRD x -> GRD y -> GRD (alt x y).
Axiom G9 : GRD x -> GRD y -> GRD (mer x y).
Axiom G10 : GRD x -> GRD y -> GRD (comm x y).
Axiom G11 : GRD x -> GRD y -> GRD (cond x B y).
Axiom G12 : GRD x -> GRD (hide L x).
Axiom G13 : GRD x -> GRD (enc L x).
End GUARDED.

Section PARALLEL_OPERATORS.
Variable x y z : proc.
Variable E F : Set.
Variable e : E.
Variable f : F.
Variable a b : act.
Axiom CM1 : alt (alt (Lmer x y) (Lmer y x)) (comm x y) = mer x y.
Axiom CM2 : seq (ia E a e) x = Lmer (ia E a e) x.
Axiom CM3 : seq (ia E a e) (mer x y) = Lmer (seq (ia E a e) x) y.
Axiom CM4 : alt (Lmer x z) (Lmer y z) = Lmer (alt x y) z.
Axiom
  CM5 :
    seq (comm (ia E a e) (ia F b f)) x = comm (seq (ia E a e) x) (ia F b f).
Axiom
  CM6 :
    seq (comm (ia E a e) (ia F b f)) x = comm (ia E a e) (seq (ia F b f) x).
Axiom
  CM7 :
    seq (comm (ia E a e) (ia F b f)) (mer x y) =
    comm (seq (ia E a e) x) (seq (ia F b f) y).
Axiom CM8 : alt (comm x z) (comm y z) = comm (alt x y) z.
Axiom CM9 : alt (comm x y) (comm x z) = comm x (alt y z).
End PARALLEL_OPERATORS.

Section STANDARD_CONCURRENCY. 
Variable x y z : proc.
Axiom SC1 : Lmer x (mer y z) = Lmer (Lmer x y) z.
Axiom SC3 : comm y x = comm x y.
Axiom SC4 : comm x (comm y z) = comm (comm x y) z.
Axiom SC5 : Lmer (comm x y) z = comm x (Lmer y z).
End STANDARD_CONCURRENCY.

Goal forall x y : proc, mer x y = mer y x.
intros.
elim CM1.
elim CM1.
elim SC3.
elim (A1 (Lmer x y) (Lmer y x)).
apply refl_equal.
Save SC6.

(* The next axiom should be proven correct *)

Goal forall x y z : proc, mer x (mer y z) = mer (mer x y) z.
intros.
repeat elim CM1.
(* Repeat Elim SC1. *)
repeat elim CM8.
repeat elim CM9.
repeat elim CM4.
repeat elim SC5.
repeat elim SC4.
repeat elim CM1.
repeat elim A2.
repeat elim SC1.
repeat elim CM1.
elim (A1 (Lmer z x) (Lmer x z)).
repeat elim A2.
elim (SC3 x z).
elimtype
 (alt (Lmer z (alt (Lmer y x) (alt (Lmer x y) (comm y x))))
    (alt (Lmer (comm y z) x)
       (alt (Lmer (comm x y) z) (alt (Lmer (comm z x) y) (comm x (comm y z))))) =
  alt (Lmer (comm x y) z)
    (alt (Lmer z (alt (Lmer x y) (alt (Lmer y x) (comm x y))))
       (alt (comm (Lmer x y) z) (alt (comm (Lmer y x) z) (comm x (comm y z)))))).
apply refl_equal.
elim
 (A1
    (alt (Lmer z (alt (Lmer x y) (alt (Lmer y x) (comm x y))))
       (alt (comm (Lmer x y) z) (alt (comm (Lmer y x) z) (comm x (comm y z)))))
    (Lmer (comm x y) z)).
repeat elim A2.
elimtype
 (alt (Lmer (comm y z) x)
    (alt (Lmer (comm x y) z) (alt (Lmer (comm z x) y) (comm x (comm y z)))) =
  alt (comm (Lmer x y) z)
    (alt (comm (Lmer y x) z) (alt (comm x (comm y z)) (Lmer (comm x y) z)))).
elimtype
 (alt (Lmer y x) (alt (Lmer x y) (comm y x)) =
  alt (Lmer x y) (alt (Lmer y x) (comm x y))).
apply refl_equal.
elim SC3.
elim A1.
elim A2.
elim (A1 (comm x y) (Lmer y x)).
apply refl_equal.
elim (SC3 (Lmer y x) z).
elim SC5.
elim
 (A1 (alt (Lmer (comm z y) x) (alt (comm x (comm y z)) (Lmer (comm x y) z)))
    (comm (Lmer x y) z)).
repeat elim A2.
elimtype
 (alt (Lmer (comm x y) z) (alt (Lmer (comm z x) y) (comm x (comm y z))) =
  alt (comm x (comm y z)) (alt (Lmer (comm x y) z) (comm (Lmer x y) z))).
elim (SC3 y z).
apply refl_equal.
elim (A1 (alt (Lmer (comm x y) z) (comm (Lmer x y) z)) (comm x (comm y z))).
elim A2.
elim (SC3 (Lmer x y) z).
elim SC5.
apply refl_equal.
Save SC7.

Section CONDITION.
Variable x y : proc.
Axiom COND1 : x = cond x true y.
Axiom COND2 : y = cond x false y.
End CONDITION.

Section SUM.
Variable D : Set.
Variable d : D.
Variable x y : D -> proc.
Variable p : proc.
Variable L : ehlist.
Axiom SUM1 : p = D + (fun d : D => p).
Axiom SUM3 : alt (D + x) (x d) = D + x.
Axiom SUM4 : alt (D + x) (D + y) = D + (fun d : D => alt (x d) (y d)).
Axiom SUM5 : D + (fun d : D => seq (x d) p) = seq (D + x) p.
Axiom SUM6 : D + (fun d : D => Lmer (x d) p) = Lmer (D + x) p.
Axiom SUM7 : D + (fun d : D => comm (x d) p) = comm (D + x) p.
Axiom SUM8 : D + (fun d : D => hide L (x d)) = hide L (D + x).
Axiom SUM9 : D + (fun d : D => enc L (x d)) = enc L (D + x).
End SUM.

Section HIDE.
Variable x y : proc.
Variable E : Set.
Variable e : E.
Variable a : act.
Variable L : ehlist.
Axiom TI1 : ~ In_ehlist a L -> ia E a e = hide L (ia E a e).
Axiom TI2 : In_ehlist a L -> ia one tau i = hide L (ia E a e).
Axiom TI3 : Delta = hide L Delta.
Axiom TI4 : alt (hide L x) (hide L y) = hide L (alt x y). 
Axiom TI5 : seq (hide L x) (hide L y) = hide L (seq x y). 
End HIDE.

Section ENCAPSULATION. 
Variable x y : proc. 
Variable E : Set.
Variable e : E.
Variable a : act. 
Variable L : ehlist.
Axiom D1 : ~ In_ehlist a L -> ia E a e = enc L (ia E a e).
Axiom D2 : In_ehlist a L -> Delta = enc L (ia E a e). 
Axiom D3 : Delta = enc L Delta.
Axiom D4 : alt (enc L x) (enc L y) = enc L (alt x y).
Axiom D5 : seq (enc L x) (enc L y) = enc L (seq x y).
End ENCAPSULATION. 

Axiom Handshaking : forall x y z : proc, Delta = comm x (comm y z).

Axiom
  T1 :
    forall (D : Set) (d : D) (a : act),
    ia D a d = seq (ia D a d) (ia one tau i).

Goal
forall (D : Set) (d : D) (a : act) (x : proc),
seq (ia D a d) x = seq (ia D a d) (seq (ia one tau i) x).
intros.
elimtype
 (seq (seq (ia D a d) (ia one tau i)) x =
  seq (ia D a d) (seq (ia one tau i) x)).
elim T1.
apply refl_equal.
apply sym_equal.
apply A5.
Save T1'.
 

Axiom
  KFAR2 :
    forall (D : Set) (d : D) (int : act) (x y : proc) (I : ehlist),
    In_ehlist int I ->
    x = alt (seq (ia D int d) (seq (ia D int d) x)) y ->
    seq (ia one tau i) (hide I x) = seq (ia one tau i) (hide I y).


Axiom
  RSP :
    forall (D : Set) (x y : D -> proc) (G : (D -> proc) -> D -> proc),
    (forall (p : D -> proc) (d : D), GRD (G p d)) ->
    (forall d : D, x d = G x d) ->
    (forall d : D, y d = G y d) -> forall d : D, x d = y d.

Hint Resolve G2 G5 G6 G7 G8 G9 G10 G11 G12 G13.

Goal forall B : bool, true = B \/ false = B.
intro.
elim B.
auto.
auto.
Save Lemma4.

Section EXP2_.
Variable x y : proc.
Goal alt (Lmer x y) (alt (Lmer y x) (comm x y)) = mer x y.
elim CM1.
elim A2.
apply refl_equal.
Save EXP2.
End EXP2_.

 
Section EXP3_.
Variable x y z : proc. 
Goal
alt (Lmer x (mer y z))
  (alt (Lmer y (mer x z))
     (alt (Lmer z (mer x y))
        (alt (Lmer (comm y z) x)
           (alt (Lmer (comm x y) z) (Lmer (comm x z) y))))) = 
mer x (mer y z).

elim (EXP2 x (mer y z)).
elim EXP2.

elim CM4.
elim SC1.
elim (SC6 x z).
elim CM4.
elim SC1.
elim (SC6 x y).
elim CM9.
elim CM9.
elim Handshaking.
elim A6.

elim SC5.
elim SC5.
repeat elim A2.
reflexivity.

Save EXP3.
End EXP3_. 

Goal
forall x y z u : proc,
alt (Lmer x (mer y (mer z u)))
  (alt (Lmer y (mer x (mer z u)))
     (alt (Lmer z (mer x (mer y u)))
        (alt (Lmer u (mer x (mer y z)))
           (alt (Lmer (comm z u) (mer x y))
              (alt (Lmer (comm y z) (mer x u))
                 (alt (Lmer (comm y u) (mer x z))
                    (alt (Lmer (comm x y) (mer z u))
                       (alt (Lmer (comm x z) (mer y u))
                          (Lmer (comm x u) (mer y z)))))))))) =
mer x (mer y (mer z u)).


intros.
elim (EXP2 x (mer y (mer z u))).
elim EXP3.
repeat elim CM4.
repeat elim SC1.
repeat elim CM9.
repeat elim SC5.
repeat elim Handshaking.
unfold Delta in |- *.
repeat elim CM2.
repeat elim A7.
repeat elim A6.
repeat elim A2.
elim (SC6 x (mer z u)).
elim (SC6 x (mer y u)).
elim (SC6 x (mer y z)).
elim (SC6 x u).
elim (SC6 x y).
elim (SC6 x z).
elim (SC6 y z).
apply refl_equal.
Save EXP4.

Section EXPH4_.
Variable x y z u : proc.
Variable H : ehlist.

Goal
alt (enc H (Lmer x (mer y (mer z u))))
  (alt (enc H (Lmer y (mer x (mer z u))))
     (alt (enc H (Lmer z (mer x (mer y u))))
        (alt (enc H (Lmer u (mer x (mer y z))))
           (alt (enc H (Lmer (comm z u) (mer x y)))
              (alt (enc H (Lmer (comm y z) (mer x u)))
                 (alt (enc H (Lmer (comm y u) (mer x z)))
                    (alt (enc H (Lmer (comm x y) (mer z u)))
                       (alt (enc H (Lmer (comm x z) (mer y u)))
                          (enc H (Lmer (comm x u) (mer y z))))))))))) =
enc H (mer x (mer y (mer z u))).

elim EXP4.
repeat elim D4.
apply refl_equal.
Save EXPH4.
End EXPH4_.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_paralleldef2B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_diagonalsmeet : 
   forall A B C D, 
   PG A B C D ->
   exists X, BetS A X C /\ BetS B X D.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
let Tf:=fresh in
assert (Tf:exists a b c d m, (neq A B /\ neq C D /\ Col A B a /\ Col A B b /\ neq a b /\ Col C D c /\ Col C D d /\ neq c d /\ ~ Meet A B C D /\ BetS a m d /\ BetS c m b)) by (conclude_def Par );destruct Tf as [a[b[c[d[m]]]]];spliter.
assert (Par C D A B) by (conclude lemma_parallelsymmetric).
assert (TP C D A B) by (conclude lemma_paralleldef2B).
assert (OS A B C D) by (conclude_def TP ).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col D C D) by (conclude_def Col ).
assert (~ eq A D).
 {
 intro.
 assert (Col D C A) by (conclude cn_equalitysub).
 assert (Col C D A) by (forward_using lemma_collinearorder).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col A B A) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (BetS A D E /\ Cong D E A D)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (~ Col D C A).
 {
 intro.
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col A B A) by (conclude_def Col ).
 assert (Col C D A) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 assert (~ Meet A B C D) by (conclude_def Par ).
 contradict.
 }
assert (TS A D C E) by (conclude_def TS ).
assert (OS B A D C) by (forward_using lemma_samesidesymmetric).
assert (TS B D C E) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists F, (BetS B F E /\ Col D C F /\ nCol D C B)) by (conclude_def TS );destruct Tf as [F];spliter.
assert (BetS E F B) by (conclude axiom_betweennesssymmetry).
assert (BetS E D A) by (conclude axiom_betweennesssymmetry).
assert (Col E D A) by (conclude_def Col ).
assert (neq E D) by (forward_using lemma_betweennotequal).
assert (neq E A) by (forward_using lemma_betweennotequal).
assert (~ Meet A D B C) by (conclude_def Par ).
assert (~ eq B C).
 {
 intro.
 assert (Col D B C) by (conclude_def Col ).
 assert (Col D C B) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists S, (BetS B C S /\ Cong C S B C)) by (conclude lemma_extension);destruct Tf as [S];spliter.
assert (BetS S C B) by (conclude axiom_betweennesssymmetry).
assert (Col S C B) by (conclude_def Col ).
assert (neq S B) by (forward_using lemma_betweennotequal).
assert (neq C B) by (forward_using lemma_betweennotequal).
assert (~ Meet E A S B).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists R, (neq E A /\ neq S B /\ Col E A R /\ Col S B R)) by (conclude_def Meet );destruct Tf as [R];spliter.
 assert (Col B C S) by (conclude_def Col ).
 assert (Col S B C) by (forward_using lemma_collinearorder).
 assert (Col B C R).
 by cases on (eq B R \/ neq B R).
 {
  assert (Col B C R) by (conclude_def Col ).
  close.
  }
 {
  assert (Col B R C) by (conclude lemma_collinear4).
  assert (Col B C R) by (forward_using lemma_collinearorder).
  close.
  }
(** cases *)
 assert (Col A D E) by (conclude_def Col ).
 assert (Col E A D) by (forward_using lemma_collinearorder).
 assert (neq A D) by (forward_using lemma_betweennotequal).
 assert (Col A D R) by (conclude lemma_collinear4).
 assert (Meet A D B C) by (conclude_def Meet ).
 contradict.
 }
assert (Col D F C) by (forward_using lemma_collinearorder).
assert (BetS D F C) by (conclude lemma_collinearbetween).
assert (BetS C F D) by (conclude axiom_betweennesssymmetry).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (neq E A) by (conclude lemma_inequalitysymmetric).
assert (neq B S) by (forward_using lemma_betweennotequal).
assert (neq S B) by (conclude lemma_inequalitysymmetric).
assert (~ Col E A C).
 {
 intro.
 assert (Col B C S) by (conclude_def Col ).
 assert (Col S B C) by (forward_using lemma_collinearorder).
 assert (Meet E A S B) by (conclude_def Meet ).
 contradict.
 }
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS C H A /\ BetS E F H)) by (conclude postulate_Pasch_outer);destruct Tf as [H];spliter.
assert (Col E F H) by (conclude_def Col ).
assert (Col E F B) by (conclude_def Col ).
assert (neq E F) by (forward_using lemma_betweennotequal).
assert (neq F E) by (conclude lemma_inequalitysymmetric).
assert (Col F E H) by (forward_using lemma_collinearorder).
assert (Col F E B) by (forward_using lemma_collinearorder).
assert (Col E H B) by (conclude lemma_collinear4).
assert (BetS A H C) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists R, (BetS A E R /\ Cong E R A E)) by (conclude lemma_extension);destruct Tf as [R];spliter.
assert (Col A E R) by (conclude_def Col ).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (neq A R) by (forward_using lemma_betweennotequal).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists T, (BetS C B T /\ Cong B T C B)) by (conclude lemma_extension);destruct Tf as [T];spliter.
assert (~ Meet A R T C).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists p, (neq A R /\ neq T C /\ Col A R p /\ Col T C p)) by (conclude_def Meet );destruct Tf as [p];spliter.
 assert (Col A E R) by (conclude_def Col ).
 assert (Col C B T) by (conclude_def Col ).
 assert (Col A D E) by (conclude_def Col ).
 assert (Col R A p) by (forward_using lemma_collinearorder).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col A R A) by (conclude_def Col ).
 assert (Col E A D) by (forward_using lemma_collinearorder).
 assert (Col A E R) by (conclude_def Col ).
 assert (Col E A R) by (forward_using lemma_collinearorder).
 assert (neq A D) by (forward_using lemma_betweennotequal).
 assert (Col A D R) by (conclude lemma_collinear4).
 assert (Col A R D) by (forward_using lemma_collinearorder).
 assert (Col A D p) by (conclude lemma_collinear5).
 assert (Col B T C) by (forward_using lemma_collinearorder).
 assert (Col T C B) by (forward_using lemma_collinearorder).
 assert (neq C T) by (forward_using lemma_betweennotequal).
 assert (neq T C) by (conclude lemma_inequalitysymmetric).
 assert (Col C B p) by (conclude lemma_collinear4).
 assert (Col B C p) by (forward_using lemma_collinearorder).
 assert (Meet A D B C) by (conclude_def Meet ).
 contradict.
 }
assert (BetS T B C) by (conclude axiom_betweennesssymmetry).
assert (Col T B C) by (conclude_def Col ).
assert (neq T C) by (forward_using lemma_betweennotequal).
assert (neq B C) by (forward_using lemma_betweennotequal).
assert (Col E B H) by (forward_using lemma_collinearorder).
assert (BetS E H B) by (conclude lemma_collinearbetween).
assert (BetS B H E) by (conclude axiom_betweennesssymmetry).
assert (~ Col B E A).
 {
 intro.
 assert (Col A D E) by (conclude_def Col ).
 assert (Col E A D) by (forward_using lemma_collinearorder).
 assert (Col E A B) by (forward_using lemma_collinearorder).
 assert (Col A D B) by (conclude lemma_collinear4).
 assert (eq B B) by (conclude cn_equalityreflexive).
 assert (Col B C B) by (conclude_def Col ).
 assert (Meet A D B C) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS B M D /\ BetS A M H)) by (conclude postulate_Pasch_inner);destruct Tf as [M];spliter.
assert (BetS A H C) by (conclude axiom_betweennesssymmetry).
assert (BetS A M C) by (conclude lemma_3_6b).
close.
Qed.

End Euclid.



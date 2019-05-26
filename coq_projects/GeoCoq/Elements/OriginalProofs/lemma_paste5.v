Require Export GeoCoq.Elements.OriginalProofs.lemma_rectangleparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.proposition_34.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crossimpliesopposite.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samenotopposite.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crisscross.

Section Euclid.

Context `{Ax:area}.

Lemma lemma_paste5 : 
   forall B C D E L M b c d e l m, 
   EF B M L D b m l d -> EF M C E L m c e l -> BetS B M C -> BetS b m c -> BetS E L D -> BetS e l d -> RE M C E L -> RE m c e l ->
   EF B C E D b c e d.
Proof.
intros.
assert (PG M C E L) by (conclude lemma_rectangleparallelogram).
assert (PG m c e l) by (conclude lemma_rectangleparallelogram).
let Tf:=fresh in
assert (Tf:exists P, (BetS M P E /\ BetS C P L)) by (conclude lemma_diagonalsmeet);destruct Tf as [P];spliter.
let Tf:=fresh in
assert (Tf:exists p, (BetS m p e /\ BetS c p l)) by (conclude lemma_diagonalsmeet);destruct Tf as [p];spliter.
assert (Par M C E L) by (conclude_def PG ).
assert (nCol M C L) by (forward_using lemma_parallelNC).
assert (Par m c e l) by (conclude_def PG ).
assert (nCol m c l) by (forward_using lemma_parallelNC).
assert (Cong_3 C M L L E C) by (conclude proposition_34).
assert (Cong_3 c m l l e c) by (conclude proposition_34).
assert (ET C M L L E C) by (conclude axiom_congruentequal).
assert (ET c m l l e c) by (conclude axiom_congruentequal).
assert (CR M E C L) by (conclude_def RE ).
assert (CR m e c l) by (conclude_def RE ).
assert (ET c m l c l e) by (forward_using axiom_ETpermutation).
assert (ET c l e c m l) by (conclude axiom_ETsymmetric).
assert (ET c l e m c l) by (forward_using axiom_ETpermutation).
assert (ET m c l c l e) by (conclude axiom_ETsymmetric).
assert (ET C M L C L E) by (forward_using axiom_ETpermutation).
assert (ET C L E C M L) by (conclude axiom_ETsymmetric).
assert (ET C L E M C L) by (forward_using axiom_ETpermutation).
assert (ET M C L C L E) by (conclude axiom_ETsymmetric).
assert (TS M C L E) by (forward_using lemma_crossimpliesopposite).
assert (TS m c l e) by (forward_using lemma_crossimpliesopposite).
assert (ET M C L m c l) by (conclude axiom_halvesofequals).
assert (EF M C E L e c m l) by (forward_using axiom_EFpermutation).
assert (EF e c m l M C E L) by (conclude axiom_EFsymmetric).
assert (EF e c m l E C M L) by (forward_using axiom_EFpermutation).
assert (EF E C M L e c m l) by (conclude axiom_EFsymmetric).
assert (TS E C L M) by (conclude lemma_oppositesidesymmetric).
assert (TS e c l m) by (conclude lemma_oppositesidesymmetric).
assert (ET M C L E C L) by (forward_using axiom_ETpermutation).
assert (ET E C L M C L) by (conclude axiom_ETsymmetric).
assert (ET E C L C L M) by (forward_using axiom_ETpermutation).
assert (ET m c l e c l) by (forward_using axiom_ETpermutation).
assert (ET e c l m c l) by (conclude axiom_ETsymmetric).
assert (ET e c l c l m) by (forward_using axiom_ETpermutation).
assert (ET E C L e c l) by (conclude axiom_halvesofequals).
assert (EF B M L D d b m l) by (forward_using axiom_EFpermutation).
assert (EF d b m l B M L D) by (conclude axiom_EFsymmetric).
assert (EF d b m l D B M L) by (forward_using axiom_EFpermutation).
assert (EF D B M L d b m l) by (conclude axiom_EFsymmetric).
assert (Col B M C) by (conclude_def Col ).
assert (Col M C B) by (forward_using lemma_collinearorder).
assert (neq B C) by (forward_using lemma_betweennotequal).
assert (Par E L M C) by (conclude lemma_parallelsymmetric).
assert (Par E L B C) by (conclude lemma_collinearparallel).
assert (Par B C E L) by (conclude lemma_parallelsymmetric).
assert (Col E L D) by (conclude_def Col ).
assert (neq L D) by (forward_using lemma_betweennotequal).
assert (neq D L) by (conclude lemma_inequalitysymmetric).
assert (Par B C D L) by (conclude lemma_collinearparallel).
assert (neq E L) by (forward_using lemma_betweennotequal).
assert (neq M C) by (forward_using lemma_betweennotequal).
assert (~ CR B D C L).
 {
 intro.
 assert (~ Col C L M).
  {
  intro.
  assert (Col M C L) by (forward_using lemma_collinearorder).
  assert (eq L L) by (conclude cn_equalityreflexive).
  assert (Col E L L) by (conclude_def Col ).
  assert (Meet E L M C) by (conclude_def Meet ).
  assert (~ Meet E L M C) by (conclude_def Par ).
  contradict.
  }
 assert (~ Col C L D).
  {
  intro.
  assert (Col D L C) by (forward_using lemma_collinearorder).
  assert (Col E L D) by (conclude_def Col ).
  assert (Col D L E) by (forward_using lemma_collinearorder).
  assert (neq L D) by (forward_using lemma_betweennotequal).
  assert (neq D L) by (conclude lemma_inequalitysymmetric).
  assert (Col L E C) by (conclude lemma_collinear4).
  assert (Col E L C) by (forward_using lemma_collinearorder).
  assert (eq C C) by (conclude cn_equalityreflexive).
  assert (Col M C C) by (conclude_def Col ).
  assert (Meet E L M C) by (conclude_def Meet ).
  assert (~ Meet E L M C) by (conclude_def Par ).
  contradict.
  }
 assert (eq L L) by (conclude cn_equalityreflexive).
 assert (Col C L L) by (conclude_def Col ).
 assert (BetS D L E) by (conclude axiom_betweennesssymmetry).
 assert (Col C L P) by (conclude_def Col ).
 assert (OS D M C L) by (unfold OS; exists E; exists L; exists P; splits;auto).
 assert (BetS C M B) by (conclude axiom_betweennesssymmetry).
 assert (neq C M) by (forward_using lemma_betweennotequal).
 assert (Out C M B) by (conclude lemma_ray4).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (Col C C L) by (conclude_def Col ).
 assert (OS D B C L) by (conclude lemma_sameside2).
 assert (OS B D C L) by (forward_using lemma_samesidesymmetric).
 assert (~ TS B C L D) by (conclude lemma_samenotopposite).
 assert (~ Col B C L).
  {
  intro.
  assert (Col B M C) by (conclude_def Col ).
  assert (Col B C M) by (forward_using lemma_collinearorder).
  assert (neq B C) by (forward_using lemma_betweennotequal).
  assert (Col C M L) by (conclude lemma_collinear4).
  assert (Col M C L) by (forward_using lemma_collinearorder).
  assert (Col E L L) by (conclude_def Col ).
  assert (Meet E L M C) by (conclude_def Meet ).
  assert (~ Meet E L M C) by (conclude_def Par ).
  contradict.
  }
 assert (TS B C L D) by (conclude (lemma_crossimpliesopposite B D C L)).
 contradict.
 }
assert (CR B L D C) by (conclude lemma_crisscross).
let Tf:=fresh in
assert (Tf:exists R, (BetS B R L /\ BetS D R C)) by (conclude_def CR );destruct Tf as [R];spliter.
assert (Col b m c) by (conclude_def Col ).
assert (Col m c b) by (forward_using lemma_collinearorder).
assert (neq b c) by (forward_using lemma_betweennotequal).
assert (Par e l m c) by (conclude lemma_parallelsymmetric).
assert (Par e l b c) by (conclude lemma_collinearparallel).
assert (Par b c e l) by (conclude lemma_parallelsymmetric).
assert (Col e l d) by (conclude_def Col ).
assert (neq l d) by (forward_using lemma_betweennotequal).
assert (neq d l) by (conclude lemma_inequalitysymmetric).
assert (Par b c d l) by (conclude lemma_collinearparallel).
assert (neq e l) by (forward_using lemma_betweennotequal).
assert (neq m c) by (forward_using lemma_betweennotequal).
assert (~ CR b d c l).
 {
 intro.
 assert (~ Col c l m).
  {
  intro.
  assert (Col m c l) by (forward_using lemma_collinearorder).
  assert (eq l l) by (conclude cn_equalityreflexive).
  assert (Col e l l) by (conclude_def Col ).
  assert (Meet e l m c) by (conclude_def Meet ).
  assert (~ Meet e l m c) by (conclude_def Par ).
  contradict.
  }
 assert (~ Col c l d).
  {
  intro.
  assert (Col d l c) by (forward_using lemma_collinearorder).
  assert (Col e l d) by (conclude_def Col ).
  assert (Col d l e) by (forward_using lemma_collinearorder).
  assert (neq l d) by (forward_using lemma_betweennotequal).
  assert (neq d l) by (conclude lemma_inequalitysymmetric).
  assert (Col l e c) by (conclude lemma_collinear4).
  assert (Col e l c) by (forward_using lemma_collinearorder).
  assert (eq c c) by (conclude cn_equalityreflexive).
  assert (Col m c c) by (conclude_def Col ).
  assert (Meet e l m c) by (conclude_def Meet ).
  assert (~ Meet e l m c) by (conclude_def Par ).
  contradict.
  }
 assert (eq l l) by (conclude cn_equalityreflexive).
 assert (Col c l l) by (conclude_def Col ).
 assert (BetS d l e) by (conclude axiom_betweennesssymmetry).
 assert (Col c l p) by (conclude_def Col ).
 assert (OS d m c l)
   by (unfold OS; exists e;exists l;exists p;splits;auto).
 assert (BetS c m b) by (conclude axiom_betweennesssymmetry).
 assert (neq c m) by (forward_using lemma_betweennotequal).
 assert (Out c m b) by (conclude lemma_ray4).
 assert (eq c c) by (conclude cn_equalityreflexive).
 assert (Col c c l) by (conclude_def Col ).
 assert (OS d b c l) by (conclude lemma_sameside2).
 assert (OS b d c l) by (forward_using lemma_samesidesymmetric).
 assert (~ TS b c l d) by (conclude lemma_samenotopposite).
 assert (~ Col b c l).
  {
  intro.
  assert (Col b m c) by (conclude_def Col ).
  assert (Col b c m) by (forward_using lemma_collinearorder).
  assert (neq b c) by (forward_using lemma_betweennotequal).
  assert (Col c m l) by (conclude lemma_collinear4).
  assert (Col m c l) by (forward_using lemma_collinearorder).
  assert (Col e l l) by (conclude_def Col ).
  assert (Meet e l m c) by (conclude_def Meet ).
  assert (~ Meet e l m c) by (conclude_def Par ).
  contradict.
  }
 assert (TS b c l d) by (conclude (lemma_crossimpliesopposite b d c l)).
 contradict.
 }
assert (CR b l d c) by (conclude lemma_crisscross).
let Tf:=fresh in
assert (Tf:exists r, (BetS b r l /\ BetS d r c)) by (conclude_def CR );destruct Tf as [r];spliter.
assert (EF D B C L d b c l) by (conclude axiom_paste2).
assert (EF D B C L b d l c) by (forward_using axiom_EFpermutation).
assert (EF b d l c D B C L) by (conclude axiom_EFsymmetric).
assert (EF b d l c B D L C) by (forward_using axiom_EFpermutation).
assert (EF B D L C b d l c) by (conclude axiom_EFsymmetric).
assert (ET E C L l e c) by (forward_using axiom_ETpermutation).
assert (ET l e c E C L) by (conclude axiom_ETsymmetric).
assert (ET l e c L E C) by (forward_using axiom_ETpermutation).
assert (ET L E C l e c) by (conclude axiom_ETsymmetric).
assert (BetS D L E) by (conclude axiom_betweennesssymmetry).
assert (BetS d l e) by (conclude axiom_betweennesssymmetry).
assert (Par B C L E) by (forward_using lemma_parallelflip).
assert (Col E L D) by (conclude_def Col ).
assert (Col L E D) by (forward_using lemma_collinearorder).
assert (neq E D) by (forward_using lemma_betweennotequal).
assert (neq D E) by (conclude lemma_inequalitysymmetric).
assert (Par B C D E) by (conclude lemma_collinearparallel).
assert (Par M L C E) by (conclude_def PG ).
assert (Par C E M L) by (conclude lemma_parallelsymmetric).
assert (TP C E M L) by (conclude lemma_paralleldef2B).
assert (OS M L C E) by (conclude_def TP ).
assert (OS L M C E) by (forward_using lemma_samesidesymmetric).
assert (neq M C) by (forward_using lemma_betweennotequal).
assert (neq C M) by (conclude lemma_inequalitysymmetric).
assert (BetS C M B) by (conclude axiom_betweennesssymmetry).
assert (Out C M B) by (conclude lemma_ray4).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col C C E) by (conclude_def Col ).
assert (OS L B C E) by (conclude lemma_sameside2).
assert (OS B L C E) by (forward_using lemma_samesidesymmetric).
assert (neq E L) by (forward_using lemma_betweennotequal).
assert (Out E L D) by (conclude lemma_ray4).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col C E E) by (conclude_def Col ).
assert (OS B D C E) by (conclude lemma_sameside2).
assert (OS D B C E) by (forward_using lemma_samesidesymmetric).
assert (~ CR B D C E).
 {
 intro.
 assert (~ Col B C E).
  {
  intro.
  assert (eq E E) by (conclude cn_equalityreflexive).
  assert (Col D E E) by (conclude_def Col ).
  assert (Meet B C D E) by (conclude_def Meet ).
  assert (~ Meet B C D E) by (conclude_def Par ).
  contradict.
  }
 assert (TS B C E D) by (conclude (lemma_crossimpliesopposite B D C E)).
 assert (~ TS B C E D) by (conclude lemma_samenotopposite).
 contradict.
 }
assert (CR B E D C) by (conclude lemma_crisscross).
let Tf:=fresh in
assert (Tf:exists T, (BetS B T E /\ BetS D T C)) by (conclude_def CR );destruct Tf as [T];spliter.
assert (Par b c l e) by (forward_using lemma_parallelflip).
assert (Col e l d) by (conclude_def Col ).
assert (Col l e d) by (forward_using lemma_collinearorder).
assert (neq e d) by (forward_using lemma_betweennotequal).
assert (neq d e) by (conclude lemma_inequalitysymmetric).
assert (Par b c d e) by (conclude lemma_collinearparallel).
assert (Par m l c e) by (conclude_def PG ).
assert (Par c e m l) by (conclude lemma_parallelsymmetric).
assert (TP c e m l) by (conclude lemma_paralleldef2B).
assert (OS m l c e) by (conclude_def TP ).
assert (OS l m c e) by (forward_using lemma_samesidesymmetric).
assert (neq m c) by (forward_using lemma_betweennotequal).
assert (neq c m) by (conclude lemma_inequalitysymmetric).
assert (BetS c m b) by (conclude axiom_betweennesssymmetry).
assert (Out c m b) by (conclude lemma_ray4).
assert (eq c c) by (conclude cn_equalityreflexive).
assert (Col c c e) by (conclude_def Col ).
assert (OS l b c e) by (conclude lemma_sameside2).
assert (OS b l c e) by (forward_using lemma_samesidesymmetric).
assert (neq e l) by (forward_using lemma_betweennotequal).
assert (Out e l d) by (conclude lemma_ray4).
assert (eq e e) by (conclude cn_equalityreflexive).
assert (Col c e e) by (conclude_def Col ).
assert (OS b d c e) by (conclude lemma_sameside2).
assert (OS d b c e) by (forward_using lemma_samesidesymmetric).
assert (~ CR b d c e).
 {
 intro.
 assert (~ Col b c e).
  {
  intro.
  assert (eq e e) by (conclude cn_equalityreflexive).
  assert (Col d e e) by (conclude_def Col ).
  assert (Meet b c d e) by (conclude_def Meet ).
  assert (~ Meet b c d e) by (conclude_def Par ).
  contradict.
  }
 assert (TS b c e d) by (conclude (lemma_crossimpliesopposite b d c e)).
 assert (~ TS b c e d) by (conclude lemma_samenotopposite).
 contradict.
 }
assert (CR b e d c) by (conclude lemma_crisscross).
let Tf:=fresh in
assert (Tf:exists t, (BetS b t e /\ BetS d t c)) by (conclude_def CR );destruct Tf as [t];spliter.
assert (EF B D E C b d e c) by (conclude axiom_paste2).
assert (EF B D E C b c e d) by (forward_using axiom_EFpermutation).
assert (EF b c e d B D E C) by (conclude axiom_EFsymmetric).
assert (EF b c e d B C E D) by (forward_using axiom_EFpermutation).
assert (EF B C E D b c e d) by (conclude axiom_EFsymmetric).
close.
Qed.

End Euclid.



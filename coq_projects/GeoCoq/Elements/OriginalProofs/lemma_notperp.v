Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidereflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_sameside2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_12.
Require Export GeoCoq.Elements.OriginalProofs.lemma_8_7.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_notperp : 
   forall A B C P, 
   BetS A C B -> nCol A B P ->
   exists X, nCol A B X /\ OS X P A B /\ ~ Per A C X.
Proof.
intros.
assert (neq C B) by (forward_using lemma_betweennotequal).
assert (neq B C) by (conclude lemma_inequalitysymmetric).
assert (~ eq C P).
 {
 intro.
 assert (nCol A B C) by (conclude cn_equalitysub).
 assert (Col A C B) by (conclude_def Col ).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists Q, (BetS B C Q /\ Cong C Q C P)) by (conclude lemma_extension);destruct Tf as [Q];spliter.
assert (~ eq P Q).
 {
 intro.
 assert (Col B C Q) by (conclude_def Col ).
 assert (Col B C P) by (conclude cn_equalitysub).
 assert (Col A C B) by (conclude_def Col ).
 assert (Col C B A) by (forward_using lemma_collinearorder).
 assert (Col C B P) by (forward_using lemma_collinearorder).
 assert (Col B A P) by (conclude lemma_collinear4).
 assert (Col A B P) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS P M Q /\ Cong M P M Q)) by (conclude proposition_10);destruct Tf as [M];spliter.
assert (Col A C B) by (conclude_def Col ).
assert (Col C B A) by (forward_using lemma_collinearorder).
assert (neq C B) by (forward_using lemma_betweennotequal).
assert (Col C B Q) by (conclude_def Col ).
assert (Col B A Q) by (conclude lemma_collinear4).
assert (Col A B Q) by (forward_using lemma_collinearorder).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (OS P P A B) by (conclude lemma_samesidereflexive).
assert (neq Q P) by (conclude lemma_inequalitysymmetric).
assert (BetS Q M P) by (conclude axiom_betweennesssymmetry).
assert (Out Q P M) by (conclude lemma_ray4).
assert (Col A Q B) by (forward_using lemma_collinearorder).
assert (OS P M A B) by (conclude lemma_sameside2).
assert (OS M P A B) by (forward_using lemma_samesidesymmetric).
assert (~ Col A B M).
 {
 intro.
 assert (Col B M Q) by (conclude lemma_collinear4).
 assert (Col P M Q) by (conclude_def Col ).
 assert (Col M Q P) by (forward_using lemma_collinearorder).
 assert (Col M Q B) by (forward_using lemma_collinearorder).
 assert (neq M Q) by (forward_using lemma_betweennotequal).
 assert (Col Q P B) by (conclude lemma_collinear4).
 assert (Col Q B P) by (forward_using lemma_collinearorder).
 assert (Col Q B A) by (forward_using lemma_collinearorder).
 assert (neq B Q) by (forward_using lemma_betweennotequal).
 assert (neq Q B) by (conclude lemma_inequalitysymmetric).
 assert (Col B P A) by (conclude lemma_collinear4).
 assert (Col A B P) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists R, Perp_at M R A B R) by (conclude proposition_12);destruct Tf as [R];spliter.
let Tf:=fresh in
assert (Tf:exists E, (Col M R R /\ Col A B R /\ Col A B E /\ Per E R M)) by (conclude_def Perp_at );destruct Tf as [E];spliter.
assert (Per M R E) by (conclude lemma_8_2).
assert (~ eq M R).
 {
 intro.
 assert (Col A B M) by (conclude cn_equalitysub).
 contradict.
 }
assert (neq A C) by (forward_using lemma_betweennotequal).
assert (Col A B C) by (forward_using lemma_collinearorder).
assert (~ Per A C M).
 {
 intro.
 assert (~ neq R C).
  {
  intro.
  assert (Col B A C) by (forward_using lemma_collinearorder).
  assert (Col B A R) by (forward_using lemma_collinearorder).
  assert (neq B A) by (conclude lemma_inequalitysymmetric).
  assert (Col A C R) by (conclude lemma_collinear4).
  assert (Per R C M) by (conclude lemma_collinearright).
  assert (~ Per M R C) by (conclude lemma_8_7).
  assert (Per E R M) by (conclude lemma_8_2).
  assert (Col B C R) by (conclude lemma_collinear4).
  assert (Col B C E) by (conclude lemma_collinear4).
  assert (neq C B) by (forward_using lemma_betweennotequal).
  assert (neq B C) by (conclude lemma_inequalitysymmetric).
  assert (Col C R E) by (conclude lemma_collinear4).
  assert (Col E R C) by (forward_using lemma_collinearorder).
  assert (neq C R) by (conclude lemma_inequalitysymmetric).
  assert (Per C R M) by (conclude lemma_collinearright).
  assert (Per M R C) by (conclude lemma_8_2).
  contradict.
  }
 assert (~ eq M C).
  {
  intro.
  assert (Col A B M) by (conclude cn_equalitysub).
  contradict.
  }
 assert (Cong Q C P C) by (forward_using lemma_congruenceflip).
 assert (BetS Q M P) by (conclude axiom_betweennesssymmetry).
 assert (Cong Q M P M) by (forward_using lemma_doublereverse).
 assert (Per Q M C) by (conclude_def Per ).
 assert (neq C Q) by (forward_using lemma_betweennotequal).
 assert (neq Q C) by (conclude lemma_inequalitysymmetric).
 assert (Per E R M) by (conclude lemma_8_2).
 assert (neq Q R) by (conclude cn_equalitysub).
 assert (Col B C Q) by (conclude_def Col ).
 assert (Col C B Q) by (forward_using lemma_collinearorder).
 assert (Col Q B C) by (forward_using lemma_collinearorder).
 assert (Col B E R) by (conclude lemma_collinear4).
 assert (Col B E Q) by (conclude lemma_collinear4).
 assert (~ neq B E).
  {
  intro.
  assert (Col E R Q) by (conclude lemma_collinear4).
  assert (Per Q R M) by (conclude lemma_collinearright).
  assert (Per Q C M) by (conclude cn_equalitysub).
  assert (Per M C Q) by (conclude lemma_8_2).
  assert (~ Per Q M C) by (conclude lemma_8_7).
  contradict.
  }
 assert (Col A E R) by (conclude cn_equalitysub).
 assert (Col A B Q) by (forward_using lemma_collinearorder).
 assert (Col A E Q) by (conclude cn_equalitysub).
 assert (neq A E) by (conclude cn_equalitysub).
 assert (Col E R Q) by (conclude lemma_collinear4).
 assert (Per Q R M) by (conclude lemma_collinearright).
 assert (Per Q C M) by (conclude cn_equalitysub).
 assert (Per M C Q) by (conclude lemma_8_2).
 assert (~ Per Q M C) by (conclude lemma_8_7).
 contradict.
 }
exists M;close.
Qed.

End Euclid.



Require Export GeoCoq.Elements.OriginalProofs.lemma_30helper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crossimpliesopposite.
Require Export GeoCoq.Elements.OriginalProofs.proposition_30A.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma parnotmeet: forall A B C D,
 Par A B C D -> ~ Meet A B C D.
Proof.
intros.
conclude_def Par.
Qed.

Lemma proposition_30 : 
   forall A B C D E F G H K, 
   Par A B E F -> Par C D E F -> BetS G H K -> Col A B G -> Col E F H -> Col C D K -> neq A G -> neq E H -> neq C K ->
   Par A B C D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists b, (BetS A G b /\ Cong G b A G)) by (conclude lemma_extension);destruct Tf as [b];spliter.
let Tf:=fresh in
assert (Tf:exists f, (BetS E H f /\ Cong H f E H)) by (conclude lemma_extension);destruct Tf as [f];spliter.
let Tf:=fresh in
assert (Tf:exists d, (BetS C K d /\ Cong K d C K)) by (conclude lemma_extension);destruct Tf as [d];spliter.
assert (nCol C D E) by (forward_using lemma_parallelNC).
assert (neq C D) by (forward_using lemma_NCdistinct).
assert (Col A G b) by (conclude_def Col ).
assert (Col G A b) by (forward_using lemma_collinearorder).
assert (Col G A B) by (forward_using lemma_collinearorder).
assert (neq G A) by (conclude lemma_inequalitysymmetric).
assert (Col A b B) by (conclude lemma_collinear4).
assert (Col B A b) by (forward_using lemma_collinearorder).
assert (Par E F A B) by (conclude lemma_parallelsymmetric).
assert (Par E F B A) by (forward_using lemma_parallelflip).
assert (neq A b) by (forward_using lemma_betweennotequal).
assert (neq b A) by (conclude lemma_inequalitysymmetric).
assert (Par E F b A) by (conclude lemma_collinearparallel).
assert (Par E F A b) by (forward_using lemma_parallelflip).
assert (Par A b E F) by (conclude lemma_parallelsymmetric).
assert (Col E H f) by (conclude_def Col ).
assert (Col H E f) by (forward_using lemma_collinearorder).
assert (Col H E F) by (forward_using lemma_collinearorder).
assert (neq H E) by (conclude lemma_inequalitysymmetric).
assert (Col E f F) by (conclude lemma_collinear4).
assert (Col F E f) by (forward_using lemma_collinearorder).
assert (neq E f) by (forward_using lemma_betweennotequal).
assert (neq f E) by (conclude lemma_inequalitysymmetric).
assert (Par A b F E) by (forward_using lemma_parallelflip).
assert (Par A b f E) by (conclude lemma_collinearparallel).
assert (Par A b E f) by (forward_using lemma_parallelflip).
assert (Col C K d) by (conclude_def Col ).
assert (Col K C d) by (forward_using lemma_collinearorder).
assert (Col K C D) by (forward_using lemma_collinearorder).
assert (neq K C) by (conclude lemma_inequalitysymmetric).
assert (Col C d D) by (conclude lemma_collinear4).
assert (Col D C d) by (forward_using lemma_collinearorder).
assert (Par E F C D) by (conclude lemma_parallelsymmetric).
assert (Par E F D C) by (forward_using lemma_parallelflip).
assert (neq C d) by (forward_using lemma_betweennotequal).
assert (neq d C) by (conclude lemma_inequalitysymmetric).
assert (Par E F d C) by (conclude lemma_collinearparallel).
assert (Par E F C d) by (forward_using lemma_parallelflip).
assert (Par C d E F) by (conclude lemma_parallelsymmetric).
assert (Par C d F E) by (forward_using lemma_parallelflip).
assert (Par C d f E) by (conclude lemma_collinearparallel).
assert (Par C d E f) by (forward_using lemma_parallelflip).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col E H H) by (conclude_def Col ).
assert (Col A b G) by (forward_using lemma_collinearorder).
assert (Col E f H) by (forward_using lemma_collinearorder).
assert (Col f E H) by (forward_using lemma_collinearorder).
assert (Par A b f E) by (forward_using lemma_parallelflip).
assert (Par A b H E) by (conclude lemma_collinearparallel).
assert (Par H E A b) by (conclude lemma_parallelsymmetric).
assert (Par E H b A) by (forward_using lemma_parallelflip).
assert (Col b A G) by (forward_using lemma_collinearorder).
assert (Par E H G A) by (conclude lemma_collinearparallel).
assert (Par E H A G) by (forward_using lemma_parallelflip).
assert (Par A G E H) by (conclude lemma_parallelsymmetric).
assert (Par C d f E) by (forward_using lemma_parallelflip).
assert (Col f E H) by (forward_using lemma_collinearorder).
assert (Par C d H E) by (conclude lemma_collinearparallel).
assert (Par H E C d) by (conclude lemma_parallelsymmetric).
assert (Par H E d C) by (forward_using lemma_parallelflip).
assert (Col C K d) by (conclude_def Col ).
assert (Col d C K) by (forward_using lemma_collinearorder).
assert (neq C K) by (forward_using lemma_betweennotequal).
assert (neq K C) by (conclude lemma_inequalitysymmetric).
assert (Par H E K C) by (conclude lemma_collinearparallel).
assert (Par E H C K) by (forward_using lemma_parallelflip).
assert (TP E H C K) by (conclude lemma_paralleldef2B).
assert (OS C K E H) by (conclude_def TP ).
assert (nCol E H K) by (forward_using lemma_parallelNC).
assert (BetS K H G) by (conclude axiom_betweennesssymmetry).
assert (TS K E H G) by (conclude_def TS ).
assert (TS C E H G) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists Q, (BetS C Q G /\ Col E H Q /\ nCol E H C)) by (conclude_def TS );destruct Tf as [Q];spliter.
assert (Par E f C d) by (conclude lemma_parallelsymmetric).
assert (TP E f C d) by (conclude lemma_paralleldef2B).
assert (OS C d E f) by (conclude_def TP ).
assert (OS d C E f) by (forward_using lemma_samesidesymmetric).
assert (Col E H f) by (conclude_def Col ).
assert (Col H E f) by (forward_using lemma_collinearorder).
assert (Col H E Q) by (forward_using lemma_collinearorder).
assert (Col E f Q) by (conclude lemma_collinear4).
assert (nCol C E f) by (forward_using lemma_parallelNC).
assert (nCol E f C) by (forward_using lemma_NCorder).
assert (TS C E f G) by (conclude_def TS ).
assert (TS d E f G) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists P, (BetS d P G /\ Col E f P /\ nCol E f d)) by (conclude_def TS );destruct Tf as [P];spliter.
assert (~ ~ (CR A f G H \/ CR A E G H)).
 {
 intro.
 assert (CR A E G H) by (conclude lemma_30helper).
 contradict.
 }
assert (~ ~ (CR C f K H \/ CR C E K H)).
 {
 intro.
 assert (CR C E K H) by (conclude lemma_30helper).
 contradict.
 }
assert (Col F E H) by (forward_using lemma_collinearorder).
assert (Col B A G) by (forward_using lemma_collinearorder).
assert (Par A B F E) by (forward_using lemma_parallelflip).
assert (Par A B H E) by (conclude lemma_collinearparallel).
assert (Par A B E H) by (forward_using lemma_parallelflip).
assert (Par E H A B) by (conclude lemma_parallelsymmetric).
assert (Par E H B A) by (forward_using lemma_parallelflip).
assert (Par E H G A) by (conclude lemma_collinearparallel).
assert (Par E H A G) by (forward_using lemma_parallelflip).
assert (Par A G E H) by (conclude lemma_parallelsymmetric).
assert (nCol A G H) by (forward_using lemma_parallelNC).
assert (Par C D F E) by (forward_using lemma_parallelflip).
assert (Par C D H E) by (conclude lemma_collinearparallel).
assert (Par C D E H) by (forward_using lemma_parallelflip).
assert (Par E H C D) by (conclude lemma_parallelsymmetric).
assert (Par E H D C) by (forward_using lemma_parallelflip).
assert (Col D C K) by (forward_using lemma_collinearorder).
assert (Par E H K C) by (conclude lemma_collinearparallel).
assert (Par E H C K) by (forward_using lemma_parallelflip).
assert (Par C K E H) by (conclude lemma_parallelsymmetric).
assert (nCol C K H) by (forward_using lemma_parallelNC).
assert (nCol K H C) by (forward_using lemma_NCorder).
assert (nCol E H K) by (forward_using lemma_parallelNC).
assert (Col E H f) by (conclude_def Col ).
assert (neq H f) by (forward_using lemma_betweennotequal).
assert (neq f H) by (conclude lemma_inequalitysymmetric).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col E H H) by (conclude_def Col ).
assert (nCol f H K) by (conclude lemma_NChelper).
assert (nCol K H f) by (forward_using lemma_NCorder).
assert (Col K H H) by (conclude_def Col ).
assert (Par A b C d).
by cases on (CR A f G H \/ CR A E G H).
{
 assert (TS A G H f) by (forward_using lemma_crossimpliesopposite).
 assert (Par A b C d).
 by cases on (CR C f K H \/ CR C E K H).
 {
  assert (TS f H K C) by (forward_using lemma_crossimpliesopposite).
  assert (Par A b C d)
   by (apply (proposition_30A _ _ _ _ E f G H K);assumption).
  close.
  }
 {
  let Tf:=fresh in
  assert (Tf:exists M, (BetS C M E /\ BetS K M H)) by (conclude_def CR );destruct Tf as [M];spliter.
  assert (Col K M H) by (conclude_def Col ).
  assert (Col K H M) by (forward_using lemma_collinearorder).
  assert (BetS f H E) by (conclude axiom_betweennesssymmetry).
  assert (OS f C K H) by (conclude_def OS ).
  assert (eq K K) by (conclude cn_equalityreflexive).
  assert (Col K H K) by (conclude_def Col ).
  assert (TS C K H d) by (conclude_def TS ).
  assert (TS f K H d) by (conclude lemma_planeseparation).
  let Tf:=fresh in
  assert (Tf:exists m, (BetS f m d /\ Col K H m /\ nCol K H f)) by (conclude_def TS );destruct Tf as [m];spliter.
  assert (Par f E C d) by (conclude lemma_parallelsymmetric).
  assert (~ Meet f E C d) by (auto using parnotmeet).
  assert (Col f H E) by (forward_using lemma_collinearorder).
  assert (neq f E) by (forward_using lemma_betweennotequal).
  assert (neq f H) by (conclude lemma_inequalitysymmetric).
  assert (neq K d) by (forward_using lemma_betweennotequal).
  assert (Col H K m) by (forward_using lemma_collinearorder).
  assert (BetS H m K) by (conclude lemma_collinearbetween).
  assert (BetS K m H) by (conclude axiom_betweennesssymmetry).
  assert (BetS d m f) by (conclude axiom_betweennesssymmetry).
  assert (CR d f K H) by (conclude_def CR ).
  assert (nCol C K H) by (forward_using lemma_NCorder).
  assert (Col C K d) by (conclude_def Col ).
  assert (neq d K) by (conclude lemma_inequalitysymmetric).
  assert (Col C K K) by (conclude_def Col ).
  assert (nCol d K H) by (conclude lemma_NChelper).
  assert (TS d H K f) by (forward_using lemma_crossimpliesopposite).
  assert (Par d C E f) by (forward_using lemma_parallelflip).
  assert (BetS d K C) by (conclude axiom_betweennesssymmetry).
  assert (TS f H K d) by (conclude lemma_oppositesidesymmetric).
  assert (Par A b d C).
  { simple eapply proposition_30A.
    exact H40.
    exact H171.
    exact H2.
    exact H9.
    exact H11.
    exact H172.
    exact H138.
    exact H173.
 }
  assert (Par A b C d) by (forward_using lemma_parallelflip).
  close.
  }
(** cases *)
 close.
 }
{
 assert (Par A b C d).
 by cases on (CR C f K H \/ CR C E K H).
 {
  let Tf:=fresh in
  assert (Tf:exists M, (BetS C M f /\ BetS K M H)) by (conclude_def CR );destruct Tf as [M];spliter.
  assert (Col K M H) by (conclude_def Col ).
  assert (Col K H M) by (forward_using lemma_collinearorder).
  assert (nCol K H E) by (forward_using lemma_NCorder).
  assert (nCol K H C) by (forward_using lemma_NCorder).
  assert (OS E C K H) by (conclude_def OS ).
  assert (eq K K) by (conclude cn_equalityreflexive).
  assert (Col K H K) by (conclude_def Col ).
  assert (TS C K H d) by (conclude_def TS ).
  assert (TS E K H d) by (conclude lemma_planeseparation).
  let Tf:=fresh in
  assert (Tf:exists m, (BetS E m d /\ Col K H m /\ nCol K H E)) by (conclude_def TS );destruct Tf as [m];spliter.
  assert (Par E f C d) by (conclude lemma_parallelsymmetric).
  assert (~ Meet E f C d) by (auto using parnotmeet).
  assert (Col E H f) by (forward_using lemma_collinearorder).
  assert (neq E f) by (forward_using lemma_betweennotequal).
  assert (neq E H) by (conclude lemma_inequalitysymmetric).
  assert (neq K d) by (forward_using lemma_betweennotequal).
  assert (Col H K m) by (forward_using lemma_collinearorder).
  assert (BetS H m K) by (conclude lemma_collinearbetween).
  assert (BetS K m H) by (conclude axiom_betweennesssymmetry).
  assert (BetS d m E) by (conclude axiom_betweennesssymmetry).
  assert (CR d E K H) by (conclude_def CR ).
  assert (nCol C K H) by (forward_using lemma_NCorder).
  assert (Col C K d) by (conclude_def Col ).
  assert (neq d K) by (conclude lemma_inequalitysymmetric).
  assert (Col C K K) by (conclude_def Col ).
  assert (nCol d K H) by (conclude lemma_NChelper).
  assert (TS d H K E) by (forward_using lemma_crossimpliesopposite).
  assert (Par d C f E) by (forward_using lemma_parallelflip).
  assert (BetS d K C) by (conclude axiom_betweennesssymmetry).
  assert (TS E H K d) by (conclude lemma_oppositesidesymmetric).
  assert (TS A G H E) by (forward_using lemma_crossimpliesopposite).
  assert (BetS f H E) by (conclude axiom_betweennesssymmetry).
  assert (Par A b d C) by (conclude proposition_30A).
  assert (Par A b C d) by (forward_using lemma_parallelflip).
  close.
  }
 {
  assert (TS C H K E) by (forward_using lemma_crossimpliesopposite).
  assert (TS E H K C) by (conclude lemma_oppositesidesymmetric).
  assert (TS A G H E) by (forward_using lemma_crossimpliesopposite).
  assert (BetS f H E) by (conclude axiom_betweennesssymmetry).
  assert (Par A b C d).
   { 
  simple eapply proposition_30A.
   exact H62.
   exact H70.
   exact H2.
   exact H9.
   exact H143.
   exact H13.
   exact H142.
   exact H141.
  }
  close.
  }
(** cases *)
 close.
 }
(** cases *)
assert (Par A b d C) by (forward_using lemma_parallelflip).
assert (Col d C D) by (forward_using lemma_collinearorder).
assert (neq D C) by (conclude lemma_inequalitysymmetric).
assert (Par A b D C) by (conclude lemma_collinearparallel).
assert (Par A b C D) by (forward_using lemma_parallelflip).
assert (Par C D A b) by (conclude lemma_parallelsymmetric).
assert (Par C D b A) by (forward_using lemma_parallelflip).
assert (Col b A B) by (forward_using lemma_collinearorder).
assert (nCol A B E) by (forward_using lemma_parallelNC).
assert (neq B A) by (forward_using lemma_NCdistinct).
assert (Par C D B A) by (conclude lemma_collinearparallel).
assert (Par C D A B) by (forward_using lemma_parallelflip).
assert (Par A B C D) by (conclude lemma_parallelsymmetric).
close.
Qed.

End Euclid.



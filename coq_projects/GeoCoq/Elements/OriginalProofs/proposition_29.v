Require Export GeoCoq.Elements.OriginalProofs.proposition_31.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crossbar2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_supplementinequality.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angletrichotomy2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_supplementsymmetric.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_29 : 
   forall A B C D E G H, 
   Par A B C D -> BetS A G B -> BetS C H D -> BetS E G H -> TS A G H D ->
   CongA A G H G H D /\ CongA E G B G H D /\ RT B G H G H D.
Proof.
intros.
assert (Col C H D) by (conclude_def Col ).
assert (neq G H) by (forward_using lemma_betweennotequal).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq C D) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists R, (BetS A R D /\ Col G H R /\ nCol G H A)) by (conclude_def TS );destruct Tf as [R];spliter.
assert (TS D G H A) by (conclude lemma_oppositesidesymmetric).
assert (nCol G H D) by (conclude_def TS ).
assert (nCol D H G) by (forward_using lemma_NCorder).
assert (Col D H C) by (forward_using lemma_collinearorder).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col D H H) by (conclude_def Col ).
assert (neq C H) by (forward_using lemma_betweennotequal).
assert (nCol C H G) by (conclude lemma_NChelper).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col C H C) by (conclude_def Col ).
assert (neq C D) by (forward_using lemma_betweennotequal).
assert (nCol C D G) by (conclude lemma_NChelper).
let Tf:=fresh in
assert (Tf:exists P Q S, (BetS P G Q /\ CongA Q G H G H C /\ CongA Q G H C H G /\ CongA H G Q C H G /\ CongA P G H G H D /\ CongA P G H D H G /\ CongA H G P D H G /\ Par P Q C D /\ Cong P G H D /\ Cong G Q C H /\ Cong G S S H /\ Cong P S S D /\ Cong C S S Q /\ BetS P S D /\ BetS C S Q /\ BetS G S H)) by (conclude proposition_31);destruct Tf as [P[Q[S]]];spliter.
assert (~ Meet A B C D) by (conclude_def Par ).
assert (eq P P) by (conclude cn_equalityreflexive).
assert (neq P G) by (forward_using lemma_betweennotequal).
assert (neq G P) by (conclude lemma_inequalitysymmetric).
assert (Out G P P) by (conclude lemma_ray4).
assert (Col G S H) by (conclude_def Col ).
assert (Col G H S) by (forward_using lemma_collinearorder).
assert (CongA G H D P G H) by (conclude lemma_equalanglessymmetric).
assert (nCol P G H) by (conclude lemma_equalanglesNC).
assert (nCol G H P) by (forward_using lemma_NCorder).
assert (OS A P G H) by (conclude_def OS ).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (neq G H) by (forward_using lemma_betweennotequal).
assert (Out G H H) by (conclude lemma_ray4).
assert (~ LtA H G A H G P).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists M, (BetS P M H /\ Out G A M)) by (conclude lemma_crossbar2);destruct Tf as [M];spliter.
 assert (Cong G S H S) by (forward_using lemma_congruenceflip).
 assert (Cong S P S D) by (forward_using lemma_congruenceflip).
 let Tf:=fresh in
 assert (Tf:exists K, (BetS G M K /\ BetS D H K)) by (conclude postulate_Euclid5);destruct Tf as [K];spliter.
 assert (Col G A M) by (conclude lemma_rayimpliescollinear).
 assert (Col G M K) by (conclude_def Col ).
 assert (Col M G A) by (forward_using lemma_collinearorder).
 assert (Col M G K) by (forward_using lemma_collinearorder).
 assert (neq G M) by (conclude lemma_raystrict).
 assert (neq M G) by (conclude lemma_inequalitysymmetric).
 assert (Col G A K) by (conclude lemma_collinear4).
 assert (Col A G B) by (conclude_def Col ).
 assert (Col A G K) by (forward_using lemma_collinearorder).
 assert (Col G A B) by (forward_using lemma_collinearorder).
 assert (Col G A K) by (forward_using lemma_collinearorder).
 assert (neq A G) by (forward_using lemma_betweennotequal).
 assert (neq G A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B K) by (conclude lemma_collinear4).
 assert (Col H D K) by (conclude_def Col ).
 assert (Col H D C) by (forward_using lemma_collinearorder).
 assert (neq H D) by (forward_using lemma_betweennotequal).
 assert (Col D K C) by (conclude lemma_collinear4).
 assert (Col C D K) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ LtA H G P H G A).
 {
 intro.
 assert (nCol P G H) by (forward_using lemma_NCorder).
 assert (CongA P G H H G P) by (conclude lemma_ABCequalsCBA).
 assert (LtA P G H H G A) by (conclude lemma_angleorderrespectscongruence2).
 assert (~ Col H G A).
  {
  intro.
  assert (Col G H A) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA H G A A G H) by (conclude lemma_ABCequalsCBA).
 assert (CongA A G H H G A) by (conclude lemma_equalanglessymmetric).
 assert (LtA P G H A G H) by (conclude lemma_angleorderrespectscongruence).
 assert (eq H H) by (conclude cn_equalityreflexive).
 assert (Out G H H) by (conclude lemma_ray4).
 assert (Supp P G H H Q) by (conclude_def Supp ).
 assert (BetS D H C) by (conclude axiom_betweennesssymmetry).
 assert (eq G G) by (conclude cn_equalityreflexive).
 assert (neq H G) by (conclude lemma_inequalitysymmetric).
 assert (Out H G G) by (conclude lemma_ray4).
 assert (Supp D H G G C) by (conclude_def Supp ).
 assert (CongA G H D D H G) by (conclude lemma_ABCequalsCBA).
 assert (CongA P G H D H G) by (conclude lemma_equalanglestransitive).
 assert (CongA H G Q G H C) by (conclude lemma_supplements).
 assert (Supp A G H H B) by (conclude_def Supp ).
 assert (LtA H G B H G Q) by (conclude lemma_supplementinequality).
 assert (BetS B G A) by (conclude axiom_betweennesssymmetry).
 assert (eq G G) by (conclude cn_equalityreflexive).
 assert (Col G H G) by (conclude_def Col ).
 assert (~ Col G H B).
  {
  intro.
  assert (Col A G B) by (conclude_def Col ).
  assert (Col B G A) by (forward_using lemma_collinearorder).
  assert (Col B G H) by (forward_using lemma_collinearorder).
  assert (neq G B) by (forward_using lemma_betweennotequal).
  assert (neq B G) by (conclude lemma_inequalitysymmetric).
  assert (Col G A H) by (conclude lemma_collinear4).
  assert (Col H G A) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (TS B G H A) by (conclude_def TS ).
 assert (TS A G H B) by (conclude lemma_oppositesidesymmetric).
 assert (OS A P G H) by (conclude_def OS ).
 assert (OS P A G H) by (forward_using lemma_samesidesymmetric).
 assert (TS P G H B) by (conclude lemma_planeseparation).
 let Tf:=fresh in
 assert (Tf:exists L, (BetS P L B /\ Col G H L /\ nCol G H P)) by (conclude_def TS );destruct Tf as [L];spliter.
 assert (BetS B L P) by (conclude axiom_betweennesssymmetry).
 assert (CongA G H C H G Q) by (conclude lemma_equalanglessymmetric).
 assert (nCol H G Q) by (conclude lemma_equalanglesNC).
 assert (~ Col G H Q).
  {
  intro.
  assert (Col H G Q) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (BetS Q G P) by (conclude axiom_betweennesssymmetry).
 assert (OS B Q G H) by (conclude_def OS ).
 assert (eq Q Q) by (conclude cn_equalityreflexive).
 assert (neq Q G) by (forward_using lemma_betweennotequal).
 assert (neq G Q) by (conclude lemma_inequalitysymmetric).
 assert (Out G Q Q) by (conclude lemma_ray4).
 let Tf:=fresh in
 assert (Tf:exists M, (BetS Q M H /\ Out G B M)) by (conclude lemma_crossbar2);destruct Tf as [M];spliter.
 assert (Cong G S H S) by (forward_using lemma_congruenceflip).
 assert (BetS Q S C) by (conclude axiom_betweennesssymmetry).
 assert (Cong S Q C S) by (conclude lemma_congruencesymmetric).
 assert (Cong S Q S C) by (forward_using lemma_congruenceflip).
 assert (nCol G H C) by (forward_using lemma_NCorder).
 let Tf:=fresh in
 assert (Tf:exists K, (BetS G M K /\ BetS C H K)) by (conclude postulate_Euclid5);destruct Tf as [K];spliter.
 assert (Col G B M) by (conclude lemma_rayimpliescollinear).
 assert (Col G M K) by (conclude_def Col ).
 assert (Col M G B) by (forward_using lemma_collinearorder).
 assert (Col M G K) by (forward_using lemma_collinearorder).
 assert (neq G M) by (conclude lemma_raystrict).
 assert (neq M G) by (conclude lemma_inequalitysymmetric).
 assert (Col G B K) by (conclude lemma_collinear4).
 assert (Col B G A) by (conclude_def Col ).
 assert (Col B G K) by (forward_using lemma_collinearorder).
 assert (Col G B A) by (forward_using lemma_collinearorder).
 assert (Col G B K) by (forward_using lemma_collinearorder).
 assert (neq B G) by (forward_using lemma_betweennotequal).
 assert (neq G B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A K) by (conclude lemma_collinear4).
 assert (Col A B K) by (forward_using lemma_collinearorder).
 assert (Col H C K) by (conclude_def Col ).
 assert (Col H C D) by (forward_using lemma_collinearorder).
 assert (neq H C) by (forward_using lemma_betweennotequal).
 assert (Col C K D) by (conclude lemma_collinear4).
 assert (Col C D K) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Col H G P).
 {
 intro.
 assert (Col G H P) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col H G A).
 {
 intro.
 assert (Col G H A) by (forward_using lemma_collinearorder).
 assert (nCol G H A) by (conclude_def TS ).
 contradict.
 }
assert (~ ~ CongA H G A H G P).
 {
 intro.
 assert (LtA H G A H G P) by (conclude lemma_angletrichotomy2).
 contradict.
 }
assert (CongA H G P P G H) by (conclude lemma_ABCequalsCBA).
assert (CongA H G P G H D) by (conclude lemma_equalanglestransitive).
assert (CongA G H D D H G) by (conclude lemma_ABCequalsCBA).
assert (CongA H G P D H G) by (conclude lemma_equalanglestransitive).
assert (CongA H G A D H G) by (conclude lemma_equalanglestransitive).
assert (~ Col A G H).
 {
 intro.
 assert (Col G H A) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A G H H G A) by (conclude lemma_ABCequalsCBA).
assert (CongA A G H D H G) by (conclude lemma_equalanglestransitive).
assert (nCol D H G) by (conclude lemma_equalanglesNC).
assert (CongA D H G G H D) by (conclude lemma_ABCequalsCBA).
assert (CongA A G H G H D) by (conclude lemma_equalanglestransitive).
assert (BetS H G E) by (conclude axiom_betweennesssymmetry).
assert (CongA A G H E G B) by (conclude proposition_15a).
assert (CongA E G B A G H) by (conclude lemma_equalanglessymmetric).
assert (CongA E G B G H D) by (conclude lemma_equalanglestransitive).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Out G H H) by (conclude lemma_ray4).
assert (Supp A G H H B) by (conclude_def Supp ).
assert (~ Col B G H).
 {
 intro.
 assert (Col A G B) by (conclude_def Col ).
 assert (Col B G A) by (forward_using lemma_collinearorder).
 assert (neq G B) by (forward_using lemma_betweennotequal).
 assert (neq B G) by (conclude lemma_inequalitysymmetric).
 assert (Col G H A) by (conclude lemma_collinear4).
 assert (Col A G H) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B G H B G H) by (conclude lemma_equalanglesreflexive).
assert (CongA G H D A G H) by (conclude lemma_equalanglessymmetric).
assert (CongA A G H H G A) by (conclude lemma_ABCequalsCBA).
assert (CongA G H D H G A) by (conclude lemma_equalanglestransitive).
assert (Supp B G H H A) by (conclude lemma_supplementsymmetric).
assert (RT B G H G H D) by (conclude_def RT ).
close.
Qed.

End Euclid.



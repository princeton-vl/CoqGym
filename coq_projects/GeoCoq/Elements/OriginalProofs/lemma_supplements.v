Require Export GeoCoq.Elements.OriginalProofs.lemma_raystrict.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray1.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rayimpliescollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray3.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supplements : 
   forall A B C D F a b c d f, 
   CongA A B C a b c -> Supp A B C D F -> Supp a b c d f ->
   CongA D B F d b f.
Proof.
intros.
assert (BetS A B F) by (conclude_def Supp ).
assert (Out B C D) by (conclude_def Supp ).
assert (BetS a b f) by (conclude_def Supp ).
assert (Out b c d) by (conclude_def Supp ).
let Tf:=fresh in
assert (Tf:exists U V u v, (Out B A U /\ Out B C V /\ Out b a u /\ Out b c v /\ Cong B U b u /\ Cong B V b v /\ Cong U V u v /\ nCol A B C)) by (conclude_def CongA );destruct Tf as [U[V[u[v]]]];spliter.
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq B U) by (conclude lemma_raystrict).
assert (neq U B) by (conclude lemma_inequalitysymmetric).
assert (neq b u) by (conclude lemma_raystrict).
assert (neq u b) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists W, (BetS U B W /\ Cong B W U B)) by (conclude lemma_extension);destruct Tf as [W];spliter.
assert (neq a b) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists w, (BetS u b w /\ Cong b w U B)) by (conclude lemma_extension);destruct Tf as [w];spliter.
assert (Cong U B b w) by (conclude lemma_congruencesymmetric).
assert (Cong B W b w) by (conclude lemma_congruencetransitive).
assert (Cong U B u b) by (forward_using lemma_congruenceflip).
assert (Cong V W v w) by (conclude axiom_5_line).
assert ((BetS B U A \/ eq A U \/ BetS B A U)) by (conclude lemma_ray1).
assert (BetS A B W).
by cases on (BetS B U A \/ eq A U \/ BetS B A U).
{
 assert (BetS A U B) by (conclude axiom_betweennesssymmetry).
 assert (BetS A B W) by (conclude lemma_3_7a).
 close.
 }
{
 assert (BetS A B W) by (conclude cn_equalitysub).
 close.
 }
{
 assert (BetS U A B) by (conclude axiom_betweennesssymmetry).
 assert (BetS A B W) by (conclude lemma_3_6a).
 close.
 }
(** cases *)
assert (Out B F W) by (conclude_def Out ).
assert ((BetS B W F \/ eq F W \/ BetS B F W)) by (conclude lemma_ray1).
assert (BetS U B F).
by cases on (BetS B W F \/ eq F W \/ BetS B F W).
{
 assert (BetS U B F) by (conclude lemma_3_7b).
 close.
 }
{
 assert (BetS U B F) by (conclude cn_equalitysub).
 close.
 }
{
 assert (BetS U B F) by (conclude axiom_innertransitivity).
 close.
 }
(** cases *)
assert (neq B F) by (forward_using lemma_betweennotequal).
assert (Out B F W) by (conclude_def Out ).
assert ((BetS b u a \/ eq a u \/ BetS b a u)) by (conclude lemma_ray1).
assert (BetS a b w).
by cases on (BetS b u a \/ eq a u \/ BetS b a u).
{
 assert (BetS a u b) by (conclude axiom_betweennesssymmetry).
 assert (BetS a b w) by (conclude lemma_3_7a).
 close.
 }
{
 assert (BetS a b w) by (conclude cn_equalitysub).
 close.
 }
{
 assert (BetS u a b) by (conclude axiom_betweennesssymmetry).
 assert (BetS a b w) by (conclude lemma_3_6a).
 close.
 }
(** cases *)
assert (Out b f w) by (conclude_def Out ).
assert ((BetS b w f \/ eq f w \/ BetS b f w)) by (conclude lemma_ray1).
assert (BetS u b f).
by cases on (BetS b w f \/ eq f w \/ BetS b f w).
{
 assert (BetS u b f) by (conclude lemma_3_7b).
 close.
 }
{
 assert (BetS u b f) by (conclude cn_equalitysub).
 close.
 }
{
 assert (BetS u b f) by (conclude axiom_innertransitivity).
 close.
 }
(** cases *)
assert (neq b f) by (forward_using lemma_betweennotequal).
assert (Out b f w) by (conclude_def Out ).
assert (neq b f) by (forward_using lemma_betweennotequal).
assert (Out b f w) by (conclude_def Out ).
assert (Col U B W) by (conclude_def Col ).
assert (Col B A U) by (conclude lemma_rayimpliescollinear).
assert (~ Col D B F).
 {
 intro.
 assert (Col B C D) by (conclude lemma_rayimpliescollinear).
 assert (Col D B C) by (forward_using lemma_collinearorder).
 assert (neq B D) by (conclude lemma_raystrict).
 assert (neq D B) by (conclude lemma_inequalitysymmetric).
 assert (Col B F C) by (conclude lemma_collinear4).
 assert (Col A B F) by (conclude_def Col ).
 assert (Col F B A) by (forward_using lemma_collinearorder).
 assert (Col F B C) by (forward_using lemma_collinearorder).
 assert (neq B F) by (forward_using lemma_betweennotequal).
 assert (neq F B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A C) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out B D V) by (conclude lemma_ray3).
assert (Out b d v) by (conclude lemma_ray3).
assert (CongA D B F d b f) by (conclude_def CongA ).
close.
Qed.

End Euclid.



Require Export GeoCoq.Elements.OriginalProofs.lemma_extension.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_ray4 : 
   forall A B E, 
   (BetS A E B \/ eq E B \/ BetS A B E) -> neq A B ->
   Out A B E.
Proof.
intros.
assert (~ eq B A).
 {
 intro.
 assert (eq A B) by (conclude lemma_equalitysymmetric).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists J, (BetS B A J /\ Cong A J A B)) by (conclude lemma_extension);destruct Tf as [J];spliter.
assert (BetS J A B) by (conclude axiom_betweennesssymmetry).
assert (Out A B E).
by cases on (BetS A E B \/ eq E B \/ BetS A B E).
{
 assert (BetS J A E) by (conclude axiom_innertransitivity).
 assert (Out A B E) by (conclude_def Out ).
 close.
 }
{
 assert (BetS J A E) by (conclude cn_equalitysub).
 assert (Out A B E) by (conclude_def Out ).
 close.
 }
{
 assert (BetS J A E) by (conclude lemma_3_7b).
 assert (Out A B E) by (conclude_def Out ).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.



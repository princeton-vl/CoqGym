Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearright.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rightreverse.
Require Export GeoCoq.Elements.OriginalProofs.lemma_altitudebisectsbase.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_droppedperpendicularunique : 
   forall A J M P, 
   Per A M P -> Per A J P -> Col A M J ->
   eq M J.
Proof.
intros.
assert (~ neq M J).
 {
 intro.
 assert (neq J M) by (conclude lemma_inequalitysymmetric).
 let Tf:=fresh in
 assert (Tf:exists E, (BetS M J E /\ Cong J E M J)) by (conclude lemma_extension);destruct Tf as [E];spliter.
 assert (neq M E) by (forward_using lemma_betweennotequal).
 let Tf:=fresh in
 assert (Tf:exists F, (BetS J M F /\ Cong M F M E)) by (conclude lemma_extension);destruct Tf as [F];spliter.
 assert (BetS E J M) by (conclude axiom_betweennesssymmetry).
 assert (BetS E J F) by (conclude lemma_3_7b).
 assert (BetS F J E) by (conclude axiom_betweennesssymmetry).
 assert (BetS E M F) by (conclude lemma_3_7a).
 assert (neq J F) by (forward_using lemma_betweennotequal).
 assert (neq F J) by (conclude lemma_inequalitysymmetric).
 assert (Col J M F) by (conclude_def Col ).
 assert (Col M J F) by (forward_using lemma_collinearorder).
 assert (Col M J A) by (forward_using lemma_collinearorder).
 assert (neq J M) by (forward_using lemma_betweennotequal).
 assert (neq M J) by (conclude lemma_inequalitysymmetric).
 assert (Col J F A) by (conclude lemma_collinear4).
 assert (Col A J F) by (forward_using lemma_collinearorder).
 assert (Per F J P) by (conclude lemma_collinearright).
 assert (Col J M F) by (conclude_def Col ).
 assert (Col J M A) by (forward_using lemma_collinearorder).
 assert (Col M F A) by (conclude lemma_collinear4).
 assert (Col A M F) by (forward_using lemma_collinearorder).
 assert (neq M F) by (forward_using lemma_betweennotequal).
 assert (neq F M) by (conclude lemma_inequalitysymmetric).
 assert (Per F M P) by (conclude lemma_collinearright).
 assert (Cong F M M E) by (forward_using lemma_congruenceflip).
 assert (Per F M P) by (conclude lemma_collinearright).
 assert (BetS F M E) by (conclude axiom_betweennesssymmetry).
 assert (Cong F P E P) by (conclude lemma_rightreverse).
 assert (Midpoint F J E) by (conclude lemma_altitudebisectsbase).
 assert (BetS F M E) by (conclude axiom_betweennesssymmetry).
 assert (Cong F M M E) by (forward_using lemma_congruenceflip).
 assert (Midpoint F M E) by (conclude_def Midpoint ).
 assert (eq J M) by (conclude lemma_midpointunique).
 contradict.
 }
close.
Qed.

End Euclid.



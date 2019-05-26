Require Export GeoCoq.Elements.OriginalProofs.lemma_PGflip.
Require Export GeoCoq.Elements.OriginalProofs.proposition_34.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_43 : 
   forall A B C D E F G H K, 
   PG A B C D -> BetS A H D -> BetS A E B -> BetS D F C -> BetS B G C -> BetS A K C -> PG E A H K -> PG G K F C ->
   EF K G B E D F K H.
Proof.
intros.
assert (PG B A D C) by (conclude lemma_PGflip).
assert (Cong_3 A B C C D A) by (conclude proposition_34).
assert (ET A B C C D A) by (conclude axiom_congruentequal).
assert (Cong_3 A E K K H A) by (conclude proposition_34).
assert (ET A E K K H A) by (conclude axiom_congruentequal).
assert (Cong_3 K G C C F K) by (conclude proposition_34).
assert (ET K G C C F K) by (conclude axiom_congruentequal).
assert (ET K G C K C F) by (forward_using axiom_ETpermutation).
assert (ET K C F K G C) by (conclude axiom_ETsymmetric).
assert (ET K C F K C G) by (forward_using axiom_ETpermutation).
assert (ET K C G K C F) by (conclude axiom_ETsymmetric).
assert (ET A B C A C D) by (forward_using axiom_ETpermutation).
assert (ET A C D A B C) by (conclude axiom_ETsymmetric).
assert (ET A C D A C B) by (forward_using axiom_ETpermutation).
assert (ET A C B A C D) by (conclude axiom_ETsymmetric).
assert (EF A K G B A K F D) by (conclude axiom_cutoff1).
assert (BetS B E A) by (conclude axiom_betweennesssymmetry).
assert (BetS D H A) by (conclude axiom_betweennesssymmetry).
assert (ET A E K H A K) by (forward_using axiom_ETpermutation).
assert (ET H A K A E K) by (conclude axiom_ETsymmetric).
assert (ET H A K E A K) by (forward_using axiom_ETpermutation).
assert (ET E A K H A K) by (conclude axiom_ETsymmetric).
assert (EF A K G B F D A K) by (forward_using axiom_EFpermutation).
assert (EF F D A K A K G B) by (conclude axiom_EFsymmetric).
assert (EF F D A K G B A K) by (forward_using axiom_EFpermutation).
assert (EF G B A K F D A K) by (conclude axiom_EFsymmetric).
assert (EF G B E K F D H K) by (conclude axiom_cutoff2).
assert (EF G B E K D F K H) by (forward_using axiom_EFpermutation).
assert (EF D F K H G B E K) by (conclude axiom_EFsymmetric).
assert (EF D F K H K G B E) by (forward_using axiom_EFpermutation).
assert (EF K G B E D F K H) by (conclude axiom_EFsymmetric).
close.
Qed.

End Euclid.



Require Import Classical.
Require Export GeoCoq.Elements.OriginalProofs.euclidean_defs.
Require Export GeoCoq.Elements.OriginalProofs.general_tactics.

Ltac remove_double_neg :=
repeat
 match goal with
 H: ~ ~ ?X |- _ => apply NNPP in H
end.

Section basic_lemmas.

Context `{Ax:euclidean_neutral}.


Lemma Col_or_nCol : forall A B C,
  Col A B C \/ nCol A B C.
Proof.
unfold nCol, Col.
intros.
tauto.
Qed.

Lemma nCol_or_Col : forall A B C,
  nCol A B C \/ Col A B C.
Proof.
unfold nCol, Col.
intros.
tauto.
Qed.

Lemma eq_or_neq : forall A B,
 eq A B \/ neq A B.
Proof.
intros;unfold neq;tauto.
Qed.

Lemma neq_or_eq : forall A B,
 neq A B \/ eq A B.
Proof.
intros;unfold neq;tauto.
Qed.

Lemma Col_nCol_False : forall A B C, nCol A B C -> Col A B C -> False.
Proof.
unfold Col, nCol;intuition.
Qed.

Lemma nCol_notCol :
 forall A B C, ~ Col A B C -> nCol A B C.
Proof.
intros.
unfold nCol, Col, neq in *.
intuition.
Qed.

Lemma not_nCol_Col : forall A B C,
  ~ nCol A B C -> Col A B C.
Proof.
intros.
unfold nCol, Col, neq in *.
tauto.
Qed.

Lemma nCol_not_Col : forall A B C,
  nCol A B C -> ~ Col A B C.
Proof.
intros.
unfold nCol, Col, neq in *.
tauto.
Qed.

End basic_lemmas.

Hint Resolve not_nCol_Col 
 nCol_not_Col nCol_notCol Col_nCol_False.

Hint Resolve 
 Col_or_nCol nCol_or_Col eq_or_neq neq_or_eq : decidability.

Tactic Notation "by" "cases" "on" constr(t) :=
(let H := hyp_of_type t in decompose [or] H; clear H) ||
   let C := fresh in (assert (C:t) by (auto with decidability || unfold neq in *;tauto);
 decompose [or] C;clear C).

Ltac remove_not_nCol :=
repeat
match goal with
 H: ~ nCol ?A ?B ?C |- _ => apply not_nCol_Col in H
end.

Ltac forward_using thm :=
 remove_not_nCol;spliter;splits;
 match goal with
  H: ?X |- _ => apply thm in H;spliter;assumption
 end.

Ltac contradict := 
 (solve [eauto using Col_nCol_False]) || contradiction || (unfold nCol in *;intuition).

Ltac conclude t :=
 spliter;
 remove_double_neg;
 solve [unfold eq in *;mysubst;assumption |
        eauto using t |
        eapply t;eauto |
        eapply t;intuition |
        apply <- t;remove_exists;eauto  |
        unfold neq,eq in *;intuition |
        unfold neq,eq in *;remove_double_neg;congruence |
        apply t;tauto
].

Ltac close := solve [assumption |
                     auto |
                     repeat (split;auto) |
                     unfold neq, nCol in *;try assumption;tauto |
                     remove_exists;eauto 15 
                    ].

Ltac conclude_def_aux t := (remove_double_neg;
  (progress (unfold t);  
   solve [remove_exists;eauto 6 | 
          remove_exists;splits;eauto  |
          remove_exists;eauto 11 |
          one_of_disjunct |
          intuition
         ])) 
 || 
 solve [unfold t in *;spliter;assumption |
        unfold t in *;destruct_all;assumption |
        unfold t in *;remove_double_neg;destruct_all;remove_exists;eauto 11  ].

(** Trick to have unfold working also with definitions within typeclasses,
 thank you Pierre Courtieu *)

Tactic Notation "conclude_def" reference(x) := (conclude_def_aux x).



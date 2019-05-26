(** * Intuitionistic FOL *)

Require Import Kripke FOL.BPCP_FOL.

(** ** Reductions *)

Section kvalidity.

  Variable R : BSRS.
  Context {b : logic}.
    
  Set Printing Implicit.

  Theorem BPCP_kprv :
    BPCP R <-> nil ⊢I (F R).
  Proof.
    rewrite BPCP_BPCP'. split.
    - apply BPCP_prv'.
    - intros H % ksoundness'. rewrite <- BPCP_BPCP'. now apply (BPCP_valid R), kvalid_valid.
  Qed.

  Theorem BPCP_kvalid :
    BPCP R <-> kvalid (F R).
  Proof.
    split.
    - now intros H % BPCP_kprv % ksoundness'.
    - intros H % kvalid_valid. now apply (BPCP_valid R).
  Qed.

End kvalidity.

Theorem BPCP_ksatis R :
  ~ BPCP R <-> ksatis (¬ F R).
Proof.
  split.
  - intros H % (BPCP_satis R). now apply ksatis_satis.
  - intros (D & eta & M & u & rho & H) H' % (BPCP_kvalid R (b:=full)).
    now apply (H u), (H' D eta M u).
Qed.




(** ** Corollaries *)

Corollary kvalid_red :
  BPCP ⪯ @kvalid full.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_kvalid R).
Qed.

Corollary kvalid_undec :
  UA -> ~ decidable (@kvalid full).
Proof.
  intros H. now apply (not_decidable kvalid_red).
Qed.

Corollary kvalid_unenum :
  UA -> ~ enumerable (compl (@kvalid full)).
Proof.
  intros H. now apply (not_coenumerable kvalid_red).
Qed.

Corollary kprv_red :
  BPCP ⪯ @prv intu full nil.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_kprv R).
Qed.

Corollary kprv_undec :
  UA -> ~ decidable (@prv intu full nil).
Proof.
  intros H. now apply (not_decidable kprv_red).
Qed.

Corollary kprv_unenum :
  UA -> ~ enumerable (compl (@prv intu full nil)).
Proof.
  intros H. apply (not_coenumerable kprv_red); trivial.
Qed.

Corollary ksatis_red :
  compl BPCP ⪯ @ksatis full.
Proof.
  exists (fun R => ¬ F R). intros R. apply (BPCP_ksatis R).
Qed.

Corollary ksatis_undec :
  UA -> ~ decidable (@ksatis full).
Proof.
  intros H1 H2 % (dec_red ksatis_red).
  now apply H1, dec_count_enum.
Qed.

Corollary ksatis_enum :
  UA -> ~ enumerable (@ksatis full).
Proof.
  intros H1 H2 % (enumerable_red ksatis_red); auto.
Qed.




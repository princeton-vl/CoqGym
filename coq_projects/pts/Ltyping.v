
Section Typage.

  Load "Metatheory".
  Load "Infer".

End Typage.

Hint Resolve wf_nil type_ax type_var: pts.
Hint Resolve wft_top: pts.


  Ltac Inversion_typ T :=
    let INVTYP := fresh "INVTYP" in
    (generalize T; intro INVTYP; inversion INVTYP using inversion_lemma;
      unfold inv_typ in |- *; clear INVTYP; intros).

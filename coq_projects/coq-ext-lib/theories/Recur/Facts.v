Require Import Coq.Classes.RelationClasses.

Lemma wf_anti_sym T (R : T -> T -> Prop) (wf : well_founded R)
: Irreflexive R.
Proof.
  refine (fun a =>
            (@Fix _ _ wf
                  (fun x => x = a -> R x a ->False)
                  (fun x rec pf pfr =>
                     rec _ match eq_sym pf in _ = t return R x t with
                             | eq_refl => pfr
                           end pf pfr)) a eq_refl).
Qed.
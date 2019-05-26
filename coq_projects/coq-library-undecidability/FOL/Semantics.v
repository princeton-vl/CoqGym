(** * Tarski Semantics *)

Require Export Undecidability.FOL.FOL.

(** ** Variables and Substitutions *)

Fixpoint vars_t (t : term) : list var :=
  match t with
  | V v => [v]
  | P p => []
  | t_f b t => vars_t t
  | t_e => []
  end.

Fixpoint consts_t (t : term) : list var :=
  match t with
  | V v => []
  | P p => [p]
  | t_f b t => consts_t t
  | t_e => []
  end.

Fixpoint subst_t x y (t : term) : term :=
  match t with
  | V v => if Dec (v = x) then y else V v
  | P p => P p
  | t_e => t_e
  | t_f b t => t_f b (subst_t x y t)
  end.

Fixpoint consts {b} (phi : form b) : list var :=
  match phi with
  | Pr t1 t2  => consts_t t1 ++ consts_t t2
  | Fal
  | Q => []
  | Impl phi psi => consts phi ++ consts psi
  | All v phi => v :: consts phi
  end.

Fixpoint subst {b} x t phi :=
  match phi with
  | Pr t1 t2 => Pr (subst_t x t t1) (subst_t x t t2)
  | Q => Q
  | Fal => Fal
  | Impl phi1 phi2 => Impl (subst x t phi1) (subst x t phi2)
  | All v phi => All v (if Dec (x = v) then phi else subst x t phi)
  end.

Definition consts_l {b} A := flat_map (@consts b) A.
Definition fresh (y : var) A := ~ y el A.


Fixpoint mkfresh (l : list nat) :=
  match l with
  | [] => 0
  | x :: l => S x + mkfresh l
  end.

Lemma mkfresh_spec l a : a el l -> a < mkfresh l.
Proof.
  induction l.
  - firstorder.
  - cbn; intros [ | ]; firstorder omega.
Qed.

Lemma make_fresh A : {z | fresh z A}.
Proof.
  exists (mkfresh A). intros ? % mkfresh_spec. omega.
Defined.

Lemma app_sub X (A A' B B' : list X) :
  A <<= A' -> B <<= B' -> A ++ B <<= A' ++ B'.
Proof.
  intros H1 H2 x [H|H] % in_app_iff.
  all: apply in_app_iff; auto.
Qed.


(** ** Interpretations *)

Class interp (domain : Type) (rho : nat -> domain) :=
  {
    i_f : bool -> domain -> domain ;
    i_e : domain ;
    i_P : domain -> domain -> Prop ;
    i_Q : Prop
  }.

Section Semantics.

  Notation const := nat.
  Variable domain : Type.  

  Definition env := var -> domain.

  Variable (eta : env).
  Context {I : interp eta}.
  
  Fixpoint eval (rho : env) (t : term) : domain :=
    match t with
    | V s => rho s
    | P p => eta p
    | t_f b t => i_f b (eval rho t)
    | t_e => i_e
    end.
  
  Definition update {X} (rho : var -> X) (v : var) (d : X) :=
    (fun v' => if (Dec (v = v')) then d else rho v').
  
  Notation "rho [[ v := d ]]" := (update rho v d) (at level 20).
  
  Fixpoint sat {b} (rho : env) (phi : form b) : Prop :=
    match phi with
    | Pr t1 t2 =>  i_P (eval rho t1) (eval rho t2)
    | Q => i_Q
    | Fal => False
    | Impl phi psi => sat rho phi -> sat rho psi
    | All v phi => forall d : domain, sat (rho [[ v := d ]]) phi
    end.
  Notation "rho ⊫ A" := (forall psi, psi el A -> sat rho psi) (at level 20).
  Notation "rho ⊨ phi" := (sat rho phi) (at level 20).

  Context {b : logic}.
  
  Lemma impl_sat A rho phi :
    sat rho (A ==> phi) <-> ((forall psi, psi el A -> sat rho psi) -> sat rho phi).
  Proof.
    induction A; cbn; firstorder congruence.
  Qed.

  Lemma impl_sat' A rho phi :
    sat rho (A ==> phi) -> ((forall psi, psi el A -> sat rho psi) -> sat rho phi).
  Proof.
    eapply impl_sat.
  Qed. 
  
End Semantics.

Ltac decs :=
  unfold update; repeat destruct _;
  subst; cbn; try congruence; try reflexivity; auto.

Notation "rho [[ v := d ]]" := (update rho v d) (at level 20).

Arguments sat {_ _} _ {_} _ _, {_} _ _ {_} _ _.
Arguments interp {_} _, _ _.



Notation "p ⊫ A" := (forall psi, psi el A -> sat _ p psi) (at level 20).
Notation "p ⊨ phi" := (sat _ p phi) (at level 20).

Implicit Type b : logic.

Definition valid b phi := forall D eta (I : interp D eta) rho, rho ⊨ phi.
Definition valid_L b A := forall D eta (I : interp D eta) rho, rho ⊫ A.
Definition satis b phi := exists D eta (I : interp D eta) rho, rho ⊨ phi.
Definition fullsatis b A := exists D eta (I : interp D eta) rho, rho ⊫ A.



(** Trivial Model *)

Section TM.

  Instance TM : interp unit (fun _ => tt) :=
    {| i_f := fun _ _ => tt; i_e := tt; i_P := fun _ _ => True; i_Q := True |}.

  Fact TM_sat (rho : var -> unit) (phi : form frag) :
    sat TM rho phi.
  Proof.
    revert rho. induction phi using form_frag_ind; cbn; auto.
  Qed.

End TM.

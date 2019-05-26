 Transparent sumor_rec.
Transparent sumbool_rec.
Transparent sig_rec.



  Theorem is_a_sort : forall t : term, decide (exists s : sort, t = Srt s).
simple destruct t; intros.
left; exists s; auto with pts.

right; red in |- *; simple induction 1; intros.
discriminate H0.

right; red in |- *; simple induction 1; intros.
discriminate H0.

right; red in |- *; simple induction 1; intros.
discriminate H0.

right; red in |- *; simple induction 1; intros.
discriminate H0.
Qed.



  Definition typed_sort (axiom : sort -> sort -> Prop) 
    (s : sort) : Prop := exists s2 : _, axiom s s2.

  Definition typ_ppal (e : env) (m t : term) : Prop :=
    ppal (typ e m) (le_type e) t.

  Definition red_to_sort_dec (e : env) (t : term) : Set :=
    ppal_dec (fun s => le_type e t (Srt s)) le_sort.

  Definition red_to_wf_prod_dec (e : env) (t : term) : Set :=
    {p : term * term |
    let (C, D) := p in
    wf_type e (Prod C D) /\
    le_type e t (Prod C D) /\
    (forall A B : term,
     le_type e t (Prod A B) -> le_type e (Prod C D) (Prod A B))} +
    {(forall C D : term, ~ le_type e t (Prod C D))}.


  (* Algorithms and properties implying the decidability of typing *)
  Record PTS_algos : Set := 
    {pa_lift : forall (n : nat) (t : term), {u : term | u = lift n t};
     pa_subst : forall u v : term, {t : term | t = subst u v};
     pa_infer_axiom : forall s : sort, ppal_dec (axiom s) le_sort;
     pa_least_sort :
      forall (e : env) (t : term), wf_type e t -> red_to_sort_dec e t;
     pa_infer_rule :
      forall x1 x2 : sort, {x3 : sort | ppal (rule_sat x1 x2) le_sort x3};
     pa_least_prod :
      forall (e : env) (t : term), wf_type e t -> red_to_wf_prod_dec e t;
     pa_le_type_prod :
      forall (e : env) (T A B : term),
      le_type (Ax T :: e) A B -> le_type e (Prod T A) (Prod T B);
     pa_inv_prod : product_inversion le_type;
     pa_topsort_untyped :
      forall (e : env) (s s' : sort) (t : term),
      le_type e (Srt s) t -> typ e t (Srt s') -> typed_sort axiom s;
     pa_le_type_dec :
      forall (e : env) (u v : term),
      wf_type e u -> wf_type e v -> decide (le_type e u v)}.


  Variable the_algos : PTS_algos.


Load "Errors".


  Definition infer_ppal_type (e : env) (m : term) : Set :=
    ({t : term | ppal (typ e m) (le_type e) t} +
     {err : type_error | expln e err &  inf_error m err})%type.


  Inductive wft_dec (e : env) (t : term) : Set :=
    | Wft_ok : wf_type e t -> wft_dec e t
    | Wft_fail :
        forall err : type_error,
        expln e err ->
        decl_error (Ax t) err ->
        ~ (exists s : sort, t = Srt s) -> wft_dec e t.

  Inductive check_dec (e : env) (m t : term) : Set :=
    | Chk_ok : typ e m t -> check_dec e m t
    | Chk_fail :
        forall err : type_error,
        expln e err -> chk_error m t err -> check_dec e m t.


  Inductive decl_dec (e : env) (d : decl) : Set :=
    | Dcl_ok : wf (d :: e) -> decl_dec e d
    | Dcl_fail :
        forall err : type_error,
        expln e err -> decl_error d err -> decl_dec e d.



  (* The type-checking module to build *)

  Record PTS_TC : Set := 
    {
      (* Infer command *)
      ptc_inf_ppal_type :
      forall (e : env) (t : term), wf e -> infer_ppal_type e t;
     
      (* Check command *)
      ptc_chk_typ : forall (e : env) (t T : term), wf e -> check_dec e t T;
     
      (* Axiom command *)
      ptc_add_typ : forall (e : env) (t : term), wf e -> decl_dec e (Ax t);
     
      (* Definition command *)
      ptc_add_def :
      forall (e : env) (t T : term), wf e -> decl_dec e (Def t T);
     
      
      (* Auxiliary functions. Would be useful to write tactics
             over the kernel. *)
      ptc_chk_wk :
      forall (e : env) (t T : term), wf e -> wf_type e T -> check_dec e t T;
     ptc_chk_wft : forall (e : env) (t : term), wf e -> wft_dec e t}.





  Lemma not_topsort :
   forall t : term,
   {s : sort | t = Srt s &  ~ typed_sort axiom s} +
   {(forall s : sort, t = Srt s -> typed_sort axiom s)}.
(*
Realizer [t:term]
  Cases t of
    (Srt s) => Cases (pa_infer_axiom the_algos s) of
                 (inleft _) => (inright sort)
               | _          => (inleft ? s)
               end
  | _        => (inright sort)
  end.
*)
simple destruct t; intros; try (right; intros s' eqs'; discriminate eqs').
case (pa_infer_axiom the_algos s); intros.
right; intros.
injection H; intros; subst s1.
inversion_clear s0.
exists x; case H0; trivial.

left; exists s; trivial.
red in |- *; intros.
inversion_clear H.
elim n with x; trivial.
Qed.




Section Fixpoint_Body.

  (* Useful for the mutual recursion  type inference <-> type checking *)

  Hypothesis
    fix_inference : forall (t : term) (e : env), wf e -> infer_ppal_type e t.


  Theorem fix_chk_wk :
   forall (e : env) (t T : term), wf e -> wf_type e T -> check_dec e t T.
(*Realizer [e:env][t,T:term]Cases (fix_inference t e) of
     (inl T')  => if (pa_le_type_dec the_algos e T' T) then Chk_ok 
                  else (Chk_fail (Expected_type t T' T))
   | (inr err) => (Chk_fail err) 
   end.
*)
intros.
case (fix_inference t e); trivial;
 [ intros (T', ppty_t) | intros (err, expl, is_err) ].
case (pa_le_type_dec the_algos e T' T); trivial.
apply type_correctness with (1 := pp_ok ppty_t).

intros le_ty.
apply Chk_ok.
apply typ_conv_wf with T'; trivial.
apply (pp_ok ppty_t).

intros not_le.
apply Chk_fail with (Expected_type t T' T); auto with pts.
constructor; auto with pts.
red in |- *; intros; apply not_le.
apply (pp_least ppty_t) with (1 := H1).

apply Chk_fail with err; auto with pts.
Defined.

  Theorem fix_add_typ :
   forall (e : env) (t : term), wf e -> decl_dec e (Ax t).
(*
Realizer [e:env][t:term]
  Cases (fix_inference t e) of
    (inl T)  => Cases (pa_least_sort the_algos e T) of
                  (inleft s) => Dcl_ok
                | _          => (Dcl_fail (Not_a_type t T))
                end
  | (inr err) => (Dcl_fail err) 
  end.
*)
intros.
case (fix_inference t e); trivial;
 [ intros (T, ppty_t) | intros (err, expl, is_err) ].
case (pa_least_sort the_algos e T); intros.
apply type_correctness with (1 := pp_ok ppty_t).

apply Dcl_ok.
inversion_clear s.
apply wf_var with x.
apply typ_conv_wf with T; auto with pts.
apply (pp_ok ppty_t).

apply (pp_least ppty_t).
apply type_conv_srt with (1 := pp_ok ppty_t).
apply (pp_ok H0).

apply Dcl_fail with (Not_a_type t T); auto with pts.
constructor; trivial.
apply (pp_ok ppty_t).

red in |- *; intros.
elim n with s.
apply (pp_least ppty_t) with (1 := H0).

apply Dcl_fail with err; auto with pts.
Defined.



Section Infer_Ref.


  Theorem infer_ref :
   forall (e : env) (n : nat), wf e -> infer_ppal_type e (Ref n).
(*Realizer [e:env][n:nat]
  Cases (list_item decl e n) of
    (inleft d) => (inl ? type_error (pa_lift the_algos (S n) (typ_of_decl d)))
  | _          => (inr term ? (Db_error n))
  end.
*)
intros.
case (list_item e n).
intros (d, itd).
left.
elim (pa_lift the_algos (S n) (typ_of_decl d)); intros.
exists x; subst x.
split; intros.
constructor; trivial.
split with d; trivial.

Inversion_typ H0.
elim fun_item with (1 := H1) (2 := itd); trivial.

right.
exists (Db_error n); auto with pts.
constructor; trivial.
generalize n n0.
elim e; simpl in |- *; trivial with arith.
simple destruct n1; intros.
elim n2 with a; trivial.

cut (length l <= n2); auto with arith.
apply H0; red in |- *; intros.
elim n3 with t; auto.
Qed.

End Infer_Ref.


Section Infer_Application.

  Let le_type_prod_l := inv_prod_l _ (pa_inv_prod the_algos).
  Let le_type_prod_r := inv_prod_r _ (pa_inv_prod the_algos).


  Definition app_chk_err (u tu : term) (e : type_error) :=
    match e with
    | Expected_type v tv _ => Apply_err u tu v tv
    | e => e
    end.

(*
  Lemma app_chk_expln: (e:env)(u,a,b:term)(err:type_error)
      	(typ_ppal e u (Prod a b))->(expln e err)
      ->(expln e (app_chk_err u (Prod a b) err)).
Intros.
(Inversion_clear H0; Simpl; Try Constructor; Trivial).
Apply (pp_ok H).

Intros.
Apply (pp_least H) with 1:=H0.

Simpl.
*)

  Theorem infer_app :
   forall (e : env) (u v : term), wf e -> infer_ppal_type e (App u v).
(*Realizer [e:env][u,v:term]
  Cases (fix_inference u e) of
    (inl y)  => Cases (pa_least_prod the_algos e y) of
                  (inleft (dom,rng)) =>
                     Cases (fix_chk_wk e v dom) of
                       Chk_ok => (inl ? type_error (pa_subst the_algos v rng))
                     | (Chk_fail err) =>
                         (inr term ? (app_chk_err u (Prod dom rng) err))
                     end
                | _  => (inr term ? (Not_a_fun u y))
                end
  | (inr err) => (inr term ? err)
  end.*)
intros.
case (fix_inference u e); trivial;
 [ intros (y, ppty_u) | intros (err, expl, is_err) ].
case (pa_least_prod the_algos e y).
apply type_correctness with (1 := pp_ok ppty_u).

intros ((dom, rng), (wfprd, (leprd, lstprd))).
case (fix_chk_wk e v dom); intros; trivial.
apply wf_type_prod_l with (1 := wfprd).

left.
case (pa_subst the_algos v rng); intros x eqx.
exists x; subst x.
split; intros.
apply type_app with dom; auto with pts.
apply typ_conv_wf with y; auto with pts.
apply (pp_ok ppty_u).

Inversion_typ H0.
apply le_type_trans with (subst v Ur); auto with pts.
apply le_type_subst0 with V.
apply le_type_prod_r with dom; auto with pts.
apply lstprd.
apply (pp_least ppty_u) with (1 := H2).

right.
exists (app_chk_err u (Prod dom rng) err).
generalize e0.
inversion_clear c; simpl in |- *; trivial.
elim H0; simpl in |- *; intros; auto.

pattern dom at 0, err in |- *.
elim H0; simpl in |- *; intros; auto.

intros.
inversion_clear e1.
constructor; intros; auto.
apply typ_conv_wf with y; trivial.
apply (pp_ok ppty_u).

apply lstprd.
apply (pp_least ppty_u) with (1 := H3); trivial.

generalize e0.
inversion_clear c; simpl in |- *; intros.
generalize H0.
case err; simpl in |- *; intros;
 try (apply Infe_subt with v; auto with pts; fail).
elim inf_no_exp with (1 := H1).

inversion_clear wfprd.
Inversion_typ H2.
elim inf_error_no_type with (1 := H0) (2 := e0) (3 := H4).

apply False_ind.
inversion_clear wfprd.
Inversion_typ H1.
inversion_clear e1.
elim H7 with s1; trivial.

constructor.

right.
exists (Not_a_fun u y); auto with pts.
constructor.
apply (pp_ok ppty_u).

red in |- *; intros.
elim n with (1 := pp_least ppty_u H0).

right.
exists err; auto with pts.
apply Infe_subt with u; trivial with pts.
Defined.


End Infer_Application.



  Theorem infer_sort :
   forall (e : env) (s : sort), wf e -> infer_ppal_type e (Srt s).
unfold infer_ppal_type in |- *.
intros.
elim (pa_infer_axiom the_algos) with s; intros.
left.
inversion_clear a.
split with (Srt x).
split; intros.
constructor; auto with pts.
apply (pp_ok H0).

generalize (pp_least H0); intros.
red in H2.
Inversion_typ H1.
apply le_type_trans with (2 := H4); auto with pts.

right.
split with (Topsort s).
constructor; trivial.
red in |- *; intros.
Inversion_typ H0.
elim b with s2; trivial.

constructor.
Defined.


  Theorem infer_abs :
   forall (e : env) (A M : term), wf e -> infer_ppal_type e (Abs A M).
(*Realizer [e:env; A,M:term]
  Cases (fix_add_typ e A) of
    Dcl_ok =>
      Cases (fix_inference M (cons ? (Ax A) e)) of
        (inl TM) =>
          Cases (not_topsort TM) of
            (inleft s) => (inr term ? (Lambda_topsort (Abs A M) s))
          | _ => (inl ? type_error (Prod A TM))
          end
       | (inr err) => (inr term ? (Under A err))
       end
  | (Dcl_fail err) => (inr term ? err)
  end.
*)
intros.
case (fix_add_typ e A); trivial; intros.
case (fix_inference M (Ax A :: e)); trivial;
 [ intros (TM, ppty_M) | intros (err, expl, is_err) ].
case (not_topsort TM); [ intros (s, is_s, tops) | intros ].
right.
exists (Lambda_topsort (Abs A M) s); auto with pts.
constructor.
rewrite <- is_s; trivial.

red in |- *; intros.
apply tops.
Inversion_typ H0.
split with s2; trivial.

left.
exists (Prod A TM).
split; intros.
elimtype (exists s' : sort, typ (Ax A :: e) TM (Srt s')); intros.
inversion_clear w.
elim (pa_infer_rule the_algos) with s x; intros.
apply type_abs with x0; auto with pts.
apply type_prod_sat with s x; auto with pts.
apply (pp_ok p).

apply (pp_ok ppty_M).

generalize t.
elim type_correctness with (1 := pp_ok ppty_M); intros.
split with s; trivial with pts.

elim t0 with s; trivial with pts; intros.
split with x.
constructor; auto with pts.

Inversion_typ H0.
apply le_type_trans with (2 := H3).
apply (pa_le_type_prod the_algos); auto with pts.
apply (pp_least ppty_M) with (1 := H1).

right.
split with (Under A err).
constructor; trivial.

apply Infe_under with M; trivial with pts.

right.
exists err; auto with pts.
inversion_clear d.
apply Infe_subt with A; trivial with pts.

constructor.
Defined.


  Theorem infer_prod :
   forall (e : env) (A B : term), wf e -> infer_ppal_type e (Prod A B).
intros.
elim fix_inference with A e; intros.
inversion_clear a.
elim (pa_least_sort the_algos) with e x; intros.
inversion_clear a.
cut (wf (Ax A :: e)); intros.
elim fix_inference with B (Ax A :: e); intros.
inversion_clear a.
elim (pa_least_sort the_algos) with (Ax A :: e) x1; intros.
inversion_clear a.
left.
elim (pa_infer_rule the_algos) with x0 x2; intros.
split with (Srt x3); split; intros.
apply type_prod_sat with x0 x2; auto with pts.
apply typ_conv_wf with x; auto with pts.
apply (pp_ok H0).

apply (pp_ok H1).

apply typ_conv_wf with x1; auto with pts.
apply (pp_ok H3).

apply (pp_ok H4).

apply (pp_ok p).

Inversion_typ H5.
apply le_type_trans with (2 := H9).
unfold le_sort in p.
apply (pp_least p).
split with s1.
apply (pp_least H1).
apply (pp_least H0); trivial with pts.

split with s2; trivial with pts.
apply (pp_least H4).
apply (pp_least H3); trivial with pts.

right.
split with (Under A (Not_a_type B x1)).
constructor.
constructor.
apply (pp_ok H3).

red in |- *; intros.
elim b with s.
apply (pp_least H3) with (1 := H4).

constructor.

apply type_correctness with (1 := pp_ok H3).

right.
inversion_clear b.
split with (Under A x1).
constructor; trivial.

apply Infe_under with B; trivial with pts.

trivial.

apply wf_var with x0.
apply type_conv_srt with x; auto.
apply (pp_ok H0).

apply (pp_ok H1).

right.
split with (Not_a_type A x).
constructor.
apply (pp_ok H0).

red in |- *; intros.
elim b with s.
apply (pp_least H0).
trivial.

constructor.

apply type_correctness with (1 := pp_ok H0).

right.
inversion_clear b.
split with x.
trivial.

apply Infe_subt with A; trivial with pts.

trivial.
Defined.


End Fixpoint_Body.



Section Infer_Full_PTS.

  Fixpoint full_ppal_type (t : term) :
   forall e : env, wf e -> infer_ppal_type e t :=
    fun e H =>
    match t return (infer_ppal_type e t) with
    | Srt s => infer_sort e s H
    | Ref n => infer_ref e n H
    | Abs A M => infer_abs full_ppal_type e A M H
    | App u v => infer_app full_ppal_type e u v H
    | Prod A B => infer_prod full_ppal_type e A B H
    end.


  Lemma tmp_add_typ : forall (e : env) (t : term), wf e -> decl_dec e (Ax t).
  Proof fix_add_typ full_ppal_type.

  Lemma tmp_check_typ_when_wf :
   forall (e : env) (t T : term), wf e -> wf_type e T -> check_dec e t T.
  Proof fix_chk_wk full_ppal_type.

  Let add_cst : forall (e : env) (t T : term), wf e -> decl_dec e (Def t T).
(*
Realizer [e:env; t,T:term]
  Cases (tmp_add_typ e T) of
    Dcl_ok => (tmp_check_typ_when_wf e t T)
  | (Dcl_fail err) => (Chk_fail err)
  end.
*)
intros.
elim (tmp_add_typ e T); trivial; intros.
elim (tmp_check_typ_when_wf e t T); trivial; intros.
left.
inversion_clear w.
apply wf_cst with s; trivial with pts.

right with err; auto with pts.

inversion_clear w.
left with s; trivial with pts.

right with err; auto with pts.
Qed.



  Lemma tmp_check_wf_type : forall (e : env) (t : term), wf e -> wft_dec e t.
(*
Realizer [e:env; t:term]
  if (is_a_sort t) then Wft_ok
  else Cases (tmp_add_typ e t) of
         Dcl_ok => Wft_ok
       | (Dcl_fail err) => (Wft_fail err)
       end.
*)
intros.
elim (is_a_sort t); intros.
left.
inversion_clear a; subst t; auto with pts.

case (tmp_add_typ e t); trivial; intros.
left.
inversion_clear w; auto with pts.
apply wft_typed with s; auto with pts.

right with err; auto with pts.
Qed.


  Let check_type : forall (e : env) (t T : term), wf e -> check_dec e t T.
(*
Realizer [e:env; t,T:term]
  Cases (tmp_check_wf_type e T) of
    Wft_ok => (tmp_check_typ_when_wf e t T)
  | (Wft_fail err) => (Chk_fail err)
  end.
*)
intros.
case (tmp_check_wf_type e T); trivial; intros.
apply tmp_check_typ_when_wf; trivial.

right with err; auto with pts.
inversion_clear d.
apply Chke_type; trivial.

apply Chke_type2; trivial.
Qed.




  Definition full_type_checker : PTS_TC :=
    Build_PTS_TC (fun e t => full_ppal_type t e) check_type tmp_add_typ
      add_cst tmp_check_typ_when_wf tmp_check_wf_type.


  (* Decidability of judgements *)
  Theorem decide_wf : forall e : env, decide (wf e).
simple induction e; intros; auto with pts.
elim H; intros.
elim a; intros.
elim tmp_add_typ with l t; intros; auto.
right.
apply decl_err_not_wf with err; trivial.

elim add_cst with l t t0; intros; auto.
right.
apply decl_err_not_wf with err; trivial.

right; red in |- *; intros.
apply b.
apply inv_wf with a; trivial.
Qed.


  Theorem decide_typ : forall (e : env) (t T : term), decide (typ e t T).
intros.
elim decide_wf with e; intros.
elim check_type with e t T; intros; auto.
right.
apply chk_error_no_type with err; trivial.

right; red in |- *; intros.
apply b.
apply typ_wf with (1 := H).
Qed.

End Infer_Full_PTS.

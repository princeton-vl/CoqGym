(** ** TM to SR with finite types *)

Require Import singleTM .

(* ** More preliminary lemmas *)

Lemma inductive_count (S:eqType) (Y:eqType) A (s:S) n (f: S -> Y):
Injective f -> count A s = n -> count (map (fun a:S => f a) A) (f s) = n.
Proof.
intros inj. revert n. induction A; intros n HC.
- destruct n; try discriminate HC. reflexivity.
- simpl in *. decide (s=a). rewrite e in *. destruct n.  discriminate HC. inversion HC.
  decide (f a = f a); try contradiction. rewrite (IHA n H0). now rewrite H0.
  decide (f s = f a). apply inj in e. contradiction. now apply IHA.
Qed.

Lemma diff_constructors_count_zero (F X Y:eqType) (A: list F) (f: F -> X) (g: Y -> X) x:
(forall a b, f a <> g b) -> count (map (fun (a:F) => f a) A) (g x) = 0.
Proof.
intros dis. induction A. auto. cbn. decide (g x = f a).
exfalso. apply (dis a x). symmetry. assumption. assumption.
Qed.

Lemma notInZero (X: eqType) (x: X) A :
  not (x el A) <-> count A x = 0.
Proof.
  split; induction A.
  -  reflexivity.
  - intros H. cbn in *. dec.
    + exfalso. apply H. left. congruence.
    + apply IHA. intros F. apply H. now right.
  - tauto.
  - cbn. dec.
    + subst a. omega.
    + intros H [E | E].
      * now symmetry in E.
      * tauto.
Qed.


Lemma in_sing {X} (x y:X) :
    x el [y] -> x = y.
Proof.
    cbn. intros [[]|[]]. reflexivity.
Qed.

Lemma in_concat_iff A l (a:A) : a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
  induction l; cbn.
  - intuition. now destruct H.
  - rewrite in_app_iff, IHl. firstorder subst. auto.
Qed.

(* Definition of String rewriting with finite types *)


(*  String Rewriting **)
Section string_rewriting.

  Variable sig: Type.
  Definition rule : Type := list sig * list sig. 
  Definition srs := list rule.

  Implicit Types (a b c: sig) (x y z u v: list sig)
                 (r: list sig* list sig) (R S: srs).

  Inductive rew' : srs -> list sig -> list sig -> Prop:=
  |rewR R x u y v : (u,v) el R -> rew' R (x++u++y) (x++v++y).
  Hint Constructors rew'. 

  Inductive rewt' (S: srs) (x: list sig) : list sig -> Prop :=
  |rewt'Refl : rewt' S x x
  |rewt'Rule y z : rew' S x y -> rewt' S y z -> rewt' S x z.
  Hint Constructors rewt'.

  Instance rewt'Trans R :
    PreOrder (rewt' R).
  Proof.
    split.
    - econstructor.
    - intros ? ? ? ? ?.
      induction H. auto. now apply rewt'Rule with (y:= y), IHrewt'. 
  Qed.

  Lemma subset_rewriting S R x y:
    S <<= R -> rewt' S x y -> rewt' R x y.
  Proof.
    intros Sub H. induction H. auto. apply rewt'Rule with (y:=y).
    inv H. apply rewR with (x:=x0) (u:=u) (v:=v). now apply Sub. exact IHrewt'.  
  Qed.

  Lemma rewrite_app R x y z:
    rewt' R x y -> rewt' R (z++x) (z++y). 
  Proof.
    induction 1. auto. inv H. revert IHrewt'. apply rewt'Rule.
    rewrite app_assoc. setoid_rewrite app_assoc at 2. now apply rewR.
  Qed.

  Lemma rewrite_right R x y z :
    rewt' R x y -> rew' R y z -> rewt' R x z.
  Proof.
    intros. induction H; eauto.
  Qed.

  Lemma rewt'_ind_left :
    forall (S : srs) x (P : list sig -> Prop),
      (P x) ->
      (forall y z : list sig, rewt' S x y -> rew' S y z -> P y -> P z) -> forall l : list sig, rewt' S x l -> P l.
  Proof.
    intros. induction H1; eauto 10 using rewt'.
  Qed.  
    
End string_rewriting.
  
Definition SR_fin (S: sigT (fun (sig:finType) => (prod (prod (srs sig) (list sig)) (list sig)))) :=
   match (projT2 S) with
    |(rules,x,y) => rewt' rules x y
   end.

Section Fix_TM.
  Variable sig : finType.
  Variable T : (sTM sig).
  Definition conf :Type := mconfig sig (states T).                                        
 
  Instance eq_dec_states : eq_dec (states T). 
  Proof. exact _. Defined.

  Inductive rsig' : Type := hash | dollar | sigma (s: sig).

  Instance eq_dec_rsig' : eq_dec rsig'.
  Proof.
    intros. hnf. decide equality. apply eq_dec_sig.
  Defined.

  Instance finType_rsig': finTypeC (EqType rsig').
  Proof.
    exists (hash::dollar::(List.map (fun s => sigma s) (elem sig))).
    intros x. destruct x; cbn. induction (elem sig); auto. induction (elem sig); auto.  
    apply inductive_count. intros x y; now inversion 1. apply (@enum_ok sig (class sig) s). 
  Defined.

  
  Inductive rsig : Type := state (q: states T) | symb (s: (FinType (EqType rsig'))).
  Definition sym : sig -> rsig := fun s => symb (sigma s). 
  Notation "#" := (symb hash).
  Notation "$" := (symb dollar).

  Global Instance eq_dec_rsig : eq_dec rsig.
  Proof.
    intros. hnf. decide equality. apply eq_dec_states.
    apply eq_dec_rsig'.
  Defined.

  Lemma state_count_one q:
    count (map (fun s : states T => state s) (elem (states T))) (state q) = 1.
  Proof.
    apply inductive_count. intros x y; now inversion 1.
    apply (@enum_ok (states T) (class (states T)) q).
  Qed.

  Lemma symb_count_one s:
    count (map (fun s0 : FinType (EqType rsig') => symb s0)
               (elem (FinType (EqType rsig')))) (symb s) = 1.
  Proof.
    apply inductive_count. intros x y; now inversion 1.
    apply (@enum_ok (FinType (EqType rsig')) (class (FinType (EqType rsig'))) s).
  Qed.

    
  Global Instance finType_rsig: finTypeC (EqType rsig).
  Proof.
    exists ((map (fun s => state s) (elem (states T)))
         ++ (map (fun s => symb s) (elem (FinType (EqType rsig'))))). intros x. destruct x.
    - rewrite <- countSplit. rewrite state_count_one.
      now rewrite (@diff_constructors_count_zero (FinType (EqType rsig'))
                  (EqType rsig) (states T) (elem (FinType (EqType (rsig')))) symb state).
    - rewrite <- countSplit. rewrite symb_count_one. 
      now rewrite (@diff_constructors_count_zero (states T)).
  Defined.

  Definition rsig_finType : finType := (@FinType (EqType rsig) finType_rsig).


  Definition halting_states : list (states T) :=
    List.filter (fun s => halt s) (elem (states T)).

  Definition not_halting_states : list (states T) :=
    List.filter (fun s => negb (halt s)) (elem (states T)).

  Lemma not_halting (q: states T) :
    halt q = false <-> q el not_halting_states.
  Proof.
    split. unfold not_halting_states. rewrite filter_In.
    intros H. split. auto. now rewrite H. unfold not_halting_states.
    rewrite filter_In. intros [H1 H2]. now destruct (halt q).  
  Qed.

  Lemma halting (q: states T) :
    halt q = true <-> q el halting_states.
  Proof.
    split. unfold halting_states. rewrite filter_In.
    intros H. split. auto. now rewrite H. unfold halting_states.
    rewrite filter_In. intros []. auto. 
  Qed.
  

  (*  ** Encoding of Configurations **)
  Definition mk_srconf (c: conf): list rsig :=
    match (ctape c) with
    | niltape _ => [state (cstate c);#;$]
    | leftof s r => [state(cstate c); #]++ (List.map sym (s::r))++[$]
    | rightof s l => [#]++(List.map sym (List.rev (s::l)))++[state(cstate c);$]
    | midtape l s r => [#]++(List.map sym (List.rev l))++ [(state(cstate c))]
                                ++ (List.map sym (s::r))++[$]
    end.
         
  Lemma sym_inj : Injective sym. 
  Proof.
    intros x y. now inversion 1.
  Qed.

  Lemma state_not_sym A B q e l:
    A++[state q] = B ++sym e::(List.map sym l) -> False.
  Proof.
    revert B e. induction l; intros B e H; cbn in *.
    - apply last_app_eq in H as [H HE]. inv HE.
    - apply (IHl (B++[sym e]) a). now rewrite <- app_assoc.
  Qed.
  
  Lemma midtape_state A B q1 q2 l r:
    A ++ (state q1)::B = List.map sym l++(state q2)::(List.map sym r)
            -> A = List.map sym l /\ B = (List.map sym r) /\ q1 = q2.
  Proof.
    revert r A B. induction l; intros r A B H; cbn in *. 
    - destruct A. rewrite app_nil_l in H. inv H. now split. inv H. exfalso.
      assert ((state q1) el (A++(state q1)::B) -> False). intros H. rewrite H2 in H.
      apply in_map_iff in H as [x [? ?]]. inv H. apply H. auto. 
    - destruct A. rewrite app_nil_l in H. inv H. inv H. destruct (IHl r A B H2).
      subst. now split. 
  Qed.

  Lemma mk_srconf_inj (c1 c2: conf) :
    mk_srconf c1 = mk_srconf c2 <-> c1 = c2.
  Proof.
    split.
    - unfold mk_srconf. destruct (ctape c1) eqn: H,(ctape c2) eqn: H'; try inversion 1;
                         subst; destruct c1,c2; cbn in *; subst; try reflexivity. 
      + apply app_inv_tail in H4. apply map_inj in H4. now subst. apply sym_inj. 
      + change [state cstate;$] with ([state cstate]++[$]) in H2.
        change [state cstate0;$] with ([state cstate0]++[$]) in H2. 
        rewrite !app_assoc in H2. apply app_inv_tail in H2.
        apply last_app_eq in H2 as [H3 H2]. repeat rewrite map_app in H3.
        apply last_app_eq in H3 as [H3 HE]. inv H2. inv HE. rewrite map_inj in H3.
        rewrite rev_eq in H3. now subst. apply sym_inj. 
      + change [state cstate; $] with ([state cstate]++[$]) in H2.
        rewrite !app_assoc, !app_comm_cons in H2. rewrite app_assoc in H2.
        apply last_app_eq in H2 as [H2 _]. exfalso.
        change (state cstate0::sym e0::List.map sym l1)
                   with ([state cstate0]++sym e0::List.map sym l1) in H2.
        rewrite app_assoc in H2.  apply (state_not_sym H2).
      + change [state cstate0; $] with ([state cstate0]++[$]) in H2.
        rewrite !app_assoc, !app_comm_cons in H2. rewrite app_assoc in H2.
        apply last_app_eq in H2 as [H2 _]. symmetry in H2.
        change (state cstate::sym e::List.map sym l0)
                          with ([state cstate]++sym e::List.map sym l0) in H2.
        rewrite app_assoc in H2. exfalso. apply (state_not_sym H2).
      + rewrite !app_comm_cons in H2. rewrite! app_assoc in H2. apply last_app_eq in H2 as [H2 _].
        assert (List.map sym (List.rev l) ++ state cstate :: List.map sym (e::l0) =
                List.map sym (List.rev l1) ++ state cstate0 :: List.map sym (e0::l2)) as H3 by auto. 
        apply midtape_state in H3 as [H3 [H4 H5]]. inv H4. apply map_inj in H6.
        subst. apply map_inj in H3. rewrite rev_eq in H3. now subst. apply sym_inj. apply sym_inj. 
    - now intros <-.
  Qed.
  

  

  (* ** Definition of Rewrite Rules Simulating a Transition **)
  
   Definition get_rules_left (q1 q2: states T) (old new: option sig) : list (list rsig * list rsig):=
    match old,new with
    |None,None => List.map (fun c => ([sym c; state q1; $], [state q2; sym c; $])) (elem sig)
    |None,Some b => List.map (fun c => ([sym c; state q1; $], [state q2; sym c; sym b; $])) (elem sig)
    |Some a,None => List.map (fun c => ([sym c; state q1; sym a], [state q2; sym c; sym a])) (elem sig)
    |Some a,Some b => List.map (fun c => ([sym c; state q1; sym a], [state q2; sym c; sym b])) (elem sig)
    end.
     
   Definition get_rules_right (q1 q2: states T) : list (list rsig * list rsig) :=
     List.map (fun a => ([state q1; #; sym a],[#; state q2; sym a])) (elem sig).
   

   Definition get_rules (q1 q2: states T) (old new: option sig) (m: move) :
     list (list rsig * list rsig) :=
    match old,new,m with
    |None,None,L => [([state q1; #],[state q2; #])] ++ (get_rules_left q1 q2 None None)
    |None,None,N => [([state q1; #],[state q2; #]);([state q1; $],[state q2; $])]
    |None,None,R => [([state q1; #;$],[state q2; #;$]); ([state q1; $],[state q2; $])]
                     ++ (get_rules_right q1 q2)
    |None,Some b,L => [([state q1; #],[state q2; #; sym b])] ++ (get_rules_left q1 q2 None (Some b))
    |None,Some b,N => [([state q1; #],[#; state q2; sym b]); ([state q1; $],[state q2; sym b; $])]
    |None,Some b,R => [([state q1; #],[#; sym b; state q2]); ([state q1; $],[sym b; state q2; $])]
    |Some a,None,L => [([#;state q1; sym a],[state q2; #; sym a])]
                       ++ (get_rules_left q1 q2 (Some a) None)
    |Some a,None,N => [([state q1; sym a],[state q2; sym a])]
    |Some a,None,R => [([state q1; sym a],[sym a; state q2])]
    |Some a,Some b,L => [([#; state q1; sym a],[state q2; #; sym b])]
                         ++ (get_rules_left q1 q2 (Some a) (Some b))
    |Some a,Some b,N => [([state q1; sym a],[state q2; sym b])]
    |Some a,Some b,R => [([state q1; sym a],[sym b; state q2])]
    end.


 
   Definition TMrules : list (list rsig * list rsig) :=
     List.concat ((List.map (fun q1 => match trans (q1,None) with
                      |(q2,(o,m)) => get_rules q1 q2 None o m
                                   end) not_halting_states) ++
                 (List.map (fun (P: states T * sig) => let (q1,s) := P in match trans (q1,Some s) with
                                                    |(q2,(o,m)) => get_rules q1 q2 (Some s) o m
                                                    end)
                           (list_prod not_halting_states (elem sig)))).
   

   (* ** Correctness Proof **)
   
   Lemma get_rules_el_TMrules (q1 q2: states T) (old new: option sig) (m: move) :
     halt q1 = false -> (trans (q1,old) = (q2,(new,m)))
     -> get_rules q1 q2 old new m <<= TMrules.
   Proof.
     intros HF HT. intros s HS. apply in_concat_iff. exists (get_rules q1 q2 old new m).
     split. assumption. apply in_app_iff. destruct old.
     - right. apply in_map_iff. exists (q1,e). rewrite HT. split. reflexivity.
       apply in_prod_iff. split. now apply not_halting. auto. 
     - left. apply in_map_iff. exists q1. rewrite HT. split. auto. now apply not_halting.
   Qed.

   Lemma rewrite_step_conf (c1: conf) :
    (halt (cstate c1) = false) -> rew' TMrules (mk_srconf c1) (mk_srconf (step c1)).
   Proof.
     intros H. unfold mk_srconf. destruct (ctape c1) eqn: CT; unfold step; rewrite CT; cbn.
     - destruct (trans (cstate c1, None)) as (q2,(new,mov)) eqn: TC;
         assert (Sub: get_rules (cstate c1) q2 None new mov <<= TMrules)
         by (now apply get_rules_el_TMrules). destruct new as [new| ]; destruct mov; cbn.
       + apply rewR with (x:=[]) (u:= [state (cstate c1);#]) (v:=[state q2;#;sym new]).
         firstorder. 
       + apply rewR with (x:=[]) (u:= [state (cstate c1);#]) (v:= [#;sym new; state q2]).
         firstorder. 
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #]) (v:=[#; state q2; sym new]).
         firstorder. 
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #]) (v:=[state q2; #]).
         firstorder. 
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #; $])(v:=[state q2; #; $]).
         firstorder. 
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #]) (v:=[state q2; #]).
         firstorder.
     - destruct (trans (cstate c1, None)) as (q2,(new,mov)) eqn: TC;
         assert (Sub: get_rules (cstate c1) q2 None new mov <<= TMrules)
         by (now apply get_rules_el_TMrules). destruct new as [new| ]; destruct mov; cbn.
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #]) (v:=[state q2; #; sym new]).
         firstorder. 
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #]) (v:=[#; sym new; state q2]).
         firstorder.
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #]) (v:=[#; state q2; sym new]).
         firstorder. 
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #])(v:=[state q2; #]).
         firstorder. 
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #; sym e]) (v:=[#; state q2; sym e]).
         apply Sub. cbn. right. right. unfold get_rules_right. apply in_map_iff. exists e. now split.
       + apply rewR with (x:=[]) (u:= [state (cstate c1); #]) (v:=[state q2; #]).
         firstorder.
     - destruct (trans (cstate c1, None)) as (q2,(new,mov)) eqn: TC;
         assert (Sub: get_rules (cstate c1) q2 None new mov <<= TMrules)
         by (now apply get_rules_el_TMrules). destruct new as [new| ]; destruct mov; cbn.
       + rewrite map_app. rewrite <- app_assoc.
         apply rewR with (x:=#::List.map sym (List.rev l)) (u:= [sym e; state (cstate c1); $])
                       (v:=[state q2; sym e; sym new;$]). 
         apply Sub. cbn. right. apply in_map_iff. exists e. now split.
       + rewrite !map_app. setoid_rewrite <- app_assoc at 2. 
         apply rewR with (x:=#::List.map sym (List.rev l) ++[sym e]) (u:= [state (cstate c1); $])
                       (v:=[sym new; state q2;$]). firstorder. 
       + apply rewR with (x:=#::List.map sym (List.rev l++[e])) (u:= [state (cstate c1); $])
                       (v:=[state q2; sym new; $]). firstorder. 
       + rewrite map_app. rewrite <- app_assoc.
         apply rewR with (x:=#::List.map sym (List.rev l)) (u:= [sym e; state (cstate c1); $])
                       (v:=[state q2; sym e;$]).
         apply Sub. cbn. right. apply in_map_iff. exists e. now split.
       + apply rewR with (x:=#::List.map sym (List.rev l++[e])) (u:= [state (cstate c1); $])
                       (v:=[state q2; $]). firstorder. 
       + apply rewR with (x:=#::List.map sym (List.rev l++[e])) (u:= [state (cstate c1); $])
                       (v:=[state q2; $]). firstorder. 
     - destruct (trans (cstate c1, Some e)) as (q2,(new,mov)) eqn: TC;
         assert (Sub: get_rules (cstate c1) q2 (Some e) new mov <<= TMrules)
         by (now apply get_rules_el_TMrules). destruct new as [new| ]; destruct mov; cbn.
       + destruct l; cbn. 
         * apply rewR with (x:=[]) (u:= [#; state (cstate c1) ; sym e]) (v:=[state q2; #; sym new]).
           firstorder. 
         * rewrite map_app. rewrite <- app_assoc.
           apply rewR with (x:=#::List.map sym (List.rev l))
                           (u:= [sym e0; state (cstate c1) ; sym e])
                           (v:=[state q2; sym e0; sym new]).
           apply Sub. cbn. right. apply in_map_iff. exists e0. now split.
       + destruct l0; cbn. 
         * rewrite map_app. rewrite <- app_assoc.
           apply rewR with (x:= # :: List.map sym (List.rev l))
                           (u:= [state (cstate c1) ; sym e]) (y:=[$])
                           (v:=[sym new; state q2]). firstorder. 
         * rewrite map_app. rewrite <- app_assoc.
           apply rewR with (x:=#::List.map sym (List.rev l))
                           (u:= [state (cstate c1) ; sym e])
                           (v:=[sym new; state q2]). firstorder. 
       + apply rewR with (x:=# :: List.map sym (List.rev l)) (u:= [state (cstate c1); sym e])
                         (v:=[state q2; sym new]). firstorder.
       + destruct l; cbn. 
         * apply rewR with (x:=[])
                           (u:= [#;state (cstate c1) ; sym e])
                           (v:=[state q2; #; sym e]). firstorder. 
         * rewrite map_app. rewrite <- app_assoc.
           apply rewR with (x:=#::List.map sym (List.rev l))
                           (u:= [sym e0; state (cstate c1) ; sym e])
                           (v:=[state q2; sym e0; sym e]).
           apply Sub. cbn. right. apply in_map_iff. exists e0. now split.
       + destruct l0; cbn. 
         * rewrite map_app. rewrite <- app_assoc.
            apply rewR with (x:=# :: List.map sym (List.rev l))
                            (u:= [state (cstate c1) ; sym e])
                            (v:=[sym e; state q2]). firstorder. 
         * rewrite map_app. rewrite <- app_assoc.
           apply rewR with (x:=#::List.map sym (List.rev l))
                           (u:= [state (cstate c1) ; sym e])
                           (v:=[sym e; state q2]). firstorder. 
       + apply rewR with (x:=# :: List.map sym (List.rev l))
                         (u:= [state (cstate c1); sym e])
                       (v:=[state q2; sym e]). firstorder. 
  Qed.   
  

  Lemma state_eqlist A B C D q1 q2:
    A ++(state q1)::B = C++(state q2)::D
    -> (exists (E F: list rsig'), C = List.map symb E /\ D = List.map symb F)
    -> A = C /\ B = D /\ q1 = q2.
  Proof.
    revert C. induction A; intros C H HA; destruct C; try rewrite !app_nil_l in H.
    - inv H. now split.
    - inv H. destruct HA as [E [F [H1 H2]]]. destruct E; inv H1.
    - rewrite <- app_comm_cons in H. inv H. destruct HA as [E [F [H1 H2]]].
      exfalso. assert ((state q1) el (A++(state q1)::B) -> False). intros H.
      rewrite H2 in H. apply in_map_iff in H as [x [? ?]]. inv H. apply H. auto.
    - inv H. specialize (IHA C H2). destruct HA as [E [F [H3 H4]]]. destruct E,F.
      inv H3. inv H3. cbn in H3. inv H3. destruct IHA as [<- [<- <-]]. exists E, []. now split.
      now split. cbn in H3. inv H3. destruct IHA as [<- [<- <-]]. exists E, (r1::F). now split.
      now split.
  Qed.

  Fact map_symb_sigma A :
    List.map symb (List.map sigma A) = List.map sym A.
  Proof.
    induction A. auto. cbn. now rewrite <- IHA.
  Qed.

  (* Automation for rewrite_step_halt Lemma. ListInv mainly eliminates contradictory
     assumptions while state_inv also solves cases *)

  Ltac listInv :=
    cbn in *;
    match goal with
    | [H: sym _ = sym _ |- _ ] => inv H
    | [H: [] = _ ::_  |- _ ] => inv H
    | [H: _::_ = _::_ |- _ ] => inv H 
    | [H: []++ _ = _ |- _ ] => rewrite app_nil_l in H
    | [H: _ ++[] = _ |- _ ] => rewrite app_nil_r in H
    | [H: _ = []++ _ |- _ ] => rewrite app_nil_l in H
    | [H: _ = _ ++[] |- _ ] => rewrite app_nil_r in H
    | [H: [] = List.map sym ?L |- _ ] => destruct L eqn: ?
    | [H: List.rev ?L = [] |- _] => apply rev_nil in H        
    | [H: _ ++ _::_ = [] |- _ ] => symmetry in H; now apply app_cons_not_nil in H               
    | [H: [] = List.map _ (List.rev (_) ++ ?e) |- _ ] =>
      apply map_app in H; now apply app_cons_not_nil in H
    | [H: _ ++ [#] = List.map sym (List.rev _ ++ ?e) |- _ ] =>
      rewrite map_app in H; let E:= fresh "E" in apply last_app_eq in H as [_ E]; inv E      
    | [H: ?x ++ [_] = #::(List.map sym ?L) |- _ ] => destruct x eqn: ?
    | [H: _ ++ [#] = List.map sym (List.rev ?L) |- _ ] => destruct L eqn: ?
    | [H: _ ++ [sym _] = List.map sym (List.rev ?L) |- _ ] => destruct L eqn:?
    | [H: _ ++ [sym _] = List.map sym (_ ++ [_]) |- _ ] =>
      rewrite map_app in H; apply last_app_eq in H as [? ?]
    | [H: ?A ++ _::_ = _::_ |- _ ] => destruct A eqn: ?                    
    end; subst.
  Ltac rep_listInv := repeat listInv.


  Ltac confeq :=
    unfold step; unfold mk_srconf;
    match goal with
      | [ |- (_::_ = _::_) /\ _ ] => split
      | [ |- (_::_ = _::_)] => reflexivity                            
      | [H: ctape _ = _ |- (_ = _) /\ _ ] => rewrite H
      | [H: trans(_,_) = _ |- _ ] => rewrite H          
      | [H: _ |- mk_mconfig _ _ = mk_mconfig _  _ /\ _ ] => split
      | [ |- mk_mconfig _ _ = mk_mconfig _ _ ] => reflexivity
      | [H: (?q,_) el list_prod not_halting_states _ |- halt ?q = false ] =>
        apply in_prod_iff in H as [? _]; now apply not_halting
      | [H: _ el not_halting_states |- halt _ = false] => now apply not_halting
        end; subst; cbn in *; try now rewrite !map_app, <- !app_assoc. 
  Ltac rep_confeq := repeat confeq.


  Ltac state_inv :=
    unfold get_rules_right in *;
    match goal with
    |[H: ?x ++ ?z::(state ?q)::?y = ?a::(?A++(state _ )::_) |- _] =>
     cbn in H; change (x++z::state q::y) with (x++[z]++(state q)::y) in H; rewrite app_assoc in H;
     rewrite app_comm_cons in H; eapply state_eqlist in H as [? [? ?]]
    |[H: ?x ++ state _ :: ?y = state _ ::_ |- _ = _ /\ _ ] =>
     apply state_eqlist with (A:= x) (B:= y) (C:= []) in H as [? [? ?]]
    |[H: ?x ++ ?z::state ?q :: ?y = state _ ::_ |- _ = _ /\ _ ] =>
     change (x++z::state q::y) with (x++[z]++state q::y) in H; rewrite app_assoc in H;
     apply state_eqlist with (A:=x++[z]) (B:= y) (C:= []) in H as [? [? ?]]
    |[H: ?x ++(state _ )::?y = ?a::(?A ++ (state _ )::_) |- _ ] =>
     cbn in H; rewrite app_comm_cons in H; eapply state_eqlist in H as [? [? ?]]
    |[H: (_,_) el List.map _ _ |- (_ = _) /\ _] => apply in_map_iff in H as [? [? ?]]
    |[H: (_,_) = (_,_) |- _ ] => inv H
    |[H: _ |- exists E F, [] = _ /\ [#;$] = _ ] => exists [],[hash; dollar]; now split
    |[H: _ |- exists E F, [] = _ /\ #::sym ?e::List.map sym ?L++[$] = _ ] =>
     exists [],(hash::sigma e::List.map sigma L++[dollar]); split; auto; cbn;
     rewrite map_app, map_symb_sigma; now cbn
    |[H: _ |- exists E F, #::(List.map sym ?A) = _ /\ [$] = _ ] =>
     exists (hash::(List.map sigma A)), [dollar]; split; auto; cbn;
     rewrite !map_app, map_symb_sigma; now cbn
    |[H: _ |- exists E F, #::(List.map sym ?A) = _ /\ sym ?e::(List.map sym ?L)++[$] = _ ] =>
     exists (hash::(List.map sigma A)), (sigma e::(List.map sigma L)++[dollar]);
     split; cbn; try rewrite map_app; now rewrite map_symb_sigma
    end.
  
  Ltac solve_inv := repeat (state_inv || confeq || listInv).

  Lemma rewrite_step_halt (c1: conf) y:
    rew' TMrules (mk_srconf c1) y -> (y = (mk_srconf (step c1)) /\ (halt (cstate c1) = false)).
  Proof.
    intros H. remember (mk_srconf c1) as a. inv H.
    apply in_concat_iff in H0 as [L [EL HL]]. unfold mk_srconf in H2. 
    destruct (ctape c1) eqn: CT1; cbn in *; apply in_app_iff in HL as [HL|HL];
      try apply in_map_iff in HL as [z [HZ ZF]]; try (destruct z as (q1, old));
        try (destruct (trans(z,None)) as (qz,(o,m)) eqn: TZ +
            destruct (trans (q1, Some old)) as (q2, (o, m)) eqn: TZ);
        destruct o as [new| ]; destruct m; cbn in HZ; subst; destruct EL;
          try apply in_sing in H; try inv H; solve_inv; destruct l0; cbn; rep_confeq.
  Qed.
  
  Lemma rewrite_steps_halt (c1: conf) y:
    rewt' TMrules (mk_srconf c1) y -> exists c2, y = (mk_srconf c2).
  Proof.
    intros H. induction H using rewt'_ind_left. 
    - eauto.
    - destruct IHrewt' as [? ->]. eapply rewrite_step_halt in H0 as [-> ?]. eauto.
  Qed.

  Theorem reach_rewrite (c1 c2:conf):
    reach c1 c2 <-> rewt' TMrules (mk_srconf c1) (mk_srconf c2).
  Proof.
    split.
    - induction 1. constructor. apply rewt'Rule with (y:=(mk_srconf (step c))).
      + now apply rewrite_step_conf.
      + assumption.
    - remember (mk_srconf c1) as y. remember (mk_srconf c2) as b.
       intros H. revert Heqy. revert c1. induction H; intros c1 Heqy; subst. 
       + apply mk_srconf_inj in Heqy. subst. constructor.
       + apply rewrite_step_halt in H as [H1 H]. subst.
         apply reachS. apply IHrewt'; auto. assumption.
  Qed.

  Definition reduction_reach_rewrite (p: conf * conf) :=
      let (c1,c2) := p in (TMrules, mk_srconf c1, mk_srconf c2). 

End Fix_TM.

Require Import PCP.Definitions.

Theorem reduction_reach_sr : Reach ⪯ SR_fin.
Proof. exists (fun S
                      => existT (fun (sig:finType) => (prod (prod (srs sig) (list sig)) (list sig)))
                               (rsig_finType (projT1 (projT2 S)))
                               (reduction_reach_rewrite (projT2 (projT2 S)))).
       intros [sig [M [c1 c2]]]. unfold Reach, SR.  cbn. apply reach_rewrite.
Qed.

(** ** SR with finite types to SR *)

Definition trans_R (Sigma : finType) (R : srs Sigma) :=
  map (fun '(x,y) => (map (@index Sigma) x, map (@index Sigma) y)) R.

Lemma red_rew     (Sigma : finType) (R : srs Sigma) (x0 y : list Sigma) :
    rew' R x0 y <-> rew (trans_R R) (map (index (X:=Sigma)) x0) (map (index (X:=Sigma)) y).
Proof.
  split.
  - intros []. cbn. autorewrite with list. econstructor.
    eapply in_map_iff. exists (u/v). eauto.
  - inversion 1. unfold trans_R in H. 
    symmetry in H0. eapply map_app_inv in H0 as (x0' & x0'' & -> & <- & (y' & y'' & -> & <- & <-) % map_app_inv ).
    unfold trans_R in H2. eapply in_map_iff in H2 as ([] & ? & ?). inv H0.
    rewrite <- !map_app in H1. enough (l = y' /\ x0' ++ l0 ++ y'' =  y) as [-> <-].
    now econstructor.
    + split; eapply map_inj; eauto using inj_index.
Qed.    


Lemma rew_inv    (Sigma : finType) (R : srs Sigma) (x0 : list Sigma) y' :
    rew (trans_R R) (map (index (X:=Sigma)) x0) y' -> exists y, y' = (map (index (X:=Sigma)) y).
Proof.
  inversion 1; subst. unfold trans_R in H1. eapply in_map_iff in H1 as ([] & ? & ?). inv H1.
  symmetry in H0. eapply map_app_inv in H0 as (x0' & x0'' & ? & ? & (y' & y'' & ? & ? & ?) % map_app_inv ); subst.
  rewrite map_inj in H4; eauto using inj_index. subst.
  eexists. rewrite <- !map_app. reflexivity.
Qed.

Lemma nrewt_ind_left :
  forall (R : SRS) s (P : string -> Prop),
    (P s) ->
    (forall y z : string, rewt R s y -> rew R y z -> P y -> P z) -> forall s0 : string, rewt R s s0 -> P s0.
Proof.
  intros. induction H1; eauto 10 using rewt.
Qed.

Lemma rewt_inv    (Sigma : finType) (R : srs Sigma) (x0 : list Sigma) y' :
    rewt (trans_R R) (map (index (X:=Sigma)) x0) y' -> exists y, y' = (map (index (X:=Sigma)) y) /\ rewt' R x0 y.
Proof.
  intros. induction H using nrewt_ind_left.
  - eauto using rewt'. 
  - destruct IHrewt as (? & -> & ?). pose proof H0. eapply rew_inv in H0 as [? ->].
    exists x1. eapply red_rew in H2. split; try reflexivity. eapply rewrite_right; eauto.
Qed.

Lemma red_rewt    (Sigma : finType) (R : srs Sigma) (x0 y : list Sigma) :
    rewt' R x0 y <-> rewt (trans_R R) (map (index (X:=Sigma)) x0) (map (index (X:=Sigma)) y).
Proof.
  split.
  - induction 1. reflexivity.
    eapply red_rew in H. eauto using rewt.
  - intros. eapply rewt_inv in H as (? & ? & ?). enough (x = y). subst. eassumption.
    eapply map_inj; eauto using inj_index.
Qed.

Lemma reduction : SR_fin ⪯ SR.
Proof.
  exists (fun '(existT _ sig (Rs,x,y)) => (trans_R Rs, map (@index sig) x, map (@index sig) y)).
  intros [Sigma ((R, x0),  y)]. cbn. eapply red_rewt.
Qed.

(** ** TM to SRH' *)

Definition SRH' '(Rs, x, A) := exists y, rewt Rs x y /\ exists a, a el A /\ a el y.

Lemma mk_srconf_state:
  forall (sig : finType) (M : sTM sig) (x : conf M) (x0 : states M), state x0 el mk_srconf x -> x0 = cstate x.
Proof.
  intros sig M x x0 H2. unfold mk_srconf in *. destruct _; cbn in *; rewrite ?in_app_iff in *.
  - intuition; congruence.
  - intuition; try congruence. inv H. eapply in_map_iff in H0 as (? & ? & ?). inv H. inv H0. inv H. inv H.
  - intuition; try congruence. eapply in_map_iff in H0 as (? & ? & ?). inv H. inv H0. inv H. reflexivity. inv H. inv H0. inv H0.
  - intuition; try congruence. eapply in_map_iff in H0 as (? & ? & ?). inv H. cbn in *. intuition. now inv H. inv H0.
    eapply in_app_iff in H0. intuition. eapply in_map_iff in H as (? & ? & ?). inv H. inv H. inv H0. inv H0.
Qed.

Lemma halt_SRH' : Halt ⪯ SRH'.
Proof.
  exists (fun '(existT2 _ _ sig M t) => (trans_R (@TMrules sig M), map (@index (FinType (EqType (rsig M)))) (@mk_srconf sig M (@initc sig M t)), map (@index (FinType (EqType (rsig M)))) (map (@state sig M) (@halting_states sig M)))).
  intros [sig M]. cbn. unfold Halt, Halt. cbn. split; intros []; intuition.
  - eapply reach_rewrite in H1.
    eapply red_rewt in H1. eexists. split. eassumption. exists (index (state (cstate x))).
    rewrite !in_map_iff. intuition; eexists.
    + rewrite in_map_iff. intuition. eexists; intuition.  eapply halting. eauto.
    + intuition.  unfold mk_srconf. destruct _; cbn; eauto.
  - destruct H1. intuition. destruct (rewt_inv H0) as [? [-> ?]].
    pose proof H.
    eapply rewrite_steps_halt in H as [? ->].
    eapply in_map_iff in H1 as (? & <- & ?). eapply in_map_iff in H2 as (? & ? & ?).
    eapply inj_index in H1 as ->. eapply in_map_iff in H as (? & <- & ?).
    eapply halting in H. eapply mk_srconf_state in H2. subst.
    exists x. cbn. intuition. 
    eapply reach_rewrite. eassumption.
Qed.

(** ** SRH' to SRH *)

Lemma rewt_R_fresh (R : SRS) (x : string) (A l : list symbol) :
  rewt (R ++ map (fun a : symbol => [a] / [fresh (sym R ++ x)]) A) x l -> ~ fresh (sym R ++ x) el l -> rewt R x l.
Proof.
  induction 1 using nrewt_ind_left; intros.
  - reflexivity.
  - inv H0. eapply in_app_iff in H2 as [|].
    + eapply rewt_left. eapply IHrewt.
      * intros [ | [|] % in_app_iff ] %in_app_iff; eapply H1; eauto.
        eapply sym_word_l in H2; eauto. edestruct fresh_spec with (l := sym R ++ x); eauto.
      * eauto using rew.
    + eapply in_map_iff in H0 as (? & ? & ?). inv H0. destruct H1; eauto.
Qed.

Lemma SRH'_SRH : SRH' ⪯ SRH.
Proof.
  exists (fun '(P, x, A) => (P ++ map (fun a => [a] / [fresh (sym P ++ x)]) A, x, fresh (sym P ++ x))).
  intros [ [R x] A]. cbn. firstorder.
  - eapply in_split in H1 as (? & ? & ->). exists (x2 ++ [fresh (sym R ++ x)] ++ x3). split.
    + transitivity (x2 ++ [x1] ++ x3). eapply rewt_subset. eassumption. eauto.
      eauto 9 using rew, rewt.
    + eauto.
  -  revert H0. induction H using nrewt_ind_left; intros.
    + edestruct fresh_spec with (l := sym R ++ x); eauto.
    + edestruct (@in_dec nat (ltac:(intros; decide equality)) (fresh (sym R ++ x)) y).
      firstorder. inv H0. eapply in_app_iff in H2 as [|].
      * destruct n. rewrite !in_app_iff in H1. intuition; eauto.
        eapply sym_word_R in H1; eauto. edestruct fresh_spec with (l := sym R ++ x); eauto.
      * eapply in_map_iff in H0 as (? & ? & ?); inv H0. exists (x0 ++ [x1] ++ y0).
        split; firstorder. eapply rewt_R_fresh; eauto.
Qed.

Lemma Halt_SRH : Halt ⪯ SRH.
Proof.
  eapply reduces_transitive. eapply halt_SRH'. eapply SRH'_SRH.
Qed.


Require Export Undecidability.Shared.Prelim.

(** * TM to SRH *)

(* ** More preliminaries, with definition of finite types *)

Definition dec (X: Prop) : Type := {X} + {~ X}.
Coercion dec2bool P (d: dec P) := if d then true else false.
Existing Class dec.
Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.

Hint Extern 4 =>  (* Improves type class inference *)
match goal with
  | [  |- dec ((fun _ => _) _) ] => cbn
end : typeclass_instances.

Tactic Notation "decide" constr(p) :=
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) :=
  destruct (Dec p) as i.
Tactic Notation "decide" "_" :=
  destruct (Dec _).

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

Structure eqType := EqType {
  eqType_X :> Type;
  eqType_dec : eq_dec eqType_X }.

Arguments EqType X {_} : rename.
Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.
Existing Instance eqType_dec.

Instance list_eq_dec X :
  eq_dec X -> eq_dec (list X).
Proof.
  unfold dec. decide equality.
Defined.

(** The definitions of finite types are adopted from the Bachelor Thesis of Jan Menz. (https://www.ps.uni-saarland.de/~menz/bachelor.php) *)

Fixpoint count (X: Type) `{eq_dec X}  (A: list  X) (x:  X) {struct A} : nat :=
  match A with
  | nil => O
  | cons y A' =>  if Dec (x=y) then S(count A' x) else count A' x end.

Class finTypeC  (type:eqType) : Type := FinTypeC {
                                            enum: list type;
                                            enum_ok: forall x: type, count enum x = 1
                                          }.

Structure finType : Type := FinType {
                                type:> eqType;
                                class: finTypeC type }.

Arguments FinType type {class}.
Existing Instance class | 0.

Canonical Structure finType_CS (X : Type) {p : eq_dec X} {class : finTypeC (EqType X)} : finType := FinType (EqType X).

Definition elem (F: finType) := @enum (type F) (class F).
Hint Unfold elem.
Hint Unfold class.

Ltac dec := repeat (destruct Dec).

Lemma countIn (X:eqType) (x:X) A:
  count A x > 0 -> x el A.
Proof.
  induction A.
  - cbn. omega.
  - cbn. dec.
    + intros. left. symmetry. exact e.
    + intros. right. apply IHA. exact H.
Qed.

Lemma elem_spec (X: finType) (x:X) : x el (elem X).
Proof.
  apply countIn.  pose proof (enum_ok x) as H. unfold elem. omega.
Qed.

Hint Resolve elem_spec.
Hint Resolve enum_ok.

Lemma countSplit (X: eqType) (A B: list X) (x: X)  : count A x + count B x = count (A ++ B) x.
Proof.
  induction A.
  - reflexivity.
  - cbn. decide (x=a).
    +cbn. f_equal; exact IHA.
    + exact IHA.
Qed.

Fixpoint pos (X : eqType) (x : X) (A : list X) :=
  match A with
  | [] => None
  | a :: A => if Dec (x = a) then Some 0 else match pos x A with Some n => Some (S n) | None => None end
  end.

Definition pos_el' (X : eqType) (x : X) (A : list X) (H : x el A) : {n | pos x A = Some n}.
Proof.
  induction A.
  - inv H.
  - decide (x = a).
    + subst. exists 0. cbn. decide (a = a); congruence.
    + destruct IHA; try firstorder congruence.
      exists (S x0). cbn. decide (x = a); rewrite ?e; congruence.
Defined.

Lemma pos_length (X : eqType) (x : X) A n :
  pos x A = Some n -> n < |A|.
Proof.
  revert n; induction A; cbn; intros.
  - inv H.
  - decide (x = a).
    + inv H. omega.
    + destruct (pos x A) eqn:E; inv H. specialize (IHA n1 eq_refl). omega.
Qed.

Lemma pos_nth (X : eqType) (x : X) A n :
  pos x A = Some n -> nth_error A n = Some x.
Proof.
  revert n; induction A; cbn; intros.
  - inv H.
  - decide (x = a).
    + now inv H.
    + destruct (pos x A) eqn:E; inv H. cbn. eauto. 
Qed.    

Definition pos_el (X : eqType) (x : X) (A : list X) (H : x el A) := proj1_sig (pos_el' H).

Definition index (X : finType) (x : X) := pos_el (elem_spec x).


Lemma map_app_inv X Y (f : X -> Y) x y z :
  map f x = y ++ z -> exists x' x'', x = x' ++ x'' /\ map f x' = y /\ map f x'' = z.
Proof.
  revert x; induction y; cbn; intros.
  - exists [], x. firstorder.
  - destruct x; inv H.
    destruct (IHy _ H2) as (x' & x'' & -> & <- & <-).
    exists (x :: x'), (x''). firstorder.
Qed.

Lemma pos_inj (X : eqType) (x y : X) (A : list X) n :
  pos x A = Some n -> pos y A = Some n -> x = y.
Proof.
  revert n; induction A; cbn; intros.
  - inv H.
  - decide (x = a); decide (y = a); subst; try congruence.
    + inv H. destruct (pos y A); inv H0.
    + inv H0. destruct (pos x A); inv H.
    + destruct (pos x A), (pos y A); inv H; inv H0. eauto.
Qed.

Lemma inj_index (X : finType) : Injective (@index X).
Proof.
  intros ? ? ?. unfold index, pos_el in *.
  do 2 destruct pos_el'. cbn in H. subst. eapply pos_inj; eauto.
Qed.

(** ** Definition of single-tape Turing Machines  *)
(** Adopted definitions from the formalization of Multitape Turing Machines taken from Asperti, Riciotti "Formalizing Turing Machines" and accompanying Matita foramlisation *)

Section Fix_Sigma.

  Variable sig : finType.

  Global Instance eq_dec_sig: eq_dec sig.
  Proof. exact _. Defined. 

  (* *** Definition of the tape *)
  
  (** A tape is essentially a triple âŒ©left,current,rightâŒª where however the current 
symbol could be missing. This may happen for three different reasons: both tapes 
are empty; we are on the left extremity of a non-empty tape (left overflow), or 
we are on the right extremity of a non-empty tape (right overflow). *)
  
  Inductive tape : Type :=
  | niltape : tape
  | leftof : sig -> list sig -> tape
  | rightof : sig -> list sig -> tape
  | midtape : list sig -> sig -> list sig -> tape.

  Global Instance eq_dec_tape: eq_dec tape.
  Proof. unfold dec. decide equality; decide (e=e0); decide (l=l0); auto;
           decide (l= l1); decide (l0=l2); auto. 
  Defined.
  
  Definition tapeToList (t : tape) : list sig :=
    match t with
    | niltape => []
    | leftof s r => s :: r
    | rightof s l => List.rev (s :: l)
    | midtape l c r => (List.rev l) ++ [c] ++ r 
    end.
  
  Definition sizeOfTape t := |tapeToList t|.

  (* symbol under head *)
  Definition current :=
    fun (t : tape) =>
      match t with
      | midtape _ c _ => Some c
      | _ => None
      end.

  (* symbol-list left of head *)
  Definition left :=
    fun (t : tape) =>
      match t with
      | niltape => []
      | leftof _ _ => []
      | rightof s l => s :: l
      | midtape l _ _ => l
      end.

  (* symbol-list right of head *)
  Definition right :=
    fun (t : tape) =>
      match t with
      | niltape => []
      | leftof s r => s :: r
      | rightof _ _ => []
      | midtape _ _ r => r
      end.

  (* makes a tape from left, current, right *)
   Definition mk_tape ls c rs :=
    match c with
    | Some c => midtape ls c rs
    | None => match ls with
             | List.nil => match rs with
                     | List.nil => niltape
                     | r :: rs => leftof r rs
                     end
             | l :: ls => rightof l ls
             end
    end.

  (* *** Definition of moves *)
  
  Inductive move : Type := L : move | R : move | N : move.

  Global Instance move_eq_dec : eq_dec move.
  Proof.
    intros. hnf. decide equality.
  Defined.

  Global Instance move_finC : finTypeC (EqType move).
  Proof.
    apply (FinTypeC (enum := [L; R; N])).
    intros []; now cbv.
  Qed.
    
  (* *** Definition of a Sigletape Turing Machine *)

  Record sTM : Type :=
    {
      states : finType; (* states of the TM *)
      trans : states * (option sig) -> states * ((option sig) * move); (* the transition function *)
      start: states; (* the start state *)
      halt : states -> bool (* decidable subset of halting states *)
    }.

  (* Definition of tape movements *)

  Definition tape_move_right :=
    fun (t : tape) =>
      match t with
        niltape => niltape
      | rightof _ _ =>t
      | leftof a rs => midtape  [ ] a rs
      | midtape ls a rs =>
        match rs with
          []  => rightof  a ls
        | a0 :: rs0 => midtape (a::ls) a0 rs0
        end
      end.


  Definition tape_move_left :=
    fun (t : tape) =>
      match t with 
        niltape => niltape 
      | leftof _ _ => t
      | rightof a ls => midtape ls a [ ]
      | midtape ls a rs => 
        match ls with 
          [] => leftof a rs
        | a0 :: ls0 => midtape ls0 a0 (a::rs)
        end
      end.

  Definition tape_move := fun (t : tape) (m : move) =>
                            match m with  R => tape_move_right t | L => tape_move_left t | N => t end.

  (* Writing on the tape *)

  Definition tape_write := fun (t : tape) (s : option sig) =>
                             match s with 
                               None => t
                             | Some s0 => midtape (left t) s0 (right t)
                             end.

  (** A single step of the machine *)
  
  Definition tape_move_mono := fun (t : tape) (mv : option sig * move) =>
                                 tape_move (tape_write t (fst mv)) (snd mv).


  (* *** Configurations of TM *)
  
  Record mconfig (states:finType) : Type :=
    mk_mconfig
      {
        cstate : states;
        ctape : tape
      }.

  Instance eq_dec_conf (s: finType): eq_dec (mconfig s).
  Proof. intros x y. destruct x,y.
         decide (cstate0 = cstate1); decide (ctape0 = ctape1);
           try (right; intros H; now inversion H). left. now subst.
  Qed.  


  (* *** Machine execution *)

  Definition step :=
    fun (M:sTM) (c:mconfig (states M)) => 
      let (news,action) := trans (cstate c, current (ctape c))
      in mk_mconfig news (tape_move_mono (ctape c) action).

  (* Initial configuration *)  
  Definition initc := fun (M : sTM) tape =>
                        mk_mconfig (@start M) tape.
    
  (* Run the machine i steps until it halts *)
  (* Returns None iff the maschine does not halt within i steps *)
  Definition loop (A:Type) := fix l n (f:A -> A) (p : A -> bool) a {struct n}:=
                              if p a then Some a  else
                                match n with
                                  O => None
                                | S m => l m f p (f a)
                                end.

  
  Definition loopM := fun (M :sTM) (i : nat) cin =>
                        loop i (@step M) (fun c => halt (cstate c)) cin. 


  
  (* *** Definition of Reachability *)

  Definition TMterminates (M: sTM) (start: mconfig (states M)) :=
    exists i outc, loopM i start = Some outc.

  Lemma loop_step_not A f p (a : A) i out:
    loop i f p (f a) = out -> (p a = false) -> (loop (S i) f p a = out). 
  Proof.
  destruct i; intros H HF; cbn in *; rewrite HF; destruct (p (f a)); assumption.   
  Qed.

  Inductive reach (M: sTM) : mconfig (states M) ->  mconfig (states M) -> Prop :=
  |reachI c : reach c c
  |reachS c d: reach (step c) d -> (halt (cstate c) = false) -> reach c d.
  Hint Constructors reach.

 
  Definition Halt' (M: sTM) (start: mconfig (states M)) :=
    exists (f: mconfig (states M)), halt (cstate f)=true /\ reach start f.

  Lemma TM_terminates_Halt (M:sTM) (start: mconfig (states M)) :
    TMterminates start <-> Halt' start.
  Proof.
    split.
    - intros [i [fin H]]. revert H. revert start. induction i; intros start H; cbn in *.
      + exists start. destruct (halt (cstate start)) eqn: HS. split; auto. inv H.
      + destruct (halt (cstate start)) eqn: HS.
        * inv H. exists fin. now split.  
        * destruct (IHi (step start)) as [q [HF RF]]. unfold loopM. assumption.
          exists q. split. assumption. now apply reachS. 
    - intros [f [HF RF]]. revert HF. induction RF; intros HR. 
      + exists 0, c. cbn. now rewrite HR.
      + destruct (IHRF HR) as [i [out LH]]. exists (S i), out. now apply loop_step_not. 
  Qed.
 
End Fix_Sigma.

Definition Halt (S: {sig:finType & sTM sig & tape sig}) :=
  Halt' (initc (projT2 (sigT_of_sigT2 S)) (projT3 S)).

Definition Reach (S: (sigT (fun (sig:finType) =>
                              (sigT (fun (M:sTM sig) => prod (mconfig sig (states M))
                                                          (mconfig sig (states M))))))) :=
  let (c1,c2) := (projT2 (projT2 S)) in
  reach c1 c2. 
     

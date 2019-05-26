Require Import Bool Arith List.
Require Import BellantoniCook.Lib BellantoniCook.Bitstring BellantoniCook.BC.

Inductive BCI : Set :=
| zeroI  : BCI
| projIn : nat -> BCI
| projIs : nat -> BCI
| succI  : bool -> BCI
| predI  : BCI
| condI  : BCI
| recI   : BCI -> BCI -> BCI -> BCI
| compI  : BCI -> list BCI -> list BCI -> BCI.


Lemma BCI_ind2' :
  forall P : BCI -> Prop,
  forall Q : list BCI -> Prop,
  Q nil ->
  (forall e l, P e -> Q l -> Q (e :: l)) ->
  P zeroI ->
  (forall i, P (projIn i)) ->
  (forall i, P (projIs i)) -> 
  (forall b, P (succI b)) ->
  P predI ->
  P condI ->
  (forall g h0 h1, P g -> P h0 -> P h1 -> P (recI g h0 h1)) ->
  (forall h rl tl, P h -> Q rl -> Q tl ->
    P (compI h rl tl)) ->
  forall e, P e.
Proof.
 fix BCI_ind2' 13; intros.
 destruct e; auto.
 apply H7; eapply BCI_ind2'; eauto.
 apply H8.
 eapply BCI_ind2'; eauto.
 revert l.
 fix BCI_ind2'0 1.
 intro.
 destruct l.
 auto.
 apply H0.
 eapply BCI_ind2'; eauto.
 apply BCI_ind2'0.
 revert l0.
 fix BCI_ind2'0 1.
 intro.
 destruct l0.
 auto.
 apply H0.
 eapply BCI_ind2'; eauto.
 apply BCI_ind2'0.
Qed.

Lemma BCI_ind2 :
  forall P : BCI -> Prop,
  P zeroI ->
  (forall i, P (projIn i)) ->
  (forall i, P (projIs i)) ->
  (forall b, P (succI b)) ->
  P predI ->
  P condI ->
  (forall g h0 h1, P g -> P h0 -> P h1 -> P (recI g h0 h1)) ->
  (forall h rl tl, P h -> (forall r, In r rl -> P r) -> 
    (forall s, In s tl -> P s) ->
    P (compI h rl tl)) ->
  forall e, P e.
Proof.
 intros.
 induction e using BCI_ind2' 
   with (Q := fun l => forall e, In e l -> P e); auto.
 simpl;intros; tauto.
 simpl.
 intros e' [ | ]; intros; subst; auto.
Qed.

Inductive TypeI :=
  | I : nat -> nat -> TypeI
  | E : ErrorI -> TypeI
    with ErrorI  :=
        | Enat : nat -> ErrorI
        | Epair : TypeI -> TypeI -> ErrorI.

Definition eq_t (e1 e2 : TypeI) : bool :=
  match e1, e2 with
    | I n1 s1, I n2 s2 => beq_nat n1 n2 && beq_nat s1 s2
    | _, _ => false
  end.

Definition unionI (e1 e2 : TypeI) :=
  match e1, e2 with
    | I n1 s1, I n2 s2 => I (max n1 n2) (max s1 s2)
    | _, _ => E (Enat 3)
  end.

Fixpoint inf_list (l : list TypeI) : TypeI :=
  match l with
    | nil => I 0 0
    | e :: l' => unionI e (inf_list l')
  end.

Fixpoint inf (e : BCI) : TypeI :=
  match e with
    | zeroI => I 0 0
    | projIn i => I (S i) 0
    | projIs i => I 0 (S i) 
    | succI b => I 0 1
    | predI => I 0 1
    | condI => I 0 4  
    | recI g h0 h1 => 
      match inf g, inf h0, inf h1 with
        | I gn gs, I h0n h0s, I h1n h1s =>
          I (maxl [S gn; h0n; h1n]) (maxl [gs; h0s-1; h1s-1])
        | _, _, _ => E (Enat 1)
      end
    | compI h nl sl => 
      match inf h with
        | I hn hs =>
          if leb hn (length nl) && leb hs (length sl)
            then 
              match inf_list (map inf nl), 
                    inf_list (map inf sl) with
                   | I nnl snl, I nsl ssl =>
                     if beq_nat snl 0 then
                       I (max nnl nsl) ssl
                       else E (Enat 4)
                   | _, _ => E (Enat 5)
                 end
            else E (Enat 6)
        | E e => E e 
      end 
end.

Fixpoint semI (e:BCI) (vnl vsl:list bs) : bs :=
  match e with
  | zeroI => nil
  | projIn i => nth i vnl nil
  | projIs i => nth i vsl nil
  | succI b => b :: hd nil vsl
  | predI => tail (hd nil vsl)
  | condI =>
      match vsl with
      | a :: b :: c :: d :: _ => 
        match a with 
          | nil => b
          | true :: _ => c
          | false :: _ => d
        end
      | a :: b :: c :: _ => 
        match a with 
          | nil => b
          | true :: _ => c
          | false :: _ => nil
        end
      | a :: b :: _ => 
        match a with 
          | nil => b
          | _ => nil
        end
      | _ => nil
      end
  | recI g h0 h1 => 
    sem_rec (semI g) (semI h0) (semI h1) 
            (hd nil vnl) (tail vnl) vsl
  | compI h nl sl => 
    semI h (map (fun ne => semI ne vnl nil) nl) 
           (map (fun se => semI se vnl vsl) sl)
  end.

Definition invI (e : BCI) : BCI :=
  compI e [projIn 1; projIn 0] nil.

Definition from_11_to_20I e := 
  compI e [projIn 0] [projIn 1].

Lemma from_11_to_20I_correct e v1 v2 :
  semI e [v1] [v2] = semI (from_11_to_20I e) [v1 ; v2] nil.
Proof.
 intros; simpl; trivial.
Qed.

Definition appI : BCI :=
  recI (projIs 0)
       (compI (succI false) nil [projIs 0])
       (compI (succI true)  nil [projIs 0]).

(*
Eval vm_compute in inf appI.
*)

Lemma appI_correct v1 v2 :
  semI appI [v1] [v2] = v1 ++ v2.
Proof.
 induction v1; simpl in *; trivial.
 intros; rewrite IHv1.
 case a; trivial.
Qed.

Notation O := zeroI.
Notation S0 := (succI false).
Notation S1 := (succI true).
Notation P := predI.

Notation "'If' e 'Nil' e0 'Then' e1 'Else' e2" :=
  (compI condI nil [e; e0; e1; e2]) (at level 65).

Notation "h ( nl , sl )" := (compI h nl sl) (at level 50).

Notation "'#' n" := (projIn n) (at level 0).
Notation "'$' n" := (projIs n) (at level 0).


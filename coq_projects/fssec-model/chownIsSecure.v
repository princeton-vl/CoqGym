Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section chownIsSecure. 
 
Lemma ChownPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Chown t -> SecureState t. 
StartPSS. 
inversion H. 
unfold SecureState in |- *. 
BreakSS. 
split. 
unfold DACSecureState in |- *. 
simpl in |- *. 
intros. 
elim (OBJeq_dec o o0). 
intro. 
rewrite <- a. 
cut (fsecmat (secmat s) o = None). 
intro. 
rewrite H6. 
eauto. 
 
unfold fsecmat in |- *. 
auto. 
 
intro. 
cut
 (match fsecmat (secmat s) o0 with
  | Some y => set_In u0 (ActReaders y) -> PreDACRead s u0 o0
  | None => True
  end /\
  match fsecmat (secmat s) o0 with
  | Some y => set_In u0 (ActWriters y) -> PreDACWrite s u0 o0
  | None => True
  end). 
elim (fsecmat (secmat s) o0). 
unfold PreDACRead, PreDACWrite, chown_acl in |- *. 
simpl in |- *. 
elim (facl (acl s) o). 
intro. 
replace
 (facl
    (set_add ACLeq_dec
       (o,
       acldata p g (UsersReaders a)
         match set_In_dec GRPeq_dec (group a) (GroupReaders a) with
         | left _ =>
             set_add GRPeq_dec g
               (set_remove GRPeq_dec (group a) (GroupReaders a))
         | right _ => GroupReaders a
         end (UsersWriters a)
         match set_In_dec GRPeq_dec (group a) (GroupWriters a) with
         | left _ =>
             set_add GRPeq_dec g
               (set_remove GRPeq_dec (group a) (GroupWriters a))
         | right _ => GroupWriters a
         end
         (set_add SUBeq_dec p
            (set_remove SUBeq_dec (owner a) (UsersOwners a))) 
         (GroupOwners a)) (set_remove ACLeq_dec (o, a) (acl s))) o0) with
 (facl (acl s) o0). 
elim (facl (acl s) o0). 
auto. 
 
auto. 
 
unfold facl in |- *. 
auto. 
 
auto. 
 
tauto. 
 
split. 
apply ReadWriteImpRead. 
auto. 
 
apply ReadWriteImpWrite. 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma ChownPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Chown t -> StarProperty t. 
StartPSP. 
inversion H; auto. 
Qed. 
 
 
Lemma ChownPCP : forall s t : SFSstate, PreservesControlProp s Chown t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
inversion H. 
split. 
intros. 
split. 
intro. 
inversion H6. 
simpl in H8. 
elim (OBJeq_dec o o0); intro. 
rewrite <- a; auto. 
 
cut (y = z). 
intro. 
cut False. 
tauto. 
 
rewrite H10 in H9; inversion H9; auto. 
 
cut (facl (chown_acl s o p g) o0 = facl (acl s) o0). 
intro H10; rewrite H10 in H8; rewrite H7 in H8; injection H8; auto. 
 
symmetry  in |- *. 
unfold chown_acl in |- *. 
elim (facl (acl s) o). 
intro; unfold facl in |- *; apply AddRemEq. 
auto. 
 
auto. 
 
simpl in H8. 
elim (OBJeq_dec o o0); intro. 
rewrite <- a; auto. 
 
cut (y = z). 
intro. 
cut False. 
tauto. 
 
rewrite H10 in H9; inversion H9; auto. 
 
cut (facl (chown_acl s o p g) o0 = facl (acl s) o0). 
intro H10; rewrite H10 in H8; rewrite H7 in H8; injection H8; auto. 
 
symmetry  in |- *. 
unfold chown_acl in |- *. 
elim (facl (acl s) o). 
intro; unfold facl in |- *; apply AddRemEq. 
auto. 
 
auto. 
 
intro;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (chown_acl s o p g) (secmat s) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s) 
        (chown_acl s o p g) (secmat s) (files s) (directories s)) u0); 
 auto. 
 
Qed. 
 
 
End chownIsSecure. 
 
Hint Resolve ChownPSS ChownPSP ChownPCP. 
 
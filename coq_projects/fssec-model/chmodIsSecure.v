Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section chmodIsSecure. 
 
Lemma ChmodPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Chmod t -> SecureState t. 
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
unfold PreDACRead, PreDACWrite, chmod_acl in |- *. 
simpl in |- *. 
elim (facl (acl s) o). 
intro. 
replace
 (facl
    (set_add ACLeq_dec
       (o,
       acldata (owner a) (group a)
         (ChangeUserR Sub (UsersReaders a) (ownerp perms))
         (ChangeGroupR (AllGrp s) (groupp perms)
            (ChangeGroupR (group a) (groupp perms) (GroupReaders a)))
         (ChangeUserW Sub (UsersWriters a) (ownerp perms))
         (ChangeGroupW (AllGrp s) (groupp perms)
            (ChangeGroupW (group a) (groupp perms) (GroupWriters a)))
         (UsersOwners a) (GroupOwners a))
       (set_remove ACLeq_dec (o, a) (acl s))) o0) with 
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
 
 
Lemma ChmodPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Chmod t -> StarProperty t. 
StartPSP. 
inversion H; auto. 
Qed. 
 
 
Lemma ChmodPCP : forall s t : SFSstate, PreservesControlProp s Chmod t. 
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
 
cut (facl (chmod_acl s Sub o perms) o0 = facl (acl s) o0). 
intro H10; rewrite H10 in H8; rewrite H7 in H8; injection H8; auto. 
 
symmetry  in |- *. 
unfold chmod_acl in |- *. 
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
 
cut (facl (chmod_acl s Sub o perms) o0 = facl (acl s) o0). 
intro H10; rewrite H10 in H8; rewrite H7 in H8; injection H8; auto. 
 
symmetry  in |- *. 
unfold chmod_acl in |- *. 
elim (facl (acl s) o). 
intro; unfold facl in |- *; apply AddRemEq. 
auto. 
 
auto. 
 
intro;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s)
        (chmod_acl s Sub o perms) (secmat s) (files s) 
        (directories s)) o0); auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s)
        (chmod_acl s Sub o perms) (secmat s) (files s) 
        (directories s)) u0); auto. 
 
Qed. 
 
 
End chmodIsSecure. 
 
Hint Resolve ChmodPSS ChmodPSP ChmodPCP.
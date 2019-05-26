Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section addUsrGrpToAclIsSecure. 
 
Lemma AddUsrGrpToAclPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s AddUsrGrpToAcl t -> SecureState t. 
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
unfold PreDACRead, PreDACWrite, addUsrGrpToAcl_acl in |- *. 
simpl in |- *. 
elim (facl (acl s) o). 
intro. 
replace
 (facl
    (set_add ACLeq_dec
       (o,
       acldata (owner a) (group a) (set_add SUBeq_dec ru (UsersReaders a))
         (set_add GRPeq_dec rg (GroupReaders a))
         (set_add SUBeq_dec wu (UsersWriters a))
         (set_add GRPeq_dec wg (GroupWriters a))
         (set_add SUBeq_dec pu (UsersOwners a))
         (set_add GRPeq_dec pg (GroupOwners a)))
       (set_remove ACLeq_dec (o, a) (acl s))) o0) with 
 (facl (acl s) o0). 
elim (facl (acl s) o0). 
auto. 
 
auto. 
 
unfold facl in |- *. 
auto. 
 
auto. 
 
trivial. 
 
split. 
apply ReadWriteImpRead. 
auto. 
 
apply ReadWriteImpWrite. 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma AddUsrGrpToAclPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s AddUsrGrpToAcl t -> StarProperty t. 
StartPSP. 
inversion H; auto. 
Qed. 
 
 
Lemma AddUsrGrpToAclPCP :
 forall s t : SFSstate, PreservesControlProp s AddUsrGrpToAcl t. 
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
 
cut (facl (addUsrGrpToAcl_acl s o ru wu pu rg wg pg) o0 = facl (acl s) o0). 
intro H10; rewrite H10 in H8; rewrite H7 in H8; injection H8; auto. 
 
symmetry  in |- *. 
unfold addUsrGrpToAcl_acl in |- *. 
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
 
cut (facl (addUsrGrpToAcl_acl s o ru wu pu rg wg pg) o0 = facl (acl s) o0). 
intro H10; rewrite H10 in H8; rewrite H7 in H8; injection H8; auto. 
 
symmetry  in |- *. 
unfold addUsrGrpToAcl_acl in |- *. 
elim (facl (acl s) o). 
intro; unfold facl in |- *; apply AddRemEq. 
auto. 
 
auto. 
 
intro;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s)
        (addUsrGrpToAcl_acl s o ru wu pu rg wg pg) 
        (secmat s) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s)
        (addUsrGrpToAcl_acl s o ru wu pu rg wg pg) 
        (secmat s) (files s) (directories s)) u0); 
 auto. 
 
Qed. 
 
 
End addUsrGrpToAclIsSecure. 
 
Hint Resolve AddUsrGrpToAclPSS AddUsrGrpToAclPSP AddUsrGrpToAclPCP. 
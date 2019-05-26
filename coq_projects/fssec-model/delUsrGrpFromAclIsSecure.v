Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section delUsrGrpFromAclIsSecure. 
 
Lemma DelUsrGrpFromAclPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s DelUsrGrpFromAcl t -> SecureState t. 
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
rewrite H7. 
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
unfold PreDACRead, PreDACWrite, delUsrGrpFromAcl_acl in |- *. 
simpl in |- *. 
elim (facl (acl s) o). 
intro. 
replace
 (facl
    (set_add ACLeq_dec
       (o,
       acldata
         match SUBeq_dec (owner a) pu with
         | left _ => root
         | right _ => owner a
         end (group a) (set_remove SUBeq_dec ru (UsersReaders a))
         (set_remove GRPeq_dec rg (GroupReaders a))
         (set_remove SUBeq_dec wu (UsersWriters a))
         (set_remove GRPeq_dec wg (GroupWriters a))
         match SUBeq_dec (owner a) pu with
         | left _ =>
             set_add SUBeq_dec root (set_remove SUBeq_dec pu (UsersOwners a))
         | right _ => set_remove SUBeq_dec pu (UsersOwners a)
         end (set_remove GRPeq_dec pg (GroupOwners a)))
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
 
 
Lemma DelUsrGrpFromAclPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s DelUsrGrpFromAcl t -> StarProperty t. 
StartPSP. 
inversion H; auto. 
Qed. 
 
 
Lemma DelUsrGrpFromAclPCP :
 forall s t : SFSstate, PreservesControlProp s DelUsrGrpFromAcl t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
inversion H. 
split. 
intros. 
split. 
intro. 
inversion H7. 
simpl in H9. 
elim (OBJeq_dec o o0); intro y0. 
rewrite <- y0; auto. 
 
cut (y = z). 
intro. 
cut False. 
tauto. 
 
rewrite H11 in H10; inversion H10; auto. 
 
cut (facl (delUsrGrpFromAcl_acl s o ru wu pu rg wg pg) o0 = facl (acl s) o0). 
intro H12; rewrite H12 in H9; rewrite H8 in H9; injection H9; auto. 
 
symmetry  in |- *. 
unfold delUsrGrpFromAcl_acl in |- *. 
elim (facl (acl s) o). 
intro; unfold facl in |- *; apply AddRemEq. 
auto. 
 
auto. 
 
simpl in H9. 
elim (OBJeq_dec o o0); intro. 
rewrite <- a; auto. 
 
cut (y = z). 
intro. 
cut False. 
tauto. 
 
rewrite H11 in H10; inversion H10; auto. 
 
cut (facl (delUsrGrpFromAcl_acl s o ru wu pu rg wg pg) o0 = facl (acl s) o0). 
intro H11; rewrite H11 in H9; rewrite H8 in H9; injection H9; auto. 
 
symmetry  in |- *. 
unfold delUsrGrpFromAcl_acl in |- *. 
elim (facl (acl s) o). 
intro; unfold facl in |- *; apply AddRemEq. 
auto. 
 
auto. 
 
intro;
 absurd
  (MACObjCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s)
        (delUsrGrpFromAcl_acl s o ru wu pu rg wg pg) 
        (secmat s) (files s) (directories s)) o0); 
 auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (objectSC s)
        (delUsrGrpFromAcl_acl s o ru wu pu rg wg pg) 
        (secmat s) (files s) (directories s)) u0); 
 auto. 
 
Qed. 
 
 
End delUsrGrpFromAclIsSecure. 
 
Hint Resolve DelUsrGrpFromAclPSS DelUsrGrpFromAclPSP DelUsrGrpFromAclPCP. 
 
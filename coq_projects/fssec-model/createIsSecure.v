Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section createIsSecure. 
 
Lemma CreatePSS :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre1 s ->
 FuncPre2 s ->
 FuncPre3 s -> SecureState s -> TransFunc u s Create t -> SecureState t. 
intros s t Sub FP1 FP2 FP3 SS TF; inversion TF. 
inversion H. 
BreakSS. 
unfold SecureState in |- *. 
split. 
unfold DACSecureState in |- *; simpl in |- *. 
intros. 
cut
 (match fsecmat (secmat s) o with
  | Some y => set_In u0 (ActReaders y) -> PreDACRead s u0 o
  | None => True
  end /\
  match fsecmat (secmat s) o with
  | Some y => set_In u0 (ActWriters y) -> PreDACWrite s u0 o
  | None => True
  end). 
elim (fsecmat (secmat s) o). 
unfold PreDACRead, PreDACWrite, create_acl in |- *; simpl in |- *. 
elim (fsecmat (secmat s) (MyDir p)); elim (fSSC (subjectSC s) Sub). 
elim (OBJNAMEeq_dec p (ObjName o)). 
intro y. 
rewrite y. 
replace (facl (acl s) o) with (None (A:=AccessCtrlListData)). 
intros. 
elim H8; intros. 
split; intro. 
tauto. 
 
tauto. 
 
symmetry  in |- *. 
unfold facl in |- *. 
apply NotInDOMIsUndef. 
rewrite y in H4. 
rewrite y in H2. 
apply UniqNames; assumption.

intro y. 
replace
 (facl
    (set_add ACLeq_dec
       (NEWFILE p,
       acldata Sub (primaryGrp s Sub)
         (ChangeUserR Sub (empty_set SUBJECT) (ownerp perms))
         (ChangeGroupR (AllGrp s) (groupp perms)
            (ChangeGroupR (primaryGrp s Sub) (groupp perms)
               (empty_set GRPNAME)))
         (ChangeUserW Sub (empty_set SUBJECT) (ownerp perms))
         (ChangeGroupW (AllGrp s) (groupp perms)
            (ChangeGroupW (primaryGrp s Sub) (groupp perms)
               (empty_set GRPNAME))) (Sub :: nil) (RootGrp s :: nil)) 
       (acl s)) o) with (facl (acl s) o). 
auto. 
 
unfold facl in |- *; apply AddEq. 
unfold NEWFILE in |- *. 
intro. 
apply y. 
rewrite H8. 
simpl in |- *. 
auto. 
 
auto. 
 
auto. 
 
auto. 
 
tauto. 
 
unfold DACSecureState in DAC. 
split. 
apply ReadWriteImpRead; auto. 
 
apply ReadWriteImpWrite; auto. 
 
unfold MACSecureState in |- *; simpl in |- *; intros. 
elim (OBJNAMEeq_dec p (ObjName o)). 
intro y. 
rewrite y. 
replace (fsecmat (secmat s) o) with (None (A:=ReadersWriters)). 
replace (fOSC (objectSC s) o) with (None (A:=SecClass)). 
elim (fSSC (subjectSC s) u0); elim (fOSC (create_oSC s Sub (ObjName o)) o);
 contradiction || auto. 
 
symmetry  in |- *. 
unfold fOSC in |- *; apply NotInDOMIsUndef. 
replace (DOM OBJeq_dec (objectSC s)) with (DOM OBJeq_dec (acl s)). 
rewrite y in H4; rewrite y in H2; apply UniqNames; assumption. 
 
symmetry  in |- *; unfold fsecmat in |- *; apply NotInDOMIsUndef. 
cut (~ set_In o (DOM OBJeq_dec (acl s))). 
unfold not in |- *. 
intros SI1 SI2; apply SI1. 
unfold FuncPre3 in FP3. 
unfold Included in FP3. 
auto. 
 
rewrite y in H4; rewrite y in H2; apply UniqNames; assumption. 
 
intro y. 
replace (fOSC (create_oSC s Sub p) o) with (fOSC (objectSC s) o). 
unfold MACSecureState in MAC; apply MAC. 
 
auto. 
 
Qed. 
 
 
 
Lemma CreatePSP :
 forall (s t : SFSstate) (u : SUBJECT),
 FuncPre1 s ->
 FuncPre2 s ->
 FuncPre3 s -> StarProperty s -> TransFunc u s Create t -> StarProperty t. 
intros s t Sub FP1 FP2 FP3 SP TF; inversion TF. 
inversion H. 
unfold StarProperty in |- *; simpl in |- *; intros u0 o1 o2. 
elim (OBJNAMEeq_dec p (ObjName o1)); elim (OBJNAMEeq_dec p (ObjName o2)). 
intros y y0. 
replace (fsecmat (secmat s) o1) with (None (A:=ReadersWriters)). 
elim (fsecmat (secmat s) o2); elim (fsecmat (secmat s) o1);
 elim (fOSC (create_oSC s Sub p) o2); elim (fOSC (create_oSC s Sub p) o1);
 trivial. 
 
eauto. 
 
intros y y0. 
replace (fsecmat (secmat s) o1) with (None (A:=ReadersWriters)). 
elim (fsecmat (secmat s) o2); elim (fOSC (create_oSC s Sub p) o2);
 elim (fOSC (create_oSC s Sub p) o1); trivial. 
 
eauto. 
 
intros y y0. 
replace (fsecmat (secmat s) o2) with (None (A:=ReadersWriters)). 
elim (fsecmat (secmat s) o1); elim (fOSC (create_oSC s Sub p) o2);
 elim (fOSC (create_oSC s Sub p) o1); trivial. 
 
eauto. 
 
intros y y0. 
replace (fOSC (create_oSC s Sub p) o1) with (fOSC (objectSC s) o1). 
replace (fOSC (create_oSC s Sub p) o2) with (fOSC (objectSC s) o2). 
unfold StarProperty in SP; apply SP. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma CreatePCP :
 forall s t : SFSstate,
 FuncPre1 s -> FuncPre2 s -> PreservesControlProp s Create t. 
intros s t FP1 FP2; unfold PreservesControlProp in |- *; intros Sub TF;
 inversion TF; unfold ControlProperty in |- *. 
inversion H. 
split. 
intros. 
split. 
intro. 
inversion H8. 
simpl in H10. 
elim (OBJNAMEeq_dec p (ObjName o)). 
intro. 
cut (facl (acl s) o = None). 
intro. 
rewrite H12 in H9. 
discriminate H9. 
 
unfold facl in |- *; apply NotInDOMIsUndef. 
rewrite a in H4; rewrite a in H2; apply UniqNames; assumption. 
 
intro. 
cut (y = z). 
intro. 
cut False. 
tauto. 
 
rewrite H12 in H11; inversion H11; auto. 
 
cut (facl (acl s) o = facl (create_acl s Sub p perms) o). 
intro EQ; rewrite <- EQ in H10; rewrite H10 in H9; injection H9; auto. 
 
auto. 
 
simpl in H10. 
elim (OBJNAMEeq_dec p (ObjName o)). 
intro. 
cut (facl (acl s) o = None). 
intro. 
rewrite H12 in H9. 
discriminate H9. 
 
unfold facl in |- *; apply NotInDOMIsUndef. 
rewrite a in H4; rewrite a in H2; apply UniqNames; assumption. 
 
intro. 
cut (y = z). 
intro. 
cut False. 
tauto. 
 
rewrite H12 in H11; inversion H11; auto. 
 
cut (facl (acl s) o = facl (create_acl s Sub p perms) o). 
intro EQ; rewrite <- EQ in H10; rewrite H10 in H9; injection H9; auto. 
 
auto. 
 
intro. 
inversion H8. 
simpl in H10. 
elim (OBJNAMEeq_dec p (ObjName o)). 
intro. 
cut (fOSC (objectSC s) o = None). 
intro. 
rewrite H12 in H9; discriminate H9. 
 
unfold fOSC in |- *; apply NotInDOMIsUndef. 
 
replace (DOM OBJeq_dec (objectSC s)) with (DOM OBJeq_dec (acl s)). 
rewrite a in H4; rewrite a in H2; eauto.
 
auto. 
 
intro. 
cut (x = y). 
intro. 
cut False. 
tauto. 
 
rewrite H12 in H11; inversion H11; auto. 
 
cut (fOSC (objectSC s) o = fOSC (create_oSC s Sub p) o). 
intro EQ; rewrite <- EQ in H10; rewrite H10 in H9; injection H9; auto. 
 
auto. 
 
intros;
 absurd
  (MACSubCtrlAttrHaveChanged s
     (mkSFS (groups s) (primaryGrp s) (subjectSC s) 
        (AllGrp s) (RootGrp s) (SecAdmGrp s) (create_oSC s Sub p)
        (create_acl s Sub p perms) (secmat s) (create_files Sub p)
        (create_directories Sub p)) u0); auto. 
 
Qed. 
 
 
End createIsSecure. 
 
Hint Resolve CreatePSS CreatePSP CreatePCP. 
 
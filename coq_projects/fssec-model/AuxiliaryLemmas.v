Require Import ModelProperties.

 (*SUBJECT, Property and TransFunc*)
Ltac OpDontChangeStPSS :=
  intros s t Sub SS TF; inversion TF;
   match goal with
   | id:(s = t) |- _ => rewrite <- id; auto
   end.
 
Ltac OpDontChangeStPSP :=
  intros s t Sub SP TF;  (* SUBJECT, Property and TransFunc *)
   inversion TF; match goal with
                 | id:(s = t) |- _ => rewrite <- id; auto
                 end. 

Ltac StartPSS := intros s t Sub SS TF; inversion TF. 

Ltac BreakSS :=
  match goal with
  | SS:(SecureState _) |- _ =>
      unfold SecureState in SS; elim SS; intros DAC MAC
  end. 

Ltac StartPSP := intros s t Sub SP TF; inversion TF. 
  
 
Lemma ReadWriteImpRead :
 forall s : SFSstate,
 DACSecureState s ->
 forall (u : SUBJECT) (o : OBJECT),
 match fsecmat (secmat s) o with
 | Some y => set_In u (ActReaders y) -> PreDACRead s u o
 | None => True
 end. 
unfold DACSecureState in |- *. 
intros. 
cut
 match fsecmat (secmat s) o with
 | Some y =>
     (set_In u (ActReaders y) -> PreDACRead s u o) /\
     (set_In u (ActWriters y) -> PreDACWrite s u o)
 | None => True
 end. 
elim (fsecmat (secmat s) o). 
intros. 
elim H0; intros. 
auto. 
 
auto. 
 
apply H. 
 
Qed. 
 
 
Lemma ReadWriteImpWrite :
 forall s : SFSstate,
 DACSecureState s ->
 forall (u : SUBJECT) (o : OBJECT),
 match fsecmat (secmat s) o with
 | Some y => set_In u (ActWriters y) -> PreDACWrite s u o
 | None => True
 end. 
unfold DACSecureState in |- *. 
intros. 
cut
 match fsecmat (secmat s) o with
 | Some y =>
     (set_In u (ActReaders y) -> PreDACRead s u o) /\
     (set_In u (ActWriters y) -> PreDACWrite s u o)
 | None => True
 end. 
elim (fsecmat (secmat s) o). 
intros. 
elim H0; intros. 
auto. 
 
auto. 
 
apply H. 
 
Qed. 
 
 
Lemma TwoImpLeft :
 forall (s : SFSstate) (u : SUBJECT),
 (forall rw : ReadersWriters,
  set_In rw (ransecmat (secmat s)) ->
  ~ set_In u (ActReaders rw) /\ ~ set_In u (ActWriters rw)) ->
 forall rw : ReadersWriters,
 set_In rw (ransecmat (secmat s)) -> ~ set_In u (ActReaders rw). 
intros. 
cut (~ set_In u (ActReaders rw) /\ ~ set_In u (ActWriters rw)). 
tauto. 
 
auto. 
 
Qed. 
 
 
Lemma TwoImpRight :
 forall (s : SFSstate) (u : SUBJECT),
 (forall rw : ReadersWriters,
  set_In rw (ransecmat (secmat s)) ->
  ~ set_In u (ActReaders rw) /\ ~ set_In u (ActWriters rw)) ->
 forall rw : ReadersWriters,
 set_In rw (ransecmat (secmat s)) -> ~ set_In u (ActWriters rw). 
intros. 
cut (~ set_In u (ActReaders rw) /\ ~ set_In u (ActWriters rw)). 
tauto. 
 
auto. 
 
Qed. 
 
 
Lemma UniqNames :
 forall (s : SFSstate) (o : OBJECT),
 FuncPre1 s ->
 ~ set_In (ObjName o, File) (domf (files s)) ->
 ~ set_In (ObjName o, Directory) (domd (directories s)) ->
 ~ set_In o (DOM OBJeq_dec (acl s)). 
intro; intro; unfold FuncPre1 in |- *; elim o; simpl in |- *; intros. 
cut
 ((forall o : OBJECT,
   set_In o (DOM OBJeq_dec (directories s)) -> ObjType o = Directory) /\
  (forall o : OBJECT, set_In o (DOM OBJeq_dec (files s)) -> ObjType o = File) /\
  DOM OBJeq_dec (acl s) =
  set_union OBJeq_dec (DOM OBJeq_dec (files s))
    (DOM OBJeq_dec (directories s))). 
intro CUT; elim CUT; intros. 
elim H3; intros. 
rewrite H5; intro. 
cut
 (set_In (a, File) (domf (files s)) \/
  set_In (a, Directory) (domd (directories s))). 
intro H7; elim H7; intro. 
auto. 
 
auto. 
 
generalize H6; elim b; intro. 
left; cut (~ set_In (a, File) (DOM OBJeq_dec (directories s))). 
intro; unfold domf in |- *. 
cut
 (set_In (a, File)
    (set_union OBJeq_dec (DOM OBJeq_dec (directories s))
       (DOM OBJeq_dec (files s)))). 
intro; eauto. 
 
auto. 
 
intro; absurd (ObjType (a, File) = Directory). 
simpl in |- *. 
intro H11; discriminate H11. 
 
auto. 
 
auto. 
right. 
cut (~ set_In (a, Directory) (DOM OBJeq_dec (files s))). 
intro; unfold domd in |- *; eauto. 
 
intro; absurd (ObjType (a, Directory) = File). 
simpl in |- *. 
intro H11; discriminate H11. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Hint Resolve UniqNames. 
 
 
Lemma eq_scIMPLYle_sc : forall a b : SecClass, eq_sc a b -> le_sc a b. 
unfold eq_sc, le_sc in |- *; intros. 
elim H; intros. 
rewrite H0; rewrite H1. 
auto. 
Qed. 
 
 
Lemma NotInDOMIsUndef2 :
 forall (s : SFSstate) (o1 o2 : OBJECT),
 ~ set_In o1 (domsecmat (secmat s)) ->
 o1 = o2 -> None = fsecmat (secmat s) o2. 
intros. 
symmetry  in |- *. 
rewrite H0 in H. 
unfold fsecmat in |- *; apply NotInDOMIsUndef; auto. 
 
Qed. 
 
Lemma NotInDOMIsUndef3 :
 forall (s : SFSstate) (p : OBJNAME) (o : OBJECT),
 FuncPre1 s ->
 FuncPre3 s ->
 ~ set_In (p, File) (domf (files s)) ->
 ~ set_In (p, Directory) (domd (directories s)) ->
 p = ObjName o -> None = fsecmat (secmat s) o. 
intros until o; elim o; simpl in |- *. 
intros until b; elim b; intros. 
rewrite <- H3. 
symmetry  in |- *; unfold fsecmat in |- *; apply NotInDOMIsUndef. 
cut (~ set_In (p, File) (DOM OBJeq_dec (acl s))). 
unfold FuncPre3, Included in H3. 
unfold FuncPre3, Included in H0. 
auto. 
 
apply UniqNames; auto. 
 
rewrite <- H3. 
symmetry  in |- *; unfold fsecmat in |- *; apply NotInDOMIsUndef. 
cut (~ set_In (p, Directory) (DOM OBJeq_dec (acl s))). 
unfold FuncPre3, Included in H3. 
unfold FuncPre3, Included in H0. 
auto. 
 
apply UniqNames; auto. 
 
Qed. 
 
 
Lemma EqfOSC6 :
 forall (s : SFSstate) (o1 o2 : OBJECT) (sc : SecClass),
 o1 <> o2 -> fOSC (objectSC s) o2 = fOSC (chobjsc_SC s o1 sc) o2. 
intros; unfold fOSC, chobjsc_SC in |- *. 
elim (fOSC (objectSC s) o1). 
intro; apply AddRemEq; auto. 
 
auto. 
 
Qed. 
 
 
Lemma EqfOSC5 :
 forall (s : SFSstate) (o : OBJECT) (p : OBJNAME),
 FuncPre1 s ->
 FuncPre2 s ->
 ~ set_In (p, File) (domf (files s)) ->
 ~ set_In (p, Directory) (domd (directories s)) ->
 p = ObjName o -> None = fOSC (objectSC s) o. 
intros. 
symmetry  in |- *; unfold fOSC in |- *; apply NotInDOMIsUndef. 
replace (DOM OBJeq_dec (objectSC s)) with (DOM OBJeq_dec (acl s)). 
rewrite H3 in H1; rewrite H3 in H2. 
auto. 
 
Qed. 
 
 
Lemma EqfOSC1 :
 forall (s : SFSstate) (o : OBJECT) (p : OBJNAME) (u : SUBJECT),
 p <> ObjName o -> fOSC (objectSC s) o = fOSC (create_oSC s u p) o. 
intros. 
unfold create_oSC in |- *. 
elim (fSSC (subjectSC s) u); elim (fsecmat (secmat s) (MyDir p)). 
intros; unfold fOSC in |- *; apply AddEq. 
intro; apply H. 
rewrite H0; simpl in |- *; auto. 
 
auto. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma EqfOSC2 :
 forall (s : SFSstate) (o : OBJECT) (p : OBJNAME) (u : SUBJECT),
 p <> ObjName o -> fOSC (objectSC s) o = fOSC (mkdir_oSC s u p) o. 
intros. 
unfold mkdir_oSC in |- *. 
elim (fSSC (subjectSC s) u); elim (fsecmat (secmat s) (MyDir p)). 
intros; unfold fOSC in |- *; apply AddEq. 
intro; apply H. 
rewrite H0; simpl in |- *; auto. 
 
auto. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma EqfOSC3 :
 forall (s : SFSstate) (o1 o2 : OBJECT),
 o1 <> o2 -> fOSC (objectSC s) o2 = fOSC (unlink_oSC s o1) o2. 
intros. 
unfold unlink_oSC in |- *. 
elim (fOSC (objectSC s) o1). 
intro; unfold fOSC in |- *; apply RemEq. 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma Eqfacl1 :
 forall (s : SFSstate) (o : OBJECT) (p : OBJNAME) (u : SUBJECT)
   (perms : PERMS),
 p <> ObjName o -> facl (acl s) o = facl (create_acl s u p perms) o. 
intros. 
unfold create_acl in |- *. 
elim (fSSC (subjectSC s) u); elim (fsecmat (secmat s) (MyDir p)). 
intros; unfold facl in |- *; apply AddEq. 
intro y1; apply H; rewrite y1; simpl in |- *; auto. 
 
auto. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma Eqfacl2 :
 forall (s : SFSstate) (o : OBJECT) (p : OBJNAME) (u : SUBJECT)
   (perms : PERMS),
 p <> ObjName o -> facl (acl s) o = facl (mkdir_acl s u p perms) o. 
intros. 
unfold mkdir_acl in |- *. 
elim (fSSC (subjectSC s) u); elim (fsecmat (secmat s) (MyDir p)). 
intros; unfold facl in |- *; apply AddEq. 
intro y1; apply H; rewrite y1; simpl in |- *; auto. 
 
auto. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma Eqfacl3 :
 forall (s : SFSstate) (o1 o2 : OBJECT),
 o1 <> o2 -> facl (acl s) o2 = facl (unlink_acl s o1) o2. 
intros. 
unfold unlink_acl in |- *. 
elim (facl (acl s) o1). 
intros; unfold facl in |- *; apply RemEq. 
auto. 
 
auto. 
 
Qed. 
 
 (*Seguir aqui*)
Lemma Eqfacl4 :
 forall (s : SFSstate) (o : OBJECT) (y z : AccessCtrlListData),
 FuncPre4 s ->
 facl (acl s) o = Some y -> facl (rmdir_acl s o) o = Some z -> False. 
unfold facl in |- *. 
intros until z. 
cut
 match PARTFUNC OBJeq_dec (acl s) o with
 | Some y => set_In (o, y) (acl s)
 | None => ~ set_In o (DOM OBJeq_dec (acl s))
 end. 
unfold rmdir_acl in |- *. 
unfold facl in |- *. 
elim (PARTFUNC OBJeq_dec (acl s) o). 
intros. 
cut (PARTFUNC OBJeq_dec (set_remove ACLeq_dec (o, a) (acl s)) o = None). 
rewrite H2. 
intro. 
discriminate H3. 
 
auto. 
 
intros. 
discriminate H1. 
 
apply DOMFuncRel4. 
Qed. 
 
 
Lemma Eqfacl5 :
 forall (s : SFSstate) (o : OBJECT) (y z : AccessCtrlListData),
 FuncPre4 s ->
 facl (acl s) o = Some y -> facl (unlink_acl s o) o = Some z -> False. 
unfold facl in |- *. 
intros until z. 
cut
 match PARTFUNC OBJeq_dec (acl s) o with
 | Some y => set_In (o, y) (acl s)
 | None => ~ set_In o (DOM OBJeq_dec (acl s))
 end. 
unfold unlink_acl in |- *. 
unfold facl in |- *. 
elim (PARTFUNC OBJeq_dec (acl s) o). 
intros. 
cut (PARTFUNC OBJeq_dec (set_remove ACLeq_dec (o, a) (acl s)) o = None). 
rewrite H2. 
intro. 
discriminate H3. 
 
auto. 
 
intros. 
discriminate H1. 
 
apply DOMFuncRel4. 
Qed. 
 
 
Lemma EqfOSC4 :
 forall (s : SFSstate) (o : OBJECT) (y z : SecClass),
 FuncPre6 s ->
 fOSC (objectSC s) o = Some y -> fOSC (rmdir_oSC s o) o = Some z -> False. 
unfold fOSC in |- *. 
intros until z. 
cut
 match PARTFUNC OBJeq_dec (objectSC s) o with
 | Some y => set_In (o, y) (objectSC s)
 | None => ~ set_In o (DOM OBJeq_dec (objectSC s))
 end. 
unfold rmdir_oSC in |- *. 
unfold fOSC in |- *. 
elim (PARTFUNC OBJeq_dec (objectSC s) o). 
intros. 
cut (PARTFUNC OBJeq_dec (set_remove OSCeq_dec (o, a) (objectSC s)) o = None). 
rewrite H2. 
intro. 
discriminate H3. 
 
auto. 
 
intros. 
discriminate H1. 
 
apply DOMFuncRel4. 
Qed. 
 
 
Lemma EqfOSC7 :
 forall (s : SFSstate) (o : OBJECT) (y z : SecClass),
 FuncPre6 s ->
 fOSC (objectSC s) o = Some y -> fOSC (unlink_oSC s o) o = Some z -> False. 
unfold fOSC in |- *. 
intros until z. 
cut
 match PARTFUNC OBJeq_dec (objectSC s) o with
 | Some y => set_In (o, y) (objectSC s)
 | None => ~ set_In o (DOM OBJeq_dec (objectSC s))
 end. 
unfold unlink_oSC in |- *. 
unfold fOSC in |- *. 
elim (PARTFUNC OBJeq_dec (objectSC s) o). 
intros. 
cut (PARTFUNC OBJeq_dec (set_remove OSCeq_dec (o, a) (objectSC s)) o = None). 
rewrite H2. 
intro. 
discriminate H3. 
 
auto. 
 
intros. 
discriminate H1. 
 
apply DOMFuncRel4. 
Qed. 
 
 
Lemma NoDACChange :
 forall (s : SFSstate) (o : OBJECT) (SSC : set (SUBJECT * SecClass))
   (OSC : set (OBJECT * SecClass)) (FILES : set (OBJECT * FILECONT))
   (DIRECTS : set (OBJECT * DIRCONT)) (SM : set (OBJECT * ReadersWriters)),
 ~
 DACCtrlAttrHaveChanged s
   (mkSFS (groups s) (primaryGrp s) SSC (AllGrp s) 
      (RootGrp s) (SecAdmGrp s) OSC (acl s) SM FILES DIRECTS) o. 
intros. 
intro. 
inversion H; simpl in H1; cut (y = z). 
intro EQ; rewrite EQ in H2; inversion H2; auto. 
 
rewrite H0 in H1; injection H1; auto. 
 
intro EQ; rewrite EQ in H2; inversion H2; auto. 
 
rewrite H0 in H1; injection H1; auto. 
 
Qed. 
 
 
Lemma NoDACChange2 :
 forall (s : SFSstate) (o : OBJECT), ~ DACCtrlAttrHaveChanged s s o. 
intros; intro;
 eapply
  (NoDACChange s o (subjectSC s) (objectSC s) (files s) 
     (directories s) (secmat s)). 
generalize H; elim s; simpl in |- *; auto. 
 
Qed. 
 
 
Lemma NoMACObjChange :
 forall (s : SFSstate) (o : OBJECT) (FILES : set (OBJECT * FILECONT))
   (DIRECTS : set (OBJECT * DIRCONT))
   (ACL : set (OBJECT * AccessCtrlListData)) (SSC : set (SUBJECT * SecClass))
   (SM : set (OBJECT * ReadersWriters)),
 ~
 MACObjCtrlAttrHaveChanged s
   (mkSFS (groups s) (primaryGrp s) SSC (AllGrp s) 
      (RootGrp s) (SecAdmGrp s) (objectSC s) ACL SM FILES DIRECTS) o. 
intros; intro. 
inversion H; simpl in H1. 
cut (x = y). 
intro EQ; rewrite EQ in H2; inversion H2; auto. 
 
rewrite H0 in H1; injection H1; auto. 
 
Qed. 
 
 
Lemma NoMACObjChange2 :
 forall (s : SFSstate) (o : OBJECT), ~ MACObjCtrlAttrHaveChanged s s o. 
intros; intro;
 eapply
  (NoMACObjChange s o (files s) (directories s) (acl s) 
     (subjectSC s) (secmat s)). 
generalize H; elim s; simpl in |- *; auto. 
 
Qed. 
 
 
Lemma NoMACSubChange :
 forall (s : SFSstate) (u : SUBJECT)
   (ACL : set (OBJECT * AccessCtrlListData)) (OSC : set (OBJECT * SecClass))
   (FILES : set (OBJECT * FILECONT)) (DIRECTS : set (OBJECT * DIRCONT))
   (SM : set (OBJECT * ReadersWriters)),
 ~
 MACSubCtrlAttrHaveChanged s
   (mkSFS (groups s) (primaryGrp s) (subjectSC s) (AllGrp s) 
      (RootGrp s) (SecAdmGrp s) OSC ACL SM FILES DIRECTS) u. 
intros; intro; inversion H. 
simpl in H1. 
cut (x = y). 
intro EQ; rewrite EQ in H2; inversion H2; auto. 
 
rewrite H0 in H1; injection H1; auto. 
 
Qed. 
 
 
Lemma NoMACSubChange2 :
 forall (s : SFSstate) (u : SUBJECT), ~ MACSubCtrlAttrHaveChanged s s u. 
intros; intro;
 eapply
  (NoMACSubChange s u (acl s) (objectSC s) (files s) 
     (directories s) (secmat s)). 
generalize H; elim s; simpl in |- *; auto. 
 
Qed. 
 
 
Lemma eq_scSym : forall a b : SecClass, eq_sc a b -> eq_sc b a. 
unfold eq_sc in |- *; intros. 
elim H; intros. 
rewrite H0; rewrite H1. 
auto. 
Qed. 
 
 
Lemma ChsubscPSS1 :
 forall (s : SFSstate) (u : SUBJECT) (y : ReadersWriters),
 (forall rw : ReadersWriters,
  ~ set_In u (ActReaders rw) /\ ~ set_In u (ActWriters rw)) ->
 ~ (set_In u (ActReaders y) \/ set_In u (ActWriters y)). 
intros. 
cut (~ set_In u (ActReaders y) /\ ~ set_In u (ActWriters y)). 
tauto. 
 
auto. 
 
Qed. 
 
 
Lemma EqfSSC1 :
 forall (s : SFSstate) (u u0 : SUBJECT) (sc : SecClass),
 u <> u0 -> fSSC (subjectSC s) u0 = fSSC (chsubsc_SC s u sc) u0. 
intros; unfold chsubsc_SC in |- *. 
elim (fSSC (subjectSC s) u). 
intros; unfold fSSC in |- *; apply AddRemEq; auto. 
 
auto. 
 
Qed. 
 
 
Lemma Close_smCorr :
 forall (s : SFSstate) (Sub : SUBJECT) (o : OBJECT),
 FuncPre5 s ->
 match fsecmat (secmat s) o with
 | Some y => set_In Sub (set_union SUBeq_dec (ActReaders y) (ActWriters y))
 | None => False
 end ->
 match fsecmat (close_sm s Sub o) o with
 | None => True
 | Some y => ~ set_In Sub (ActReaders y) /\ ~ set_In Sub (ActWriters y)
 end. 
intros until o. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
unfold close_sm in |- *. 
elim (fsecmat (secmat s) o); intros. 
elim (set_remove SUBeq_dec Sub (ActReaders a));
 elim (set_remove SUBeq_dec Sub (ActWriters a)). 
replace (fsecmat (set_remove SECMATeq_dec (o, a) (secmat s)) o) with
 (None (A:=ReadersWriters)). 
auto. 
 
symmetry  in |- *; unfold fsecmat in |- *; unfold FuncPre5 in H0; auto. 
 
intros. 
replace
 (fsecmat
    (set_add SECMATeq_dec (o, NEWRW Sub o a)
       (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
 (Some (NEWRW Sub o a)). 
unfold NEWRW in |- *; simpl in |- *; split; apply Set_remove1. 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec (o, NEWRW Sub o a)
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (NEWRW Sub o a)). 
unfold NEWRW in |- *; simpl in |- *; split; apply Set_remove1. 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec (o, NEWRW Sub o a)
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (NEWRW Sub o a)). 
unfold NEWRW in |- *; simpl in |- *; split; apply Set_remove1. 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
tauto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Close_smCorr2 :
 forall (s : SFSstate) (Sub u0 : SUBJECT) (o : OBJECT),
 FuncPre5 s ->
 match fsecmat (secmat s) o with
 | Some y => set_In Sub (set_union SUBeq_dec (ActReaders y) (ActWriters y))
 | None => False
 end ->
 match fsecmat (close_sm s Sub o) o, fsecmat (secmat s) o with
 | _, None => False
 | None, Some z => True
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
intros until o. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
unfold close_sm in |- *. 
elim (fsecmat (secmat s) o); intros. 
elim (set_remove SUBeq_dec Sub (ActReaders a));
 elim (set_remove SUBeq_dec Sub (ActWriters a)). 
replace (fsecmat (set_remove SECMATeq_dec (o, a) (secmat s)) o) with
 (None (A:=ReadersWriters)). 
auto. 
 
symmetry  in |- *; unfold fsecmat in |- *; unfold FuncPre5 in H; auto. 
 
intros. 
replace
 (fsecmat
    (set_add SECMATeq_dec (o, NEWRW Sub o a)
       (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
 (Some (NEWRW Sub o a)). 
unfold NEWRW in |- *; simpl in |- *. 
split;
 [ intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActReaders a) (x:=u0) (y:=Sub)); auto
 | intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActWriters a) (x:=u0) (y:=Sub)); auto ]. 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
intros. 
replace
 (fsecmat
    (set_add SECMATeq_dec (o, NEWRW Sub o a)
       (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
 (Some (NEWRW Sub o a)). 
unfold NEWRW in |- *; simpl in |- *. 
split;
 [ intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActReaders a) (x:=u0) (y:=Sub)); auto
 | intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActWriters a) (x:=u0) (y:=Sub)); auto ]. 
 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
intros. 
replace
 (fsecmat
    (set_add SECMATeq_dec (o, NEWRW Sub o a)
       (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
 (Some (NEWRW Sub o a)). 
unfold NEWRW in |- *; simpl in |- *. 
split;
 [ intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActReaders a) (x:=u0) (y:=Sub)); auto
 | intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActWriters a) (x:=u0) (y:=Sub)); auto ]. 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
tauto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Eqfsecmat1 :
 forall (s : SFSstate) (o1 o2 : OBJECT) (u : SUBJECT),
 o1 <> o2 -> fsecmat (secmat s) o2 = fsecmat (close_sm s u o1) o2. 
unfold close_sm, fsecmat in |- *; intros;
 elim (PARTFUNC OBJeq_dec (secmat s) o1). 
intro; elim (set_remove SUBeq_dec u (ActReaders a));
 elim (set_remove SUBeq_dec u (ActWriters a)). 
auto. 
 
auto. 
 
auto. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma Close_smCorr3 :
 forall (s : SFSstate) (Sub : SUBJECT) (o : OBJECT),
 fsecmat (secmat s) o = None -> fsecmat (close_sm s Sub o) o = None. 
intros until o; unfold close_sm in |- *. 
intro. 
generalize H. 
elim (fsecmat (secmat s) o). 
intros y H0; discriminate H0. 
 
auto. 
 
Qed. 
 
 
Lemma OwnerClose_smCorr2 :
 forall (s : SFSstate) (Sub u0 : SUBJECT) (o : OBJECT),
 FuncPre5 s ->
 match fsecmat (secmat s) o with
 | Some y => set_In Sub (set_union SUBeq_dec (ActReaders y) (ActWriters y))
 | None => False
 end ->
 match fsecmat (ownerclose_sm s Sub o) o, fsecmat (secmat s) o with
 | _, None => False
 | None, Some z => True
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
intros until o. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
unfold ownerclose_sm in |- *. 
elim (fsecmat (secmat s) o); intros. 
elim (set_remove SUBeq_dec Sub (ActReaders a));
 elim (set_remove SUBeq_dec Sub (ActWriters a)). 
replace (fsecmat (set_remove SECMATeq_dec (o, a) (secmat s)) o) with
 (None (A:=ReadersWriters)). 
auto. 
 
symmetry  in |- *; unfold fsecmat in |- *; unfold FuncPre5 in H0; auto. 
 
intros. 
replace
 (fsecmat
    (set_add SECMATeq_dec (o, NEWRWOC Sub o a)
       (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
 (Some (NEWRWOC Sub o a)). 
unfold NEWRWOC in |- *; simpl in |- *. 
split;
 [ intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActReaders a) (x:=u0) (y:=Sub)); auto
 | intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActWriters a) (x:=u0) (y:=Sub)); auto ]. 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
intros. 
replace
 (fsecmat
    (set_add SECMATeq_dec (o, NEWRWOC Sub o a)
       (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
 (Some (NEWRWOC Sub o a)). 
unfold NEWRWOC in |- *; simpl in |- *. 
split;
 [ intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActReaders a) (x:=u0) (y:=Sub)); auto
 | intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActWriters a) (x:=u0) (y:=Sub)); auto ]. 
 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
intros. 
replace
 (fsecmat
    (set_add SECMATeq_dec (o, NEWRWOC Sub o a)
       (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
 (Some (NEWRWOC Sub o a)). 
unfold NEWRWOC in |- *; simpl in |- *. 
split;
 [ intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActReaders a) (x:=u0) (y:=Sub)); auto
 | intro;
    eapply
     (Set_remove2 (A:=SUBJECT) (Aeq_dec:=SUBeq_dec) (B:=
        ActWriters a) (x:=u0) (y:=Sub)); auto ]. 
 
unfold fsecmat in |- *; apply AddEq1. 
auto. 
 
tauto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Eqfsecmat2 :
 forall (s : SFSstate) (o1 o2 : OBJECT) (u : SUBJECT),
 o1 <> o2 -> fsecmat (secmat s) o2 = fsecmat (ownerclose_sm s u o1) o2. 
unfold ownerclose_sm, fsecmat in |- *; intros;
 elim (PARTFUNC OBJeq_dec (secmat s) o1). 
intro; elim (set_remove SUBeq_dec u (ActReaders a));
 elim (set_remove SUBeq_dec u (ActWriters a)). 
auto. 
 
auto. 
 
auto. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma OwnerClose_smCorr3 :
 forall (s : SFSstate) (Sub : SUBJECT) (o : OBJECT),
 fsecmat (secmat s) o = None -> fsecmat (ownerclose_sm s Sub o) o = None. 
intros until o; unfold ownerclose_sm in |- *. 
intro. 
generalize H. 
elim (fsecmat (secmat s) o). 
intros y H0; discriminate H0. 
 
auto. 
 
Qed. 
 
 
Lemma Open_smCorr3 :
 forall (s : SFSstate) (Sub : SUBJECT) (o : OBJECT) (m : MODE),
 FuncPre5 s ->
 fsecmat (open_sm s Sub o m) o = None -> fsecmat (secmat s) o = None. 
intros until m; intro; unfold open_sm in |- *. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
elim m; elim (fsecmat (secmat s) o). 
intro; intro;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (set_add SUBeq_dec Sub (ActReaders a)) (ActWriters a))
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (mkRW (set_add SUBeq_dec Sub (ActReaders a)) (ActWriters a))). 
intros H2; discriminate H2. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
intro;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o,
        mkRW (set_add SUBeq_dec Sub (empty_set SUBJECT)) (empty_set SUBJECT))
        (secmat s)) o) with
  (Some
     (mkRW (set_add SUBeq_dec Sub (empty_set SUBJECT)) (empty_set SUBJECT))). 
intro H2; discriminate H2. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
intro; intro;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (ActReaders a) (set_add SUBeq_dec Sub (ActWriters a)))
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (mkRW (ActReaders a) (set_add SUBeq_dec Sub (ActWriters a)))). 
intro H2; discriminate H2. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
intro;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o,
        mkRW (empty_set SUBJECT) (set_add SUBeq_dec Sub (empty_set SUBJECT)))
        (secmat s)) o) with
  (Some
     (mkRW (empty_set SUBJECT) (set_add SUBeq_dec Sub (empty_set SUBJECT)))). 
intro H2; discriminate H2. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Open_smCorr21 :
 forall (s : SFSstate) (Sub u0 : SUBJECT) (o : OBJECT) (m : MODE),
 Sub <> u0 ->
 FuncPre5 s ->
 match fsecmat (open_sm s Sub o READ) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActReaders y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActWriters y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
intros. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
unfold open_sm in |- *. 
elim (fsecmat (secmat s) o). 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (set_add SUBeq_dec Sub (ActReaders a)) (ActWriters a))
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (mkRW (set_add SUBeq_dec Sub (ActReaders a)) (ActWriters a))). 
simpl in |- *. 
split; (intros; eauto). 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o,
        mkRW (set_add SUBeq_dec Sub (empty_set SUBJECT)) (empty_set SUBJECT))
        (secmat s)) o) with
  (Some
     (mkRW (set_add SUBeq_dec Sub (empty_set SUBJECT)) (empty_set SUBJECT))). 
auto. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Open_smCorr22 :
 forall (s : SFSstate) (Sub u0 : SUBJECT) (o : OBJECT) (m : MODE),
 Sub <> u0 ->
 FuncPre5 s ->
 match fsecmat (open_sm s Sub o WRITE) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActWriters y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActReaders y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z =>
     (set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)) /\
     (set_In u0 (ActWriters y) -> set_In u0 (ActWriters z))
 end. 
intros. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
unfold open_sm in |- *. 
elim (fsecmat (secmat s) o). 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (ActReaders a) (set_add SUBeq_dec Sub (ActWriters a)))
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (mkRW (ActReaders a) (set_add SUBeq_dec Sub (ActWriters a)))). 
simpl in |- *. 
split; (intro; eauto). 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o,
        mkRW (empty_set SUBJECT) (set_add SUBeq_dec Sub (empty_set SUBJECT)))
        (secmat s)) o) with
  (Some
     (mkRW (empty_set SUBJECT) (set_add SUBeq_dec Sub (empty_set SUBJECT)))). 
auto. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Eqfsecmat3 :
 forall (s : SFSstate) (o1 o2 : OBJECT) (u : SUBJECT) (m : MODE),
 o1 <> o2 -> fsecmat (secmat s) o2 = fsecmat (open_sm s u o1 m) o2. 
intros until m; unfold fsecmat, open_sm in |- *. 
elim m; elim (fsecmat (secmat s) o1). 
intros; apply AddRemEq; auto. 
 
intros; apply AddEq; auto. 
 
intros; apply AddRemEq; auto. 
 
intros; apply AddEq; auto. 
 
Qed. 
 
 
Lemma Chobjsc_Corr :
 forall (s : SFSstate) (o : OBJECT) (sc : SecClass),
 FuncPre6 s ->
 (fOSC (objectSC s) o = None <-> fOSC (chobjsc_SC s o sc) o = None). 
intros; unfold chobjsc_SC in |- *. 
cut
 match fOSC (objectSC s) o with
 | Some y => set_In (o, y) (objectSC s)
 | None => ~ set_In o (DOM OBJeq_dec (objectSC s))
 end. 
split. 
intro H1; rewrite H1; auto. 
 
generalize H0; elim (fOSC (objectSC s) o). 
intro; intro;
 replace
  (fOSC
     (set_add OSCeq_dec (o, sc) (set_remove OSCeq_dec (o, a) (objectSC s))) o)
  with (Some sc). 
intro H2; discriminate H2. 
 
unfold fOSC in |- *; apply AddEq1. 
auto. 
 
auto. 
 
unfold fOSC in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Aux1 :
 forall y : SecClass, ~ (Some y = None <-> None = None :>option SecClass). 
intro; unfold iff in |- *; intro H; elim H; intros. 
absurd (Some y = None); auto. 
intro D; discriminate D. 
 
Qed. 
 
 
Lemma Chsubsc_Corr :
 forall (s : SFSstate) (u : SUBJECT) (sc : SecClass),
 FuncPre7 s ->
 (fSSC (subjectSC s) u = None <-> fSSC (chsubsc_SC s u sc) u = None). 
intros; unfold chsubsc_SC in |- *. 
cut
 match fSSC (subjectSC s) u with
 | Some y => set_In (u, y) (subjectSC s)
 | None => ~ set_In u (DOM SUBeq_dec (subjectSC s))
 end. 
split. 
intro H1; rewrite H1; auto. 
 
generalize H0; elim (fSSC (subjectSC s) u). 
intro; intro;
 replace
  (fSSC
     (set_add SSCeq_dec (u, sc) (set_remove SSCeq_dec (u, a) (subjectSC s)))
     u) with (Some sc). 
intro H2; discriminate H2. 
 
unfold fSSC in |- *; apply AddEq1; auto. 
auto. 
 
auto. 
 
unfold fSSC in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Open_smCorr31 :
 forall (s : SFSstate) (Sub u0 : SUBJECT) (o : OBJECT) (m : MODE),
 FuncPre5 s ->
 match fsecmat (open_sm s Sub o READ) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActReaders y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActWriters y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z => set_In u0 (ActWriters y) -> set_In u0 (ActWriters z)
 end. 
intros. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
unfold open_sm in |- *. 
elim (fsecmat (secmat s) o). 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (set_add SUBeq_dec Sub (ActReaders a)) (ActWriters a))
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (mkRW (set_add SUBeq_dec Sub (ActReaders a)) (ActWriters a))). 
simpl in |- *; auto. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o,
        mkRW (set_add SUBeq_dec Sub (empty_set SUBJECT)) (empty_set SUBJECT))
        (secmat s)) o) with
  (Some
     (mkRW (set_add SUBeq_dec Sub (empty_set SUBJECT)) (empty_set SUBJECT))). 
simpl in |- *; auto. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
Qed. 
 
 
Lemma Open_smCorr32 :
 forall (s : SFSstate) (Sub u0 : SUBJECT) (o : OBJECT) (m : MODE),
 FuncPre5 s ->
 match fsecmat (open_sm s Sub o WRITE) o, fsecmat (secmat s) o with
 | Some y, None =>
     ActWriters y = set_add SUBeq_dec Sub (empty_set SUBJECT) /\
     ActReaders y = empty_set SUBJECT
 | None, _ => False
 | Some y, Some z => set_In u0 (ActReaders y) -> set_In u0 (ActReaders z)
 end. 
intros. 
cut
 match fsecmat (secmat s) o with
 | Some y => set_In (o, y) (secmat s)
 | None => ~ set_In o (DOM OBJeq_dec (secmat s))
 end. 
unfold open_sm in |- *. 
elim (fsecmat (secmat s) o). 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o, mkRW (ActReaders a) (set_add SUBeq_dec Sub (ActWriters a)))
        (set_remove SECMATeq_dec (o, a) (secmat s))) o) with
  (Some (mkRW (ActReaders a) (set_add SUBeq_dec Sub (ActWriters a)))). 
simpl in |- *; auto. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
intros;
 replace
  (fsecmat
     (set_add SECMATeq_dec
        (o,
        mkRW (empty_set SUBJECT) (set_add SUBeq_dec Sub (empty_set SUBJECT)))
        (secmat s)) o) with
  (Some
     (mkRW (empty_set SUBJECT) (set_add SUBeq_dec Sub (empty_set SUBJECT)))). 
simpl in |- *; auto. 
 
unfold fsecmat in |- *; apply AddEq1; auto. 
 
unfold fsecmat in |- *; apply DOMFuncRel4. 
 
Qed. 
 
Hint Resolve eq_scIMPLYle_sc eq_scSym Eqfsecmat1 Close_smCorr3 TwoImpLeft
  TwoImpRight EqfOSC1 ChsubscPSS1 Eqfsecmat2 NoMACObjChange NoDACChange
  NoMACSubChange EqfOSC6 Eqfacl1 Eqfacl2 Eqfacl3 EqfOSC1 EqfOSC2 EqfOSC3 Aux1
  NotInDOMIsUndef2 Eqfacl4 EqfOSC4 EqfOSC5 EqfSSC1 OwnerClose_smCorr3
  Open_smCorr3 Eqfsecmat3 Chobjsc_Corr NoMACObjChange2 NoDACChange2
  NoMACSubChange2 Chsubsc_Corr NotInDOMIsUndef3 Eqfacl5 EqfOSC7. 

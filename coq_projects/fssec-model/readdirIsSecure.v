Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section readdirIsSecure. 
 
Lemma ReaddirPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Readdir t -> SecureState t. 
OpDontChangeStPSS. 
Qed. 
 
 
Lemma ReaddirPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Readdir t -> StarProperty t. 
OpDontChangeStPSP. 
Qed. 
 
 
Lemma ReaddirPCP : forall s t : SFSstate, PreservesControlProp s Readdir t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
split. 
intros. 
split. 
intro. 
absurd (DACCtrlAttrHaveChanged t t o0); auto. 
 
intro; absurd (MACObjCtrlAttrHaveChanged t t o0); auto. 
 
intros; absurd (MACSubCtrlAttrHaveChanged t t u0); auto. 
 
Qed. 
 
 
End readdirIsSecure. 
 
Hint Resolve ReaddirPSS ReaddirPSP ReaddirPCP. 
 
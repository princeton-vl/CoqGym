Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section readIsSecure. 
 
Lemma ReadPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Read t -> SecureState t. 
OpDontChangeStPSS. 
Qed. 
 
 
Lemma ReadPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Read t -> StarProperty t. 
OpDontChangeStPSP. 
Qed. 
 
 
Lemma ReadPCP : forall s t : SFSstate, PreservesControlProp s Read t. 
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
 
 
End readIsSecure. 
 
Hint Resolve ReadPSS ReadPSP ReadPCP. 
 
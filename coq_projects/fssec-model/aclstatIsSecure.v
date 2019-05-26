Require Import ModelProperties.
Require Import AuxiliaryLemmas.

Section aclstatIsSecure.

Lemma AclstatPSS :
 forall (s t : SFSstate) (u : SUBJECT),
 SecureState s -> TransFunc u s Aclstat t -> SecureState t.
OpDontChangeStPSS.
Qed. 
 
 
Lemma AclstatPSP :
 forall (s t : SFSstate) (u : SUBJECT),
 StarProperty s -> TransFunc u s Aclstat t -> StarProperty t. 
OpDontChangeStPSP. 
Qed. 
 
 
Lemma AclstatPCP : forall s t : SFSstate, PreservesControlProp s Aclstat t. 
intros; unfold PreservesControlProp in |- *; intros Sub TF; inversion TF;
 unfold ControlProperty in |- *. 
split. 
intros. 
split. 
intros; absurd (DACCtrlAttrHaveChanged t t o0); auto. 
 
intro; absurd (MACObjCtrlAttrHaveChanged t t o0); auto. 
 
intros; absurd (MACSubCtrlAttrHaveChanged t t u0); auto. 
 
Qed. 
 
   
End aclstatIsSecure. 
 
Hint Resolve AclstatPSS AclstatPSP AclstatPCP. 
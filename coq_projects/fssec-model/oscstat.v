Require Export DACandMAC. 
 
Section Oscstat. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                           oscstat                                 *) 
(*********************************************************************) 
 
(*This operation outputs the security class of a given object.       *) 
 
Inductive oscstat (u : SUBJECT) (o : OBJECT) :
SFSstate -> Exc SecClass -> Prop :=
    OscstatOK : PreMAC s u o -> oscstat u o s (fOSC (objectSC s) o). 
 
End Oscstat.
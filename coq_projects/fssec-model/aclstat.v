Require Export DACandMAC. 
 
Set Implicit Arguments.
Unset Strict Implicit. 
 
(*********************************************************************) 
(*                           aclstat                                 *) 
(*********************************************************************) 
 
(*This operation outputs the information stored in the ACL of a given*) 
(*object. PreDACRead should be satisfied for the invoking user and   *) 
(*object. There is no change of state.                               *) 
 
Section Aclstat. 
 
Variable s : SFSstate. 
 
Inductive aclstat (u : SUBJECT) (o : OBJECT) :
SFSstate -> Exc AccessCtrlListData -> Prop :=
    AclstatOK :
      PreDACRead s u o ->
      aclstat u o s
        match facl (acl s) o with
        | None => None (A:=AccessCtrlListData)
        | Some y =>
            Some
              (acldata (owner y) (group y) (UsersReaders y) 
                 (GroupReaders y) (UsersWriters y) 
                 (GroupWriters y) (UsersOwners y) (GroupOwners y))
        end. 
 
End Aclstat.
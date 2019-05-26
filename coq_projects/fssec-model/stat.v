Require Export DACandMAC. 
Set Implicit Arguments.
Unset Strict Implicit. 
 
Section Stat. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                             stat                                  *) 
(*********************************************************************) 
 
(*This operation outputs the UNIX security information stored in the *) 
(*ACL of a given object. Note that in our model the only precondition*) 
(*for this operation is that the user has DAC read                   *) 
(*access to the object and not, as in the standar UNIX, execute      *) 
(*access.                                                            *) 
 
(*This function computes object's mode from the object's ACL by      *) 
(*owner, group and AllGrp in UsersReaders, UsersWriters,             *) 
(*GroupReaders and GroupWriters.                                     *) 
 
Parameter comp_mode : AccessCtrlListData -> PERMS. 
 
(*This record stores the security attributes present in a            *) 
(*conventinoal i-node.                                               *) 
 
Record stat_struct : Set := stat_fields
  {st_mode : PERMS; st_uid : SUBJECT; st_gid : GRPNAME}. 
 
Inductive stat (u : SUBJECT) (o : OBJECT) :
SFSstate -> Exc stat_struct -> Prop :=
    StatOK :
      PreDACRead s u o ->
      stat u o s
        match facl (acl s) o with
        | None => None (A:=stat_struct)
        | Some y => Some (stat_fields (comp_mode y) (owner y) (group y))
        end. 
 
End Stat.
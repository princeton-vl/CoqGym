Require Export SFSstate. 
Set Implicit Arguments.
Unset Strict Implicit. 
 
Section InitialState. 
 
(*********************************************************************) 
(*                  Initial State of the System                      *) 
(*********************************************************************) 
 
Parameter SysGroups : GRPNAME -> set SUBJECT. 
Parameter SysPrimaryGrp : SUBJECT -> GRPNAME. 
Parameter SysSubjectSC : set (SUBJECT * SecClass). 
Parameter SysAllGrp SysRootGrp SysSecAdmGrp : GRPNAME. 
 
Axiom SysSubjectSCIsPARTFUNC : IsPARTFUNC SUBeq_dec SysSubjectSC. 
 
Axiom RootBelongsToRootGrp : set_In root (SysGroups SysRootGrp). 
 
Axiom RootBelongsToAllGrp : set_In root (SysGroups SysAllGrp). 
 
Axiom SecofrBelongsToSecAdmGrp : set_In root (SysGroups SysSecAdmGrp). 
 
Axiom SecofrBelongsToAllGrp : set_In root (SysGroups SysAllGrp). 
 
 
(*In the initial state the parameters previously defined are some of *) 
(*its fields, the others being empty sets (of apropriate types) which*) 
(*in turn are (trivially) partial functions.                         *) 
 
Definition InitState : SFSstate :=
  mkSFS SysGroups SysPrimaryGrp SysSubjectSC SysAllGrp SysRootGrp
    SysSecAdmGrp (empty_set (OBJECT * SecClass))
    (empty_set (OBJECT * AccessCtrlListData))
    (empty_set (OBJECT * ReadersWriters)) (empty_set (OBJECT * FILECONT))
    (empty_set (OBJECT * DIRCONT)). 
 
 
End InitialState. 
 
Hint Resolve SysSubjectSCIsPARTFUNC.
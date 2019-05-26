Require Import Prelim. 

(** ** PCP and MPCP *)

Section pcp_definition.
  Variable X:Type.

  Definition pcp : Type := list (list X * list X). 
  Definition mpcp : Type := (list X * list X) * pcp. 

  Definition trans_mpcp_pcp : mpcp -> pcp := fun M => (fst M)::(snd M).
  Coercion trans_mpcp_pcp : mpcp >-> pcp.

  Definition solution (P:pcp) :=
    concat (map fst P) = concat (map snd P). 

  Definition pcp_solution P S :=
    S <> nil /\ S <<= P /\ solution S. 

  Definition MPCP (M: mpcp) := exists S, pcp_solution (fst M::snd M) ((fst M)::S).
  Definition PCP (P: pcp) := exists S, pcp_solution P S. 
  
End pcp_definition.

Definition PCPD (S: sigT (fun X => pcp X)) := PCP (projT2 S).
Definition MPCPD (S: sigT (fun X => mpcp X)) := MPCP (projT2 S). 
(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)



Ltac ExistHyp t := match goal with
                   | H1:t |- _ => idtac
                   end.

Ltac HypOfType t := match goal with
                    | H1:t |- _ => H1
                    end.

Ltac CleanDuplicatedHyps :=
  repeat match goal with
         | H:?X1 |- _ => clear H; ExistHyp X1
         end.

Ltac not_exist_hyp t := match goal with
  | H1:t |- _ => fail 2
 end || idtac.

Ltac assert_if_not_exist H :=
  not_exist_hyp H;assert H.


Ltac suppose t := cut t;[intro|idtac].

Ltac use H := decompose [and ex] H; clear H.

Ltac print_goal := match goal with
 |- ?G => idtac G
end.

Ltac DecompEx H P := elim H;intro P;intro;clear H.

Ltac DecompExAnd H P :=
  elim H;intro P;
  let id:=fresh in intro id;decompose [and] id;clear id;clear H.

Ltac DecompAndAll :=
 repeat
 match goal with
   | H:(?X1 /\ ?X2) |- _ => decompose [and] H;clear H
end.

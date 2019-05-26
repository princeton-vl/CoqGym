(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export freepoints.

(* Exprime un triplet D E F suivant les coordonnées sur la base A B C *)


Ltac freepoints_independant A B C H D E F :=
  rewrite (free_points_area_elimination A B C D E F H) in *.

(* Exprime tout suivant une base A B C *)

Ltac iter_coord_expr A B C H E :=
  match constr:(E) with
  | (?X1 = ?X2) =>
      iter_coord_expr A B C H X1; iter_coord_expr A B C H X2
  | (?X1 + ?X2) =>
      iter_coord_expr A B C H X1; iter_coord_expr A B C H X2
  | (?X1 * ?X2) =>
      iter_coord_expr A B C H X1; iter_coord_expr A B C H X2
  | (?X1 / ?X2) =>
      iter_coord_expr A B C H X1; iter_coord_expr A B C H X2
  | (?X1 - ?X2) =>
      iter_coord_expr A B C H X1; iter_coord_expr A B C H X2
  | (- ?X1) => iter_coord_expr A B C H X1
  | (/ ?X1) => iter_coord_expr A B C H X1
  | ?X5 =>
      match constr:(X5) with
      | (S ?X1 ?X2 ?X3) =>
          match constr:(X1) with
          | A =>
              match constr:(X2) with
              | B => idtac
              | C => idtac
              | _ =>
                  match constr:(X3) with
                  | B => idtac
                  | C => idtac
                  | _ => freepoints_independant A B C H X1 X2 X3
                  end
              end
          | B =>
              match constr:(X2) with
              | A => idtac
              | _ =>
                  match constr:(X3) with
                  | A => idtac
                  | _ => freepoints_independant A B C H X1 X2 X3
                  end
              end
          | C =>
              match constr:(X2) with
              | A => idtac
              | _ =>
                  match constr:(X3) with
                  | A => idtac
                  | _ => freepoints_independant A B C H X1 X2 X3
                  end
              end
          | _ =>
              match constr:(X2) with
              | A =>
                  match constr:(X3) with
                  | C => idtac
                  | B => idtac
                  | _ => freepoints_independant A B C H X1 X2 X3
                  end
              | B =>
                  match constr:(X3) with
                  | A => idtac
                  | _ => freepoints_independant A B C H X1 X2 X3
                  end
              | C =>
                  match constr:(X3) with
                  | A => idtac
                  | _ => freepoints_independant A B C H X1 X2 X3
                  end
              | _ => freepoints_independant A B C H X1 X2 X3
              end
          end
      | _ => idtac
      end
  end.


Ltac only_use_area_coordinates :=
  unfold Det3,Col in *;
   match goal with
   | H:(S ?X1 ?X2 ?X3 <> 0) |- ?X4 =>
       (** If there are three non collinear points in the context we use them *)
       iter_coord_expr X1 X2 X3 H X4; unfold Det3 in *; basic_simpl;
        uniformize_signed_areas; basic_simpl
   | A:Point, B:Point, H:?A<>?B |- ?X4 =>
       (** Othewise we build a point which is not collinear to two existing points *)
       let T := fresh in 
       (assert (T:=(build_point_not_collinear_1 A B H));
       decompose [ex] T;clear T);only_use_area_coordinates  
    | A:Point |- ?X4 =>
       let T := fresh in 
       (assert (T:=(build_point_not_collinear_2 A));
       decompose [ex] T;clear T);only_use_area_coordinates  
   end.

(** A few tests *)

Lemma test_only_use_area_coordinates_1 : forall A B C D, S A B C <> 0 -> S D B C + S A D C  + S A B D = S A B C.
Proof.
intros.
only_use_area_coordinates.
uniformize_signed_areas.
field.
auto.
Qed.

Lemma test_only_use_area_coordinates_2 : forall A B C D,  A<> B -> S D B C + S A D C  + S A B D = S A B C.
Proof.
intros.
only_use_area_coordinates.
field.
auto.
Qed.

Lemma test_only_use_area_coordinates_3 : forall A B C D,   S D B C + S A D C  + S A B D = S A B C.
Proof.
intros.
only_use_area_coordinates.
field.
auto.
Qed.


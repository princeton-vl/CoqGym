(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Inductive capa : Set :=
  | Read : capa
  | Write : capa
  | Both : capa
  | Nil : capa.

Inductive capst : capa -> capa -> Prop :=
  | capst_refl : forall c : capa, capst c c
  | capst_nil : forall c : capa, capst c Nil
  | capst_both : forall c : capa, capst Both c.

Parameter type : Set.

Parameter getcap : type -> capa.

Parameter getobj : type -> type.

Parameter typest : type -> type -> Prop.

Axiom typest_refl : forall t : type, typest t t.

Axiom
  typest_trans :
    forall t t' : type,
    typest t t' -> forall t'' : type, typest t' t'' -> typest t t''.

Theorem capst_trans :
 forall c c' c'' : capa, capst c c' -> capst c' c'' -> capst c c''.
Proof.
intros c c' c''.
intro cst1.
case cst1.
intros; assumption.
intros k cst.
inversion_clear cst.
apply capst_nil.
apply capst_nil.
intros; apply capst_both.
Qed.

Parameter PP : Set.
Parameter VV : Set.

Axiom PP_decidable : forall p q : PP, {p = q} + {p <> q}.
Axiom VV_decidable : forall x y : VV, {x = y} + {x <> y}.

Inductive name : Set :=
  | pname : PP -> name
  | vname : VV -> name.

Inductive proc : Set :=
  | nil : proc
  | inp : name -> VV -> proc -> proc
  | out : name -> name -> proc -> proc
  | par : proc -> proc -> proc
  | res : VV -> type -> proc -> proc
  | ban : proc -> proc
  | sum : proc -> proc -> proc
  | mat : name -> name -> proc -> proc.

Definition subs_var_name (n m : name) (x : VV) : name :=
  match n with
  | pname p => n
  | vname v => match VV_decidable x v with
               | left _ => m
               | right _ => n
               end
  end.

Fixpoint subs_var_proc (P : proc) : name -> VV -> proc :=
  fun (n : name) (x : VV) =>
  match P with
  | nil => nil
  | inp m v qq =>
      inp (subs_var_name m n x) v
        match VV_decidable x v with
        | left _ => qq
        | right _ => subs_var_proc qq n x
        end
  | out m1 m2 qq =>
      out (subs_var_name m1 n x) (subs_var_name m2 n x)
        (subs_var_proc qq n x)
  | par qq rr => par (subs_var_proc qq n x) (subs_var_proc rr n x)
  | res v t qq =>
      res v t
        match VV_decidable x v with
        | left _ => qq
        | right _ => subs_var_proc qq n x
        end
  | ban qq => ban (subs_var_proc qq n x)
  | sum qq rr => sum (subs_var_proc qq n x) (subs_var_proc rr n x)
  | mat m1 m2 qq =>
      mat (subs_var_name m1 n x) (subs_var_name m2 n x)
        (subs_var_proc qq n x)
  end.


Definition subs_par_name (n m : name) (p : PP) : name :=
  match n with
  | pname q => match PP_decidable p q with
               | left _ => m
               | right _ => n
               end
  | vname v => n
  end.

Fixpoint subs_par_proc (P : proc) : name -> PP -> proc :=
  fun (n : name) (p : PP) =>
  match P with
  | nil => nil
  | inp m v qq => inp (subs_par_name m n p) v (subs_par_proc qq n p)
  | out m1 m2 qq =>
      out (subs_par_name m1 n p) (subs_par_name m2 n p)
        (subs_par_proc qq n p)
  | par qq rr => par (subs_par_proc qq n p) (subs_par_proc rr n p)
  | res v t qq => res v t (subs_par_proc qq n p)
  | ban qq => ban (subs_par_proc qq n p)
  | sum qq rr => sum (subs_par_proc qq n p) (subs_par_proc rr n p)
  | mat m1 m2 qq =>
      mat (subs_par_name m1 n p) (subs_par_name m2 n p)
        (subs_par_proc qq n p)
  end.

Inductive freshname (p : PP) : name -> Prop :=
  | freshp : forall q : PP, p <> q -> freshname p (pname q)
  | freshv : forall v : VV, freshname p (vname v).

Inductive fresh (p : PP) : proc -> Prop :=
  | frnil : fresh p nil
  | frinp :
      forall (m : name) (v : VV) (Q : proc),
      freshname p m -> fresh p Q -> fresh p (inp m v Q)
  | frout :
      forall (m1 m2 : name) (Q : proc),
      freshname p m1 -> freshname p m2 -> fresh p Q -> fresh p (out m1 m2 Q)
  | frpar : forall P Q : proc, fresh p P -> fresh p Q -> fresh p (par P Q)
  | frres :
      forall (v : VV) (t : type) (Q : proc), fresh p Q -> fresh p (res v t Q)
  | frban : forall Q : proc, fresh p Q -> fresh p (ban Q)
  | frsum : forall P Q : proc, fresh p P -> fresh p Q -> fresh p (sum P Q)
  | frmat :
      forall (m1 m2 : name) (Q : proc),
      freshname p m1 -> freshname p m2 -> fresh p Q -> fresh p (mat m1 m2 Q).

Inductive freshvarname (v : VV) : name -> Prop :=
  | freshvp : forall p : PP, freshvarname v (pname p)
  | freshvv : forall x : VV, v <> x -> freshvarname v (vname x).

Inductive freshvar (v : VV) : proc -> Prop :=
  | fvnil : freshvar v nil
  | fvinp :
      forall (m : name) (x : VV) (Q : proc),
      freshvarname v m -> v <> x -> freshvar v Q -> freshvar v (inp m x Q)
  | fvout :
      forall (m1 m2 : name) (Q : proc),
      freshvarname v m1 ->
      freshvarname v m2 -> freshvar v Q -> freshvar v (out m1 m2 Q)
  | fvpar :
      forall P Q : proc, freshvar v P -> freshvar v Q -> freshvar v (par P Q)
  | fvres :
      forall (x : VV) (t : type) (Q : proc),
      v <> x -> freshvar v Q -> freshvar v (res x t Q)
  | fvban : forall Q : proc, freshvar v Q -> freshvar v (ban Q)
  | fvsum :
      forall P Q : proc, freshvar v P -> freshvar v Q -> freshvar v (sum P Q)
  | fvmat :
      forall (m1 m2 : name) (Q : proc),
      freshvarname v m1 ->
      freshvarname v m2 -> freshvar v Q -> freshvar v (mat m1 m2 Q).

Inductive act : Set :=
  | aout : PP -> PP -> act
  | ainp : PP -> PP -> act
  | about : PP -> PP -> type -> act
  | tau : act.

Inductive freshact (p : PP) : act -> Prop :=
  | faout : forall q1 q2 : PP, p <> q1 -> p <> q2 -> freshact p (aout q1 q2)
  | fainp : forall q1 q2 : PP, p <> q1 -> p <> q2 -> freshact p (ainp q1 q2)
  | fabout :
      forall (q1 q2 : PP) (t : type),
      p <> q1 -> p <> q2 -> freshact p (about q1 q2 t)
  | ftau : freshact p tau.

Inductive sem : proc -> act -> proc -> Prop :=
  | sinp :
      forall (p q : PP) (x : VV) (Q : proc),
      sem (inp (pname p) x Q) (ainp p q) (subs_var_proc Q (pname q) x)
  | sout :
      forall (p q : PP) (Q : proc),
      sem (out (pname p) (pname q) Q) (aout p q) Q
  | scoml :
      forall (P P' Q Q' : proc) (p q : PP),
      sem P (ainp p q) P' ->
      sem Q (aout p q) Q' -> sem (par P Q) tau (par P' Q')
  | scomr :
      forall (P P' Q Q' : proc) (p q : PP),
      sem P (aout p q) P' ->
      sem Q (ainp p q) Q' -> sem (par P Q) tau (par P' Q')
  | sopen :
      forall (P P' : proc) (p q : PP) (x : VV) (t : type),
      fresh q P ->
      p <> q ->
      sem (subs_var_proc P (pname q) x) (aout p q) P' ->
      sem (res x t P) (about p q t) P'
  | sclosel :
      forall (P P' Q Q' : proc) (p q r : PP) (t : type) (x : VV),
      fresh q P ->
      freshvar x P' ->
      freshvar x Q' ->
      sem P (ainp p q) P' ->
      sem Q (about p r t) Q' ->
      sem (par P Q) tau
        (res x t
           (par (subs_par_proc P' (vname x) q) (subs_par_proc Q' (vname x) r)))
  | scloser :
      forall (P P' Q Q' : proc) (p q r : PP) (t : type) (x : VV),
      fresh q P ->
      freshvar x P' ->
      freshvar x Q' ->
      sem P (ainp p q) P' ->
      sem Q (about p r t) Q' ->
      sem (par Q P) tau
        (res x t
           (par (subs_par_proc Q' (vname x) r) (subs_par_proc P' (vname x) q)))
  | sres :
      forall (P P' : proc) (mu : act) (x y : VV) (t : type),
      (forall q : PP,
       sem (subs_var_proc P (pname q) x) mu (subs_var_proc P' (pname q) y)) ->
      sem (res x t P) mu (res y t P')
  | sban :
      forall (P P' : proc) (mu : act),
      sem (par (ban P) P) mu P' -> sem (ban P) mu P'
  | sparl :
      forall (P P' Q : proc) (mu : act),
      (forall (p q : PP) (t : type), mu = about p q t -> fresh q Q) ->
      sem P mu P' -> sem (par P Q) mu (par P' Q)
  | sparr :
      forall (P P' Q : proc) (mu : act),
      (forall (p q : PP) (t : type), mu = about p q t -> fresh q Q) ->
      sem P mu P' -> sem (par Q P) mu (par Q P')
  | ssuml :
      forall (P P' Q : proc) (mu : act), sem P mu P' -> sem (sum P Q) mu P'
  | ssumr :
      forall (P P' Q : proc) (mu : act), sem P mu P' -> sem (sum Q P) mu P'
  | smat :
      forall (P P' : proc) (p : PP) (mu : act),
      sem P mu P' -> sem (mat (pname p) (pname p) P) mu P'.

Definition env : Type := PP -> type.

Definition addenv (G : env) (p : PP) (t : type) : env :=
  fun q : PP =>
  match PP_decidable p q with
  | left _ => t
  | right _ => G q
  end.

Definition envst (G D : env) : Prop := forall p : PP, typest (G p) (D p).

Definition eqvenv (G D : env) : Prop := forall p : PP, G p = D p.

Inductive typing : env -> proc -> Prop :=
  | tnil : forall G : env, typing G nil
  | tinp :
      forall (G : env) (p : PP) (x : VV) (P : proc),
      capst (getcap (G p)) Read ->
      (forall q : PP,
       fresh q P ->
       typing (addenv G q (getobj (G p))) (subs_var_proc P (pname q) x)) ->
      typing G (inp (pname p) x P)
  | tout :
      forall (G : env) (p q : PP) (P : proc),
      capst (getcap (G p)) Write ->
      typest (G q) (getobj (G p)) ->
      typing G P -> typing G (out (pname p) (pname q) P)
  | tpar :
      forall (G : env) (P Q : proc),
      typing G P -> typing G Q -> typing G (par P Q)
  | tres :
      forall (G : env) (x : VV) (t : type) (P : proc),
      (forall q : PP,
       fresh q P -> typing (addenv G q t) (subs_var_proc P (pname q) x)) ->
      typing G (res x t P)
  | tban : forall (G : env) (P : proc), typing G P -> typing G (ban P)
  | tsum :
      forall (G : env) (P Q : proc),
      typing G P -> typing G Q -> typing G (sum P Q)
  | tmat :
      forall (G : env) (p q : PP) (P : proc),
      getcap (G p) = Both ->
      getcap (G q) = Both ->
      typing G P -> typing G (mat (pname p) (pname q) P).

Definition swap_par (r p q : PP) : PP :=
  match PP_decidable r p with
  | left _ => q
  | right _ => match PP_decidable r q with
               | left _ => p
               | right _ => r
               end
  end.

Definition swap_name (n : name) (p q : PP) : name :=
  match n with
  | pname r =>
      match PP_decidable r p with
      | left _ => pname q
      | right _ =>
          match PP_decidable r q with
          | left _ => pname p
          | right _ => pname r
          end
      end
  | vname x => vname x
  end.

Fixpoint swap_proc (P : proc) : PP -> PP -> proc :=
  fun p q : PP =>
  match P with
  | inp n x p1 => inp (swap_name n p q) x (swap_proc p1 p q)
  | out n1 n2 p1 =>
      out (swap_name n1 p q) (swap_name n2 p q) (swap_proc p1 p q)
  | res x t p1 => res x t (swap_proc p1 p q)
  | par p1 p2 => par (swap_proc p1 p q) (swap_proc p2 p q)
  | ban p1 => ban (swap_proc p1 p q)
  | sum p1 p2 => sum (swap_proc p1 p q) (swap_proc p2 p q)
  | mat n1 n2 p1 =>
      mat (swap_name n1 p q) (swap_name n2 p q) (swap_proc p1 p q)
  | nil => nil
  end.

Definition swap_env (G : env) (p q : PP) : env :=
  fun r : PP =>
  match PP_decidable p r with
  | left _ => G q
  | right _ =>
      match PP_decidable q r with
      | left _ => G p
      | right _ => G r
      end
  end.
         
Axiom different : forall p : PP, exists s : PP, p <> s.

Axiom
  fresh_and_different :
    forall (p : PP) (P : proc), exists r : PP, fresh r P /\ p <> r.

Axiom
  fresh_and_two_different :
    forall (p q : PP) (P : proc),
    exists r : PP, fresh r P /\ p <> r /\ q <> r.

Axiom
  fresh_and_three_different :
    forall (p q r : PP) (P : proc),
    exists s : PP, fresh s P /\ p <> s /\ q <> s /\ r <> s.


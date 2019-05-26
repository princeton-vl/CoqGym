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


(* MACHINE *)

(* description de la machine *)

Require Import List.
Require Export fifo.
Require Export table.

Unset Standard Proposition Elimination Names.

Section MACHINE.

(* l'ensemble des sites avec un privilegie l'owner *)

Parameter Site : Set. 
 
Parameter owner : Site.

Axiom eq_site_dec : eq_dec Site. 

Definition change_site (E : Set) := change_x0 Site E eq_site_dec.

Lemma that_site :
 forall (E : Set) (f : Site -> E) (s0 : Site) (x : E),
 change_site E f s0 x s0 = x.
Proof.
 intros; unfold change_site in |- *; apply here.
Qed.

Lemma other_site :
 forall (E : Set) (f : Site -> E) (s0 s1 : Site) (x : E),
 s0 <> s1 -> change_site E f s0 x s1 = f s1.
Proof.
 intros; unfold change_site in |- *; apply elsewhere; trivial.
Qed.

(* les couples de sites correspondent aux files d'attente *)

Definition eq_queue_dec := eq_couple_dec Site Site eq_site_dec eq_site_dec.

Definition change_queue (Q : Set) :=
  change_x0y0 Site Site Q eq_site_dec eq_site_dec.

Lemma that_queue :
 forall (E : Set) (f : Site -> Site -> E) (s0 s1 : Site) (x : E),
 change_queue E f s0 s1 x s0 s1 = x.
Proof.
 intros; unfold change_queue in |- *; apply here2.
Qed.

Lemma other_queue :
 forall (E : Set) (f : Site -> Site -> E) (s0 s1 s2 s3 : Site) (x : E),
 s2 <> s0 \/ s3 <> s1 -> change_queue E f s0 s1 x s2 s3 = f s2 s3.
Proof.
 intros; unfold change_queue in |- *; apply elsewhere2; trivial.
Qed.

(* l'ensemble des sites est fini, la liste des sites sert a parcourir
et \`a sommer sur l'ensemble des sites *)

Parameter LS : list Site.

Axiom finite_site : list_of_elements Site eq_site_dec LS.

Lemma in_s_LS : forall s : Site, In s LS.
Proof.
 intros; apply only_once_in with (eq_E_dec := eq_site_dec);
  exact (finite_site s).
Qed.

End MACHINE.

Section MESSAGES.

(* il y a trois sortes de messages *)
	
Inductive Message : Set :=
  | dec : Message
  | inc_dec : Site -> Message
  | copy : Message.

Theorem eq_message_dec : eq_dec Message.
Proof.
 unfold eq_dec in |- *; double induction a b; intros.
 auto.

 right; discriminate.

 right; discriminate.

 right; discriminate.

 case (eq_site_dec s0 s); intros.
 rewrite e; auto.

 right; injection; auto.

 right; discriminate.

 right; discriminate.

 right; discriminate.

 auto.
Qed.

End MESSAGES.

Section TABLES.

(* la vision en table est globale sur l'ensemble des sites, on peut
aussi la voir distribuee chaque site etant proprietaire de son entree
*)

Definition Date_table := Site -> nat.

Definition Send_table := Site -> Z.

Definition Rec_table := Site -> bool.

End TABLES.

Section BAG.

(* l'ensemble des messages est distribue sur les files d'attente, ceci
pour respecter la contrainte que les messages entre deux sites sont
recus dans l'ordre dans lequel ils sont emis *)
 
Definition Bag_of_message := Site -> Site -> queue Message.

Definition card_mess (m : Message) (q : queue Message) :=
  card Message eq_message_dec m q.

Lemma pos_card_mess :
 forall (m : Message) (q : queue Message), (card_mess m q >= 0)%Z.
Proof.
 intros; unfold card_mess in |- *; apply card_pos.
Qed.

Lemma strct_pos_card_mess :
 forall (m : Message) (q : queue Message),
 In_queue Message m q -> (card_mess m q > 0)%Z.
Proof.
 intros; unfold card_mess in |- *; apply card_strct_pos; trivial.
Qed.

Lemma diff_or_elsewhere :
 forall (m m' : Message) (bom : Bag_of_message) (s1 s2 s3 s4 : Site),
 first Message (bom s3 s4) = value Message m ->
 m <> m' ->
 first Message (bom s1 s2) <> value Message m' \/ s1 <> s3 \/ s2 <> s4.
Proof.
 intros; case (eq_queue_dec s1 s3 s2 s4); intro.
 decompose [and] a; rewrite H1; rewrite H2; rewrite H; left; injection; auto.

 auto.
Qed.

End BAG.

Section CONFIGURATION.

(* une configuration est un etat de la machine a un instant donne,
bien qu'il n'y ait pas d'horloge globale ou plus exactement que les
transitions ne soient pas deterministes, la variable time permet
d'ordonner les transitions et donc de dater le dernier positionnement
du drapeau rt sur chaque site *)

Definition access (s : Site) (rt : Rec_table) := s = owner \/ rt s = true.		

Record Config : Set := mkconfig
  {time : nat;
   dt : Date_table;
   st : Send_table;
   rt : Rec_table;
   bm : Bag_of_message}.
	
End CONFIGURATION.

Section ALT_DEF.

(* la nature de la file d'attente entre un site et l'owner est
particuliere. C'est une alternance de messages dec et inc_dec dans
laquelle les messages inc_dec sont isoles. De plus l'information
pernmettant de savoir qu'une file est vide ou commence par un message
dec est utile car elle est caracteristique d'un site ayant son drapeau
rt non positionne *)

Inductive D_queue : queue Message -> Prop :=
  | D_empty : D_queue (empty Message)
  | D_dec : forall qm : queue Message, D_queue (input Message dec qm).

Inductive alternate : queue Message -> Prop :=
  | alt_null : alternate (empty Message)
  | alt_single_inc :
      forall s0 : Site,
      alternate (input Message (inc_dec s0) (empty Message))
  | alt_dec_alt :
      forall qm : queue Message,
      alternate qm -> alternate (input Message dec qm)
  | alt_inc_dec :
      forall (qm : queue Message) (s0 : Site),
      alternate qm ->
      alternate (input Message (inc_dec s0) (input Message dec qm)).

Lemma not_D_queue :
 forall (q0 : queue Message) (s0 : Site),
 ~ D_queue (input Message (inc_dec s0) q0).
Proof.
 intros; red in |- *; intro.
 inversion H.
Qed.
	
Lemma D_first_out :
 forall q0 : queue Message, D_queue q0 -> D_queue (first_out Message q0).
Proof.
 intros; elim H; simpl in |- *.
 apply D_empty.

 simple destruct qm.
 apply D_empty.

 intros; apply D_dec.
Qed.
	
Lemma alt_first_out :
 forall q0 : queue Message, alternate q0 -> alternate (first_out Message q0).
Proof.
 intros; elim H; simpl in |- *.
 apply alt_null.

 intro; apply alt_null.
 
 simple induction qm; intros.
 apply alt_null.

 apply alt_dec_alt; trivial.

 simple induction qm; intros.
 apply alt_single_inc.

 apply alt_inc_dec; trivial.
Qed.

End ALT_DEF.

Section RELAT_DEF.

(* la relation de parentee entre deux sites est definie par le fait
que le site fils possede dans sa file d'attente en direction de
l'owner, un message inc_dec relatif au site pere. Cette relation
traduit le fait que le fils a ete positionne (rt actif) par un message
copy venant du pere. Cette relation est provisoire, elle disparait
lorsque l'owner lit le message inc_dec. Cette relation est croissante
avec le temps time d'ou l'utilite des champs time et date. En fait, on
peut montrer directement que cette relation est sans cycle, il reste a
admettre ou prouver qu'une relation sans cycle sur un ensemble fini
est bien fondee pour pouvoir se passer des champs time et date *)

Variable c0 : Config.

Inductive parent : Site -> Site -> Prop :=
    parent_intro :
      forall s1 s0 : Site,
      In_queue Message (inc_dec s1) (bm c0 s0 owner) -> parent s1 s0.

Inductive ancestor : Site -> Site -> Prop :=
  | short : forall s1 s0 : Site, parent s1 s0 -> ancestor s1 s0
  | long :
      forall s2 s1 s0 : Site,
      parent s2 s1 -> ancestor s1 s0 -> ancestor s2 s0.

End RELAT_DEF.


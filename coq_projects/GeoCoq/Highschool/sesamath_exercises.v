Require Export GeoCoq.Highschool.triangles.
Require Export GeoCoq.Highschool.circumcenter.
Require Export GeoCoq.Highschool.gravityCenter.

(** In this file we give as example the proof of some exercises given in
french high-school at 8th Grade (quatrième).
The exercise is taken from 
http://mep-outils.sesamath.net/manuel_numerique/index.php?ouvrage=ms4_2011&page_gauche=169
 *)


(** #
<script type="text/javascript" src="https://www.geogebra.org/scripts/deployggb.js"></script>
<script type="text/javascript">
    var applet35 = new GGBApplet({material_id: "xXKV5j7J"}, true);
    var applet36 = new GGBApplet({material_id: "Pp4K9rkb"}, true);
    var applet37 = new GGBApplet({material_id: "pgjEKRMd"}, true);
    var applet38 = new GGBApplet({material_id: "rkDYJXyK"}, true);
    var applet39 = new GGBApplet({material_id: "wPE3EwBr"}, true);
    var applet40 = new GGBApplet({material_id: "FJ859DxG"}, true);
    var applet41 = new GGBApplet({material_id: "mPTQra6U"}, true);
    var applet42 = new GGBApplet({material_id: "d8PwNtGa"}, true);
    var applet44 = new GGBApplet({material_id: "N9SyfPGd"}, true);
    var applet45 = new GGBApplet({material_id: "dFfwvBut"}, true);
    var applet46 = new GGBApplet({material_id: "yV7nKC8E"}, true);
    var applet47 = new GGBApplet({material_id: "eKuUrjFE"}, true);
    var applet48 = new GGBApplet({material_id: "yV7nKC8E"}, true);
    var applet49 = new GGBApplet({material_id: "t2QJ3xbF"}, true);
    var applet50 = new GGBApplet({material_id: "WdJ6GvzE"}, true);
    var applet52 = new GGBApplet({material_id: "rAdHpavY"}, true);

 window.onload = function() {
        applet35.inject('applet_container35', 'preferHTML5');
        applet36.inject('applet_container36', 'preferHTML5');
        applet37.inject('applet_container37', 'preferHTML5');
        applet38.inject('applet_container38', 'preferHTML5');
        applet39.inject('applet_container39', 'preferHTML5');
        applet40.inject('applet_container40', 'preferHTML5');
        applet41.inject('applet_container41', 'preferHTML5');
        applet42.inject('applet_container42', 'preferHTML5');
        applet44.inject('applet_container44', 'preferHTML5');
        applet45.inject('applet_container45', 'preferHTML5');
        applet46.inject('applet_container46', 'preferHTML5');
        applet47.inject('applet_container47', 'preferHTML5');
        applet48.inject('applet_container48', 'preferHTML5');
        applet49.inject('applet_container49', 'preferHTML5');
        applet50.inject('applet_container50', 'preferHTML5');
        applet52.inject('applet_container52', 'preferHTML5');

 } </script>
# **)





Section Exercices.

Context `{TE:Tarski_euclidean}.


(**
Exercice 35 : Dans un triangle rectangle
a. GAZ est un triangle rectangle en A. Les points F, E et R sont
les milieux respectifs de [AZ], [GZ] et [GA]. Fais une figure.
b. Quelle est la nature du quadrilatère FERA ?
Prouve-le.
*)

	(** # <div style="width:748px;height:397px;display:block" id="applet_container35"></div> # **)

Lemma sesamath_4ieme_G2_ex35 : 
 forall G A Z F E R,
 ~ Col G A Z ->
 Per G A Z ->
 Midpoint F A Z ->
 Midpoint E G Z ->
 Midpoint R G A ->
 Rectangle F E R A.
Proof.
intros G A Z F E R HnCol HPER HM1 HM2 HM3.
assert_diffs.
assert_cols.
assert (Par A Z E R)
 by (perm_apply (triangle_mid_par Z A G R E);finish).
assert (Par A G F E)
 by perm_apply (triangle_mid_par A G Z E F).
assert (Par A F E R)
 by (apply par_col_par_2 with Z;finish).
assert (Par A R E F)
 by (apply par_col_par_2 with G;finish;Par).
assert (~Col A R F)
  by (intro;apply HnCol;ColR).
assert (Par_strict A R E F)
 by (apply par_not_col_strict with F;finish).
assert (Plg F E R A)
  by (apply pars_par_plg;finish;Par).
assert (Per F A R)
 by (apply col_col_per_per with Z G;finish).
apply (plg_per_rect);auto.
Qed.

(**
Exercice 36 : Dans un triangle isocèle
ABC est un triangle isocèle en A. [AH] est la hauteur issue de A.
Les points I et J sont les milieux respectifs de [AB] et [AC].

Quelle est la nature de AIHJ ?
*)

(** A first solution using the fact that A I H J is a parallelogram whose
   diagonals are perpendicular *)

(** # <div style="width:448px;height:397px;display:block" id="applet_container36"></div> # **)

Lemma sesamath_4ieme_G2_ex36_aux :
 forall A B C I J K,
 ~ Col A B C ->
 Midpoint I A B ->
 Midpoint J A C ->
 Midpoint K B C ->
 Plg I J K B.
Proof.
intros.
assert_diffs.
assert (Par A B J K)
 by (perm_apply (triangle_mid_par B A C J K);finish).
assert (Par B I J K)
 by (apply par_col_par_2 with A;finish).
assert (Par B C I J)
 by (perm_apply (triangle_mid_par B C A J I);finish).
assert (Par B K I J)
 by (apply par_col_par_2 with C;finish).
assert (~ Col B K J)
  by (intro;apply H;ColR).
assert (Par_strict B K I J)
 by (apply par_not_col_strict with J;finish).
assert (Plg I J K B)
 by  (apply pars_par_plg;finish).
assumption.
Qed.

Lemma sesamath_4ieme_G2_ex36 :
 forall A B C H I J,
 isosceles B A C -> 
 Perp A H B C ->
 Col B H C ->
 Midpoint I A B ->
 Midpoint J A C ->
 Rhombus A I H J.
Proof.
intros.
assert_diffs.
assert_cols.
assert (~ Col B A C /\
       B <> H /\ C <> H /\ Midpoint H B C /\ CongA H A B H A C)
 by (apply (isosceles_foot__midpoint_conga B A C );finish).
spliter.
assert (Plg A I H J).
 {
 assert (Plg J H I A).
  apply (sesamath_4ieme_G2_ex36_aux C A B J H I);finish.
 apply parallelogram_to_plg. (* todo simplify plg vs parallelogram *)
 apply plg_to_parallelogram in H14.
 apply Plg_perm in H14.
 spliter;auto.
 }
assert (Par I J B C)
  by (perm_apply (triangle_mid_par B C A J I);finish).
assert (Perp A H I J)
  by (perm_apply (cop_par_perp__perp B C I J A H)).
apply perp_rmb;finish.
Qed.

(**
Exercice 37 : Avec une médiatrice
SEL est un triangle quelconque. Les points I, M et A sont les milieux respectifs
de [LS], [SE] et [EL]. La médiatrice de [LE] coupe la droite (IM) en O.
a. Fais une figure.
b. Que représente (AO) pour le triangle IMA?
Prouve-le.
*)

	(** # <div style="width:748px;height:397px;display:block" id="applet_container37"></div> # **)

Lemma sesamath_4ieme_G2_ex37 :
forall S E L I M A O,
~Col S E L ->
Midpoint I L S ->
Midpoint M S E ->
Midpoint A E L ->
Perp_bisect A O L E ->
Coplanar S E L O ->
Perp A O I M.
Proof.
intros.
assert_diffs.
assert_cols.
assert (Par L E I M) 
  by (perm_apply (triangle_mid_par L E S M I);finish).
assert (Perp A O L E)
  by(apply(perp_bisect_perp A O L E);finish).
assert (Perp I M O A).
  apply(cop_par_perp__perp L E I M O A);Perp.
  apply coplanar_pseudo_trans with S E L; Cop.
assert (Perp A O I M);finish.
Qed.

(**
Exercice 38 avec une médiane
a. Construis un triangle EAU quelconque.
b. Construis la médiane [EL].
Place N milieu de [AE] et M milieu de [EU].
O est le point d'intersection de (EL) et de (MN).
c. Est-il vrai que (OL) est une médiane du triangle LMN ?
Justifie ta réponse.
*)

	(** # <div style="width:748px;height:397px;display:block" id="applet_container38"></div> # **)

Lemma sesamath_4ieme_G2_ex38 :
forall E A U M N L,
~ Col E A U ->
Midpoint N E A ->
Midpoint M E U ->
Midpoint L U A ->
exists O : Tpoint, Col O E L /\ Midpoint O M N.
Proof.
intros.
assert_diffs.
assert_cols.
assert( ~Col U E A);finish.
assert (Plg M L N E)
  by (apply (sesamath_4ieme_G2_ex36_aux U E A M L N);finish).
assert (Parallelogram M L N E)
  by (apply(plg_to_parallelogram M L N E);finish).
assert (exists X, Midpoint X M N /\ Midpoint X L E)
  by (apply plg_mid;finish).
destruct H18 as [X [HX HX2]].
exists X.
assert_cols;split;finish.
Qed.

(** Exercice 39 Dans un demi-cercle
Sur la figure ci-dessous, le point A appartient au cercle de diamètre [CT]
et de centre S.
Les droites (HS) et (CA) sont perpendiculaires.
- Montre que H est le milieu du segment [CA].
*)

	(** # <div style="width:748px;height:397px;display:block" id="applet_container39"></div> # **)

Lemma sesamath_4ieme_G2_ex39:
forall S C T H A,
~Col A C T ->
is_circumcenter S C T A->
Midpoint S C T ->
Col C H A ->
Perp S H A C ->
Midpoint H A C.
Proof.
intros.
assert_diffs.
assert_cols.
assert (Cong C S T S /\ Cong T S A S /\ Cong A S C S)
  by ( apply(circumcenter_cong S C T A);finish).
spliter.
assert(Per C A T)
  by (perm_apply(midpoint_thales S C T A);finish).
assert(Perp T A A C)
  by (perm_apply(per_perp T A C);finish).
assert(Par S H T A)
  by (perm_apply(l12_9 S H T A A C);finish).
assert(Midpoint H A C)
  by (perm_apply(triangle_par_mid A T C S H);finish).
assumption.
Qed.

(**
Exercice 40 : ABC est un triangle quelconque. R est un point de [BC]. On appelle S, T,
M et N les milieux respectifs de [BR], [RC], [AB] et [AC].
a- Montre que (NT) est parallèle à (MS).
b- Montre que MNTS est un parallélogramme.
*)


	(** # <div style="width:748px;height:397px;display:block" id="applet_container40"></div> # **)


Lemma sesamath_4ieme_G2_ex40 :
forall A B C M R N S T,
~Col A B C ->
Bet C R B ->
Midpoint M A B ->
Midpoint N A C ->
Midpoint S B R ->
Midpoint T R C ->
Par M S N T /\ Parallelogram M S T N.
Proof.
intros.
assert_diffs.
assert_cols.
assert_all_diffs_by_contradiction.
(*
assert (R<>A)
 by (intro;treat_equalities;apply H;finish). *)
assert (Par A R M S)
 by (perm_apply (triangle_mid_par A R B S M);finish).
assert (Par A R N T)
 by (perm_apply (triangle_mid_par A R C T N);finish).
assert(Par M S N T)
 by (perm_apply(par_trans M S A R);finish).
split.
assumption.
assert(Par C B N M)
 by (perm_apply (triangle_mid_par B C A N M);finish).

destruct (eq_dec_points R B).
{
treat_equalities.
assert(Plg M N T S)
 by(apply(sesamath_4ieme_G2_ex36_aux A S C M N T);finish).
assert(Parallelogram M N T S)
 by(apply(plg_to_parallelogram M N T S);finish).
apply(Plg_perm M N T S);finish. (* todo improve finish *)
}
destruct (eq_dec_points R C).
{
treat_equalities.
assert(Plg N M S T)
 by(apply(sesamath_4ieme_G2_ex36_aux A T B N M S);finish).
assert(Parallelogram N M S T)
 by(apply(plg_to_parallelogram N M S T);finish).
apply(Plg_perm N M S T);finish.
}
assert_all_diffs_by_contradiction.

assert(Par M N B R)
 by(apply(par_col_par M N B C R);finish).
assert(Par M N R S)
 by(apply(par_col_par M N R B S);finish).
assert(Par M N S T)
 by(apply(par_col_par M N S R T);finish;ColR).
assert (~Col M S T)
  by (intro;apply H;ColR).
apply(par_2_plg);finish.
Qed.

(**
Exercice 41 :
Sur la figure suivante, THL est un triangle quelconque, O est le milieu
du segment [TH], E celui de [TL] et S est un point de [HL].
a- Montre que les angles SAE et TSH ont la même mesure.
b- Montre que A est le milieu de [TS].
*)
	(** # <div style="width:748px;height:397px;display:block" id="applet_container41"></div> # **)

Lemma sesamath_4ieme_G2_ex41 :
forall (T L H O E S A: Tpoint) (a b : Tpoint ->Tpoint ->Tpoint -> Prop),
~ Col T L H ->
Midpoint E T L ->
Midpoint O T H ->
A <> T ->
A <> O ->
A <> E ->
A <> S ->
Bet T A S ->
Bet O A E ->
Bet H S L ->
S <> H ->
S <> L ->
CongA S A E T S H /\ Midpoint A T S.
Proof.
intros.
assert_diffs.
assert_cols.
assert(OS H L T T)
  by (apply(one_side_reflexivity H L T);finish).
assert(OS H S T T)
  by(apply(col_one_side H L S T T);finish).
assert(~ Col H S T)
  by(apply(one_side_not_col123 H S T T);finish).
assert( OS T S H H)
  by(apply(one_side_reflexivity T S H);finish).
assert(OS T A H H)
  by(apply(col_one_side T S A H H);finish).
assert(Bet T O H)
  by(apply(midpoint_bet T O H);finish).
assert(Out T O H)
  by(apply(bet_out T O H);finish).
assert(Out T H O)
  by(apply(l6_6 T O H);finish).
assert(OS T A H O)
  by(apply(out_out_one_side T A H H O);finish).
assert(OS T A O H)
  by(apply(one_side_symmetry T A H O);finish).
assert(Par H L O E)
  by(apply(triangle_mid_par H L T E O);finish).
assert(Par H L O A)
  by(apply(par_col_par H L O E A);finish).
assert(Par H S O A)
  by(apply(par_col_par_2 H L O A S);finish).
assert(Out T A S)
  by(apply(bet_out T A S);finish).
assert(CongA O A T H S T)
  by(apply(l12_22_a A O S H T);finish).
assert(CongA O A T E A S)
  by(apply(l11_14 O A T E S);finish).
assert(CongA H S T E A S)
  by(apply(conga_trans H S T O A T E A S);finish).
assert(Midpoint A S T)
  by(apply(triangle_par_mid S H T O A);finish).
split;finish.
Qed.

(**
Exercice 42 :
ABC est un triangle quelconque. [BI] et [CJ] sont deux médianes, elles se coupent en G.
On désigne par K le milieu de [BG] et L celui de [CG].
a- Quelle est la nature du quadrilatère IJKL ?
Prouve-le.
b- Que peut-on dire de la position du point G sur chacune des médiane [BI] et [CJ]?
*)

	(** # <div style="width:748px;height:397px;display:block" id="applet_container42"></div> # **)
Lemma sesamath_4ieme_G2_ex42 :
forall A B C I K L J G,
~Col A B C ->
is_gravity_center G A B C ->
Midpoint I A C ->
Midpoint J A B ->
Midpoint K B G ->
Midpoint L C G ->
Parallelogram I J K L.
Proof.
intros.
assert_diffs.
assert_cols.
assert (G<>A)
  by (apply(is_gravity_center_diff_1 A B C G);finish). (* todo improve assert_diffs *)
assert (Par B C K L)
  by(apply(triangle_mid_par B C G L K);finish).
assert (G<>C)
  by (apply(is_gravity_center_diff_3 A B C G);finish).
assert_diffs.
assert (Midpoint J B A)
  by(apply(l7_2 J A B);finish).
assert(is_gravity_center G C B A)
  by(apply(is_gravity_center_perm_5 A B C G);finish). (* todo improve finish to include permutations of gravity center *)
assert(Midpoint G J L)
  by(apply(is_gravity_center_third C B A G L J);finish).
assert_diffs.
assert(Parallelogram I L K J)
  by(apply(varignon.varignon_aux_aux A C G B I L K J);finish).
apply(Plg_perm I L K J);finish. (* todo improve finish to include permuations of Plg and other quadrilaterals *)
Qed.

(**
Exercice 44 :
ABCD est un parallélogramme. I est le milieu de [AD] et J le milieu de [BC].
a- Démontre que BJDI est un parallélogramme.
b- Est-il vrai que les droites (BI) et (DJ) divisent la diagonale [AC] en trois parties égales ?
Justifie ta réponse (ce problème est posé par Euclide dans le Livre III de sas "Eléments").
*)
	(** # <div style="width:748px;height:397px;display:block" id="applet_container44"></div> # **)

Lemma sesamath_4ieme_G2_ex44_1 :
forall A B C D I J E F,

Parallelogram_strict A B C D ->
Midpoint I A D ->
Midpoint J B C ->
Bet A E C ->
Bet I E B ->
Bet A F C ->
Bet D F J ->
Parallelogram B J D I.
Proof.
intros.
assert_diffs.
assert_cols.
assert_ncols.
apply (Parallelogram_strict_Parallelogram A B C D) in H.
assert(Par A D B C)
  by (apply(plg_par_2 A B C D);finish).
assert(Cong A D B C)
  by (apply(plg_cong_2 A B C D);finish).
assert(Cong D I B J)
  by (apply(cong_cong_half_2 A I D C J B);finish).
assert(Par A D B J)
  by (apply(par_col_par A D B C);finish).
assert(Par D I B J)
  by (apply(par_col_par_2 D A B J);finish).
assert(exists M : Tpoint, Midpoint M A C /\ Midpoint M B D)
  by (apply(plg_mid A B C D);finish).
destruct H31.
spliter.
assert(Par D C I x)
  by(apply(triangle_mid_par D C A x I);finish).
assert(Par A B x J)
  by(apply(triangle_mid_par A B C J x);finish).
assert(Par A B C D)
  by (apply(plg_par_1 A B C D);finish).
assert(Par D C x J)
  by(apply(par_trans D C A B x J);finish).
assert(Par x J I x)
  by(apply(par_trans x J D C I x);finish).
assert(Col x J I) 
  by (apply (par_id x J I);finish).
show_distinct I J.
{
 assert(~Par A D C B).  (apply(inter_uniqueness_not_par A D C B I);finish).
 assert (Par A D C B);finish.
}
destruct (midpoint_existence A B) as  [x0 Hx0].
destruct (midpoint_existence D C) as  [x1 Hx1].
assert(Par A B J x /\ Cong A x0 J x)
  by(apply(triangle_mid_par_cong_1 C A B x0 J x);finish).
assert(Par B A I x /\ Cong B x0 I x)
  by(apply(triangle_mid_par_cong_1 D B A x0 I x);finish).
spliter.
assert(Cong A x0 I x)
  by(apply(cong_transitivity A x0 x0 B I x);finish).
assert( Cong I x J x)
  by(apply(cong_transitivity I x A x0 J x);finish).
assert(Midpoint x I J)
  by(apply(l7_20_bis x I J);finish).
apply (mid_plg B J D I x);finish.
Qed.


(**
Exercice 45 :
ABC est un triangle quelconque.
- I est le milieu de [BC].
- M est le symétrique de I par rapport au point A.
- J est le milieu de [AI].

La parallèle à (AC) passent par J coupe (BC) en K.
a- Démontre que K est le milieu de [IC].
b- Démontre que les droites (AK) et (MC) sont parallèles.
c- Que représente le point d'intersection des droites (CA) et (MK) pour le triangle MIC?
*) 
	(** # <div style="width:748px;height:397px;display:block" id="applet_container45"></div> # **)

Lemma sesamath_4ieme_G2_ex45 :
forall A B C I K J M G,
~ Col A B C ->
Midpoint I B C ->
Col I A M ->
Midpoint A I M ->
Midpoint J A I ->
Par J K A C ->
Col K I C ->
Col G C A /\ Col G M K ->
Midpoint K I C /\ Par A K M C /\ is_gravity_center G C M I.
Proof.
intros.
assert_diffs.
assert_cols.
assert (~ Col C I A)
  by (intro;apply H;ColR).
spliter.
split.
assert(Midpoint K C I).
  (apply(triangle_par_mid C A I J K);finish).
finish.
destruct (eq_dec_points I M).
{
treat_equalities.
intuition.
}
assert (~ Col I M C)
  by (intro;apply H14;ColR).
assert_diffs.
assert(Midpoint K C I).
 (apply(triangle_par_mid C A I J K);finish).
split.
assert(Par M C A K)
  by(apply(triangle_mid_par M C I K A);finish).
Par.
exists.
assert(~ Col C M I);finish.
exists A.
exists K.
split.
assert(Midpoint A M I);finish.
repeat split;finish.
Qed.

(**
Exercice 47 :
Sur une droite (d), on considère trois points A, B et C tels que B soit le milieu de [AC].
Sur une droite (d'), on considère un point A'.
B' est le point d'intersection de (d') et de la parallèle à (AA') passant par B.
C' est le point d'intersection de (d') et de la parallèle à (AA') passant par C.
a- Construis cette figure.
b- Que dire de B'? Prouve-le.
*)
	(** # <div style="width:748px;height:397px;display:block" id="applet_container47"></div> # **)

Lemma sesamath_4ieme_G2_ex47 :
forall A B C A' B' C',
~Col A C C' ->
~Col A A' C'->
Col B' A' C' ->
Midpoint B A C->
Par A A' B B' ->
Par A A' C C' ->
Midpoint B' A' C'.
Proof.
intros.
assert_diffs.
assert_cols.
destruct (midpoint_existence A C') as [x Hx].
assert_cols.
assert(Par B B' A A');finish.
assert(Par B B' C C')
  by(apply(par_trans B B' A A' C C');finish;Par).
assert(Par C C' B x)
  by(apply(triangle_mid_par C C' A x B);finish).
assert(Par B B' B x)
  by(apply(par_trans B B' C C' B x);finish).
assert(Col B B' x)
  by(apply(par_id B B' x);finish).
assert( Par A A' B x)
  by(apply(par_trans A A' B B' B x);finish).
assert_diffs.
assert(x=B'\/x<>B')
  by(apply(eq_dec_points x B');finish).
destruct H14.
destruct H14.
assert(Col A C' A')
  by(apply(l6_16_1 C' x A' A);finish;Par).
destruct H0.
assert(Col A A' C');finish.
assert(Par B x B' B);finish.
assert(Par B x B' x)
  by(apply(par_col_par B x B' B x);finish).
assert( Par A A' B' x)
  by(apply(par_trans A A' B x B' x);finish).
assert(Midpoint B' A' C')
  by(apply(triangle_par_mid A' A C' x B');finish).
assumption.
Qed.

End Exercices.
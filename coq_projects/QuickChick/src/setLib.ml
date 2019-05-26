open GenericLib

let set_singleton (c : coq_expr) : coq_expr = gApp (gInject "set1") [c]
let set_empty : coq_expr = gInject "set0"
let set_full : coq_expr = gInject "setT"

let set_bigcup (x : string) (p : coq_expr) (c : var -> coq_expr) : coq_expr =
  gApp (gInject "bigcup") [p; gFun [x] (fun [x] -> c x)]

let set_suchThat (x : string) (t : coq_expr) (p : var -> coq_expr) : coq_expr =
  gFunTyped [("x", t)] (fun [x] -> p x)

let set_eq c1 c2 = gApp (gInject "set_eq") [c1;c2]

let set_incl c1 c2 = gApp (gInject "set_incl") [c1;c2]

let set_union c1 c2 = gApp (gInject "setU") [c1;c2]

let set_int c1 c2 = gApp (gInject "setI") [c1;c2]

let imset f s =
  gApp (gInject "imset") [f; s]

let sub0set =
  gApp ~explicit:true (gInject "sub0set") [hole; hole]

let imset_set0_subset =
  gApp ~explicit:true (gInject "imset_set0_subset") [hole; hole; hole; hole]

let rec set_unions = function
  | [] -> failwith "empty set unions"
  | [x] -> x
  | x::xs -> set_union x (set_unions xs)

let set_eq_refl x =
  gApp (gInject "set_eq_refl") [x]

let set_incl_refl =
  gApp ~explicit:true (gInject "subset_refl") [hole; hole]

let incl_subset l1 l2 p =
  gApp (gInject "incl_subset") [l1; l2; p]

let incl_refl =
  gApp (gInject "incl_refl") [hole]

let incl_hd_same p =
  gApp ~explicit:true (gInject "incl_hd_same") [hole; hole; hole; hole; p]

let incl_tl p =
  gApp (gInject "incl_tl") [hole; p]

let setU_set_eq_compat x1 x2 =
  gApp (gInject "setU_set_eq_compat") [x1; x2]

let setU_set0_r x1 x2 =
  gApp (gInject "setU_set0_r") [x1; x2]

let set_eq_trans x1 x2 =
  gApp (gInject "set_eq_trans") [x1; x2]

let set_incl_trans x1 x2 =
  gApp (gInject "subset_trans") [x1; x2]


let setU_set0_l x1 x2 =
  gApp (gInject "setU_set0_l") [x1; x2]

let setU_set0_neut_eq x1 x2 =
  gApp (gInject "setU_set0_neut_eq") [x1; x2]

let eq_bigcupl x1 x2 p = gApp (gInject "eq_bigcupl") [x1; x2; p]

let cons_set_eq x l = gApp (gInject "cons_set_eq") [x; l]

let singl_set_eq a x = gApp ~explicit:true (gInject "singl_set_eq") [a; x]

let bigcup_setU_l x1 x2 x3 = gApp (gInject "bigcup_setU_l") [x1; x2; x3]

let bigcup_set1 x1 x2 = gApp (gInject "bigcup_set1") [x1 ; x2]

let subset_respects_set_eq_l p1 p2 =
  gApp (gInject "subset_respects_set_eq_l") [p1; p2]

let subset_respects_set_eq_r p1 p2 =
  gApp (gInject "subset_respects_set_eq_r") [p1; p2]

let subset_respects_set_eq p1 p2 p3 =
  gApp ~explicit:true (gInject "subset_respects_set_eq")
    [hole; hole; hole; hole; hole; p1; p2; p3]

(* maybe add a new lemma? *)
let subset_set_eq_compat p1 p2 p3 =
  gApp (gInject "subset_respects_set_eq") [p1; p2; p3]

let incl_bigcupl p =
  gApp (gInject "incl_bigcupl") [p]

let incl_bigcup_compat p1 p2 =
  gApp (gInject "incl_bigcup_compat") [p1; p2]

let imset_isSome s =
  gApp ~explicit:true (gInject "imset_isSome") [hole; s]

let isSomeSet a =
  gFun ["x"]
    (fun [x] ->
       gApp (gInject "is_true")
         [gApp ~explicit:true (gInject "isSome") [a; gVar x]]
    )

let incl_subset l1 l2 p =
  gApp ~explicit:true (gInject "incl_subset") [hole; l1; l2; p]

let setU_set_subset_compat p1 p2 =
  gApp (gInject "setU_set_subset_compat") [p1; p2]

let setI_subset_compat p1 p2 =
  gApp ~explicit:true (gInject "setI_subset_compat")
    [hole; hole; hole; hole; hole; p1; p2]


let nil_subset p =
  gApp (gInject "nil_subset") [p]

let cons_subset (hd : coq_expr) (tl : coq_expr) (p : coq_expr) (phd : coq_expr) (ptl : coq_expr) =
  gApp ~explicit:true (gInject "cons_subset") [hole; hd; tl; p; phd; ptl]

let setI_set_incl hsub1 hsub2 =
  gApp ~explicit:true (gInject "setI_set_incl") [hole; hole; hole; hole; hsub1; hsub2]

let setI_set_eq_r p =
  gApp ~explicit:true (gInject "setI_set_eq_r") [hole; hole; hole; hole; p]

let setU_subset_r s2 p =
  gApp ~explicit:true (gInject "setU_subset_r") [hole; hole; s2; hole; p]

let setU_subset_l s2 p =
  gApp ~explicit:true (gInject "setU_subset_l") [hole; hole; s2; hole; p]

let imset_set0_incl f x h =
  gApp ~explicit:true (gInject "imset_set0_incl") [hole; hole; f; x; h]

let imset_singl_incl x f y h =
  gApp ~explicit:true (gInject "imset_singl_incl") [hole; hole; x; f; y; h]

let imset_union_incl s1 s2 f x hin =
  gApp ~explicit:true (gInject "imset_union_incl") [hole; hole; s1; s2; f; x; hin]

let imset_incl h =
  gApp (gInject "imset_incl") [h]

let rewrite_set_r seq p =
  gApp ~explicit:true (gInject "rewrite_set_r") [hole; hole; hole; hole; p; seq]

let rewrite_set_l seq p =
  gApp ~explicit:true (gInject "rewrite_set_l") [hole; hole; hole; hole; p; seq]


let imset_bigcup_incl_l f a g x h =
  gApp ~explicit:true
    (gInject "imset_bigcup_incl_l")
    [hole; hole; hole; f; a; g; x; h]

let set_eq_set_incl_r heq =
  gApp ~explicit:true (gInject "set_eq_set_incl_r") [hole; hole; hole; heq]

let set_eq_set_incl_l heq =
  gApp ~explicit:true (gInject "set_eq_set_incl_l") [hole; hole; hole; heq]

let in_imset f s x hin =
  gApp ~explicit:true (gInject "in_imset") [hole; hole; f; s; x; hin]

let lift_union_compat h1 h2 =
  gApp
    ~explicit:true (gInject "union_lift_subset_compat")
    [hole; hole; hole; hole; hole; h1; h2]

let lift_subset_pres_r h =
  gApp
    ~explicit:true (gInject "lift_subset_pres_r")
    [hole; hole; hole; hole; h]

let lift_subset_pres_l h =
  gApp
    ~explicit:true (gInject "lift_subset_pres_l")
    [hole; hole; hole; hole; h]

let bigcup_set0_subset f s =
  gApp
    ~explicit:true (gInject "bigcup_set0_subset")
    [hole; hole; f; s]

let bigcup_set_U h1 h2 =
  gApp
    ~explicit:true (gInject "bigcup_set_U")
    [hole; hole; hole; hole; hole; hole; h1; h2]

let bigcup_set_I_l h =
  gApp
    ~explicit:true (gInject "bigcup_set_I_l")
    [hole; hole; hole; hole; hole; hole; h]

let set_incl_setI_l h =
  gApp
    ~explicit:true (gInject "set_incl_setI_l")
    [hole; hole; hole; hole; h]

let set_incl_setI_r h =
  gApp
    ~explicit:true (gInject "set_incl_setI_r")
    [hole; hole; hole; hole; h]

let set_incl_setU_l h1 h2 =
  gApp
    ~explicit:true (gInject "set_incl_setU_l")
    [hole; hole; hole; hole; h1; h2]

let bigcup_cons_subset a b h1 h2 =
  gApp
    ~explicit:true (gInject "bigcup_cons_subset")
    [a; b; hole; hole; hole; hole; h1; h2]

let bigcup_cons_subset_r a b h1 h2 =
  gApp
    ~explicit:true (gInject "bigcup_cons_subset_r")
    [a; b; hole; hole; hole; hole; hole; h1; h2]

let bigcup_setI_cons_subset_r a b h1 h2 h3 =
  gApp
    ~explicit:true (gInject "bigcup_setI_cons_subset_r")
    [a; b; hole;
     hole; hole; hole; hole; hole; h1; h2; h3]

let imset_bigcup_setI_cons_subset_r a b h1 h2 h3 =
  gApp
    ~explicit:true (gInject "imset_bigcup_setI_cons_subset_r")
    [a; b; hole; hole; hole; hole; hole; hole; h1; h2; h3]

let bigcup_nil_subset =
  gApp
    ~explicit:true (gInject "bigcup_nil_subset")
    [hole; hole; hole; hole]

let isSome_subset p =
  gApp
    ~explicit:true (gInject "isSome_subset")
    [hole; hole; hole; hole; hole; p]


(* let bigcup_cons_setI_subset_compat a f h1 h2 = *)
(*   gApp *)
(*     ~explicit:true (gInject "bigcup_cons_setI_subset_compat") *)
(*     [a; hole; f; hole; hole; hole; hole; hole; h1; h2] *)

let bigcup_cons_setI_subset_pres a f h =
  gApp
    ~explicit:true (gInject "bigcup_cons_setI_subset_pres")
    [a; hole; f; hole; hole; hole; hole; h]

let bigcup_cons_setI_subset_compat_backtrack h1 h2 =
  gApp
    ~explicit:true (gInject "bigcup_cons_setI_subset_compat_backtrack")
    [hole; hole; hole; hole; hole; hole; hole; h1; h2]

let bigcup_cons_setI_subset_compat_backtrack_weak h1 h2 =
  gApp
    ~explicit:true (gInject "bigcup_cons_setI_subset_compat_backtrack_weak")
    [hole; hole; hole; hole; hole; hole; h1; h2]

let bigcup_cons_setI_subset_pres_backtrack h =
  gApp
    ~explicit:true (gInject "bigcup_cons_setI_subset_pres_backtrack")
    [hole; hole; hole; hole; hole; hole; h]

let bigcup_cons_setI_subset_pres_backtrack_weak h =
  gApp
    ~explicit:true (gInject "bigcup_cons_setI_subset_pres_backtrack_weak")
    [hole; hole; hole; hole; hole; h]

let bigcup_nil_setI f l s =
  gApp
    ~explicit:true (gInject "bigcup_nil_setI")
    [hole; hole; f; l; s]

let isSome_set_eq h1 h2 =
    gApp
    ~explicit:true (gInject "isSome_set_eq")
    [hole; hole; hole; h1; h2]

let set_eq_isSome_sound h =
    gApp
    ~explicit:true (gInject "set_eq_isSome_sound")
    [hole; hole; hole; h]

let set_eq_isSome_complete h =
    gApp
    ~explicit:true (gInject "set_eq_isSome_complete")
    [hole; hole; hole; h]

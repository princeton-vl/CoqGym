open GenericLib


let semGenSize gen size =
  gApp (gInject "semGenSize") [gen; size]

let semGen gen =
  gApp (gInject "semGen") [gen]

let semReturn x =
  gApp (gInject "semReturn") [x]


let arbitrarySize size =
  gApp (gInject "arbitrarySize") [size]

let oneOf_freq p1 p2 p3 =
  gApp ~explicit:true (gInject "oneOf_freq") [hole; p1; p2; p3]

let semFreqSize g gs size hall =
  gApp ~explicit:true (gInject "semFreqSize") [hole; g; gs; size; hall]

let semFreq g gs hall =
  gApp ~explicit:true (gInject "semFreq") [hole; g; gs; hall]

let semBindSize g f size =
  gApp (gInject "semBindSize") [g; f; size]

let semBindSizeMon g f gMon fMon =
  gApp
    ~explicit:true
    (gInject "semBindSizeMonotonic")
    [hole; hole; g; f; gMon; fMon]


let backtrackSizeMonotonic lst proof =
  gApp (gInject "backtrackSizeMonotonic") [lst; proof]

let backtrackSizeMonotonicOpt lst proof =
  gApp (gInject "backtrackSizeMonotonicOpt") [lst; proof]


let semBacktrack_sound g =
  gApp ~explicit:true (gInject "semBacktrack_sound") [hole; g]

let semBacktrack_complete g =
  gApp ~explicit:true (gInject "semBacktrack_complete") [hole; g]

let semBacktrackSize g s =
  gApp ~explicit:true (gInject "semBacktrackSize") [hole; g; s]

let returnGenSizeMonotonic x =
  gApp (gInject "returnGenSizeMonotonic") [x]

let returnGenSizeMonotonicOpt x =
  gApp (gInject "returnGenSizeMonotonicOpt") [x]

let bindMonotonic p s fp =
  gApp ~explicit:true
    (gInject "bindMonotonic") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let bindMonotonicOpt p s fp =
  gApp ~explicit:true
    (gInject "bindMonotonicOpt") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let bindOptMonotonic p s fp =
  gApp ~explicit:true
    (gInject "bindOptMonotonic") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let bindOptMonotonicOpt p s fp =
  gApp ~explicit:true
    (gInject "bindOptMonotonicOpt") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

(* let suchThatMaybeMonotonic p pred = *)
(*   gApp ~explicit:true *)
(*     (gInject "suchThatMaybeMonotonic") [hole; hole; pred; p] *)

(* let suchThatMaybeOptMonotonic p pred = *)
(*   gApp ~explicit:true *)
(*     (gInject "suchThatMaybeOptMonotonic") [hole; hole; pred; p] *)

let suchThatMaybeMonotonicOpt p pred =
  gApp ~explicit:true
    (gInject "suchThatMaybeMonotonicOpt") [hole; hole; pred; p]

let suchThatMaybeOptMonotonicOpt p pred =
  gApp ~explicit:true
    (gInject "suchThatMaybeOptMonotonicOpt") [hole; hole; pred; p]

let semBindOptSizeMonotonicIncl_r g f s sf hg hf =
  gApp ~explicit:true (gInject "semBindOptSizeMonotonicIncl_r")
    [hole; hole; g; f; s; sf; hg; hf]

let semBindSizeMonotonicIncl_r g f s sf hg hf =
  gApp ~explicit:true (gInject "semBindSizeMonotonicIncl_r")
    [hole; hole; g; f; s; sf; hg; hf]

let semBindOptSizeMonotonicIncl_l g f s sf mon monf hg hf =
  gApp ~explicit:true (gInject "semBindOptSizeMonotonicIncl_l")
    [hole; hole; g; f; s; sf; mon; monf; hg; hf]

let semBindSizeMonotonicIncl_l g f s sf mon monf hg hf =
  gApp ~explicit:true (gInject "semBindSizeMonotonicIncl_l")
    [hole; hole; g; f; s; sf; mon; monf; hg; hf]

let semSuchThatMaybe_complete g f s mon h =
  gApp ~explicit:true (gInject "semSuchThatMaybe_complete") [hole; g; f; s; mon; h]

let semSuchThatMaybeOpt_complete g f s mon h =
  gApp ~explicit:true (gInject "semSuchThatMaybeOpt_complete") [hole; g; f; s; mon; h]

let semSuchThatMaybe_sound g f s h =
  gApp ~explicit:true (gInject "semSuchThatMaybe_sound") [hole; g; f; s; h]

let semSuchThatMaybeOpt_sound g f s h =
  gApp ~explicit:true (gInject "semSuchThatMaybeOpt_sound") [hole; g; f; s; h]

let semBindSizeOpt_subset_compat h1 h2 =
  gApp ~explicit:true (gInject "semBindSizeOpt_subset_compat")
    [hole; hole; hole; hole; hole; hole; h1; h2]

let semBindOptSizeOpt_subset_compat h1 h2 =
  gApp ~explicit:true (gInject "semBindOptSizeOpt_subset_compat")
    [hole; hole; hole; hole; hole; hole; h1; h2]

let suchThatMaybe_subset_compat p h =
  gApp ~explicit:true (gInject "suchThatMaybe_subset_compat")
    [hole; p; hole; hole; h]

let suchThatMaybeOpt_subset_compat p h =
  gApp ~explicit:true (gInject "suchThatMaybeOpt_subset_compat")
    [hole; p; hole; hole; h]

let nat_set_ind typ ginst sinst cinst hb hi x =
 gApp ~explicit:true (gInject "nat_set_ind") [typ; ginst; sinst; cinst; hb; hi; x]


  Inductive gen_sort : Set :=
    | Gprop : gen_sort
    | Gset : gen_sort
    | Gtype : nat -> gen_sort
    | Gtypeset : nat -> gen_sort.

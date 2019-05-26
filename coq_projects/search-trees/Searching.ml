type nat_tree =
   NIL 
|  Bin of int * nat_tree * nat_tree ;;

 let search_occ_dec p =
    let rec sch = function NIL -> false
                         | Bin(n,t1,t2) -> if p <= n
                            then if p < n then sch t1 else true
                            else sch t2
    in sch ;;

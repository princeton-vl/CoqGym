
open Feedback

let error s = msg_notice (Pp.str ("Error: " ^ s))
let notice s = msg_notice (Pp.str s)
let info s = msg_info (Pp.str s)

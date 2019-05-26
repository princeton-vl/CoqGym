
#use "load.ml";;


let read_file f =
  let c = open_in f in
  let cs = parse (lexer (Stream.of_channel c)) in
  let cl = ref [] in
  let _ = Stream.iter (fun c -> cl:=c::!cl) cs in
  List.rev !cl
;;

let com s = Stream.next (parse (lexer (Stream.of_string s)));;

let (Definition (_,d,t)) = com "

  Lemma Diagram:
   (x:A)((u:A)(R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)->(coherence y z))
     ->(y,z,u:A)(R x u)->(Rstar u y)
           ->(v:A)(R x v)->(Rstar v z)->(coherence y z).
Proof [x:A][hyp_ind:(u:A)(R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)
                      ->(coherence y z)]
     [y,z,u:A][t1:(R x u)][t2:(Rstar u y)][v:A][u1:(R x v)][u2:(Rstar v z)]
        ([Hyp0:(x0,y0,z0:A)(R x0 y0)->(R x0 z0)
                    ->(P:Prop)((z1:A)(Rstar y0 z1)->(Rstar z0 z1)->P)->P]
             [hyp_ind0:(u0:A)(R x u0)->(y0,z0:A)(Rstar u0 y0)->(Rstar u0 z0)
                        ->(P:Prop)((z1:A)(Rstar y0 z1)->(Rstar z0 z1)->P)->P]
              (Hyp0 x u v t1 u1 (coherence y z)
                [z0:A][H:(Rstar u z0)][H0:(Rstar v z0)]
                   (hyp_ind0 u t1 y z0 t2 H (coherence y z)
                     [z1:A][H1:(Rstar y z1)][H2:(Rstar z0 z1)]
                        (hyp_ind0 v u1 z z1 u2
                          (Rstar_transitive v z0 z1 H0 H2)
                          (coherence y z)
                          [z2:A][H3:(Rstar z z2)][H4:(Rstar z1 z2)]
                            [P:Prop][H5:(z3:A)(Rstar y z3)->(Rstar z z3)->P]
                                (H5 z2
                                  (Rstar_transitive y z1 z2 H1 H4) H3))))
            Hyp2 hyp_ind).
";;
for i = 1 to 100 do add_def !eNV d t done;;


let a = parse_ast "
   ([x:A][hyp_ind:(u:A)(R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)
                      ->(coherence y z)]
     [y,z,u:A][t1:(R x u)][t2:(Rstar u y)][v:A][u1:(R x v)][u2:(Rstar v z)]
        ([Hyp0:(x0,y0,z0:A)(R x0 y0)->(R x0 z0)
                    ->(P:Prop)((z1:A)(Rstar y0 z1)->(Rstar z0 z1)->P)->P]
             [hyp_ind0:(u0:A)(R x u0)->(y0,z0:A)(Rstar u0 y0)->(Rstar u0 z0)
                        ->(P:Prop)((z1:A)(Rstar y0 z1)->(Rstar z0 z1)->P)->P]
              (Hyp0 x u v t1 u1 (coherence y z)
                [z0:A][H:(Rstar u z0)][H0:(Rstar v z0)]
                   (hyp_ind0 u t1 y z0 t2 H (coherence y z)
                     [z1:A][H1:(Rstar y z1)][H2:(Rstar z0 z1)]
                        (hyp_ind0 v u1 z z1 u2
                          (Rstar_transitive v z0 z1 H0 H2)
                          (coherence y z)
                          [z2:A][H3:(Rstar z z2)][H4:(Rstar z1 z2)]
                            [P:Prop][H5:(z3:A)(Rstar y z3)->(Rstar z z3)->P]
                                (H5 z2
                                  (Rstar_transitive y z1 z2 H1 H4) H3))))
            Hyp2 hyp_ind))
 :: ( ((x:A)((u:A)(R x u)->(y:A)(z:A)(Rstar u y)->(Rstar u z)->(coherence y z))
     ->(y,z,u:A)(R x u)->(Rstar u y)
           ->(v:A)(R x v)->(Rstar v z)->(coherence y z)) ::Prop) ";;
let t = raw_constr_of_com empty_evd (gLOB nil_sign) a;;
let ty t = fexecute empty_evd nil_sign t;;
for i = 1 to 100 do ty t done;;

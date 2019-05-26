let test_pair (x, y) = 
  let w = Bit_vector.makeWriter () in
  let _ = Bool_pair_extracted.serialize_bool_pair (x, y) w in
  let r = Bit_vector.writerToReader w in
  let (x', y') = Bool_pair_extracted.deserialize_bool_pair r in
  let true = x = x' && y = y' in
  ()
                             
let _ = test_pair (false, false)
let _ = test_pair (false, true)
let _ = test_pair (true, false)
let _ = test_pair (true, true)

(* serialize -> truncate unused bytes, add one byte to indicate how many bits of the last byte are padding *)
type node = {bytes : bytes;
             mutable next : node option}
              
type iterator = {head : node;
                 mutable node : node;
                 mutable i : int;
                 mutable count : int}

type writer = iterator
type reader = iterator

exception Out_of_bounds
            
let byte_length = 8
             
let makeNode n =
  {bytes = Bytes.make n (Char.chr 0);
   next = None}
  
let makeIter node =
  {head = node;
   node = node;
   i = 0;
   count = 0}

let initialLength = 100
  
let makeWriter () =
  makeIter (makeNode initialLength)

let insert iter c =
  let length = Bytes.length iter.node.bytes in
  (if iter.i = length
   then (let node' = (makeNode (length * 2))
         in iter.node.next <- Some (node');
            iter.node <- node';
            iter.i <- 0));
   Bytes.set iter.node.bytes iter.i c;
   iter.i <- iter.i + 1;
   iter.count <- iter.count + 1

let read iter =
  let length = Bytes.length iter.node.bytes
  in (if iter.i = length
      then match iter.node.next with
           | Some node' -> (iter.node <- node';
                            iter.i <- 0)
           | None -> raise Out_of_bounds);
     let c = Bytes.get iter.node.bytes iter.i
     in (iter.i <- iter.i + 1;
         c)  

let hasNext iter =
  iter.i < iter.count

let pushBack = insert

let writerToReader (iter : iterator) : reader =
  makeIter (iter.head)

let pop : reader -> char =
  read

let numBytes (w : writer) : int =
  w.count

let writerToBytes (w : writer) =
  let iter = makeIter w.head in
  let bytes = Bytes.make w.count (Char.chr 0) in
  let rec loop i =
    if i < w.count
    then (Bytes.set bytes i (read iter);
          loop (i + 1)) in
  loop 0;
  bytes

let bytesToReader (b : bytes) : reader =
  makeIter {bytes = b; next = None}

let rec nat_of_int n =
  if n <= 0 then Datatypes.O
  else Datatypes.S (nat_of_int (n - 1))

let rec int_of_nat = function
  | Datatypes.O -> 0
  | Datatypes.S n -> int_of_nat n + 1

let nat_of_string s = nat_of_int (int_of_string s)
let string_of_nat n = string_of_int (int_of_nat n)

let raw_bytes_of_int (x : int) : bytes =
  let buf = Bytes.make 4 '\x00' in
  Bytes.set buf 0 (char_of_int (x land 0xff));
  Bytes.set buf 1 (char_of_int ((x lsr 8) land 0xff));
  Bytes.set buf 2 (char_of_int ((x lsr 16) land 0xff));
  Bytes.set buf 3 (char_of_int ((x lsr 24) land 0xff));
  buf

let int_of_raw_bytes (buf : bytes) : int =
   (int_of_char (Bytes.get buf 0)) lor
  ((int_of_char (Bytes.get buf 1)) lsl 8) lor
  ((int_of_char (Bytes.get buf 2)) lsl 16) lor
  ((int_of_char (Bytes.get buf 3)) lsl 24)

type t = int


let current_number = ref 0

let initialize () =
  current_number := 0


let fresh () =
  current_number := !current_number + 1 ;
    !current_number


let to_string (i : t) =
  "'" ^ (string_of_int i)


let eq (i : t) (j : t) = (i = j)

open Types


type id = int
type env = (variable_name * int) list


let current_rename_id = ref 0

let string_of_id evid = "V" ^ (string_of_int evid)

let initialize () =
  current_rename_id := 0

let empty = []

let fresh () =
  let evid = !current_rename_id in
    current_rename_id := evid + 1 ;
    evid

let add (rnenv : env) (varnm : variable_name) =
  let evid = !current_rename_id in
  let rec aux acc lst =
    match lst with
    | []                             -> (varnm, evid) :: rnenv
    | (v, e) :: tail  when v = varnm -> List.rev_append acc ((v, e) :: tail)
    | (v, e) :: tail                 -> aux ((v, e) :: acc) tail
  in
    current_rename_id := evid + 1 ;
    (aux [] rnenv, evid)

let rec find (rnenv : env) (varnm : variable_name) =
  match rnenv with
  | []                             -> assert false
  | (v, e) :: tail  when v = varnm -> e
  | _ :: tail                      -> find tail varnm

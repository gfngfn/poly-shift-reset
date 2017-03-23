open Types

type t = (variable_name * poly_type) list


let empty = []

(*
let show tyenv = List.fold_right (fun (v, p) s -> "[" ^ v ^ " : " ^ (string_of_poly_type p) ^ "]" ^ s) tyenv ""
*)

let add (tyenv : t) (varnm : variable_name) (pty : poly_type) =
  let rec aux acc lst =
    match lst with
    | []                             -> List.rev_append acc ((varnm, pty) :: [])
    | (v, p) :: tail  when v = varnm -> List.rev_append acc ((varnm, pty) :: tail)
    | (v, p) :: tail                 -> aux ((v, p) :: acc) tail
  in
    aux [] tyenv


let rec find tyenv varnm =
  match tyenv with
  | []                             -> None
  | (v, p) :: tail  when v = varnm -> Some(p)
  | _ :: tail                      -> find tail varnm


let quantifiables : Typevar.t list ref = ref []

let make_polymorphic tyenv ty =
  let rec listup ty =
    let (tymain, _) = ty in
      match tymain with
      | TypeVariable(i) -> if Typevar.mem i (!quantifiables) then () else quantifiables := i :: (!quantifiables)
      | FuncType(tydom, tycod, tyans1, tyans2) ->
          begin listup tydom ; listup tycod ; listup tyans1 ; listup tyans2 end
      | _ -> ()
  in
  let enclose lst pty =
    List.fold_right (fun i pt -> Forall(i, pt)) lst pty
  in
    quantifiables := [] ;
    listup ty ;
    enclose (!quantifiables) (Mono(ty))
    

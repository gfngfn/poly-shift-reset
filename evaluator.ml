open Types

module Rename : sig
  type id
  type env
  val initialize : unit -> unit
  val empty : env
  val fresh : unit -> id
  val add : env -> variable_name -> (env * id)
  val find : env -> variable_name -> id
end = struct
  type id = int
  type env = (variable_name * int) List

  let current_rename_id = ref 0

  let initialize () =
    current_rename_id := 0

  let empty = []

  let fresh () =
    let evid = !current_rename_id in
      current_rename_id := evid + 1 ;
      evid

  let add (rnenv : t) (varnm : variable_name) =
    let evid = !current_rename_id in
    let rec aux acc lst =
      match lst with
      | []                             -> (varnm, evid) :: rnenv
      | (v, e) :: tail  when v = varnm -> List.rev_append acc ((v, e) :: tail)
      | (v, e) :: tail                 -> add ((v, e) :: acc) tail
    in
      current_rename_id := evid + 1 ;
      (aux [] rnenv, evid)

  let rec find (rnenv : t) (varnm : variable_name) =
    match rnenv with
    | []                             -> assert false
    | (v, e) :: tail  when v = varnm -> e
    | _ :: tail                      -> find tail varnm
end


type eval_term =
  | EvIntConst   of int
  | EvBoolConst  of bool
  | EvVar        of Rename.id
  | EvApply      of eval_term * eval_term
  | EvLambda     of Rename.id * eval_term
  | EvFixPoint   of Rename.id * eval_term
  | EvIfThenElse of eval_term * eval_term * eval_term
  | EvShift      of Rename.id * eval_term
  | EvReset      of eval_term


let rec transform_into_eval_style (rnenv : Rename.env) ((astmain, _) : abstract_term) =
  let iter = transform_into_eval_style in
    match astmain with
    | IntConst(ic)                 -> let evidK = Rename.fresh () in EvLambda(evidK, EvApply(evidK, EvIntConst(ic)))
    | BoolConst(bc)                -> let evidK = Rename.fresh () in EvLambda(evidK, EvApply(evidK, EvBoolConst(bc)))
    | Var(varnm)                   -> let evidK = Rename.fresh () in EvLambda(evidK, EvApply(evidK, EvVar(Rename.find rnenv varnm)))
    | Lambda(varnm, ast1)          ->
        let evidK = Rename.fresh () in
        let (rnenvnew, evid) = Rename.add rnenv varnm in
          EvLambda(evidK, EvApply(evidK, EvLambda(evid, iter rnenvnew ast1)))

    | FixPoint(varnm, ast1)        -> let (rnenvnew, evid) = Rename.add rnenv varnm in EvFixPoint(evid, iter rnenvnew ast1)
    | LetIn(varnm, ast1, ast2)     -> let (rnenvnew, evid) = Rename.add rnenv varnm in EvApply(EvLambda(evid, iter rnenvnew ast2), iter rnenv ast1)
    | IfThenElse(ast0, ast1, ast2) -> EvIfThenElse(iter rnenv ast0, iter rnenv ast1, iter rnenv ast2)
    | Shift(varnm, ast1)           -> let (rnenvnew, evid) = Rename.add rnenv varnm in EvShift(evid, iter rnenvnew ast1)
    | Reset(ast1)                  -> EvReset(iter rnenv ast1)


let rec eval env evtm =
  evtm (*temporary*)

let main (ast : abstract_term) =
  eval (EvReset(transform_into_eval_style Rename.empty ast))

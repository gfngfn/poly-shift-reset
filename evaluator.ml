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
  type env = (variable_name * int) list

  let current_rename_id = ref 0

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
end


type eval_term =
  | EvIntConst         of int
  | EvBoolConst        of bool
  | EvVar              of Rename.id
  | EvApply            of eval_term * eval_term
  | EvLambda           of Rename.id * eval_term
  | EvFixPointOfLambda of Rename.id * eval_term
  | EvIfThenElse       of eval_term * eval_term * eval_term


let rec transform_into_eval_style (rnenv : Rename.env) ((astmain, _) : abstract_term) =
  let ( @--> ) evid evtm = EvLambda(evid, evtm) in
  let ( ~@ ) evid = EvVar(evid) in
  let ( *@ ) evtm1 evtm2 = EvApply(evtm1, evtm2) in
  let letin evid evtm1 evtm2 = ((evid @--> evtm2) *@ evtm1) in
  let iter = transform_into_eval_style in
    match astmain with
    | IntConst(ic)  -> let evidK = Rename.fresh () in (evidK @--> (EvVar(evidK) *@ EvIntConst(ic)))
    | BoolConst(bc) -> let evidK = Rename.fresh () in (evidK @--> (EvVar(evidK) *@ EvBoolConst(bc)))
    | Var(varnm)    -> let evidK = Rename.fresh () in (evidK @--> (EvVar(evidK) *@ EvVar(Rename.find rnenv varnm)))

    | Apply(ast1, ast2) ->
        let evidK = Rename.fresh () in
        let evidM = Rename.fresh () in
        let evidN = Rename.fresh () in
          (evidK @-->
            ((iter rnenv ast1) *@ (evidM @-->
                                    ((iter rnenv ast2) *@ (evidN @-->
                                                            ((EvApply(~@ evidM, ~@ evidN)) *@ (~@ evidK)))))))

    | Lambda(varnm, ast1) ->
        let evidK = Rename.fresh () in
        let (rnenvnew, evid) = Rename.add rnenv varnm in
          (evidK @--> ((~@ evidK) *@ (EvLambda(evid, iter rnenvnew ast1))))

    | FixPointOfLambda(varf, varx, ast1) ->
        let evidK = Rename.fresh () in
        let (rnenvnewf, evidf) = Rename.add rnenv varf in
        let (rnenvnewx, evidx) = Rename.add rnenvnewf varx in
          (evidK @--> ((~@ evidK) *@ (EvFixPointOfLambda(evidx, iter rnenvnewx ast1))))

    | LetIn(varnm, ast1, ast2) ->
        let evidK = Rename.fresh () in
        let evidM = Rename.fresh () in
        let (rnenvnew, evid) = Rename.add rnenv varnm in
          (evidK @-->
            (letin evid ((iter rnenv ast1) *@ (evidM @--> (~@ evidM)))
              ((iter rnenvnew ast2) *@ (~@ evidK))))

    | IfThenElse(ast0, ast1, ast2) ->
        let evidK = Rename.fresh () in
        let evidM = Rename.fresh () in
          (evidK @-->
            ((iter rnenv ast0) *@ (evidM @-->
                                     (EvIfThenElse(~@ evidM, (iter rnenv ast1) *@ (~@ evidK), (iter rnenv ast2) *@ (~@ evidK))))))

    | Shift(varnm, ast1) ->
        let evidK = Rename.fresh () in
        let evidL = Rename.fresh () in
        let evidM = Rename.fresh () in
        let evidN = Rename.fresh () in
        let (rnenvnew, evid) = Rename.add rnenv varnm in
          (evidK @-->
             (letin evid (evidN @--> evidL @--> ((~@ evidL) *@ ((~@ evidK) *@ (~@ evidN))))
                ((iter rnenv ast1) *@ (evidM @--> (~@ evidM)))))

    | Reset(ast1) ->
        let evidK = Rename.fresh () in
        let evidM = Rename.fresh () in
          (evidK @-->
            ((~@ evidK) *@ ((iter rnenv ast1) *@ (evidM @--> (~@ evidM)))))


let rec eval env evtm =
  evtm (*temporary*)


let main (ast : abstract_term) =
  let (_, ty) = ast in
    eval (transform_into_eval_style Rename.empty (Reset(ast), ty))

open Types

exception EmptyList
exception DivisionByZero

type eval_term =
  | EvIntConst         of int
  | EvBoolConst        of bool
  | EvVar              of Rename.id
  | EvApply            of eval_term * eval_term
  | EvLambda           of Rename.id * eval_term
  | EvFixPointOfLambda of Rename.id * Rename.id * eval_term
  | EvIfThenElse       of eval_term * eval_term * eval_term
  | EvPrimPlus         of eval_term * eval_term
  | EvPrimMinus        of eval_term * eval_term
  | EvPrimTimes        of eval_term * eval_term
  | EvPrimDivides      of eval_term * eval_term
  | EvPrimEqual        of eval_term * eval_term
  | EvPrimLeq          of eval_term * eval_term
  | EvPrimGeq          of eval_term * eval_term
  | EvPrimLessThan     of eval_term * eval_term
  | EvPrimGreaterThan  of eval_term * eval_term
  | EvPrimAnd          of eval_term * eval_term
  | EvPrimOr           of eval_term * eval_term
  | EvPrimNot          of eval_term
  | EvNil
  | EvCons             of eval_term * eval_term
  | EvPrimIsEmpty      of eval_term
  | EvPrimListHead     of eval_term
  | EvPrimListTail     of eval_term


let rec string_of_eval_term evtm =
  let iter = string_of_eval_term in
  let rs = Rename.string_of_id in
    match evtm with
    | EvIntConst(ic)                  -> string_of_int ic
    | EvBoolConst(bc)                 -> string_of_bool bc
    | EvVar(id)                       -> rs id
    | EvApply(t1, t2)                 -> "(" ^ (iter t1) ^ " " ^ (iter t2) ^ ")"
    | EvLambda(id, t)                 -> "(\\" ^ (rs id) ^ ". " ^ (iter t) ^ ")"
    | EvFixPointOfLambda(idf, idx, t) -> "(fix " ^ (rs idf) ^ ". \\" ^ (rs idx) ^ ". " ^ (iter t) ^ ")"
    | EvIfThenElse(t0, t1, t2)        -> "(if " ^ (iter t0) ^ " then " ^ (iter t1) ^ " else " ^ (iter t2) ^ ")"
    | EvNil                           -> "[]"
    | EvCons(t1, t2)                  -> "(" ^ (iter t1) ^ " :: " ^ (iter t2) ^ ")"
    | _                               -> "(primitive)"

let ( @--> ) evid evtm = EvLambda(evid, evtm)
let ( ~@ ) evid = EvVar(evid)
let ( *@ ) evtm1 evtm2 = EvApply(evtm1, evtm2)
let letin evid evtm1 evtm2 = ((evid @--> evtm2) *@ evtm1)


let rec transform_into_eval_style (rnenv : Rename.env) ((astmain, _) : abstract_term) =
  let iter = transform_into_eval_style in
    match astmain with
    | IntConst(ic)  -> let evidK = Rename.fresh () in (evidK @--> ((~@ evidK) *@ EvIntConst(ic)))
    | BoolConst(bc) -> let evidK = Rename.fresh () in (evidK @--> ((~@ evidK) *@ EvBoolConst(bc)))
    | Var(varnm)    -> let evidK = Rename.fresh () in (evidK @--> ((~@ evidK) *@ EvVar(Rename.find rnenv varnm)))
    | Nil           -> let evidK = Rename.fresh () in (evidK @--> ((~@ evidK) *@ EvNil))

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
          (evidK @--> ((~@ evidK) *@ (EvFixPointOfLambda(evidf, evidx, iter rnenvnewx ast1))))

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


module Evalenv : sig
  type t

  val create : unit -> t
  val add : t -> Rename.id -> eval_term -> unit
  val find : t -> Rename.id -> eval_term
end = struct
  type t = (Rename.id, eval_term) Hashtbl.t

  let create : unit -> t = (fun () -> Hashtbl.create 1024)

  let add (env : t) (evid : Rename.id) (evtm : eval_term) = Hashtbl.add env evid evtm

  let find (env : t) (evid : Rename.id) = Hashtbl.find env evid
end


let rec eval (env : Evalenv.t) (evtm : eval_term) =
  match evtm with
  | ( EvIntConst(_)
    | EvBoolConst(_)
    | EvLambda(_, _)
    | EvFixPointOfLambda(_, _, _) )   -> evtm

  | EvVar(evid)                       -> Evalenv.find env evid

  | EvNil                -> EvNil

  | EvCons(evtm1, evtm2) ->
      let value1 = eval env evtm1 in
      let value2 = eval env evtm2 in
        EvCons(value1, value2)

  | EvIfThenElse(evtm0, evtm1, evtm2) ->
      if eval_bool env evtm0 then eval env evtm1 else eval env evtm2

  | EvApply(evtm1, evtm2) ->
     let value1 = eval env evtm1 in
      begin
        match value1 with
        | EvLambda(evid, evtm1sub) ->
            let value2 = eval env evtm2 in
            begin Evalenv.add env evid value2 ; eval env evtm1sub end

        | EvFixPointOfLambda(evidf, evidx, evtm1sub) ->
            let value2 = eval env evtm2 in
            begin Evalenv.add env evidf value1 ; Evalenv.add env evidx value2 ; eval env evtm1sub end

        | _ -> assert false
      end

  | EvPrimPlus(evtm1, evtm2)        -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in EvIntConst(ic1 + ic2)
  | EvPrimMinus(evtm1, evtm2)       -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in EvIntConst(ic1 - ic2)
  | EvPrimTimes(evtm1, evtm2)       -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in EvIntConst(ic1 * ic2)
  | EvPrimDivides(evtm1, evtm2)     -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in
                                         if ic2 = 0 then raise DivisionByZero else EvIntConst(ic1 / ic2)

  | EvPrimEqual(evtm1, evtm2)       -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in EvBoolConst(ic1 = ic2)
  | EvPrimLeq(evtm1, evtm2)         -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in EvBoolConst(ic1 <= ic2)
  | EvPrimGeq(evtm1, evtm2)         -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in EvBoolConst(ic1 >= ic2)
  | EvPrimLessThan(evtm1, evtm2)    -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in EvBoolConst(ic1 < ic2)
  | EvPrimGreaterThan(evtm1, evtm2) -> let (ic1, ic2) = eval_int_pair env (evtm1, evtm2) in EvBoolConst(ic1 > ic2)

  | EvPrimAnd(evtm1, evtm2)         -> let (bc1, bc2) = eval_bool_pair env (evtm1, evtm2) in EvBoolConst(bc1 && bc2)
  | EvPrimOr(evtm1, evtm2)          -> let (bc1, bc2) = eval_bool_pair env (evtm1, evtm2) in EvBoolConst(bc1 || bc2)
  | EvPrimNot(evtm)                 -> let bc = eval_bool env evtm in EvBoolConst(not bc)

  | EvPrimIsEmpty(evtm)             -> eval_list env evtm (fun () -> EvBoolConst(true)) (fun _ _ -> EvBoolConst(false))
  | EvPrimListHead(evtm)            -> eval_list env evtm (fun () -> raise EmptyList) (fun vH vT -> vH)
  | EvPrimListTail(evtm)            -> eval_list env evtm (fun () -> raise EmptyList) (fun vH vT -> vT)


and eval_list env evtm fnil fcons =
  match eval env evtm with
  | EvNil          -> fnil ()
  | EvCons(vH, vT) -> fcons vH vT
  | _              -> assert false


and eval_int_pair env (evtm1, evtm2) =
  let ic1 = eval_int env evtm1 in
  let ic2 = eval_int env evtm2 in
    (ic1, ic2)


and eval_bool_pair env (evtm1, evtm2) =
  let bc1 = eval_bool env evtm1 in
  let bc2 = eval_bool env evtm2 in
    (bc1, bc2)


and eval_bool env evtm =
  match eval env evtm with
  | EvBoolConst(bc) -> bc
  | _               -> assert false


and eval_int env evtm =
  match eval env evtm with
  | EvIntConst(ic) -> ic
  | _              -> assert false


let main (env : Evalenv.t) (rnenv : Rename.env) (ast : abstract_term) =
  let (_, ty) = ast in
  let tvidM = Rename.fresh () in
    eval env ((transform_into_eval_style rnenv (Reset(ast), ty)) *@ (tvidM @--> (~@ tvidM)))


let primitives =
  let evid1 = Rename.fresh () in
  let evid2 = Rename.fresh () in
    [
      ("+",   (evid1 @--> evid2 @--> (EvPrimPlus(~@ evid1, ~@ evid2))));
      ("-",   (evid1 @--> evid2 @--> (EvPrimMinus(~@ evid1, ~@ evid2))));
      ("*",   (evid1 @--> evid2 @--> (EvPrimTimes(~@ evid1, ~@ evid2))));
      ("/",   (evid1 @--> evid2 @--> (EvPrimDivides(~@ evid1, ~@ evid2))));
      ("==",  (evid1 @--> evid2 @--> (EvPrimEqual(~@ evid1, ~@ evid2))));
      ("<=",  (evid1 @--> evid2 @--> (EvPrimLeq(~@ evid1, ~@ evid2))));
      (">=",  (evid1 @--> evid2 @--> (EvPrimGeq(~@ evid1, ~@ evid2))));
      ("<",   (evid1 @--> evid2 @--> (EvPrimLessThan(~@ evid1, ~@ evid2))));
      (">",   (evid1 @--> evid2 @--> (EvPrimGreaterThan(~@ evid1, ~@ evid2))));
      ("&&",  (evid1 @--> evid2 @--> (EvPrimAnd(~@ evid1, ~@ evid2))));
      ("||",  (evid1 @--> evid2 @--> (EvPrimOr(~@ evid1, ~@ evid2))));
      ("not", (evid1 @--> (EvPrimNot(~@ evid1))));
      ("is_empty", (evid1 @--> (EvPrimIsEmpty(~@ evid1))));
      ("head",     (evid1 @--> (EvPrimListHead(~@ evid1))));
      ("tail",     (evid1 @--> (EvPrimListTail(~@ evid1))));
      ("::",       (evid1 @--> evid2 @--> (EvCons(~@ evid1, ~@ evid2))));
    ]

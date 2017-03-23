open Types

exception EmptyList
exception DivisionByZero
exception Bug of string


type 'a _eval_term =
  | EvIntConst         of int
  | EvBoolConst        of bool
  | EvVar              of Rename.id
  | EvApply            of 'a _eval_term * 'a _eval_term
  | EvLambda           of Rename.id * 'a _eval_term
  | EvFixPointOfLambda of Rename.id * Rename.id * 'a _eval_term
  | EvEvaluatedAbs     of 'a * Rename.id option * Rename.id * 'a _eval_term
  | EvIfThenElse       of 'a _eval_term * 'a _eval_term * 'a _eval_term
  | EvPrimPlus         of 'a _eval_term * 'a _eval_term
  | EvPrimMinus        of 'a _eval_term * 'a _eval_term
  | EvPrimTimes        of 'a _eval_term * 'a _eval_term
  | EvPrimDivides      of 'a _eval_term * 'a _eval_term
  | EvPrimEqual        of 'a _eval_term * 'a _eval_term
  | EvPrimLeq          of 'a _eval_term * 'a _eval_term
  | EvPrimGeq          of 'a _eval_term * 'a _eval_term
  | EvPrimLessThan     of 'a _eval_term * 'a _eval_term
  | EvPrimGreaterThan  of 'a _eval_term * 'a _eval_term
  | EvPrimAnd          of 'a _eval_term * 'a _eval_term
  | EvPrimOr           of 'a _eval_term * 'a _eval_term
  | EvPrimNot          of 'a _eval_term
  | EvNil
  | EvCons             of 'a _eval_term * 'a _eval_term
  | EvPrimIsEmpty      of 'a _eval_term
  | EvPrimListHead     of 'a _eval_term
  | EvPrimListTail     of 'a _eval_term


module Evalenv : sig
  type t

  val create : unit -> t
  val add : t -> Rename.id -> t _eval_term -> unit
  val find : t -> Rename.id -> t _eval_term
  val copy : t -> t

end = struct
  type t = Tag of (Rename.id, t _eval_term) Hashtbl.t

  let create () =
    let env = Hashtbl.create 1024 in Tag(env)

  let add ((Tag(env)) : t) (evid : Rename.id) (evtm : t _eval_term) = Hashtbl.add env evid evtm

  let find ((Tag(env)) : t) (evid : Rename.id) = Hashtbl.find env evid

  let copy ((Tag(env)) : t) =
    let envnew = Hashtbl.copy env in Tag(envnew)
end


type eval_term = Evalenv.t _eval_term


let rec string_of_eval_term evtm =
  let iter = string_of_eval_term in
  let rs = Rename.string_of_id in
    match evtm with
    | EvIntConst(ic)                       -> string_of_int ic
    | EvBoolConst(bc)                      -> string_of_bool bc
    | EvVar(id)                            -> rs id
    | EvApply(t1, t2)                      -> "(" ^ (iter t1) ^ " " ^ (iter t2) ^ ")"
    | EvLambda(id, t)                      -> "(\\" ^ (rs id) ^ ". " ^ (iter t) ^ ")"
    | EvFixPointOfLambda(idf, idx, t)      -> "(fix " ^ (rs idf) ^ ". \\" ^ (rs idx) ^ ". " ^ (iter t) ^ ")"
    | EvEvaluatedAbs(_, Some(idf), idx, t) -> "(abs! " ^ (rs idf) ^ ". " ^ (rs idx) ^ ". " ^ (iter t) ^ ")"
    | EvEvaluatedAbs(_, None, idx, t)      -> "(abs! _. " ^ (rs idx) ^ ". " ^ (iter t) ^ ")"
    | EvIfThenElse(t0, t1, t2)             -> "(if " ^ (iter t0) ^ " then " ^ (iter t1) ^ " else " ^ (iter t2) ^ ")"
    | EvNil                                -> "[]"
    | EvCons(t1, t2)                       -> "(" ^ (iter t1) ^ " :: " ^ (iter t2) ^ ")"
(*    | EvPrimPlus(t1, t2)                   -> "(" ^ (iter t1) ^ " + " ^ (iter t2) ^ ")" *)
    | _                                    -> "(primitive-with-args)"


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


let rec eval (env : Evalenv.t) (evtm : eval_term) =
  match evtm with
  | ( EvIntConst(_)
    | EvBoolConst(_)
    | EvEvaluatedAbs(_, _, _, _) ) -> evtm
  | EvLambda(evidx, evtm1)                  -> let envabs = Evalenv.copy env in EvEvaluatedAbs(envabs, None, evidx, evtm1)
  | EvFixPointOfLambda(evidf, evidx, evtm1) -> let envabs = Evalenv.copy env in EvEvaluatedAbs(envabs, Some(evidf), evidx, evtm1)

  | EvVar(evid)                       -> eval env (Evalenv.find env evid)

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
        | EvEvaluatedAbs(envabs, evidfopt, evidx, evtm1sub) ->
            let value2 = eval env evtm2 in
            begin
              begin
                match evidfopt with
                | None        -> ()
                | Some(evidf) -> Evalenv.add envabs evidf value1
              end ;
              Evalenv.add envabs evidx value2 ; eval envabs evtm1sub
            end

        | _ -> raise (Bug((string_of_eval_term evtm) ^ " ->* " ^ (string_of_eval_term (EvApply(value1, evtm2)))))
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
  | EvPrimListHead(evtm)            ->
      let _ = print_string ((string_of_eval_term evtm) ^ " ---> ") in (* for debug *)
        eval_list env evtm (fun () -> raise EmptyList) (fun vH vT ->
          let _ = print_endline (string_of_eval_term (EvCons(vH, vT))) in (* for debug *)
            vH)
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
  let evtm = ((transform_into_eval_style rnenv (Reset(ast), ty)) *@ (tvidM @--> (~@ tvidM))) in
  let _ = print_endline (string_of_eval_term evtm) in (* for debug *)
    eval env evtm


let primitives =
  let binary op =
    let evidQ = Rename.fresh () in
    let evidA = Rename.fresh () in
    let evidB = Rename.fresh () in
    let evidK = Rename.fresh () in
      (evidA @--> evidQ @--> ((~@ evidQ) *@ (evidB @--> evidK @--> ((~@ evidK) *@ (op (~@ evidA) (~@ evidB))))))
  in
  let unary op =
    let evidA = Rename.fresh () in
    let evidK = Rename.fresh () in
      (evidA @--> evidK @--> ((~@ evidK) *@ (op (~@ evidA))))
  in
    [
      ("+",   binary (fun x y -> EvPrimPlus(x, y)));
      ("-",   binary (fun x y -> EvPrimMinus(x, y)));
      ("*",   binary (fun x y -> EvPrimTimes(x, y)));
      ("/",   binary (fun x y -> EvPrimDivides(x, y)));
      ("==",  binary (fun x y -> EvPrimEqual(x, y)));
      ("<=",  binary (fun x y -> EvPrimLeq(x, y)));
      (">=",  binary (fun x y -> EvPrimGeq(x, y)));
      ("<",   binary (fun x y -> EvPrimLessThan(x, y)));
      (">",   binary (fun x y -> EvPrimGreaterThan(x, y)));
      ("&&",  binary (fun x y -> EvPrimAnd(x, y)));
      ("||",  binary (fun x y -> EvPrimOr(x, y)));
      ("not",      unary (fun x -> EvPrimNot(x)));
      ("is_empty", unary (fun x -> EvPrimIsEmpty(x)));
      ("head",     unary (fun x -> EvPrimListHead(x)));
      ("tail",     unary (fun x -> EvPrimListTail(x)));
      ("::",  binary (fun x y -> EvCons(x, y)));
    ]

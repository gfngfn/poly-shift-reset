open Types

type variable_id = int
type eval_term =
  | EvVar        of variable_id
  | EvApply      of eval_term * eval_term
  | EvLambda     of variable_id * eval_term
  | EvFixPoint   of variable_id * eval_term
  | EvIfThenElse of eval_term * eval_term * eval_term
  | EvShift      of variable_id * eval_term
  | EvReset      of eval_term
  | EvIntConst   of int
  | EvBoolConst  of bool


let rec transform_into_eval_style (ast : abstract_term) =
  let iter = transform_into_eval_style in
    match ast with
    | Var()

let rec eval evtm =

let main (ast : abstract_term) =
  eval (EvReset(transform_into_eval_style ast))

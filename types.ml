
let print_for_debug msg = ()


type variable_name = string

type mono_type = mono_type_main * Range.t
and mono_type_main =
  | TypeVariable of int
  | IntType
  | BoolType
  | FuncType     of mono_type * mono_type * mono_type * mono_type

type poly_type =
  | Forall of int * poly_type
  | Mono   of mono_type

type source_tree = source_tree_main * Range.t
and source_tree_main =
  | SrcVar        of variable_name
  | SrcApply      of source_tree * source_tree
  | SrcLambda     of (variable_name * Range.t) * source_tree
  | SrcFixPoint   of (variable_name * Range.t) * source_tree
  | SrcLetIn      of (variable_name * Range.t) * source_tree * source_tree
  | SrcIfThenElse of source_tree * source_tree * source_tree
  | SrcShift      of (variable_name * Range.t) * source_tree
  | SrcReset      of source_tree
  | SrcIntConst   of int
  | SrcBoolConst  of bool

type abstract_tree = abstract_tree_main * int
and abstract_tree_main =
  | Var        of variable_name
  | Apply      of abstract_tree * abstract_tree
  | Lambda     of variable_name * abstract_tree
  | FixPoint   of variable_name * abstract_tree
  | LetIn      of variable_name * abstract_tree * abstract_tree
  | IfThenElse of abstract_tree * abstract_tree * abstract_tree
  | Shift      of variable_name * abstract_tree
  | Reset      of abstract_tree
  | IntConst   of int
  | BoolConst  of bool


let rec string_of_source_tree sast =
  let iter = string_of_source_tree in
  let (sastmain, _) = sast in
    match sastmain with
    | SrcVar(varnm)                         -> varnm
    | SrcApply(sast1, sast2)                -> "(" ^ (iter sast1) ^ " " ^ (iter sast2) ^ ")"
    | SrcLambda((varnm, _), sast1)          -> "(fun " ^ varnm ^ ". " ^ (iter sast1) ^ ")"
    | SrcFixPoint((varnm, _), sast1)        -> "(fix " ^ varnm ^ ". " ^ (iter sast1) ^ ")"
    | SrcLetIn((varnm, _), sast1, sast2)    -> "(let " ^ varnm ^ " = " ^ (iter sast1) ^ " in " ^ (iter sast2) ^ ")"
    | SrcIfThenElse(sast0, sast1, sast2)    -> "(if " ^ (iter sast0) ^ " then " ^ (iter sast1) ^ " else " ^ (iter sast2) ^ ")"
    | SrcShift((varnm, _), sast1)           -> "(shift " ^ varnm ^ ". " ^ (iter sast1) ^ ")"
    | SrcReset(sast1)                       -> "(reset " ^ (iter sast1) ^ ")"
    | SrcIntConst(nc)                       -> string_of_int nc
    | SrcBoolConst(bc)                      -> string_of_bool bc


let rec string_of_mono_type (srcty : mono_type) =
  let iter = string_of_mono_type in
  let iter_enclose srcty =
    match srcty with
    | (FuncType(_, _, _, _), _) -> "(" ^ (iter srcty) ^ ")"
    | _                         -> iter srcty
  in
  let (srctymain, _) = srcty in
    match srctymain with
    | TypeVariable(i)                        -> "'" ^ (string_of_int i)
    | IntType                                -> "int"
    | BoolType                               -> "bool"
    | FuncType(tydom, tycod, tyans1, tyans2) -> (iter_enclose tydom) ^ " / " ^ (iter_enclose tyans1) ^
                                                  " -> " ^ (iter_enclose tycod) ^ " / " ^ (iter tyans2)

(*
let rec string_of_abstract_tree (ast : abstract_tree) =
  let iter = string_of_abstract_tree in
  let (astmain, layer) = ast in
  let strlayer s = "(" ^ (string_of_int layer) ^ "| " ^ s ^ ")" in
    match astmain with
    | OrdContentOf(ovnm)           -> strlayer ovnm
    | PermContentOf(pvnm)          -> strlayer pvnm
    | Apply(ast1, ast2)            -> strlayer ((iter ast1) ^ " " ^ (iter ast2))
    | Lambda(varnm, ast1)           -> strlayer ("\\" ^ varnm ^ ". " ^ (iter ast1))
    | FixPoint(varnm, ast1)         -> strlayer ("fix " ^ varnm ^ ". " ^ (iter ast1))
    | IfThenElse(ast0, ast1, ast2) -> strlayer ("if " ^ (iter ast0) ^ " then " ^ (iter ast1) ^ " else " ^ (iter ast2))
    | Shift(varnm, ast1)                   -> strlayer ("next " ^ (iter ast1))
    | Prev(ast1)                   -> strlayer ("prev " ^ (iter ast1))
    | Box(ast1)                    -> strlayer ("box " ^ (iter ast1))
    | Unbox(pvnm, i, ast1, ast2)   -> strlayer ("unbox " ^ pvnm ^ " =" ^ (string_of_int i) ^ " " ^ (iter ast1) ^ " in " ^ (iter ast2))
    | IntConst(ic)                 -> strlayer (string_of_int ic)
    | BoolConst(bc)                -> strlayer (string_of_bool bc)
*)

let rec erase_range_of_mono_type (srcty : mono_type) =
  let (srctymain, _) = srcty in
  let iter = erase_range_of_mono_type in
  let dr = Range.dummy "erased" in
    match srctymain with
    | FuncType(tydom, tycod, tyans1, tyans2) -> (FuncType(iter tydom, iter tycod, iter tyans1, iter tyans2), dr)
    | _                                      -> (srctymain, dr)

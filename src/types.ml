
type variable_name = string

type mono_type = mono_type_main * Range.t
and mono_type_main =
  | IntType
  | BoolType
  | TypeVariable of Typevar.t
  | FuncType     of mono_type * mono_type * mono_type * mono_type
  | ListType     of mono_type


type poly_type =
  | Forall of Typevar.t * poly_type
  | Mono   of mono_type

type source_term = source_term_main * Range.t
and source_term_main =
  | SrcIntConst   of int
  | SrcBoolConst  of bool
  | SrcVar        of variable_name
  | SrcApply      of source_term * source_term
  | SrcLambda     of (variable_name * Range.t) * source_term
  | SrcFixPoint   of (variable_name * Range.t) * source_term
  | SrcLetIn      of (variable_name * Range.t) * source_term * source_term
  | SrcIfThenElse of source_term * source_term * source_term
  | SrcNil
  | SrcShift      of (variable_name * Range.t) * source_term
  | SrcReset      of source_term

type abstract_term = abstract_term_main * mono_type
and abstract_term_main =
  | IntConst         of int
  | BoolConst        of bool
  | Var              of variable_name
  | Apply            of abstract_term * abstract_term
  | Lambda           of variable_name * abstract_term
  | FixPointOfLambda of variable_name * variable_name * abstract_term
  | LetIn            of variable_name * abstract_term * abstract_term
  | IfThenElse       of abstract_term * abstract_term * abstract_term
  | Nil
  | Shift            of variable_name * abstract_term
  | Reset            of abstract_term


let rec subst_mono_type (ty : mono_type) (i : Typevar.t) (tynew : mono_type) =
  let iter t = subst_mono_type t i tynew in
    match ty with
    | (TypeVariable(j), _)        when Typevar.eq i j -> tynew
    | (FuncType(tydom, tycod, tyans1, tyans2), tyrng) -> (FuncType(iter tydom, iter tycod, iter tyans1, iter tyans2), tyrng)
    | _                                               -> ty


let rec subst_poly_type (pty : poly_type) (i : Typevar.t) (tynew : mono_type) =
  match pty with
  | Mono(ty)                               -> Mono(subst_mono_type ty i tynew)
  | Forall(j, ptysub)  when Typevar.eq i j -> pty
  | Forall(j, ptysub)                      -> Forall(j, subst_poly_type ptysub i tynew)


let rec string_of_source_term sast =
  let iter = string_of_source_term in
  let (sastmain, _) = sast in
    match sastmain with
    | SrcVar(varnm)                         -> varnm
    | SrcApply(sast1, sast2)                -> "(" ^ (iter sast1) ^ " " ^ (iter sast2) ^ ")"
    | SrcLambda((varnm, _), sast1)          -> "(\\" ^ varnm ^ ". " ^ (iter sast1) ^ ")"
    | SrcFixPoint((varnm, _), sast1)        -> "(fix " ^ varnm ^ ". " ^ (iter sast1) ^ ")"
    | SrcLetIn((varnm, _), sast1, sast2)    -> "(let " ^ varnm ^ " = " ^ (iter sast1) ^ " in " ^ (iter sast2) ^ ")"
    | SrcIfThenElse(sast0, sast1, sast2)    -> "(if " ^ (iter sast0) ^ " then " ^ (iter sast1) ^ " else " ^ (iter sast2) ^ ")"
    | SrcShift((varnm, _), sast1)           -> "(shift " ^ varnm ^ ". " ^ (iter sast1) ^ ")"
    | SrcReset(sast1)                       -> "(reset " ^ (iter sast1) ^ ")"
    | SrcIntConst(nc)                       -> string_of_int nc
    | SrcBoolConst(bc)                      -> string_of_bool bc
    | SrcNil                                -> "[]"


let rec string_of_mono_type (srcty : mono_type) =
  let iter = string_of_mono_type in
  let iter_enclose srcty =
    match srcty with
    | (FuncType(_, _, _, _), _) -> "(" ^ (iter srcty) ^ ")"
    | _                         -> iter srcty
  in
  let (srctymain, _) = srcty in
    match srctymain with
    | TypeVariable(i)                        -> Typevar.to_string i
    | IntType                                -> "int"
    | BoolType                               -> "bool"
    | FuncType(tydom, tycod, tyans1, tyans2) -> (iter_enclose tydom) ^ " / " ^ (iter_enclose tyans1) ^
                                                  " -> " ^ (iter_enclose tycod) ^ " / " ^ (iter tyans2)
    | ListType(tycnt)                        -> (iter_enclose tycnt) ^ " list"

let rec string_of_poly_type (pty : poly_type) =
  let iter = string_of_poly_type in
  match pty with
  | Mono(ty) -> string_of_mono_type ty
  | Forall(i, ptysub) -> "(" ^ (Typevar.to_string i) ^ ". " ^ (iter ptysub) ^ ")"


let rec string_of_abstract_term (ast : abstract_term) =
  let iter = string_of_abstract_term in
  let (astmain, ty) = ast in
    match astmain with
    | Var(varnm)                         -> varnm
    | Apply(ast1, ast2)                  -> "(" ^ (iter ast1) ^ " " ^ (iter ast2) ^ ")"
    | Lambda(varnm, ast1)                -> "((\\" ^ varnm ^ ". " ^ (iter ast1) ^ ") : " ^ (string_of_mono_type ty) ^ ")"
    | FixPointOfLambda(varf, varx, ast1) -> "(fix " ^ varf ^ ". \\" ^ varx ^ ". " ^ (iter ast1) ^ ")"
    | LetIn(varnm, ast1, ast2)           -> "(let " ^ varnm ^ " = " ^ (iter ast1) ^ " in " ^ (iter ast2) ^ ")"
    | IfThenElse(ast0, ast1, ast2)       -> "(if " ^ (iter ast0) ^ " then " ^ (iter ast1) ^ " else " ^ (iter ast2) ^ ")"
    | Shift(varnm, ast1)                 -> "(shift " ^ varnm ^ ". " ^ (iter ast1) ^ ")"
    | Reset(ast1)                        -> "(reset " ^ (iter ast1) ^ ")"
    | IntConst(ic)                       -> string_of_int ic
    | BoolConst(bc)                      -> string_of_bool bc
    | Nil                                -> "[]"


let rec erase_range_of_mono_type (srcty : mono_type) =
  let (srctymain, _) = srcty in
  let iter = erase_range_of_mono_type in
  let dr = Range.dummy "erased" in
    match srctymain with
    | FuncType(tydom, tycod, tyans1, tyans2) -> (FuncType(iter tydom, iter tycod, iter tyans1, iter tyans2), dr)
    | _                                      -> (srctymain, dr)

open Types

exception InternalInclusionError
exception InternalContradictionError
exception InclusionError of mono_type * mono_type
exception ContradictionError of mono_type * mono_type

type t = (Typevar.t * mono_type) list


let empty = []


let rec find (theta: t) (i : Typevar.t) =
  match theta with
  | []                                   -> None
  | (j, ty) :: tail  when Typevar.eq i j -> Some(ty)
  | _ :: tail                            -> find tail i


let rec apply_to_mono_type (theta : t) (ty : mono_type) =
  let iter = apply_to_mono_type theta in
  let (tymain, tyrng) = ty in
    match tymain with
    | TypeVariable(i) ->
        begin
          match find theta i with
          | None        -> ty
          | Some(tyaft) -> tyaft
        end
    | FuncType(tydom, tycod, tyans1, tyans2) -> (FuncType(iter tydom, iter tycod, iter tyans1, iter tyans2), tyrng)
    | _ -> ty


let rec apply_to_abstract_term (theta : t) (ast : abstract_term) =
  let iter = apply_to_abstract_term theta in
  let (astmain, ty) = ast in
  let astmainnew =
    match astmain with
    | ( Var(_) | IntConst(_) | BoolConst(_) ) -> astmain
    | Apply(ast1, ast2)                       -> Apply(iter ast1, iter ast2)
    | Lambda(varnm, ast1)                     -> Lambda(varnm, iter ast1)
    | FixPoint(varnm, ast1)                   -> FixPoint(varnm, iter ast1)
    | LetIn(varnm, ast1, ast2)                -> LetIn(varnm, iter ast1, iter ast2)
    | IfThenElse(ast0, ast1, ast2)            -> IfThenElse(iter ast0, iter ast1, iter ast2)
    | Shift(varnm, ast1)                      -> Shift(varnm, iter ast1)
    | Reset(ast1)                             -> Reset(iter ast1)
  in
    (astmainnew, apply_to_mono_type theta ty)


let compose (theta2 : t) (theta1 : t) =
  let theta1new = List.map (fun (i, ty) -> (i, apply_to_mono_type theta2 ty)) theta1 in
  let theta2new = List.filter (fun (i, ty) -> match find theta1 i with None -> true | Some(_) -> false) theta2 in
    List.append theta2new theta1new


let rec occurs (i : Typevar.t) ((tymain, _) : mono_type) =
  let iter = occurs i in
  match tymain with
  | TypeVariable(j)  when Typevar.eq i j -> true
  | FuncType(t1, t2, t3, t4)             -> (iter t1) || (iter t2) || (iter t3) || (iter t4)
  | _                                    -> false


let rec unify_sub (theta : t) (lst : (mono_type * mono_type) list) =
  match lst with
  | []                                                     -> theta
  | (((tymain1, _) as ty1), ((tymain2, _) as ty2)) :: tail ->
      begin
        match (tymain1, tymain2) with
        | (TypeVariable(i1), TypeVariable(i2)) ->
            if Typevar.eq i1 i2 then unify_sub theta tail else
              unify_sub (compose [(i1, ty2)] theta) tail

        | (TypeVariable(i1), _) ->
            if occurs i1 ty2 then raise InternalInclusionError else
              unify_sub (compose [(i1, ty2)] theta) tail

        | (_, TypeVariable(i2)) ->
            if occurs i2 ty1 then raise InternalInclusionError else
              unify_sub (compose [(i2, ty1)] theta) tail
              
        | (FuncType(tydom1, tycod1, tya1, tyb1), FuncType(tydom2, tycod2, tya2, tyb2)) -> unify_sub theta (List.append [(tydom1, tydom2); (tycod1, tycod2); (tya1, tya2); (tyb1, tyb2)] tail)

        | (IntType, IntType) -> unify_sub theta tail
        | (BoolType, BoolType) -> unify_sub theta tail
        | _                  -> raise InternalContradictionError
      end


let unify (ty1 : mono_type) (ty2 : mono_type) =
  try
    unify_sub empty [(ty1, ty2)]
  with
  | InternalInclusionError     -> raise (InclusionError(ty1, ty2))
  | InternalContradictionError -> raise (ContradictionError(ty1, ty2))

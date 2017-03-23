open Types

exception InternalInclusionError
exception InternalContradictionError
exception InclusionError of mono_type * mono_type
exception ContradictionError of mono_type * mono_type

type t = (Typevar.t * mono_type) list


let show theta =
  print_endline "+---- ---- ---- ----" ;
  List.iter (fun (i, ty) -> print_endline ("| " ^ (Typevar.to_string i) ^ " = " ^ (string_of_mono_type ty))) theta ;
  print_endline "+---- ---- ---- ----"


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
    | ListType(tycnt) -> (ListType(iter tycnt), tyrng)
    | _ -> ty


let rec apply_to_abstract_term (theta : t) (ast : abstract_term) =
  let iter = apply_to_abstract_term theta in
  let (astmain, ty) = ast in
  let astmainnew =
    match astmain with
    | ( Var(_) | IntConst(_) | BoolConst(_) ) -> astmain
    | Apply(ast1, ast2)                       -> Apply(iter ast1, iter ast2)
    | Lambda(varnm, ast1)                     -> Lambda(varnm, iter ast1)
    | FixPointOfLambda(varf, varx, ast1)      -> FixPointOfLambda(varf, varx, iter ast1)
    | LetIn(varnm, ast1, ast2)                -> LetIn(varnm, iter ast1, iter ast2)
    | IfThenElse(ast0, ast1, ast2)            -> IfThenElse(iter ast0, iter ast1, iter ast2)
    | Nil                                     -> Nil
    | Shift(varnm, ast1)                      -> Shift(varnm, iter ast1)
    | Reset(ast1)                             -> Reset(iter ast1)
  in
    (astmainnew, apply_to_mono_type theta ty)


let compose (theta2 : t) (theta1 : t) =
  let theta1new = List.map (fun (i, ty) -> (i, apply_to_mono_type theta2 ty)) theta1 in
  let theta2new = List.filter (fun (i, ty) -> match find theta1 i with None -> true | Some(_) -> false) theta2 in
    List.append theta2new theta1new


let add (theta : t) (i : Typevar.t) (ty : mono_type) =
  let rec aux acc lst =
    match lst with
    | []                                  -> (i, ty) :: theta
    | (j, t) :: tail  when Typevar.eq i j -> List.rev_append acc ((i, ty) :: tail)
    | (j, t) :: tail                      -> aux ((j, t) :: acc) tail
  in
    aux [] theta


let rec replace (theta : t) (i : Typevar.t) (tynew : mono_type) =
  List.map (fun (j, t) -> (j, subst_mono_type t i tynew)) theta


let rec occurs (i : Typevar.t) ((tymain, _) : mono_type) =
  let iter = occurs i in
    match tymain with
    | TypeVariable(j)  when Typevar.eq i j -> true
    | FuncType(t1, t2, t3, t4)             -> (iter t1) || (iter t2) || (iter t3) || (iter t4)
    | ListType(t1)                         -> iter t1
    | _                                    -> false


let rec unify_sub (acctheta : t) (eqnlst : (mono_type * mono_type) list) =
  let neweqnlst = List.map (fun (ty1, ty2) -> (apply_to_mono_type acctheta ty1, apply_to_mono_type acctheta ty2)) eqnlst in
(*
  let _ = show acctheta in (*for debug*)
  let _ = List.iter (fun (ty1, ty2) -> print_string ("[" ^ (string_of_mono_type ty1) ^ "] = [" ^ (string_of_mono_type ty2) ^ "], ")) neweqnlst in (*for debug*)
  let _ = print_endline "$" in (*for debug*)
*)
  match neweqnlst with
  | []                                                           -> acctheta
  | (((tymain1, rng1) as ty1), ((tymain2, rng2) as ty2)) :: tail ->
      begin
        match (tymain1, tymain2) with
        | (IntType, IntType) -> unify_sub acctheta tail

        | (BoolType, BoolType) -> unify_sub acctheta tail

        | (TypeVariable(i1), TypeVariable(i2)) ->
            if Typevar.eq i1 i2 then
              unify_sub acctheta tail
            else
              let ty2new = if Range.is_dummy rng2 && not (Range.is_dummy rng1) then (tymain2, rng1) else ty2 in
                unify_sub (add (replace acctheta i1 ty2new) i1 ty2new) tail

        | (TypeVariable(i1), _) ->
            if occurs i1 ty2 then raise InternalInclusionError else
              let ty2new = if Range.is_dummy rng2 && not (Range.is_dummy rng1) then (tymain2, rng1) else ty2 in
                unify_sub (add (replace acctheta i1 ty2new) i1 ty2new) tail

        | (_, TypeVariable(i2)) ->
            if occurs i2 ty1 then raise InternalInclusionError else
              let ty1new = if Range.is_dummy rng1 && not (Range.is_dummy rng2) then (tymain1, rng2) else ty1 in
                unify_sub (add (replace acctheta i2 ty1new) i2 ty1new) tail

        | (FuncType(tydom1, tycod1, tya1, tyb1), FuncType(tydom2, tycod2, tya2, tyb2)) ->
            unify_sub acctheta (List.append [(tydom1, tydom2); (tycod1, tycod2); (tya1, tya2); (tyb1, tyb2)] tail)

        | (ListType(tycnt1), ListType(tycnt2)) ->
            unify_sub acctheta ((tycnt1, tycnt2) :: tail)

        | _                  -> raise InternalContradictionError
      end


let unify (ty1 : mono_type) (ty2 : mono_type) =
  try
    unify_sub empty [(ty1, ty2)]
  with
  | InternalInclusionError     -> raise (InclusionError(ty1, ty2))
  | InternalContradictionError -> raise (ContradictionError(ty1, ty2))

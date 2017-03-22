open Types

exception UndefinedVariable of variable_name * Range.t
exception Impure of Range.t


let (@>) = Subst.apply_to_mono_type
let (@@) = Subst.compose
let fresh () =
  let i = Typevar.fresh () in ((TypeVariable(ref (Unbound(i))), Range.dummy "fresh"), i)


let rec subst_mono_type ty i tynew =
  let iter t = subst_mono_type t i tynew in
    match ty with
    | (TypeVariable({contents= Unbound(j)}), _)  when Typevar.eq i j       -> tynew
    | (TypeVariable({contents= Link(tysub)}), _) -> subst_mono_type tysub i tynew
    | (FuncType(tydom, tycod, tyans1, tyans2), tyrng) -> (FuncType(iter tydom, iter tycod, iter tyans1, iter tyans2), tyrng)
    | _                                               -> ty


let rec subst_poly_type (pty : poly_type) (i : Typevar.t) (tynew : mono_type) =
  match pty with
  | Mono(ty)                               -> Mono(subst_mono_type ty i tynew)
  | Forall(j, ptysub)  when Typevar.eq i j -> pty
  | Forall(j, ptysub)                      -> Forall(j, subst_poly_type ptysub i tynew)


let rec instantiate pty =
  match pty with
  | Mono(ty) -> ty
  | Forall(i, ptysub) ->
      let (vN, _) = fresh () in
        instantiate (subst_poly_type ptysub i vN)


let rec typecheck_pure (thetapre : Subst.t) (tyenv : Typeenv.t) (sast : source_term) =
  let (sastmain, rng) = sast in
    match sastmain with
    | SrcVar(varnm) ->
        begin
          match Typeenv.find tyenv varnm with
          | Some(pty) -> (Var(varnm), thetapre @> (instantiate pty), thetapre)
          | None     -> raise (UndefinedVariable(varnm, rng))
        end

    | SrcLambda((varnm, varrng), sast1) ->
        let (vdom, _) = fresh () in
        let (vans, _) = fresh () in
        let (e1, ty1, tyans1, theta1) = typecheck thetapre (Typeenv.add tyenv varnm (Mono(vdom))) vans sast1 in
          (Lambda(varnm, e1), (FuncType(theta1 @> vdom, ty1, theta1 @> vans, tyans1), rng), theta1)

    | SrcReset(sast1) ->
        let (vG, _) = fresh () in
        let (e1, ty1, tyans1, theta1) = typecheck thetapre tyenv vG sast1 in
        let thetaU = Subst.unify vG tyans1 in
          (Reset(e1), ty1, thetaU @@ theta1)

    | SrcIntConst(ic)  -> (IntConst(ic), (IntType, rng), thetapre)
    | SrcBoolConst(bc) -> (BoolConst(bc), (BoolType, rng), thetapre)

    | _ -> raise (Impure(rng))


and typecheck (thetapre : Subst.t) (tyenv : Typeenv.t) (tyans : mono_type) (sast : source_term) =
  let (sastmain, rng) = sast in
    match sastmain with
    | ( SrcVar(_) | SrcLambda(_, _) | SrcReset(_, _) | SrcIntConst(_) | SrcBoolConst(_) ) ->
        let (e, ty, theta) = typecheck_pure thetapre tyenv sast in
          (e, ty, tyans, theta)

    | SrcApply(sast1, sast2) ->
        let (vB, _) = fresh () in
        let (e2, ty2, tyG, theta2) = typecheck thetapre tyenv vB sast2 in
        let (e1, ty1, tyD, theta1) = typecheck theta2 tyenv tyG sast1 in
        let (vR, _) = fresh () in
        let thetaU = Subst.unify ty1 (FuncType(theta1 @> ty2, vR, tyans, theta1 @> vB), Range.dummy "tc-apply") in
          (Apply(e1, e2), thetaU @> vR, thetaU @> tyD, thetaU @@ theta1)

    | SrcLetIn((varnm, varrng), sast1, sast2) ->
        let (e1, ty1, theta1) = typecheck_pure thetapre tyenv sast1 in
        let pty1 = Typeenv.make_polymorphic tyenv ty1 in
        let (e2, ty2, tyB, theta2) = typecheck theta1 (Typeenv.add tyenv varnm pty1) tyans sast2 in
          (LetIn(varnm, e1, e2), ty2, tyB, theta2)

    | SrcShift((varnm, varrng), sast1) ->
        let (vT, _) = fresh () in
        let (vX, iX) = fresh () in
        let pty = Forall(iX, Mono((FuncType(vT, tyans, vX, vX), Range.dummy "tc-shift"))) in
        let (vG, _) = fresh () in
        let (e1, ty1, tyB, theta1) = typecheck thetapre (Typeenv.add tyenv varnm pty) vG sast1 in
        let thetaU = Subst.unify (theta1 @> vG) ty1 in
          (Shift(varnm, e1), thetaU @> vT, thetaU @> tyB, thetaU @@ theta1)

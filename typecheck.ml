open Types

exception UndefinedVariable of variable_name * Range.t


let (@>) = Subst.apply
let (@@) = Subst.compose


let typecheck_pure (tyenv : Typeenv.t) (sast : source_term) =
  let (sastmain, rng) = sast in
    match sastmain with
    | SrcVar(varnm) ->
        begin
          match Typeenv.find tyenv varnm with
          | Some(ty) -> (Var(varnm), ty, Subst.empty)
          | None     -> raise (UndefinedVariable(varnm, rng))
        end

    | SrcLambda((varnm, varrng), sast1) ->
        let vdom = TypeVariable(Typevar.fresh ()) in
        let vans = TypeVariable(Typevar.fresh ()) in
        let (e1, ty1, tyans1, theta1) = typecheck (Typeenv.add tyenv varnm (Mono(vdom))) vans sast1 in
          (Lambda(varnm, e1), FuncType(theta1 @> vdom, ty1, theta1 @> vans, tyans1)

    | SrcReset(sast1) ->
        let vans = Typevar.fresh () in
        let (e1, ty1, tyans1, theta1) = typecheck tyenv vans sast1 in
        let thetaU = Subst.unify vans tyans1 in
          (Reset(e1), ty1, thetaU @@ theta1)

    | _ -> assert false


and typecheck (tyenv : Typeenv.t) (tyans : mono_type) (sast : source_term) =
  let (sastmain, rng) = sast in
    match sastmain with
    | ( SrcVar(_) | SrcLambda(_, _) | SrcReset(_, _) ) ->
        let (e, ty, theta) = typecheck_pure tyenv sast in
          (e, ty, tyans, theta)

    | SrcApply(sast1, sast2) ->
    | SrcLetIn((varnm, varrng), sast1) ->
    | SrcShift((varnm, varrng), sast1) ->

open Types

exception UndefinedVariable of variable_name * Range.t
exception ValueRestriction of Range.t


let print_for_debug_typecheck msg =
  ()

let (@>) = Subst.apply_to_mono_type
let (@@) = Subst.compose
let fresh () =
  let i = Typevar.fresh () in ((TypeVariable(i), Range.dummy "fresh"), i)


let rec instantiate (pty : poly_type) =
  match pty with
  | Mono(ty) -> ty
  | Forall(i, ptysub) ->
      let (vN, _) = fresh () in
        instantiate (subst_poly_type ptysub i vN)


let is_pure ((sastmain, _) : source_term) =
  match sastmain with
  | ( SrcVar(_) | SrcLambda(_, _) | SrcFixPoint(_, _) | SrcReset(_, _) | SrcIntConst(_) | SrcBoolConst(_) ) -> true
  | _                                                                                                       -> false


let rec typecheck_pure (thetapre : Subst.t) (tyenv : Typeenv.t) (sast : source_term) =
  let (sastmain, rng) = sast in
    match sastmain with
    | SrcVar(varnm) ->
        begin
          match Typeenv.find tyenv varnm with
          | None      -> raise (UndefinedVariable(varnm, rng))
          | Some(pty) ->
              let (tyresmain, _) = (thetapre @> (instantiate pty)) in
              let tyres = (tyresmain, rng) in
              let _ = print_for_debug_typecheck ("Var " ^ varnm ^ " : " ^ (string_of_mono_type tyres)) in (*for debug*)
                ((Var(varnm), tyres), tyres, thetapre)
        end

    | SrcLambda((varnm, _), sast1) ->
        let (e1, tyabs, theta1) = typecheck_abstraction thetapre tyenv varnm sast1 in
          ((Lambda(varnm, e1), tyabs), tyabs, theta1)

    | SrcFixPoint((varf, _), sastabs) ->
        begin
          match sastabs with
          | (SrcLambda((varx, _), sast1), _) ->
               let (vF, _) = fresh () in
               let (e1, tyabs, theta1) = typecheck_abstraction thetapre (Typeenv.add tyenv varf (Mono(vF))) varx sast1 in
               let thetaU = Subst.unify vF tyabs in
               let tyres = thetaU @> tyabs in
                 ((FixPointOfLambda(varf, varx, e1), tyres), tyres, thetaU @@ theta1)

          | (_, rng1) -> raise (ValueRestriction(rng1))
        end

    | SrcReset(sast1) ->
        let (vG, _) = fresh () in
        let (e1, ty1, tyans1, theta1) = typecheck thetapre tyenv vG sast1 in
        let thetaU = Subst.unify vG tyans1 in
        let tyres = thetaU @> ty1 in
          ((Reset(e1), tyres), tyres, thetaU @@ theta1)

    | SrcIntConst(ic)  -> let tyres = (IntType, rng) in ((IntConst(ic), tyres), tyres, thetapre)
    | SrcBoolConst(bc) -> let tyres = (BoolType, rng) in ((BoolConst(bc), tyres), tyres, thetapre)

    | _ -> assert false


and typecheck_abstraction (thetapre : Subst.t) (tyenv : Typeenv.t) (varnm : variable_name) (sast1 : source_term) =
  let (_, rng) = sast1 in
  let (vdom, _) = fresh () in
  let (vans, _) = fresh () in
  let (e1, ty1, tyans1, theta1) = typecheck thetapre (Typeenv.add tyenv varnm (Mono(vdom))) vans sast1 in
  let tyres = (FuncType(theta1 @> vdom, ty1, theta1 @> vans, tyans1), rng) in
    (e1, tyres, theta1)


and typecheck (thetapre : Subst.t) (tyenv : Typeenv.t) (tyans : mono_type) (sast : source_term) =
  let (sastmain, rng) = sast in
    match sastmain with
    | _  when is_pure sast ->
        let (e, ty, theta) = typecheck_pure thetapre tyenv sast in
          (e, ty, tyans, theta)

    | SrcApply(sast1, sast2) ->
        let (vB, _) = fresh () in
        let (e2, ty2, tyG, theta2) = typecheck thetapre tyenv vB sast2 in
        let (e1, ty1, tyD, theta1) = typecheck theta2 tyenv tyG sast1 in
        let (vR, _) = fresh () in
        let _ = print_for_debug_typecheck ("App1 " ^ (string_of_source_term sast) ^ " : " ^ (string_of_mono_type vR)) in (*for debug*)
        let thetaU = Subst.unify ty1 (FuncType(theta1 @> ty2, vR, tyans, theta1 @> vB), Range.dummy "tc-apply") in
        let tyres = thetaU @> vR in
        let _ = print_for_debug_typecheck ("App2 " ^ (string_of_source_term sast) ^ " : " ^ (string_of_mono_type tyres)) in (*for debug*)
          ((Apply(e1, e2), tyres), tyres, thetaU @> tyD, thetaU @@ theta1)

    | SrcLetIn((varnm, varrng), sast1, sast2) ->
        if is_pure sast1 then
          let (e1, ty1, theta1) = typecheck_pure thetapre tyenv sast1 in
          let pty1 = Typeenv.make_polymorphic tyenv ty1 in
          let _ = print_for_debug_typecheck ("Let " ^ varnm ^ " : " ^ (string_of_poly_type pty1)) in (*for debug*)
          let (e2, ty2, tyB, theta2) = typecheck theta1 (Typeenv.add tyenv varnm pty1) tyans sast2 in
            ((LetIn(varnm, e1, e2), ty2), ty2, tyB, theta2)
        else
          typecheck thetapre tyenv tyans (SrcApply((SrcLambda((varnm, varrng), sast2), Range.dummy "tc-impure-let"), sast1), rng)

    | SrcIfThenElse(sast0, sast1, sast2) ->
        let (e1, ty1, tyans1, theta1) = typecheck thetapre tyenv tyans sast1 in
        let (e2, ty2, tyans2, theta2) = typecheck theta1 tyenv (theta1 @> tyans) sast2 in
        let thetaU = Subst.unify (theta2 @> ty1) ty2 in
        let thetaV = Subst.unify (theta2 @> tyans1) tyans2 in
        let thetaVU2 = thetaV @@ thetaU @@ theta2 in
        let (e0, ty0, tyans0, theta0) = typecheck thetaVU2 tyenv (thetaVU2 @> tyans2) sast0 in
        let thetaW = Subst.unify tyans0 (BoolType, Range.dummy "tc-if") in
        let thetaWVU2 = thetaW @@ thetaVU2 in
        let tyres = thetaWVU2 @> ty2 in
          ((IfThenElse(e0, e1, e2), tyres), tyres, thetaW @> tyans0, thetaWVU2)

    | SrcShift((varnm, varrng), sast1) ->
        let (vT, _) = fresh () in
        let (vX, iX) = fresh () in
        let pty = Forall(iX, Mono((FuncType(vT, tyans, vX, vX), Range.dummy "tc-shift"))) in
        let (vG, _) = fresh () in
        let (e1, ty1, tyB, theta1) = typecheck thetapre (Typeenv.add tyenv varnm pty) vG sast1 in
        let thetaU = Subst.unify (theta1 @> vG) ty1 in
        let tyres = thetaU @> vT in
          ((Shift(varnm, e1), tyres), tyres, thetaU @> tyB, thetaU @@ theta1)

    | _ -> assert false

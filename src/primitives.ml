open Types


let type_environment =
  let it = (IntType, Range.dummy "prim-int") in
  let bt = (BoolType, Range.dummy "prim-bool") in
  let ft tydom tycod tya = (FuncType(tydom, tycod, tya, tya), Range.dummy "prim-func") in
  let lt tycnt = (ListType(tycnt), Range.dummy "prim-list") in
  let v n = Typevar.of_int n in
  let tv n = (TypeVariable(v n), Range.dummy "prim-var") in
    List.fold_right (fun (varnm, pty) tyenv -> Typeenv.add tyenv varnm pty) [
      ("+",   Forall(v (-1), Forall(v (-2), Mono(ft it (ft it it (tv (-2))) (tv (-1))))));
      ("-",   Forall(v (-1), Forall(v (-2), Mono(ft it (ft it it (tv (-2))) (tv (-1))))));
      ("*",   Forall(v (-1), Forall(v (-2), Mono(ft it (ft it it (tv (-2))) (tv (-1))))));
      ("/",   Forall(v (-1), Forall(v (-2), Mono(ft it (ft it it (tv (-2))) (tv (-1))))));
      ("==",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      ("<=",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      (">=",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      ("<",   Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      (">",   Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      ("&&",  Forall(v (-1), Forall(v (-2), Mono(ft bt (ft bt bt (tv (-2))) (tv (-1))))));
      ("||",  Forall(v (-1), Forall(v (-2), Mono(ft bt (ft bt bt (tv (-2))) (tv (-1))))));
      ("not",      Forall(v (-1), Mono(ft bt bt (tv (-1)))));
      ("is_empty", Forall(v (-1), Forall(v (-2), Mono(ft (lt (tv (-2))) bt (tv (-1))))));
      ("head",     Forall(v (-1), Forall(v (-2), Mono(ft (lt (tv (-2))) (tv (-2)) (tv (-1))))));
      ("tail",     Forall(v (-1), Forall(v (-2), Mono(ft (lt (tv (-2))) (lt (tv (-2))) (tv (-1))))));
      ("::",       Forall(v (-1), Forall(v (-3), Forall(v (-3), Mono(ft (tv (-3)) (ft (lt (tv (-3))) (lt (tv (-3))) (tv (-2))) (tv (-1)))))));
    ] Typeenv.empty


let eval_environment =
  let env = Evaluator.Evalenv.create () in
  begin
    Rename.initialize () ;
    let rnenv =
      List.fold_right (fun (opnm, evtm) rnenv ->
        let (rnenvnew, evid) = Rename.add rnenv opnm in
        begin Evaluator.Evalenv.add env evid evtm ; rnenvnew end
      ) Evaluator.primitives Rename.empty
    in
      (env, rnenv)
  end

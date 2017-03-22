open Types


let type_environment =
  let it = (IntType, Range.dummy "prim-int") in
  let bt = (BoolType, Range.dummy "prim-bool") in
  let ft tydom tycod tya = (FuncType(tydom, tycod, tya, tya), Range.dummy "prim-func") in
  let v n = Typevar.of_int n in
  let tv n = (TypeVariable(v n), Range.dummy "prim-var") in
    List.fold_right (fun (varnm, pty) tyenv -> Typeenv.add tyenv varnm pty) [
      ("+",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it it (tv (-2))) (tv (-1))))));
      ("-",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it it (tv (-2))) (tv (-1))))));
      ("*",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it it (tv (-2))) (tv (-1))))));
      ("/",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it it (tv (-2))) (tv (-1))))));
      ("==", Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      ("<=", Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      (">=", Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      ("<",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      (">",  Forall(v (-1), Forall(v (-2), Mono(ft it (ft it bt (tv (-2))) (tv (-1))))));
      ("&&", Forall(v (-1), Forall(v (-2), Mono(ft bt (ft bt bt (tv (-2))) (tv (-1))))));
      ("||", Forall(v (-1), Forall(v (-2), Mono(ft bt (ft bt bt (tv (-2))) (tv (-1))))));
    ] Typeenv.empty

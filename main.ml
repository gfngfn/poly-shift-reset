open Types

type console_line = NormalLine of string | DisplayLine of string


let report_error (category : string) (lines : console_line list) =
  let rec aux lst =
    match lst with
    | [] -> ()
    | NormalLine(l) :: tail  -> begin print_endline ("    " ^ l) ; aux tail end
    | DisplayLine(l) :: tail -> begin print_endline ("      " ^ l) ; aux tail end
  in
  let first lst =
    match lst with
    | [] -> ()
    | NormalLine(l) :: tail  -> begin print_endline l ; aux tail end
    | DisplayLine(l) :: tail -> begin print_endline ("\n      " ^ l) ; aux tail end
  in
    print_string ("! [Error at " ^ category ^ "] ") ;
    first lines


let generate_description ((_, rng1) as ty1) ((_, rng2) as ty2) =
  match (Range.is_dummy rng1, Range.is_dummy rng2) with
  | (true, true)   -> ("somewhere is wrong", ty1, ty2, [])
  | (true, false)  -> ("at " ^ (Range.to_string rng2), ty2, ty1, [])
  | (false, true)  -> ("at " ^ (Range.to_string rng1), ty1, ty2, [])
  | (false, false) -> ("at " ^ (Range.to_string rng1), ty1, ty2,
                        [NormalLine("This constraint is required by the expression at " ^ (Range.to_string rng2))])


let _ =
  let filename_in = Sys.argv.(1) in
  let fin = open_in filename_in in
    Range.initialize_for_lexer () ;
    begin
      try
        let sast = Parser.main Lexer.expr (Lexing.from_channel fin) in
        let (vA, _) = Typecheck.fresh () in
        let (e, ty, tyans, theta) = Typecheck.typecheck Subst.empty Primitives.type_environment vA sast in
        let et = Subst.apply_to_abstract_term theta e in
          print_endline (string_of_abstract_term et)
      with
      | Typecheck.UndefinedVariable(varnm, rng) ->
          report_error "Typechecker" [
            NormalLine("at " ^ (Range.to_string rng));
            NormalLine("undefined variable '" ^ varnm ^ "'.");
          ]

      | Typecheck.ValueRestriction(rng) ->
          report_error "Typechecker" [
            NormalLine ("at " ^ (Range.to_string rng));
            NormalLine ("this expression in a fixed-point operator should be an abstraction.");
          ]
      | Subst.InclusionError(ty1, ty2) ->
          let (range_desc, tyindeed, tyreq, additional) = generate_description ty1 ty2 in
            report_error "Typechecker" (List.append [
              NormalLine(range_desc ^ ":");
              NormalLine("the expression has type");
              DisplayLine(string_of_mono_type tyindeed);
              NormalLine("but is expected of type");
              DisplayLine(string_of_mono_type tyreq);
            ] additional)

      | Subst.ContradictionError(ty1, ty2) ->
          let (range_desc, tyindeed, tyreq, additional) = generate_description ty1 ty2 in
            report_error "Typechecker" (List.append [
              NormalLine(range_desc ^ ":");
              NormalLine("the type of this expression");
              DisplayLine(string_of_mono_type tyindeed);
              NormalLine("is incompatible with");
              DisplayLine(string_of_mono_type tyreq);
            ] additional)
    end

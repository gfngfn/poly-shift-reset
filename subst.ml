open Types

type t = (Typevar.t * mono_type) list


let empty = []


let apply_to_mono_type theta ty = ty


let compose theta2 theta1 = theta1


let unify ty1 ty2 = []



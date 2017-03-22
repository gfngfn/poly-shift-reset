open Types

exception UndefinedVariable of variable_name * Range.t

val fresh : unit -> (mono_type * Typevar.t)
val typecheck_pure : Subst.t -> Typeenv.t -> source_term -> (abstract_term * mono_type * Subst.t)
val typecheck : Subst.t -> Typeenv.t -> mono_type -> source_term -> (abstract_term * mono_type * mono_type * Subst.t)

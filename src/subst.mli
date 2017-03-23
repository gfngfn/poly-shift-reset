open Types

exception InclusionError of mono_type * mono_type
exception ContradictionError of mono_type * mono_type

type t

val show : t -> unit
val empty : t
val apply_to_mono_type : t -> mono_type -> mono_type
val apply_to_abstract_term : t -> abstract_term -> abstract_term
val compose : t -> t -> t
val unify : mono_type -> mono_type -> t

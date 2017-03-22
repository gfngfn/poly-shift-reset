open Types

type t

val empty : t
val apply_to_mono_type : t -> mono_type -> mono_type
val compose : t -> t -> t
val unify : mono_type -> mono_type -> t

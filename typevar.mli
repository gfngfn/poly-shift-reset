type t

val initialize : unit -> unit
val fresh : unit -> t
val to_string : t -> string
val eq : t -> t -> bool

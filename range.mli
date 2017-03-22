
type t

val dummy : string -> t

val is_dummy : t -> bool

val message : t -> string

val to_string : t -> string

val unite : t -> t -> t

val make : int -> int -> int -> t

val initialize_for_lexer : unit -> unit

val update_line : Lexing.lexbuf -> unit

val from_lexer : Lexing.lexbuf -> t

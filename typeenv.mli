open Types


type t

val empty : t
val add : t -> variable_name -> poly_type -> t
val find : t -> variable_name -> poly_type option
val make_polymorphic : t -> mono_type -> poly_type

open Types

type id
type env

val string_of_id : id -> string
val initialize : unit -> unit
val empty : env
val fresh : unit -> id
val add : env -> variable_name -> (env * id)
val find : env -> variable_name -> id

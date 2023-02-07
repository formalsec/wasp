type size = int32
type address = int64
type offset = int32

type memory
type t = memory

exception Bounds

val from_symmem2 : Symmem2.t -> t

val clone : t -> t * t

val load_value : t -> address -> offset -> Types.value_type ->
  Symvalue.sym_expr

val load_packed : Memory.pack_size -> t -> address -> offset
    ->Types.value_type -> Symvalue.sym_expr

val load_string : t -> address -> string

val store_value : t -> address -> offset -> Symvalue.sym_expr -> unit

val store_packed : Memory.pack_size -> t -> address -> offset -> Symvalue.sym_expr -> unit

val to_string : t -> string

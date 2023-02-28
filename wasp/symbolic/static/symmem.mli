type size = int32
type address = int64
type offset = int32

module type MemoryBackend = sig
  type t

  exception Bounds

  val store_byte : t -> address -> Symvalue.sym_expr -> unit

  val load_byte : t -> address -> Symvalue.sym_expr

  val from_heap : Heap.t -> t

  val clone : t -> t * t

  val to_string : t -> string
end

module LazyMemory : MemoryBackend

module MapMemory : MemoryBackend

module TreeMemory : MemoryBackend

module type SymbolicMemory =
  sig
    type t

    exception Bounds

    val from_heap : Heap.t -> t

    val clone : t -> t * t

    val load_value : t -> address -> offset -> Types.value_type ->
      Symvalue.sym_expr

    val load_packed : Memory.pack_size -> t -> address -> offset
        ->Types.value_type -> Symvalue.sym_expr

    val load_string : t -> address -> string

    val store_value : t -> address -> offset -> Symvalue.sym_expr -> unit

    val store_packed : Memory.pack_size -> t -> address -> offset -> Symvalue.sym_expr -> unit

    val to_string : t -> string

  end

module LazySMem : SymbolicMemory
module MapSMem : SymbolicMemory
module TreeSMem : SymbolicMemory

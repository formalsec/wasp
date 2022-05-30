open Values
open Symvalue

type size = int32
type address = int64
type offset = int32

(*  Represents a symbolic memory  *)
type memory = (address, (value * sym_value * int)) Hashtbl.t 
type t = memory

exception Bounds

let packed_size = function
  | Memory.Pack8 -> 1
  | Memory.Pack16 -> 2
  | Memory.Pack32 -> 4

(*  Create an empty symbolic memory  *)
let alloc sz = 
  let mem : memory = Hashtbl.create sz in
  mem

let size mem = Hashtbl.length mem

(* String representation of the symbolic memory *)
let to_string mem = 
  Hashtbl.fold (
    fun addr (cv, sv, sz) acc ->
      "(" ^ (string_of_int (Int64.to_int addr)) ^ "-> Value: " ^ (Symvalue.to_string sv) ^
      "," ^ (string_of_value cv) ^ "; Size: " ^ (string_of_int sz) ^ ")\n" ^
      acc
  ) mem ""

let load_byte mem a =  0

let store_byte mem a b = ()

let load_bytes mem a n = "bytes"

let store_bytes mem a bs = ()

let effective_address a o =
  let ea = Int64.(add a (of_int32 o)) in
  if I64.lt_u ea a then raise Bounds;
  ea

(*  Gets a variable from the symbolic memory  *)
let load_value mem a o t = 
  let ea = effective_address a o in
  let (cv, sv, sz) = try Hashtbl.find mem ea with Not_found -> 
    failwith ("Value is not stored in memory. MEMORY STATE: \n" ^ (to_string mem))
  in
  if (Types.size t = sz) then (cv, sv) else failwith "Invalid size query."

(*  Verifies if the offset is available in the specified address  *)
let is_addr_available (mem : memory) (laddr : int64) (lsize : int) : (bool * int64 option) = 
  Hashtbl.fold (
    fun raddr rval acum -> 
      (*let raddr = Int64.to_int key in*)
      match acum with
      | false, _
      | _, Some _-> acum
      | true, None ->
        let (_, _, rsize) = rval in
        if laddr = raddr && lsize < rsize then 
          (false, Some Int64.(add raddr (of_int lsize)))
        else if laddr > raddr && Int64.((add laddr (of_int lsize)) = (add raddr (of_int rsize))) then 
          (false, Some raddr)
        (* TO MERGE *)
        else if laddr < raddr && Int64.(add laddr (of_int lsize)) > raddr then 
          (true, Some raddr)
        else (true, None)
      ) mem (true, None)

(**
 *    |       |         |       |
 *    |       |         |       |
 *    |-------|<65508   |-------|<65504
 *    |       |         |       |
 *    |       |         |  4b   |           laddr = raddr => saddr = raddr + lsize =>
 *    |       |  SPLIT  |       |           => saddr = waddr + 4
 *    |  8b   |  ====>  |.......|<65504
 *    |       |         |       |           laddr > raddr => saddr = raddr =>
 *    |       |         |  4b   |           => saddr = waddr - 4
 *    |       |         |       |
 *    |-------|<65500   |-------|<65500
 *    |       |         |       |
 *)
let split_key (mem : memory) (saddr : int64) (waddr : int64) (wsize : int) : bool =
  let (cval, sval, size) = 
    try Hashtbl.find mem saddr with
    | Not_found -> Hashtbl.find mem waddr 
  in
  match sval with
  | Value (I64 x) when x = Int64.of_int 0 ->
      let zero32  = I32 (Int32.of_int 0) in
      if Int64.((saddr = (add waddr (of_int 4))) || (saddr = (sub waddr (of_int 4)))) then (
        Hashtbl.replace mem saddr (zero32, Value zero32, 4);
        true
      ) else if (saddr = waddr) then ( 
        Hashtbl.replace mem Int64.(add saddr (of_int 4)) (zero32, Value zero32, 4);
        true
      ) else false
  | Value (I64 _) ->
      let zero32  = I32 (Int32.of_int 0) in
      if Int64.((saddr = (add waddr (of_int 4))) || (saddr = (sub waddr (of_int 4)))) then (
        Hashtbl.replace mem saddr (zero32, Value zero32, 4);
        true
      ) else if (saddr = waddr) then ( 
        Hashtbl.replace mem Int64.(add saddr (of_int 4)) (zero32, Value zero32, 4);
        true
      ) else false
  | _ -> false

(*  Adds a variable to the symbolic memory  *)
let store_value mem a o v =
  let (c, sy) = v in
  let ty_size = (Types.size (Values.type_of c)) in
  let v' = (c, sy, ty_size) in
  let ea = effective_address a o in
  let (available, key) = is_addr_available mem ea ty_size in
  if available = true then (
    match key with
    (* MERGE *)
    | Some daddr -> 
        Hashtbl.remove mem daddr;
        Hashtbl.replace mem ea v'
    | None ->
        try 
          let (_, _, sz) = Hashtbl.find mem ea in
          if ty_size = sz then Hashtbl.replace mem ea v' else
            failwith ("Invalid write of size" ^ (string_of_int ty_size))
        with Not_found -> Hashtbl.add mem ea v'
  ) else (
    match key with
    (* SPLIT *)
    | Some saddr -> 
        if split_key mem saddr ea ty_size then 
          Hashtbl.replace mem ea v'
        else 
          failwith ((Int64.to_string ea) ^ " does not fit in " ^ (Int64.to_string saddr))
    | None -> 
        failwith ("Write of size " ^ (string_of_int ty_size) ^ " overwrites memory.")
  )

let load_packed sz mem a o t = 
  let ea = effective_address a o in
  let (cv, sv, size) = try Hashtbl.find mem ea with Not_found ->
    failwith ("Value not in memory. MEMORY STATE: \n" ^ (to_string mem) ^ "\n")
  in
  if (packed_size sz = size) then (cv, sv) else failwith "Invalid size query."

let store_packed sz mem a o v =
  let (c, sy) = v in
  let ty_size = packed_size sz in
  let v' = (c, sy, ty_size) in
  let ea = effective_address a o in 
  let (available, key) = is_addr_available mem ea ty_size in
  if available = true then (
    match key with
    (* MERGE *)
    | Some daddr -> 
        Hashtbl.remove mem daddr;
        Hashtbl.replace mem ea v'
    | None ->
        try 
          let (_, _, sz) = Hashtbl.find mem ea in
          if ty_size = sz then Hashtbl.replace mem ea v' else
            failwith ("Invalid write of size" ^ (string_of_int ty_size))
        with Not_found -> Hashtbl.add mem ea v'
  ) else (
    match key with
    (* SPLIT *)
    | Some saddr -> 
        if split_key mem saddr ea ty_size then 
          Hashtbl.replace mem ea v'
        else 
          failwith ((Int64.to_string ea) ^ " does not fit in " ^ (Int64.to_string saddr))
    | None -> 
        failwith ("Write of size " ^ (string_of_int ty_size) ^ " overwrites memory.")
  )


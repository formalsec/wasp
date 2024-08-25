let on_debug = ref false

let debug fmt =
  if !on_debug then Format.printf fmt
  else Format.ifprintf Format.err_formatter fmt

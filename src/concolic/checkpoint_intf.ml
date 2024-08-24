module type S = sig
  type config

  val is_checkpoint : config -> bool
end

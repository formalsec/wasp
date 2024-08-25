module Let_syntax = struct
  module Result = struct
    let ( let* ) = Result.bind

    let ( let+ ) v f = Result.map f v
  end
end

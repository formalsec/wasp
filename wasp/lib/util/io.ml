let safe_mkdir path =
  if not (Sys.file_exists path) then ignore (Sys.command ("mkdir -p " ^ path))

let save_file path data =
  let oc = open_out path in
  output_string oc data;
  close_out oc

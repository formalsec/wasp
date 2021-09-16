let safe_mkdir path =
  if not (Sys.file_exists path) then
    Unix.mkdir path 0o755

let save_file path data =
  let oc = open_out path in
  output_string oc data;
  close_out oc

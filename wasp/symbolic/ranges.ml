open Printf

let old_range_list (lst : int list) : string =
  let ranging = ref false in
  (*let lines = ref lst in*)
  let useless_lines = ref [] in
  let filelines = Batteries.File.lines_of "useless_lines.txt" in
  Batteries.Enum.iter (fun l -> if l<>"" then (useless_lines := !useless_lines @ [(int_of_string l)])) filelines;

  (*if (List.max !useless_lines) > (List.max lst) then
  	(
  		List.iter (fun f -> if f <= (List.max lst) then lines := !lines @ [f]) !useless_lines;

  	)
  else (lines := !lines @ !useless_lines);*)
  (*let sorted = List.sort_unique compare !lines in*)
  let sorted = List.sort_uniq compare lst in

  (* Iterate function by function *)
  let functions = Batteries.File.lines_of "functions.txt" in
  let ranges = ref "" in
  let total_lines = ref 0 in
  let total_passed_lines = ref 0 in
  Batteries.Enum.iter (fun l ->
    let str = Str.split (Str.regexp "-") l in
    let func_start = (int_of_string (List.nth str 0))  in
    let func_finish = (int_of_string (List.nth str 1)) in
    let size = (func_finish - func_start) in
    total_lines := !total_lines + size;
    let count = ref 0 in

    ranges := !ranges ^ "Function [" ^ l ^ "]: ";

    let start = ref 0 in
    let length = List.length sorted in
    for i=0 to length-2 do
      if ((List.nth sorted i) >= func_start) && ((List.nth sorted i) <= func_finish) then (
          if (((List.nth sorted i)+1) = (List.nth sorted (i+1))) && (!ranging = false)
            then(
              ranging := true;
              start := (List.nth sorted i)
            )
        else if (((List.nth sorted i)+1) = (List.nth sorted (i+1))) && (!ranging = true)
          then(
            ranges := !ranges
          )
        else if (((List.nth sorted i)+1) <> (List.nth sorted (i+1))) && (!ranging = true)
          then(
            if (List.memq ((List.nth sorted (i+1))-1) !useless_lines) then (
              ranges := !ranges
            )
            else(
              let to_use = ref false in
              for j=((!start)-1) to (List.nth sorted i) do
                if (List.memq j lst) then to_use := true
              done;
              if !to_use = true then (
                ranges := !ranges ^ "[" ^ (string_of_int !start) ^ "-" ^ (string_of_int ((List.nth sorted i))) ^ "]; ";
                count := !count + ((List.nth sorted i)-(!start))
              );
              ranging := false
            )
          )
        else if (((List.nth sorted i)+1) <> (List.nth sorted (i+1))) && (!ranging = false)
          then(
            if(List.memq (List.nth sorted i) lst) then (
              ranges := !ranges ^ (string_of_int ((List.nth sorted i))) ^ "; ";
              count := !count + 1
            )
          )
    ) else (
      if !ranging = true then (
        ranges := !ranges ^ "[" ^ (string_of_int !start) ^ "-" ^ (string_of_int func_finish) ^ "]; ";
        count := !count + ((func_finish)-(!start));
        ranging := false
      )
    )
    done;
    let func_coverage = ((float_of_int !count) /. (float_of_int size)) *. 100. in
    total_passed_lines := !total_passed_lines + !count;
    ranges := !ranges ^ "\t>> Function coverage: " ^ (string_of_float func_coverage) ^ "%";
    ranges := !ranges ^ "\n";
  ) functions;

  let program_percentage = ((float_of_int !total_passed_lines) /. (float_of_int !total_lines)) *. 100. in
  ranges := !ranges ^ "\n\n>>>>TOTAL PROGRAM COVERAGE: " ^ (string_of_float program_percentage) ^ "%\n";
  !ranges


let range_list (lst : int list) : string =
  let useless_lines = ref [] in
  let filelines = Batteries.File.lines_of "useless_lines.txt" in
  (* Fill the useless lines array *)
  Batteries.Enum.iter (fun l -> if l<>"" then (useless_lines := !useless_lines @ [(int_of_string l)])) filelines;
  (* Sort the traversed lines *)
  let sorted = List.sort_uniq compare lst in

  (* Iterate function by function *)
  let functions = Batteries.File.lines_of "functions.txt" in
  let ranges = ref "" in (* The string to return *)
  let total_lines = ref 0 in (* to count the total number of lines in the file *)
  let sum_percentages = ref 0. in
  let count_functions = ref 0 in
  Batteries.Enum.iter (fun l ->
    let str = Str.split (Str.regexp "-") l in
    let func_start = (int_of_string (List.nth str 0))  in
    let func_finish = (int_of_string (List.nth str 1)) in
    let size = (func_finish - func_start) in
    total_lines := !total_lines + size;

    let useless_lines_func = ref 0 in
    let passed_lines_func = ref 0 in

    (* While we have numbers inside this function *)
    for i = 0 to (List.length sorted)-1 do
      if ((List.nth sorted i) >= func_start) && ((List.nth sorted i) <= func_finish)
      then (
        passed_lines_func := !passed_lines_func + 1;
      )
    done;

    (* While we have useless lines inside this function *)
    for i = 0 to (List.length !useless_lines)-1 do
      if ((List.nth !useless_lines i) > func_start) && ((List.nth !useless_lines i) < func_finish)
      then (
        useless_lines_func := !useless_lines_func + 1;
      )
    done;


    let func_coverage = ((float_of_int !passed_lines_func)  /. ((float_of_int (size - !useless_lines_func)))) *. 100. in
    sum_percentages := !sum_percentages +. func_coverage;
    ranges := !ranges ^ "\t>> Function coverage: " ^ (string_of_float func_coverage) ^ "%";
    ranges := !ranges ^ "\n";
    count_functions := !count_functions + 1
  ) functions;

  let program_percentage = (!sum_percentages /. (float_of_int !count_functions)) in
  ranges := !ranges ^ ">>>> TOTAL PROGRAM COVERAGE: " ^ (string_of_float program_percentage) ^ "%";
  !ranges


let trim str =
  if str = "" then "" else
  let search_pos init p next =
    let rec search i =
      if p i then raise(Not_found) else
      match str.[i] with
      | ' ' | '\r' | '\t' | '\n'-> search (next i)
      | _ -> i
    in
    search init
  in
  let len = String.length str in
  try
    let left = search_pos 0 (fun i -> i >= len) (succ)
    and right = search_pos (len - 1) (fun i -> i < 0) (pred)
    in
    String.sub str left (right - left + 1)
  with
  | Not_found -> ""

 let save_useful_lines (filename : string) : unit =
    let ch : Stdlib.in_channel = Stdlib.open_in filename in
    let s = really_input_string ch (in_channel_length ch) in
    Stdlib.close_in ch;
    let str = Str.split (Str.regexp "[\n]") s in
  	let oc_1 = open_out "useless_lines.txt" in
  	for i=0 to (List.length str)-1 do
  		let l = trim (List.nth str i) in
  		if (l="") || (l="(") || (l=")") || (Batteries.String.starts_with l ";;") || (Batteries.String.starts_with l "(then") || (Batteries.String.starts_with l "(else") || (Batteries.String.starts_with l "(local ") then
  			(fprintf oc_1 "%d\n" (i+1))
  	done;
  	close_out oc_1;
    (* Now save the function lines *)
    let oc = open_out "functions.txt" in
    let ignore = ref false in
   	for i=0 to (List.length str)-1 do
        let l = List.nth str i in
        if ((Batteries.String.starts_with l "    (func $main") || (Batteries.String.starts_with l "\t(func $main")) then (ignore := true) else (
          if ((Batteries.String.starts_with l "    (func") || (Batteries.String.starts_with l "\t(func")) then
            (fprintf oc "%d-" (i+1))
          else (if (Batteries.String.starts_with l "    )") || (Batteries.String.starts_with l "\t)") then
            ( if (!ignore)=true then (ignore := false) else (
              fprintf oc "%d\n" (i+1)))
          )
        )
    done;
    close_out oc

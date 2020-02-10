

let read_file (filename:string): unit=
  let in_channel = open_in filename in
  let error = ref ""
  try
    while true do
      print_endline @@ input_line in_channel
    done;
  with e ->
    close_in in_channel;
    !error = e


let usage () : unit = print_string 
  "usage : expert_system input_file\n
  \tinput_file\tfile to evaluate\n"

let _ = 
  if (Array.length Sys.argv <> 2) 
  then usage ()
  else
    let (opened_file: unit) = read_file Sys.argv.(1) in ()


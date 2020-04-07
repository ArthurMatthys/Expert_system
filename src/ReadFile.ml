open Unix

let rec _read (in_chan:in_channel): string list =
  try 
    let line = input_line in_chan in
    if String.equal line "" then 
    _read in_chan
    else line :: _read in_chan
  with 
    End_of_file -> []

let read_file (filename:string): (string list, string) result=
   try
      Unix.access filename [Unix.R_OK ; Unix.F_OK];
      if Sys.is_directory filename
      then Result.Error "Is a directory"
      else
        let in_chan = open_in filename in
        Result.Ok (_read in_chan)
    with Unix_error(e, m1, m2) -> Result.Error (Unix.error_message e)
  
   



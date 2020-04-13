open Unix

let _read (in_chan:in_channel): string list =
  let rec _rec_read n =
    match input_line in_chan with
      | line -> if String.equal line "" then 
                    _rec_read in_chan
                  else line :: _rec_read in_chan
      | exception End_of_file -> []
in _rec_read in_chan

let read_file (filename:string): (string list, string) result=
   try
      Unix.access filename [Unix.R_OK ; Unix.F_OK];
      if Sys.is_directory filename
      then Result.Error "Is a directory"
      else
        let in_chan = open_in filename in
        let lines = _read in_chan in
        if List.length lines > 10000
        then Result.Error ("The file contain too many lines")
        else Result.ok lines
    with Unix_error(e, m1, m2) -> Result.Error (Unix.error_message e)
  
   



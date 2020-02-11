open Unix
open ReadFile

let alphabet = ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";]
let conditions = ["!";"+";"|";"^"]
let implications = ["=";"?";">";"<"]

let explode s : string list=
    let rec exp i l =
        if i < 0 then l else exp (i - 1) (Char.escaped s.[i] :: l) in
    exp (String.length s - 1) []


let rec remove_comment (lst:string list) :string list = match lst with
  | [] -> []
  | h::t -> if h = "#" then [] else h :: remove_comment t


let print_lex ((read, value):(string*int)):unit =
  Printf.printf "char : %s\tvalue : %d\n" read value


let print_lexed_line (lex_line:(string*int) list):unit =
  let _ = List.map print_lex lex_line in 
  print_newline ()


let lexer (str:string): ((string*int) list)=
  let (str_cleaned: string list) = explode @@ String.escaped str in
  let rec lex (depth:int) (lst:string list) : ((string*int )list) = match lst with
    | [] -> []
    | h::t -> let comp = ((=) h) in
      if h = " " 
      then lex depth t
      else if List.exists comp alphabet 
        then (h, 1) :: lex depth t
        else if List.exists comp conditions
          then (h, 2) :: lex depth t
          else if List.exists comp implications
            then (h, 3) :: lex depth t
            else if h = "("
            then (h, depth + 4) :: (lex (depth+1) t)
            else if h = ")"
              then (h, depth + 3) :: (lex (depth-1) t)
              else (h, -1) :: lex depth t
  in
  if List.exists ((=) "#") str_cleaned
  then lex 0 @@ remove_comment str_cleaned
  else lex 0 str_cleaned


let usage () : unit = print_string 
  "usage : expert_system input_file\n
  \tinput_file\tfile to evaluate\n"

let _ = 
  if (Array.length Sys.argv <> 2) 
  then usage ()
  else
    let (file_res: (string list, string) result) = read_file Sys.argv.(1) in
    if Result.is_error file_res
    then Printf.printf "issue reading file \"%s\" : %s" Sys.argv.(1) (Result.get_error file_res)
    else
      let (file_content: string list) = Result.get_ok file_res in
      let (lexer_res: (string*int) list list) = List.map lexer file_content in
      let _ = List.map print_lexed_line lexer_res in ()



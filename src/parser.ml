open Unix
open ReadFile
open Checker

let std_err = 2


let usage () : unit = print_string 
  "usage : expert_system input_file\n
  \tinput_file\tfile to evaluate\n"


let print_err = Printf.eprintf 

let explode (s:string) : string list=
    let rec exp i l =
        if i < 0 then l else exp (i - 1) (Char.escaped s.[i] :: l) in
    exp (String.length s - 1) []


let print_lex ((read, value):(string*int)):unit =
  Printf.printf "char : %s\tvalue : %d\n" read value


let print_lexed_line (lex_line:(string*int) list):unit =
  let _ = List.map print_lex lex_line in 
  print_newline ()


let alphabet = ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";]
let conditions = ["!";"+";"|";"^"]
let implications = ["=";"?";">";"<"]


let lexer (str:string): ((string*int) list)=
  let rec remove_comment (lst:string list) :string list = match lst with
    | [] -> []
    | h::t -> if h = "#" then [] else h :: remove_comment t
  in
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


let rec remove_empty_line (file:(string*int) list list): (string*int) list list=
  match file with
  | [] -> []
  | h::t -> if List.length h <> 0
    then h::(remove_empty_line t)
    else remove_empty_line t


let split_file (data:(string*int) list list) : ((string*int) list list)*((string*int) list)*((string*int) list) = 
  let (query:(string*int) list) = List.hd @@ List.filter (fun e -> List.nth e 0 = ("?",3)) data in
  let (init:(string*int) list) = List.hd @@ List.filter (fun e -> List.nth e 0 = ("=",3)) data in
  let (facts:(string*int) list list) = List.filter (fun e -> (not (List.nth e 0 = ("=",3))) && (not (List.nth e 0 = ("?", 3)))) data in
  (facts, init, query)


let _ = 
  if (Array.length Sys.argv <> 2) 
  then usage ()
  else
    let (file_res: (string list, string) result) = read_file Sys.argv.(1) in
    if Result.is_error file_res
    then Printf.eprintf "issue reading file \"%s\" : %s\n" Sys.argv.(1) (Result.get_error file_res)
    else
      let (file_content: string list) = Result.get_ok file_res in
      let (lexer_res: (string*int) list list) = List.map lexer file_content in
      let (check_res: (unit, string) result) = check_input lexer_res in 
      if Result.is_error check_res
      then Printf.eprintf "%s\n" @@ Result.get_error check_res
      else let cleaned_file = remove_empty_line lexer_res in
        let (facts, init, query) = split_file cleaned_file in
        let _ = List.map print_lexed_line facts in ()



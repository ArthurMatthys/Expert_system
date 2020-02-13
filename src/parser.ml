open Unix
open ReadFile
open Checker

let std_err = 2


let usage () : unit = print_string 
    "usage : expert_system [file] [-b]\n
  \tinput_file\tfile to evaluate\n
  \t\"-b\"\tChange the way to evaluate\n"


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


let index_of (lst:string list) (search:string): int=
  let rec loop (str:string list) (index:int): int = match str with
    | [] -> -1
    | h::t -> if h = search
      then index
      else loop t (index+1)
  in
  loop lst 0

let alphabet = ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";]
let implications = ["=";"?";">";"<"]
let conditions = ["^";"|";"+";"!"]


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
        else if List.exists comp implications
        then (h, 2) :: lex depth t
          else if List.exists comp conditions
          then (h, (3 + (index_of conditions h))) :: lex depth t
            else if h = "("
              then (h, depth) :: (lex (depth+1) t)
              else if h = ")"
                then (h, depth - 1) :: (lex (depth-1) t)
                else (h, -1) :: lex depth t
  in
  if List.exists ((=) "#") str_cleaned
  then lex 7 @@ remove_comment str_cleaned
  else lex 7 str_cleaned


let rec remove_empty_line (file:(string*int) list list): (string*int) list list=
  match file with
  | [] -> []
  | h::t -> if List.length h <> 0
    then h::(remove_empty_line t)
    else remove_empty_line t


let split_file (data:(string*int) list list) : ((string*int) list list)*((string*int) list)*((string*int) list) = 
  let (query:(string*int) list) = List.hd @@ List.filter (fun e -> List.nth e 0 = ("?",2)) data in
  let (init:(string*int) list) = List.hd @@ List.filter (fun e -> List.nth e 0 = ("=",2)) data in
  let (facts:(string*int) list list) = List.filter (fun e -> (not (List.nth e 0 = ("=",2))) && (not (List.nth e 0 = ("?", 2)))) data in
  (facts, init, query)


type 'a binary_tree =
  | Empty
  | Node of 'a * 'a binary_tree * 'a binary_tree


type expr =
  | Empty
  | Leaf of string
  | Ope of (string -> string -> bool)
  | Value of bool

let print_facts (fact, value_fact:(string*bool)) : unit =
  Printf.printf "fact : %s\tvalue : %b\n" fact value_fact

let get_facts (lst:(string*int) list list) : (string*bool) list =
  let (lst_flatten:(string*int) list) = List.flatten lst in
  let rec add_fact (facts:(string*int) list) (statements : (string*bool) list): (string*bool) list = match facts with
    | [] -> statements
    | (h,v) :: t -> if List.exists ((=) (h, false)) statements || v <> 1
      then add_fact t statements
      else add_fact t ((h, false)::statements)
  in
  add_fact lst_flatten []



let _ = 
  if not @@ ((Array.length Sys.argv = 2) || (Array.length Sys.argv = 3 && Sys.argv.(2) = "-b"))
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
        let lst_fact = get_facts facts in
        let (query_check:(unit,string)result) = check_consistency lst_fact query in
        if Result.is_error query_check
        then Printf.eprintf "Fact in query wasn't found in facts list : %s\n" @@ Result.get_error query_check
        else
          let (init_check:(unit,string)result) = check_consistency lst_fact init in
          if Result.is_error init_check
          then Printf.eprintf "Fact in init wasn't found in facts list : %s\n" @@ Result.get_error init_check
          else 
            let _ = print_endline "facts :" in
            let _ = List.map print_lexed_line facts in
            let _ = print_endline "query :" in
            let _ = List.map print_lex query in
            let _ = print_endline "init : " in
            let _ = List.map print_lex init in 
            let _ = print_endline "starting values : " in
            let _ = List.map print_facts lst_fact in ()



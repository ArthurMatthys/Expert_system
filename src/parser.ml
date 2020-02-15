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

let string_of_bool_option (opt:bool option): string = match opt with
  | None -> "None"
  | Some x -> string_of_bool x


let print_facts (fact, value_fact:(string*(bool option))) : unit =
  Printf.printf "fact : %s\tvalue : %s\n" fact @@ string_of_bool_option value_fact


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
          then (h, (3 + 4*depth + (index_of conditions h))) :: lex depth t
            else if h = "("
              then (h, 3 + 4*(depth+1)) :: (lex (depth+1) t)
              else if h = ")"
                then (h, 3 + 4*depth) :: (lex (depth-1) t)
                else (h, -1) :: lex depth t
  in
  if List.exists ((=) "#") str_cleaned
  then lex 0 @@ remove_comment str_cleaned
  else lex 0 str_cleaned

let map_depth (lex_str:(string*int) list): (string*int) list = 
  let rec map (str:(string*int) list) (depth: int) : (string*int) list =
    match str with
    | [] -> []
    | (h, _)::t -> if h = "("
      then (h, depth+1) :: map t (depth+1)
      else if h = ")"
        then (h, depth) :: map t (depth-1)
        else (h, depth) :: map t depth
  in 
  map lex_str 0

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
  | Ope of string
        (*
          | Ope of (string -> string -> bool)
        *)
  | Value of bool

let get_facts (lst:(string*int) list list) : (string*(bool option)) list =
  let (lst_flatten:(string*int) list) = List.flatten lst in
  let rec add_fact (facts:(string*int) list) (statements : (string*(bool option)) list): (string*(bool option)) list = match facts with
    | [] -> statements
    | (h,v) :: t -> if List.exists ((=) (h, None)) statements || v <> 1
      then add_fact t statements
      else add_fact t ((h, None)::statements)
  in
  add_fact lst_flatten []

let remove_parenthesis (facts_list:(string*int)list) : (string*int) list =
  let rec rm_parent (facts_lst:(string*int)list) : (string*int) list =
    match facts_lst with
    | [] -> []
    | h::[] -> []
    | h::t -> h :: rm_parent t
  in
  match facts_list with 
  | [] -> []
  | (h,v)::t -> if h = "("
    then rm_parent t
    else facts_list

let count_even_parenthesis (facts_list:(string*int)list) : bool =
  let rec count (facts_lst:(string*int)list) (nbr:int) : bool =
    match facts_lst with
    | [] -> nbr = 0
    | (h,_)::t -> if h = "("
      then count t (nbr+1)
      else
        if h = ")"
        then count t (nbr-1)
        else count t nbr
  in
  count facts_list 0

let filteri (func: int -> 'a -> bool) (lst:'a list): 'a list = 
  let rec loop_filteri (func: int -> 'a -> bool) (lst:'a list) (index: int): 'a list =
    match lst with
    | [] -> []
    | h::t -> if func index h
      then h :: loop_filteri func t (index + 1)
      else loop_filteri func t (index + 1)
  in
  loop_filteri func lst 0


let rec btree_of_list (facts_list:(string*int)list) : (expr binary_tree) =
  let rec find_priority_ope (facts_lst:(string*int)list) (index_max: int) (value: int) (index: int): int =
    match facts_lst with
    | [] -> index_max
    | (h,v)::t -> if v >= 3 && (value = 0 || v <= value) 
                  then find_priority_ope t index v (index + 1)
                  else find_priority_ope t index_max value (index + 1)
  in
  match facts_list with
  | [] -> Empty
  | (h,v)::[] -> Node (Leaf h, Empty, Empty)
  | _ -> let split_index = find_priority_ope facts_list 0 0 0 in
    let ((ope, _): (string*int)) = List.nth facts_list split_index in
    let _ = print_string @@ "index : " ^ (string_of_int split_index) in
    let _ = print_lexed_line facts_list in
    Node (Ope ope,
          btree_of_list @@ remove_parenthesis @@ filteri (fun index _ -> index < split_index) facts_list,
         btree_of_list @@ remove_parenthesis @@ filteri (fun index _ -> index > split_index) facts_list)

let rec print_tree (tree: expr binary_tree): unit =
  match tree with
  | Empty ->()
  | Node (Ope node, right, left) -> print_tree left; print_string node; print_tree right
  | Node (Leaf node, right, Empty) -> print_string node; print_tree right
  | Node (Leaf node, Empty, left) -> print_tree left; print_string node
  | Node (_,_,_) -> ()

let rec remove_imply (lst:(string*int) list) : (string*int) list =
  match lst with 
  | [] -> []
  | (h,v)::t -> if v = 2
    then []
    else (h,v):: remove_imply t

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
      else let (cleaned_file: (string*int) list list) = remove_empty_line lexer_res in
        let (facts, init, query) = split_file cleaned_file in
        let (lst_fact:(string*(bool option)) list) = get_facts facts in
        let (query_check:(unit,string)result) = check_consistency lst_fact query in
        if not @@ List.for_all count_even_parenthesis facts 
        then Printf.eprintf "There is a line where a parenthesis is not matched"
        else
          if Result.is_error query_check
          then Printf.eprintf "Fact in query wasn't found in facts list : %s\n" @@ Result.get_error query_check
          else
            let (init_check:(unit,string)result) = check_consistency lst_fact init in
            if Result.is_error init_check
            then Printf.eprintf "Fact in init wasn't found in facts list : %s\n" @@ Result.get_error init_check
            else 
              let (lst_tree:(expr binary_tree) list) = List.map (fun e -> btree_of_list @@ remove_imply e) facts in
              let _ = print_endline "facts :" in
              let _ = List.map print_lexed_line facts in
              let _ = print_endline "query :" in
              let _ = List.map print_lex query in
              let _ = print_endline "init : " in
              let _ = List.map print_lex init in 
              let _ = print_endline "starting values : " in
              let _ = List.map print_facts lst_fact in
              let _ = print_endline "tree : " in
              let _ = List.map print_tree lst_tree in ()



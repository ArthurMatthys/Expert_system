open Unix
open Btree
open Checker
open Lexer
open Library
open ReadFile

let print_err = Printf.eprintf 

let usage () : unit = print_string 
    "usage : expert_system [file] [-b]\n
  \tinput_file\tfile to evaluate\n
  \t\"-b\"\tChange the way to evaluate\n"


let string_of_bool_option (opt:bool option): string = match opt with
  | None -> "None"
  | Some x -> string_of_bool x


let print_facts (fact, value_fact:(string*(bool option))) : unit =
  Printf.printf "fact : %s\tvalue : %s\n" fact @@ string_of_bool_option value_fact


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


let get_facts (lst:(string*int) list list) : (string*(bool option)) list =
  let (lst_flatten:(string*int) list) = List.flatten lst in
  let rec add_fact (facts:(string*int) list) (statements : (string*(bool option)) list): (string*(bool option)) list = match facts with
    | [] -> statements
    | (h,v) :: t -> if List.exists ((=) (h, None)) statements || v <> 1
      then add_fact t statements
      else add_fact t ((h, None)::statements)
  in
  add_fact lst_flatten []


let rec remove_imply (lst:(string*int) list) : (string*int) list =
  match lst with 
  | [] -> []
  | (h,v)::t -> if v = 2
    then []
    else (h,v):: remove_imply t


let do_mandatory (facts:(string*int) list list) (facts_dict:((string, bool option) Hashtbl.t)): unit = ()



let do_bonus (facts:(string*int) list list) (facts_dict:((string, bool option) Hashtbl.t)): unit = ()


let initialize_facts (lst_facts: (string*(bool option)) list) (init: (string*int) list) : (string, bool option) Hashtbl.t =
  let m = Hashtbl.create 26 in m

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
        let (lst_facts:(string*(bool option)) list) = get_facts facts in
        let (query_check:(unit,string)result) = check_consistency lst_facts query in
        if not @@ List.for_all count_even_parenthesis facts 
        then Printf.eprintf "There is a line where a parenthesis is not matched"
        else
          if Result.is_error query_check
          then Printf.eprintf "Fact in query wasn't found in facts list : %s\n" @@ Result.get_error query_check
          else
            let (init_check:(unit,string)result) = check_consistency lst_facts init in
            if Result.is_error init_check
            then Printf.eprintf "Fact in init wasn't found in facts list : %s\n" @@ Result.get_error init_check
            else
              if Array.length Sys.argv = 2
              then do_mandatory facts (initialize_facts lst_facts init)
              else do_bonus facts (initialize_facts lst_facts init)



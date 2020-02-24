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

let forbidden_chars = ["<=>";"|"]


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


let print_hash (key:string) (value:bool option) : unit =
  if Option.is_none value
  then let _ = print_endline @@ key ^ " -> None" in ()
  else let _ = print_endline @@ key ^ " -> " ^ (string_of_bool @@ Option.get value) in ()

(*
  Backward-chaining inference engine
 *)
let find_tree (tree_lst : exp_ast list) (fact : string) : exp_ast list =
(*
  Recursive function that parses the tree and checks wether the letter is found on the right side (after the implication)
*)
  let rec dig_right (tree : exp_ast) : bool = 
  match tree with
    | Imply (left, right) -> dig_right right
    | Empty -> false
    | Letter l -> if l = fact then true else false
    | And (left, right) -> dig_right left || dig_right right
    | Not (right) -> dig_right right
    | Or (left, right) -> dig_right left || dig_right right
    | Xor (left, right) -> dig_right left || dig_right right
    | _ -> false
  in
  (* Function that retrieves the tree if a true is found, otherwise an empty *)
  let dig (tree : exp_ast) : exp_ast =
    let (result: bool) = dig_right tree in
    match result with
    | true -> tree
    | false -> Empty
  in
  (* Create a list out of it *)
  let (tmp_result: exp_ast list) = List.map (fun x -> dig x) tree_lst in
  (* Filter all the empty trees *)
  let (filtered_result: exp_ast list) = List.filter (fun x -> x <> Empty) tmp_result in
  filtered_result

(* Tail recursive function that checks wether all elements of the list are the same *)
let check_incoherence_in_lst (status_list_execution: (bool option) list) : bool =
  let rec incoherence_in_lst (status_list_execution: (bool option) list) (previous_type: (bool option)): bool =
  match status_list_execution with
  | [] -> true
  | h::t -> if (Option.is_none previous_type && Option.is_none h) ||
              (Option.is_some previous_type && Option.is_some h && (Option.get previous_type = Option.get h))
            then incoherence_in_lst t h
            else false
  in
  incoherence_in_lst status_list_execution (List.nth status_list_execution 0)

let rec do_intermediarymandatory (facts: exp_ast list) (query: string) (facts_dict:((string, bool option) Hashtbl.t)) : unit =
  (* Collect all the trees containing the letter on the right side *)
  let (tmp_lst:exp_ast list) = find_tree facts query in
  (* Collect the current status of the letter in the hash_table *)
  let (status_query_htable: bool option) = Hashtbl.find facts_dict query in
  (* If the list is empty (meaning no letter on the right), then set status to false, else, if incoherence with previous status -> print error *)
  if List.length tmp_lst <= 0
  then 
    if Option.is_none status_query_htable || Option.get status_query_htable = false
    then Hashtbl.replace facts_dict query (Some false)
    else print_string ("An error has been encountered -> Incoherence with the letter " ^ query ^ "\n")
  (* As the list is not empty, we check wether all the results coincide, otherwise, print error *)
  else
    (* Check if we are in an infinite loop (e.g. --> If the rletter type is different than None --> we are in a recursive and set the value to False) *)
    (* Problem in the logic for the if --> NEED TO FIX IT *)
    (* if Option.is_some rletter && (Option.get rletter = query) if rletter = letter *)
    then
    (*  Case where infinite loop and more than 1 list containing the letter, then send to the next one *)
      if List.length tmp_lst > 1
      (* send with new list without current one, so that if we are in an infinite loop configuration, we send the list without the current one to check previous ones *)
      then do_intermediarymandatory (List.tl tmp_lst) query facts_dict
      else Hashtbl.replace facts_dict query (Some false)
    else
      (* Check the status for all the trees *)
      let (status_list_execution: (bool option) list) = List.map (fun x -> evaluate_expr x facts_dict facts) tmp_lst in
      (* Bool that states wether there is an incoherence in between the trees *)
      let (no_incoherence_in_lst: bool) = check_incoherence_in_lst status_list_execution in
      (* If there's no incoherence in the list *)
      if no_incoherence_in_lst = true
      (* Then set the value to the value of the first element of the list *)
      then Hashtbl.replace facts_dict query (List.nth status_list_execution 0)
      else print_string ("An error has been encountered -> Incoherence with the letter " ^ query ^ "\n")

let do_mandatory (facts: exp_ast list) (query: string list) (facts_dict:((string, bool option) Hashtbl.t)): unit =
  (* First test
  let _ = print_string "\n\n\nDEBUT DEBUG\n" in
  (* // À fixer : boucler sur les lettres de la query *)
  let (debug: exp_ast list list) = List.map (fun x -> find_tree facts x) query in
  (* Print function for debug *)
  let _ = List.iter (fun x -> List.iter print_exp_ast x) debug in
  let _ = print_string "FIN DEBUG\n\n\n" in
  let _ = Hashtbl.iter print_hash facts_dict in
  let _ = Hashtbl.replace facts_dict "W" (Some true) in
  let _ = print_string "\n\n\n" in
  let _ = Hashtbl.iter print_hash facts_dict in
  let _ = print_string "\n\n\n" in
  let _ = Hashtbl.iter print_hash facts_dict in () *)
  List.iter (fun x -> do_intermediarymandatory facts x facts_dict) query



let do_bonus (facts:(string*int) list list) (facts_dict:((string, bool option) Hashtbl.t)): unit = ()


let initialize_facts (lst_facts: (string*(bool option)) list) (init: (string*int) list) : (string, bool option) Hashtbl.t =
  let m = Hashtbl.create 26 in m

(* 
    Aim fo the function : 
    Tail recursion that checks wether the list contains any of the forbidden chars passed in parameter (after or during the implication) and returns a Result type : ok, or the line of the error
    The status bool helps checking wether we are prior or past the =>/<=> sign. False --> prior, true --> during or after
    The forbidden_chars contains a list of strings that are forbidden chars. In our case -> "|" and "<" ==> Declared at the top of this file
    Entire_lst is used to have a working copy of the entire line, for the error management
 *)

let initialize_mandatory (initialize:(string*int) list) (facts: (string*bool option) list) : (string, bool option) Hashtbl.t =
  let hash = Hashtbl.create @@ List.length facts in 
  let rec add_true_facts init : unit = match init with
    | [] -> ()
    | (h,_)::t -> Hashtbl.add hash h @@ Some (true); add_true_facts t
  in
  let rec add_leftover facts : unit = match facts with
    | [] -> ()
    | (h,_)::t -> if Hashtbl.mem hash h 
      then add_leftover t
      else Hashtbl.add hash h None; add_leftover t
  in
  add_true_facts initialize; add_leftover facts; hash

let check_correctness_imply_list (lst:(string*int) list): unit = 
  let rec check_correctness_imply (lst:(string*int) list) (forbidden_chars: (string) list) (status:(bool)): ((unit, string) result) =
    match lst with 
    | [] -> Result.Ok()
    | (h,v)::t -> if (v = 2 || v = 4 || status = true)
      then
        let comp = ((=) h) in
          if List.exists comp forbidden_chars
          then Result.Error (h)
          else check_correctness_imply t forbidden_chars true 
      else check_correctness_imply t forbidden_chars false 
  in
  let result = check_correctness_imply lst forbidden_chars false in
  if Result.is_error result
  then begin Printf.eprintf "Error in line \"%s\" : with char %s\n" (recreate_line lst) (Result.get_error result) ; exit 1 end
  else ()

let rec remove_bool_opt (lst : (string*int) list) : string list = match lst with
  | [] -> []
  | (h,v)::t -> h :: remove_bool_opt t

let _ =
  if not @@ ((Array.length Sys.argv = 2) || (Array.length Sys.argv = 3 && Sys.argv.(2) = "-b"))
  then usage ()
  else
    let (bonus:bool) = Array.length Sys.argv = 3 in
    let (file_res: (string list, string) result) = read_file Sys.argv.(1) in
    if Result.is_error file_res
    then Printf.eprintf "issue reading file \"%s\" : %s\n" Sys.argv.(1) (Result.get_error file_res)
    else
      let (file_content: string list) = Result.get_ok file_res in
      let (lexer_res: (string*int) list list) = List.map lexer file_content in
      let (check_res: (unit, string) result) = if not bonus then check_input_mandatory lexer_res else check_input_bonus lexer_res in
      if Result.is_error check_res
      then Printf.eprintf "%s\n" @@ Result.get_error check_res
      else let (cleaned_file: (string*int) list list) = remove_empty_line lexer_res in
        let ((facts: (string*int) list list), (init: (string*int) list), (query: (string*int) list)) = split_file cleaned_file in
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
              if not bonus
              (* then do_mandatory facts (initialize_facts lst_facts init) *)
              (* HERE WE CHECK THE CORRECTNESS OF THE FILE --> NEED TO PARSE AND CHECK THE RETURN *)
              then let _ = List.iter check_correctness_imply_list facts in
              let (trees: exp_ast list) = List.map (fun e -> exp_ast_of_list_mandatory e) facts in
              let _ = List.map print_exp_ast trees in
              do_mandatory trees (remove_bool_opt query) @@ initialize_mandatory (List.tl init) lst_facts
              else ()
                (*
                  let (trees: exp_ast) = unite_facts in
                  let _ = print_exp_ast trees in ()
                *)

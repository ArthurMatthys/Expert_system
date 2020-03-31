open Unix
open Btree
open Checker
open Lexer
open Library
open ReadFile
open Operation

let print_err = Printf.eprintf 

let usage () : unit = print_string 
    "usage : expert_system [file] [-b]\n
  \tinput_file\tfile to evaluate\n
  \t\"-b\"\tChange the way to evaluate\n"


let string_of_bool_option (opt:bool option): string = match opt with
  | None -> "None"
  | Some x -> string_of_bool x


(* let print_facts (fact, value_fact:(string*(bool option))) : unit =
  Printf.printf "fact : %s\tvalue : %s\n" fact @@ string_of_bool_option value_fact *)
  
  let print_facts (fact, value_fact:(string*int)) : unit =
  Printf.fprintf Stdlib.stdout "print_facts: |%s-%d|\n" fact value_fact



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
    | Letter l -> l = fact
    | And (left, right) -> dig_right left || dig_right right
    | Not (right) -> dig_right right
    | Or (left, right) -> dig_right left || dig_right right
    | Xor (left, right) -> dig_right left || dig_right right
    | _ -> false
  in
  (* Filter all the empty trees *)
  let (filtered_result: exp_ast list) = List.filter (fun x -> dig_right x) tree_lst in
  filtered_result

(*
  Backward-chaining inference engine
 *)
let split_assignations_on_2_lists (tree: exp_ast): ((string list)*(string list)) =
(*
  Recursive function that parses the tree and checks wether the letter on the right side has ! in front
  If so, we check wether it has mod 2 !, and assign it into positive list
  Otherwise, negative list
*)
  let (positive_list: string list ref) = ref [] in
  let (negative_list: string list ref) = ref [] in
  let rec dig_right_split_lists (tree : exp_ast) (state_negation : int) : unit =
    match tree with
    | Imply (left, right) -> dig_right_split_lists right state_negation
    | Empty -> ()
    | Letter l -> if (state_negation mod 2 = 1) then negative_list := l::!negative_list else positive_list := l::!positive_list
    | And (left, right) -> begin dig_right_split_lists left state_negation ; dig_right_split_lists right state_negation end
    | Not (right) -> dig_right_split_lists right (state_negation + 1)
    | Or (left, right) -> begin dig_right_split_lists left state_negation ; dig_right_split_lists right state_negation end
    | Xor (left, right) -> begin dig_right_split_lists left state_negation ; dig_right_split_lists right state_negation end
    | _ -> ()
  in
  let _ = dig_right_split_lists tree 0 in
  (!positive_list,!negative_list)

(* Tail recursive function that checks wether all elements of the list are the same, and that the*)
let check_incoherence_in_lst (status_list_execution: (bool option) list) (initial_status: bool option) : bool =
  let rec incoherence_in_lst (status_list_execution: (bool option) list) (previous_type: (bool option)) : bool =
  match status_list_execution with
  | [] -> true
  | h::t -> if previous_type = h && initial_status = Some true && h = initial_status 
              then incoherence_in_lst t h
            else if previous_type = h && initial_status = None
              then incoherence_in_lst t h
            else false
  in
  incoherence_in_lst status_list_execution (List.hd status_list_execution)

(* DEBUG *)
let int_of_booloption = function None -> 0 | Some false -> 2 | Some true -> 1

let int_of_bool = function false -> 2 | true -> 1


(* Do_mandatory : Solve the mandatory part of the program *)
let do_mandatory (facts: exp_ast list) (queries: string list) (facts_dict:((string, bool option) Hashtbl.t)): ((string, bool option) Hashtbl.t) =
  let rec evaluate (tree : exp_ast) (past_queries: string list) (current_table: ((string, bool option) Hashtbl.t)): ((bool option, string) result) =
      match tree with
      | Empty -> Result.ok (Some false)
      | Letter l -> let status = Hashtbl.find current_table l in if Option.is_none status
                                                                 then Hashtbl.find (Result.get_ok (rec_mandatory l past_queries current_table)) l
                                                                 else status
      | And (left, right) -> my_and (evaluate left past_queries current_table) (evaluate right past_queries current_table)
      | Or (left, right) -> my_or (evaluate left past_queries current_table) (evaluate right past_queries current_table)
      | Xor (left, right) -> my_xor (evaluate left past_queries current_table) (evaluate right past_queries current_table)
      | Not (right) -> my_not (evaluate right past_queries current_table)
      | Imply (left, right) ->  evaluate left past_queries current_table
      | _ -> Result.ok (Some false)
  and
  evaluate_trees_hashtbls (tree: exp_ast) (past_queries: string list) (current_table: ((string, bool option) Hashtbl.t)): ((((string, bool option) Hashtbl.t), string) result) =
    let ((positive_assign, negative_assign):((string list)*(string list))) = split_assignations_on_2_lists tree in
    let (status_list_execution: (bool option)) = evaluate tree past_queries current_table in
    let neg_status_list_execution = if Option.is_none status_list_execution
                                      then status_list_execution
                                    else if Option.get status_list_execution = true
                                      then Some false
                                    else
                                      Some true
    in
    let _ = List.iter (fun x -> Hashtbl.replace current_table x status_list_execution) positive_assign in
    let _ = List.iter (fun x -> Hashtbl.replace current_table x neg_status_list_execution) negative_assign in

    Result.Ok current_table
    (* Pour chaque arbre
        1. Récupérer les arguments de l'arbre à droite et les placer dans l'une des 2 listes -> Not and normal
        2. Récupérer la valeur pour chaque arbre, et l'ajouter (en négation si nécessaire)
        3. Vérifier la valeur pour chaque Hashtbl
        4. Youpi !!!
    *)
  (* and
  intermediary_evaluation (query: string) (past_queries: string list) (current_table: ((string, bool option) Hashtbl.t)): ((string, bool option) Hashtbl.t) =
  let toto = facts_dict in toto *)
  and
  (* Renvoie un bool option qui correspond à la valeur de ma query *)
  rec_mandatory (query: string) (past_queries: string list) (current_table: ((string, bool option) Hashtbl.t)): ((((string, bool option) Hashtbl.t), string) result) =
    if List.mem query past_queries 
    then begin Hashtbl.replace current_table query None ; Result.ok current_table end
    else
      (* Collect all the trees containing the letter on the right side *)
      let (tmp_lst:exp_ast list) = find_tree facts query in
      (* let _ = List.map print_exp_ast tmp_lst in *)
      (* Collect the current status of the letter in the hash_table *)
      let (status_query_htable: bool option) = Hashtbl.find current_table query in
      (* If the list is empty (meaning no letter on the right), then set status to false, else, if incoherence with previous status -> print error *)
      if List.length tmp_lst <= 0
      then 
      begin
      (* If the value of query in Hastable is None, False and that the value in untouched Hashtable is not true, set to false *)
        if (Option.is_none status_query_htable || Option.get status_query_htable = false) && Option.get (Hashtbl.find facts_dict query) <> true
        then begin Hashtbl.replace current_table query (Some false) ; Result.ok current_table end
        else
        begin
          (* If the value of query in Hastable is true, and that the value in untouched Hashtable is also true, return this value *)
          if Option.get (Hashtbl.find facts_dict query) = true && Option.get status_query_htable = true
          then Result.ok current_table
          else Result.Error("An incoherence for letter " ^ query ^ " has been found")
        end
      end
      (* As the list is not empty, we check wether all the results coincide, otherwise, print error *)
      else
        (* For each tree, collect the arguments on the right of the imply, and  return 2 lists, positives arg and negative args*)
        let (all_hashtables: ((((string, bool option) Hashtbl.t), string) result) list)  = List.map (fun x -> evaluate_trees_hashtbls x (query::past_queries) (Hashtbl.copy current_table)) tmp_lst
      (* Pour chaque arbre
        1. Récupérer les arguments de l'arbre à droite et les placer dans l'une des 2 listes -> Not and normal
        2. Récupérer la valeur pour chaque arbre, et l'ajouter (en négation si nécessaire)
        3. Vérifier la valeur pour chaque Hashtbl
        4. Youpi !!!
      *)

        (* Check the status for all the trees *)
        (* let _ = List.map (fun x ->  evaluate_trees_hashtbls  x (query::past_queries) (Hashtbl.copy current_table)) tmp_lst in *)
        (* let (status_list_execution: (bool option) list) = List.map (fun x -> evaluate x (query::past_queries)) tmp_lst in *)
        (* Bool that states wether there is an incoherence between the trees and the result of the trees and the initial state of trees *)
        (* let (no_incoherence_in_lst: bool) = check_incoherence_in_lst status_list_execution (Hashtbl.find initial_dict query) in *)
        (* If there's no incoherence in the list *)
        (* if no_incoherence_in_lst *)
        (* Then set the value to the value of the first element of the list *)
        (* then begin Hashtbl.replace current_table query (List.hd status_list_execution) ; current_table end
        else begin Hashtbl.replace current_table query None ; current_table end *)
  in
  let _ = List.map (fun x -> rec_mandatory x [] (Hashtbl.copy facts_dict)) (List.tl queries) 
  (* let _ = rec_mandatory x [] (Hashtbl.copy facts_dict) in *)
  in facts_dict



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

let forbidden_chars = ["<=>";"|"; "^"]

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
        (* debug *)
        let _ = List.iter (fun x -> List.iter print_facts x) facts in
        (* debug *)
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
              (* let (blob,testi) = split_assignations_on_2_lists (List.hd trees) in
              let _ = List.iter (fun x -> Printf.fprintf Stdlib.stdout "blob: |%s|\n" x) blob in
              let _ = List.iter (fun x -> Printf.fprintf Stdlib.stdout "test: |%s|\n" x) testi *)
              ()

              (* let dictionnary_ready = initialize_mandatory (List.tl init) lst_facts in *)
              (* let results_hashtable = do_mandatory trees (remove_bool_opt query) @@ initialize_mandatory (List.tl init) lst_facts in
              let _ = Printf.fprintf Stdlib.stdout "DEBUG MAIN\n" in
               let _ = Hashtbl.iter (fun x y -> Printf.fprintf Stdlib.stdout "|%s:%d|-" x (int_of_booloption y)) results_hashtable in
                print_string "\n" *)
              else ()
                (*
                  let (trees: exp_ast) = unite_facts in
                  let _ = print_exp_ast trees in ()
                *)

open Unix
open Btree
open Checker
open Lexer
open Library
open ReadFile
open Operation

let print_err = Printf.eprintf 

let usage () : unit = print_string 
    "usage : expert_system [file] [-b] [-c]\n
  \tinput_file\tfile to evaluate\n
  \t\"-b\"\tChange the way to evaluate\n
  \t\"-c\"\tDon't care about initial facts. Can be used to look for incoherence with initial facts. Option '-b' required\n"


let string_of_bool_option (opt:bool option): string = match opt with
  | None -> "None"
  | Some x -> string_of_bool x


(* let print_facts (fact, value_fact:(string*(bool option))) : unit =
   Printf.printf "fact : %s\tvalue : %s\n" fact @@ string_of_bool_option value_fact *)

(* let print_facts (fact, value_fact:(string*int)) : unit =
   Printf.fprintf Stdlib.stdout "print_facts: |%s-%d|\n" fact value_fact *)



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

(* let get_facts_mandatory (lst:(string*int) list list) : ((string*int) list) =
   let (lst_flatten:(string*int) list) = List.flatten lst in
   let rec add_fact (facts:(string*int) list) (statements : (string*(bool option)) list): (string*(bool option)) list = match facts with
    | [] -> statements
    | (h,v) :: t -> if List.exists ((=) (h, None)) statements || v <> 1
      then add_fact t statements
      else add_fact t ((h, None)::statements)
   in
   add_fact lst_flatten [] *)


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
  Recursive function that parses the tree and checks wether the letter on the right side has ! in front
  If so, we check wether it has mod 2 !, and assign it into positive list
  Otherwise, negative list
*)
let split_assignations_on_2_lists (tree: exp_ast): ((string list)*(string list)) =
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

(* Tail recursive function that checks wether all value of the letter in the list of Hashtable are the same everywhere *)
let check_incoherence_in_lst (status_list_execution: (((((string, bool option) Hashtbl.t), string) result) list)) (query: string) : ((bool, string) result) =
  let rec incoherence_in_lst (el_list_execution: (((((string, bool option) Hashtbl.t), string) result) list))
      (previous_type: ((((string, bool option) Hashtbl.t), string) result)) : ((bool, string) result) =
    match el_list_execution with
    | [] -> Result.ok true
    | h::t -> if Result.is_error h
      then Result.Error (Result.get_error h)
      else
        let (previous_bool: bool option) = Hashtbl.find (Result.get_ok previous_type) query in
        let (bool_h: bool option) = Hashtbl.find (Result.get_ok h) query in
        if previous_bool = bool_h
        then incoherence_in_lst t h
        else Result.Error("An incoherence for letter " ^ query ^ " has been found")
  in
  incoherence_in_lst status_list_execution (List.hd status_list_execution)

(* Tail recursive function that changes the value of the current_table, and checks at the same time any error*)
let assign_result_to_hashtbl_and_check_error (positive_assign: string list) (status_evaluation: (bool option)) 
    (current_table: ((string, bool option) Hashtbl.t)) (positive_list: bool): ((unit, string) result) =
  let rec assign (positive_assign: string list) : ((unit, string) result) =
    match positive_assign with
    | [] -> Result.ok ()
    (* if status_evaluation == what was before, don't change *)
    | h::t -> let value = Hashtbl.find current_table h in
      if status_evaluation = value
      then assign t
      else if (Option.is_none value) && (not @@ Option.is_none status_evaluation)
      then begin Hashtbl.replace current_table h status_evaluation ; assign t end
      else
        Result.Error("An incoherence for letter " ^ h ^ " has been found")
  in
  assign positive_assign

(* DEBUG *)
let int_of_intoption = function None -> -1 | Some x -> x

(* let int_of_bool = function false -> 2 | true -> 1 *)


(* Do_mandatory : Solve the mandatory part of the program *)
(* let do_mandatory (facts: exp_ast list) (queries: string list) (facts_dict:((string, bool option) Hashtbl.t)): ((string, bool option) Hashtbl.t) = *)
let do_mandatory (facts: exp_ast list) (queries: string list) (facts_dict:((string, bool option) Hashtbl.t)): (((string, bool option) Hashtbl.t, string) result list) =
  (* Function evaluates if no errors are found, otherwise, returns it without evaluating *)
  let rec evaluate (tree : exp_ast) (past_queries: string list) (current_table: ((string, bool option) Hashtbl.t)): ((bool option, string) result) =
    match tree with
    | Empty -> Result.ok (Some false)
    | Letter l -> let status = Hashtbl.find current_table l in if Option.is_none status
      then let (ret_mandatory:((((string, bool option) Hashtbl.t), string) result)) = rec_mandatory l past_queries current_table in
        if Result.is_error ret_mandatory
        then Result.Error (Result.get_error ret_mandatory)
        else Result.ok (Hashtbl.find (Result.get_ok ret_mandatory) l)
        (* else let ret =  Hashtbl.find (Result.get_ok ret_mandatory) l in if Option.is_none ret then Result.ok (Some false) else Result.ok ret *)
      else Result.ok status
    | And (left, right) -> my_and (evaluate left past_queries current_table) (evaluate right past_queries current_table)
    | Or (left, right) -> my_or (evaluate left past_queries current_table) (evaluate right past_queries current_table)
    | Xor (left, right) -> my_xor (evaluate left past_queries current_table) (evaluate right past_queries current_table)
    | Not (right) -> my_not (evaluate right past_queries current_table)
    | Imply (left, right) ->  evaluate left past_queries current_table
    | _ -> Result.ok (Some false)
  and
    (* Function that evaluates each tree and parses for any error. If none is found, change value when necessary, or return error *)
    evaluate_trees_hashtbls (tree: exp_ast) (past_queries: string list) (current_table: ((string, bool option) Hashtbl.t)): ((((string, bool option) Hashtbl.t), string) result) =
    (* Retrieve all the positive and negative values that will be changed with the result of the evaluation [at the right of imply] *)
    let ((positive_assign, negative_assign):((string list)*(string list))) = split_assignations_on_2_lists tree in
    (* Result of the evaluation *)
    let (status_evaluation: ((bool option, string) result)) = evaluate tree past_queries current_table in
    (* If it's an error, return it *)
    if Result.is_error status_evaluation
    then Result.Error (Result.get_error status_evaluation)
    (* Else, change it *)
    else 
      (* Calculate the inverse of the status, for the negative values *)
      let (neg_status_evaluation:((bool option, string) result)) = if Option.is_none (Result.get_ok status_evaluation) then status_evaluation
        else if (Result.get_ok status_evaluation) = Some true then Result.ok (Some false)
        else Result.ok (Some true)
      in
      (* Change status in hashtabl, and check wether error occurs *)
      let (modified_hshtable_positive: ((unit, string) result)) = assign_result_to_hashtbl_and_check_error positive_assign (Result.get_ok status_evaluation) current_table true in
      let (modified_hshtable_negative: ((unit, string) result)) = assign_result_to_hashtbl_and_check_error negative_assign (Result.get_ok neg_status_evaluation) current_table false in
      (* Check if error is found in change of hashtable, if not, return it *)
      if Result.is_error modified_hshtable_positive
      then Result.Error (Result.get_error modified_hshtable_positive)
      else 
      if Result.is_error modified_hshtable_negative
      then Result.Error (Result.get_error modified_hshtable_negative)
      else Result.ok current_table
  and
    (* Renvoie un bool option qui correspond à la valeur de ma query *)
    rec_mandatory (query: string) (past_queries: string list) (current_table: ((string, bool option) Hashtbl.t)): ((((string, bool option) Hashtbl.t), string) result) =
    if List.mem query past_queries 
    then begin Hashtbl.replace current_table query (Some false) ; Result.ok current_table end
    else
      (* Collect all the trees containing the letter on the right side *)
      let (tmp_lst:exp_ast list) = find_tree facts query in
      (* Collect the current status of the letter in the hash_table *)
      let (status_query_htable: bool option) = Hashtbl.find current_table query in
      (* If the list is empty (meaning no letter on the right), then set status to false, else, if incoherence with previous status -> print error *)
      match List.length tmp_lst with
      (* If the value of query in Hastable is None, False and that the value in untouched Hashtable is not true, set to false *)
      | 0 ->  if (Option.is_none status_query_htable || status_query_htable = Some false) && ((Hashtbl.find facts_dict query) <> Some true)
        then begin Hashtbl.replace current_table query (Some false) ; Result.ok current_table end
        else
          (* If the value of query in Hastable is true, and that the value in untouched Hashtable is also true, return this value *)
        if Hashtbl.find facts_dict query = Some true && status_query_htable = Some true
        then Result.ok current_table
        else Result.Error("An incoherence for letter " ^ query ^ " has been found")
      (* As the list is not empty, we check wether all the results coincide, otherwise, print error *)
      (* Evaluate each tree and retrieve *)
      | _ ->  let (all_hashtables: ((((string, bool option) Hashtbl.t), string) result) list) = List.map (fun x -> evaluate_trees_hashtbls x (query::past_queries) (current_table)) tmp_lst in
        (* Check wether there is an error *)
        let (error_is_present: ((((string, bool option) Hashtbl.t), string) result) list) = List.filter(fun x -> Result.is_error x) all_hashtables in
        if List.length error_is_present > 0
        then List.hd error_is_present
        else
          (* Bool that states wether there is an incoherence between the trees and the result of the trees and the initial state of trees *)
          let (no_incoherence_in_lst: ((bool, string) result)) = check_incoherence_in_lst all_hashtables query in
          if Result.is_error no_incoherence_in_lst
          then Result.Error (Result.get_error no_incoherence_in_lst)
          else
            let _ = Hashtbl.replace current_table query (Hashtbl.find (Result.get_ok (List.hd all_hashtables)) query)
            in Result.ok current_table
  in
  let (ret:((((string, bool option) Hashtbl.t), string) result) list) = List.map (fun x -> rec_mandatory x [] (Hashtbl.copy facts_dict)) queries
  in ret
(* let _ = rec_mandatory x [] (Hashtbl.copy facts_dict) in *)



(*
  * Evaluate function for bonus :
  * Retrieves a bool, and checks the value of the letter bitwisely
*)
let evaluate_bonus (tree : exp_ast) (index_list: (string*int) list) (actual_nbr:int) : bool =
  let rec tail_evaluate (tree : exp_ast): bool =
    match tree with
    | Empty -> false
    | Letter l -> let (_, index) = List.find (fun (str, _) -> str = l) index_list in (((1 lsl index) land actual_nbr) > 0)
    | And (left, right) -> (tail_evaluate left) && (tail_evaluate right)
    | Or (left, right) -> (tail_evaluate left) || (tail_evaluate right)
    | Xor (left, right) -> (tail_evaluate left) <> (tail_evaluate right)
    | Not (right) -> not (tail_evaluate right)
    | _ -> false
  in
  tail_evaluate tree 

(* Function that constructs the wanted number for bonus evaluation with bitwise operators *)
let rec add (init:int) (max:int) : int = 
  if init = (max - 1) 
  then (1 lsl init)
  else (1 lsl init) + (add (init + 1) max)

(* Create the list of ints satisfying the equation *)
let get_lst (tree:exp_ast) (tupled_facts:(string * int) list) (nbr_init: int) (nbr_max:int) : (int list) = 
  let rec get_lst_rec (nbr:int) = 
    if nbr > nbr_max
    then []
    else
    if evaluate_bonus tree tupled_facts nbr
    then nbr :: get_lst_rec (nbr+1)
    else get_lst_rec (nbr+1)
  in
  get_lst_rec nbr_init

(* Compare bitwisely the ints *)
(* let bitcompare_int (int_lst: int list) : int =
   let int_ref = List.hd int_lst in
    let rec bit_compare (int_lst: int list) (coherent:int) : int =
      match int_lst with
      | [] -> coherent
      | h::[] -> (lnot (h lxor int_ref)) land coherent
      | h::t -> let simil = lnot (h lxor int_ref) in
                let cohe_tmp = simil land coherent in
                let _ = Printf.fprintf Stdlib.stdout "simil : %d\n" simil in
                let _ = Printf.fprintf Stdlib.stdout "cohe_tmp : %d\n" cohe_tmp in
                bit_compare t cohe_tmp
    in bit_compare (List.tl int_lst) int_ref *)

let bitcompare_int (int_lst : int list) (nbr_max:int) : int =
  let int_ref = List.hd int_lst in
  let rec bit_compare (int_lst: int list) (coherent:int) : int =
    match int_lst with
    | [] -> coherent
    | h::[] -> ((lnot (h lxor int_ref)) land nbr_max) land coherent
    | h::t -> let simil = (lnot (h lxor int_ref)) land nbr_max in
      let cohe_tmp = simil land coherent in
      bit_compare t cohe_tmp
  in match int_lst with
  | [] -> -1
  | h::[] -> h
  | h1::h2::[] -> (lnot(h1 lxor h2)) land nbr_max
  | h1::h2::t -> bit_compare t ((lnot(h1 lxor h2)) land nbr_max)

let retrieve_bite_value (index_letter:int) (actual_nbr:int) : bool =
  (((1 lsl index_letter) land actual_nbr) > 0)

let do_bonus (tree:exp_ast) ((list_none,list_true,tupled_facts):((string*bool option)list)*((string*bool option)list)*((string * int) list))
    (queries: string list) (check:bool) (facts_dict:((string, bool option) Hashtbl.t)): unit =
  (* let _ = Printf.fprintf Stdlib.stdout "DEBUG-check: |%s|\n" (string_of_bool check) in *)
  let (bit_max:int) = List.length tupled_facts in 
  (* Dans l'input, voir si incohérence dans le truc *)
  let (nbr_init:int) = if check then 0 else add (List.length list_none) bit_max in
  let (nbr_max:int) = add 0 bit_max in
  let _ = Printf.fprintf Stdlib.stdout "\nDEBUG-INTS: nbr_init: %d-nbr_max: %d\n" nbr_init nbr_max in 
  let (ret:int list) = get_lst tree tupled_facts nbr_init nbr_max in
  let _ = List.iter (fun x -> Printf.fprintf Stdlib.stdout "DEBUG-ret: |%d|\n" x) ret in
  let (verdict_int:int option) = match List.length ret with
    | 0 -> None
    | 1 -> Some nbr_max
    | _ -> Some (bitcompare_int ret nbr_max)
  in let _ = Printf.fprintf Stdlib.stdout "DEBUG VERDICT %d\n" (int_of_intoption verdict_int) in
  match verdict_int with
  | None -> if check 
    then Printf.fprintf Stdlib.stdout "Incoherence in relations\n"
    else Printf.fprintf Stdlib.stdout "Incoherence either in initial facts or in relations\n"
  | _ -> List.iter (fun x ->
      let (_, index_letter) = List.find (fun (str, _) -> str = x) tupled_facts in 
      match (retrieve_bite_value index_letter (Option.get verdict_int)) with
      | true -> 
        let (value:bool option) = Some (retrieve_bite_value index_letter (List.hd ret)) in
        if Hashtbl.find facts_dict x = Some true && value <> (Some true)
        then Printf.fprintf Stdlib.stdout "An incoherence for letter %s has been found\n" x
        else Printf.fprintf Stdlib.stdout "%s : %s \n" x (string_of_bool_option value)
      | false -> if Hashtbl.find facts_dict x = Some true
        then Printf.fprintf Stdlib.stdout "An incoherence for letter %s has been found\n" x
        else Printf.fprintf Stdlib.stdout "%s : None\n" x 
    ) (List.tl queries)

(* Transform the dict into a key-index tuple list *)
let dict_to_tuplelist (dict:(string, bool option) Hashtbl.t) : (((string*bool option)list)*((string*bool option)list)*((string*int)list)) = 
  (* Filter hashtable with elemens whose Bool Option value is None *)
  let (list_none: (string*bool option)list) = Hashtbl.fold (fun k v acc -> if v = None then (k, v) :: acc else acc) dict [] in
  (* let _ = Printf.fprintf Stdlib.stdout "DEBUG list_none\n" in
     let _ = List.iter (fun (str,ind) -> Printf.fprintf Stdlib.stdout "|%s:%s" str (string_of_bool_option ind)) list_none in
     let _ = Printf.fprintf Stdlib.stdout "\n" in *)
  (* Filter hashtable with elemens whose Bool Option value is Some true *)
  let (list_true: (string*bool option)list) = Hashtbl.fold (fun k v acc -> if v = Some true then (k, v) :: acc else acc) dict [] in
  (* let _ = Printf.fprintf Stdlib.stdout "DEBUG list_true\n" in
     let _ = List.iter (fun (str,ind) -> Printf.fprintf Stdlib.stdout "|%s:%s" str (string_of_bool_option ind)) list_true in
     let _ = Printf.fprintf Stdlib.stdout "\n" in *)
  (* Get length list_none, to add in index *)
  let (nbr: int) = List.length list_none in
  (* Create the tuple, with at last the list of key-index elements *)
  (list_none, list_true, (List.append (List.mapi (fun ind (string,bool) -> (string, ind)) list_none) (List.mapi (fun ind (string,bool) -> (string, ind + nbr)) list_true)))

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

let rec remove_bool_opt2 (lst : (string*bool option) list) : string list = match lst with
  | [] -> []
  | (h,v)::t -> h :: remove_bool_opt2 t

let print_result_mandatory (result_global: (((string, bool option) Hashtbl.t, string) result list)) (result_queries:(((string, bool option) Hashtbl.t, string) result list))
    (queries: string list) : unit =
  (* We first check wether there is an error in any of the 2 lists, if so, just print the error ! *)
  let (result:((string, bool option) Hashtbl.t, string) result list) = List.filter (fun x -> Result.is_error x) result_global in
  match List.length result with
  (* For each and every array in the query list, we will print it's corresponding value *)
  | 0 -> List.iteri (fun ind x -> let (table_of_query:(string, bool option) Hashtbl.t) = Result.get_ok (List.nth result_queries ind) in
                      let (value_of_query_in_proper_table) = Hashtbl.find table_of_query x in
                      Printf.fprintf Stdlib.stdout "%s : %s\n" x (string_of_bool_option value_of_query_in_proper_table)
                    ) queries
  (* Print the corresponding error *)
  | _ -> Printf.fprintf Stdlib.stdout "%s\n" (Result.get_error (List.hd result))

let _ =
  if not @@ ((Array.length Sys.argv = 2) || (Array.length Sys.argv = 3 && Sys.argv.(2) = "-b")
             || (Array.length Sys.argv = 4 && ((Sys.argv.(2) = "-c" && Sys.argv.(3) = "-b") || (Sys.argv.(2) = "-b" && Sys.argv.(3) = "-c"))))
  then usage ()
  else
    let (bonus:bool) = Array.length Sys.argv > 2 in
    let (check:bool) = Array.length Sys.argv = 4 && ((Sys.argv.(2) = "-c") || (Sys.argv.(3) = "-c")) in
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
        (* let _ = List.iter (fun x -> List.iter print_facts x) facts in *)
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
            (* let dictionnary_ready = initialize_mandatory (List.tl init) lst_facts in *)
            let (result_query: (((string, bool option) Hashtbl.t, string) result list)) = do_mandatory trees (List.tl (remove_bool_opt query)) @@ initialize_mandatory (List.tl init) lst_facts in
            (* Do the same with all letters, in order to check for incoherence *)
            let (result_global: (((string, bool option) Hashtbl.t, string) result list)) = do_mandatory trees (remove_bool_opt2 lst_facts) @@ initialize_mandatory (List.tl init) lst_facts in
            let _ = print_result_mandatory result_global result_query (List.tl (remove_bool_opt query))
            in ()
          else 
            (* Construct the tree of the bonus *)
            let _ = Printf.fprintf Stdlib.stdout "1\n" in
            let (tree_bonus:exp_ast) = exp_ast_of_list_bonus facts in              
            let _ = Printf.fprintf Stdlib.stdout "2\n" in


            let _ = print_exp_ast tree_bonus in
            (* Construct a tuple list of all the facts [used later for decoding of bites]  *)
            let ((list_none:(string*bool option)list),(list_true:(string*bool option)list),(tupled_facts:(string * int) list)) = dict_to_tuplelist @@ initialize_mandatory (List.tl init) lst_facts in
            let _ = Printf.fprintf Stdlib.stdout "3\n" in

            (* let _ = Printf.fprintf Stdlib.stdout "DEBUG TUPLELIST \n" in
               let _ = List.iter (fun (str,ind) -> Printf.fprintf Stdlib.stdout "|%s:%d" str ind) tupled_facts in *)
            (* Do bonus execution *)
            let _ = do_bonus tree_bonus (list_none,list_true,tupled_facts) (remove_bool_opt query) check @@ initialize_mandatory (List.tl init) lst_facts
            in ()
                (*
                  let (trees: exp_ast) = unite_facts in
                  let _ = print_exp_ast trees in ()
                *)


(* let _ = List.map print_exp_ast trees in *)
(* let (blob,testi) = split_assignations_on_2_lists (List.hd trees) in
   let _ = List.iter (fun x -> Printf.fprintf Stdlib.stdout "blob: |%s|\n" x) blob in
   let _ = List.iter (fun x -> Printf.fprintf Stdlib.stdout "test: |%s|\n" x) testi *)
(* () *)
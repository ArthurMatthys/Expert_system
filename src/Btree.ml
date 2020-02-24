open Library
open Operation

type exp_ast =
  | Equi of exp_ast * exp_ast
  | Imply of exp_ast * exp_ast
  | And of exp_ast * exp_ast
  | Or of exp_ast * exp_ast
  | Xor of exp_ast * exp_ast
  | Not of exp_ast
  | Letter of string
  | Empty

let print_exp_ast (expr:exp_ast) : unit =
  let rec print (expression:exp_ast) : unit = 
    match expression with 
    | Equi (left,right) -> print_string "equi("; print left; print_string " , "; print right;print_string ")"
    | Imply (left,right) -> print_string "imply("; print left; print_string " , "; print right;print_string ")"
    | And (left, right) -> print_string "and("; print left; print_string " , "; print right; print_string ")"
    | Or (left, right) -> print_string "or("; print left; print_string " , "; print right; print_string ")"
    | Xor (left, right) -> print_string "xor("; print left; print_string " , "; print right; print_string ")"
    | Not (right) -> print_string "not("; print right; print_string ")"
    | Letter letter -> print_string letter
    | Empty -> ()
  in
  print expr ; print_newline ()


let _filteri (func: int -> 'a -> bool) (lst:'a list): 'a list = 
  let rec loop__filteri (func: int -> 'a -> bool) (lst:'a list) (index: int): 'a list =
    match lst with
    | [] -> []
    | h::t -> if func index h
      then h :: loop__filteri func t (index + 1)
      else loop__filteri func t (index + 1)
  in
  loop__filteri func lst 0


let _ope_of_string ((ope,_):(string*int)) : (bool option -> bool option -> bool option) =
  let func_type (my_fun: (bool->bool->bool)) (a: bool option) (b: bool option) : bool option=
    if Option.is_none a || Option.is_none b
    then None
    else Some (my_fun (Option.get a) (Option.get b))
  in
  match ope with
  | "^" -> func_type (<>)
  | "|" -> func_type (||)
  | "+" -> func_type (&&)
  | "!" -> (fun a _ -> if Option.is_none a then None
             else Some (not (Option.get a)))
  | _ -> (fun _ _ -> None)

(* Celui de la partie bonus *)
let rec exp_ast_of_list_bonus (facts_list:(string*int)list) : exp_ast = 
  let rec find_priority_ope (facts_lst:(string*int)list) (index_max: int) (value: int) (index: int): int =
    match facts_lst with
    | [] -> index_max
    | (h,v)::t -> if v >= 3 && (value = 0 || v <= value) 
                  then find_priority_ope t index v (index + 1)
                  else find_priority_ope t index_max value (index + 1)
  in
  match facts_list with
  | [] -> Empty
  | (h,v)::[] -> Letter h
  | _ -> let split_index = find_priority_ope facts_list 0 0 0 in
    let (left:(string*int)list) = remove_parenthesis @@ _filteri (fun index _ -> index < split_index) facts_list in
    let (right:(string*int)list) = remove_parenthesis @@ _filteri (fun index _ -> index > split_index) facts_list in
    match List.nth facts_list split_index with
    | ("<=>", _) -> And (Or (Not (exp_ast_of_list_bonus left), exp_ast_of_list_bonus right), Or(exp_ast_of_list_bonus left, Not (exp_ast_of_list_bonus right)))
    | ("=>", _) -> Or (Not (exp_ast_of_list_bonus left), exp_ast_of_list_bonus right)
    | ("+", _) -> And (exp_ast_of_list_bonus left, exp_ast_of_list_bonus right)
    | ("|", _) -> Or (exp_ast_of_list_bonus left, exp_ast_of_list_bonus right)
    | ("^", _) -> Xor (exp_ast_of_list_bonus left, exp_ast_of_list_bonus right)
    | ("!", _) -> Not (exp_ast_of_list_bonus right)
    | _ -> Empty

(* Celui de la partie mandatory *)
let rec exp_ast_of_list_mandatory (facts_list:(string*int)list) : exp_ast = 
  let rec find_priority_ope (facts_lst:(string*int)list) (index_max: int) (value: int) (index: int): int =
    match facts_lst with
    | [] -> index_max
    | (h,v)::t -> if v >= 3 && (value = 0 || v <= value) 
                  then find_priority_ope t index v (index + 1)
                  else find_priority_ope t index_max value (index + 1)
  in
  match facts_list with
  | [] -> Empty
  | (h,v)::[] -> Letter h
  | _ -> let split_index = find_priority_ope facts_list 0 0 0 in
    let (left:(string*int)list) = remove_parenthesis @@ _filteri (fun index _ -> index < split_index) facts_list in
    let (right:(string*int)list) = remove_parenthesis @@ _filteri (fun index _ -> index > split_index) facts_list in
    match List.nth facts_list split_index with
    | ("=>", _) -> Imply (exp_ast_of_list_mandatory left, exp_ast_of_list_mandatory right)
    | ("+", _) -> And (exp_ast_of_list_mandatory left, exp_ast_of_list_mandatory right)
    | ("|", _) -> Or (exp_ast_of_list_mandatory left, exp_ast_of_list_mandatory right)
    | ("^", _) -> Xor (exp_ast_of_list_mandatory left, exp_ast_of_list_mandatory right)
    | ("!", _) -> Not (exp_ast_of_list_mandatory right)
    | _ -> Empty
(* 
let evaluate_expr (expr : exp_ast) (facts_dict:((string, bool option) Hashtbl.t)): bool option =
  let rec evaluate (tree : exp_ast) : bool option =
    match tree with
    | Empty -> Some false
    | Letter l -> Hashtbl.find facts_dict l
    | And (left, right) -> my_and (evaluate left) (evaluate right)
    | Or (left, right) -> my_or (evaluate left) (evaluate right)
    | Xor (left, right) -> my_xor (evaluate left) (evaluate right)
    | Not (right) -> my_not (evaluate right)
    | _ -> Some false
  in
  evaluate expr *)

let pop_element_from_list (element: 'a) (lst: 'a list) : ('a list) =
  let rec pop_el_from_list (element: 'a) (lst: 'a list) : ('a list) =
  match lst with
  | [] -> []
  | h::t -> if h <> element
            then h :: pop_el_from_list element t
            else pop_el_from_list element t
  in
  pop_el_from_list element lst

(*
Cas lettre pas bon, si None rappeler la fonction, si c'est Some, renvoie le Bool 
Pour éviter les boucles infs, rajouter rlettre en paramètre et si lettre == l, alors false
*)

let evaluate_expr (expr : exp_ast) (facts_dict:((string, bool option) Hashtbl.t)) (facts: exp_ast list) (rletter: string option): bool option =
  let rec evaluate (tree : exp_ast) : bool option =
    match tree with
    | Empty -> Some false
    | Letter l -> let status = Hashtbl.find facts_dict l in if Option.is_none status then do_intermediarymandatory (pop_element_from_list tree facts) l facts_dict else status
    | And (left, right) -> my_and (evaluate left) (evaluate right)
    | Or (left, right) -> my_or (evaluate left) (evaluate right)
    | Xor (left, right) -> my_xor (evaluate left) (evaluate right)
    | Not (right) -> my_not (evaluate right)
    | _ -> Some false
  in
  evaluate expr
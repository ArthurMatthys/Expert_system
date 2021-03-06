open Library

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

  (*
    Check correctness of tree (no "y" char present)
    Returns true if tree contains the letter "y"
 *)
let check_correctness_tree (tree : exp_ast) : bool =
  let rec _check_correctness_tree (tree : exp_ast) : bool = 
    match tree with
    | Imply (left, right) -> _check_correctness_tree left || _check_correctness_tree right
    | Empty -> false
    | Letter l -> l = "y" (* y is the char being *)
    | And (left, right) -> _check_correctness_tree left || _check_correctness_tree right
    | Not (right) -> _check_correctness_tree right
    | Or (left, right) -> _check_correctness_tree left || _check_correctness_tree right
    | Xor (left, right) -> _check_correctness_tree left || _check_correctness_tree right
    | _ -> false
  in
  _check_correctness_tree tree


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
let rec exp_ast_of_list_bonus (facts:((string*int) list) list) : exp_ast =
  let rec inner_recursion (facts_list:(string*int)list) : exp_ast = 
    let rec find_priority_ope (facts_lst:(string*int)list) (index_max: int) (value: int) (index: int): int =
      match facts_lst with
      | [] -> index_max
      | (h,v)::t -> if v >= 3 && (value = 0 || (h <> "!" && v <= value) || (h = "!" && v < value ))
                    then find_priority_ope t index v (index + 1)
                    else find_priority_ope t index_max value (index + 1)
    in
    match facts_list with
    | [] -> Letter "y"
    | (h,_)::[] -> Letter h
    | _ -> let split_index = find_priority_ope facts_list 0 0 0 in
      let (left:(string*int)list) = remove_parenthesis @@ _filteri (fun index _ -> index < split_index) facts_list in
      let (right:(string*int)list) = remove_parenthesis @@ _filteri (fun index _ -> index > split_index) facts_list in
      match List.nth facts_list split_index with
      | ("<=>", _) -> And (Or (Not (inner_recursion left), inner_recursion right), Or(inner_recursion left, Not (inner_recursion right)))
      | ("=>", _) -> Or (Not (inner_recursion left), inner_recursion right)
      | ("+", _) -> And (inner_recursion left, inner_recursion right)
      | ("|", _) -> Or (inner_recursion left, inner_recursion right)
      | ("^", _) -> Xor (inner_recursion left, inner_recursion right)
      | ("!", _) -> Not (inner_recursion right)
      | _ -> Letter "y"
  in
  match facts with
  | [] -> Empty
  | h::[] -> inner_recursion h
  | h::t -> And(inner_recursion h, exp_ast_of_list_bonus t)

(* Celui de la partie mandatory *)
let rec exp_ast_of_list_mandatory (facts_list:(string*int)list) : exp_ast = 
  let rec find_priority_ope (facts_lst:(string*int)list) (index_max: int) (value: int) (index: int): int =
    match facts_lst with
    | [] -> index_max
    | (h,v)::t -> if v >= 3 && (value = 0 || (h <> "!" && v <= value) || (h = "!" && v < value ))
                  then find_priority_ope t index v (index + 1)
                  else find_priority_ope t index_max value (index + 1)
  in
  match facts_list with
  | [] -> Letter "y"
  | (h,_)::[] -> Letter h
  | _ -> let split_index = find_priority_ope facts_list 0 0 0 in
    let (left:(string*int)list) = remove_parenthesis @@ _filteri (fun index _ -> index < split_index) facts_list in
    let (right:(string*int)list) = remove_parenthesis @@ _filteri (fun index _ -> index > split_index) facts_list in
    match List.nth facts_list split_index with
    | ("=>", _) -> Imply (exp_ast_of_list_mandatory left, exp_ast_of_list_mandatory right)
    | ("+", _) -> And (exp_ast_of_list_mandatory left, exp_ast_of_list_mandatory right)
    | ("|", _) -> Or (exp_ast_of_list_mandatory left, exp_ast_of_list_mandatory right)
    | ("^", _) -> Xor (exp_ast_of_list_mandatory left, exp_ast_of_list_mandatory right)
    | ("!", _) -> Not (exp_ast_of_list_mandatory right)
    | _ -> Letter "y"
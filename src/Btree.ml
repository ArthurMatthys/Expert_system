open Library

type 'a binary_tree =
  | Empty
  | Node of 'a * 'a binary_tree * 'a binary_tree


type expr =
  | Empty
  | Leaf of string
  | Ope of (bool  option -> bool option -> bool option)


type exp_ast =
  | Imply of exp_ast * exp_ast
  | And of exp_ast * exp_ast
  | Or of exp_ast * exp_ast
  | Xor of exp_ast * exp_ast
  | Not of exp_ast
  | Letter of string
  | Empty

let rec print_exp_ast (expr:exp_ast) : unit =
  match expr with 
  | And (left, right) -> print_string "and("; print_exp_ast left; print_string " , "; print_exp_ast right; print_string ")"
  | Or (left, right) -> print_string "or("; print_exp_ast left; print_string " , "; print_exp_ast right; print_string ")"
  | Xor (left, right) -> print_string "xor("; print_exp_ast left; print_string " , "; print_exp_ast right; print_string ")"
  | Not (right) -> print_string "not("; print_exp_ast right; print_string ")"
  | Letter letter -> print_string letter
  | Empty -> ()
  | Imply (_,_) -> ()

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


let rec exp_ast_of_list (facts_list:(string*int)list) : exp_ast = 
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
    | ("+", _) -> And (exp_ast_of_list left, exp_ast_of_list right)
    | ("|", _) -> Or (exp_ast_of_list left, exp_ast_of_list right)
    | ("^", _) -> Xor (exp_ast_of_list left, exp_ast_of_list right)
    | ("!", _) -> Not (exp_ast_of_list right)
    | _ -> Empty


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
    let (ope: (bool option -> bool option -> bool option)) = _ope_of_string @@ List.nth facts_list split_index in
    Node (Ope ope,
        btree_of_list @@ remove_parenthesis @@ _filteri (fun index _ -> index < split_index) facts_list,
        btree_of_list @@ remove_parenthesis @@ _filteri (fun index _ -> index > split_index) facts_list)



let evaluate_tree (tree : expr binary_tree) (facts_dict:((string, bool option) Hashtbl.t)): bool option =
  let rec evaluate (tree : expr binary_tree) : bool option =
    match tree with
    | Empty -> Some false
    | Node(Leaf h, _, _) -> Hashtbl.find facts_dict h
    | Node(Ope h, left, Empty) -> h (evaluate left) (Some false)
    | Node(Ope h, Empty, right) -> h (evaluate right) (Some false)
    | Node(Ope h, left, right) -> h (evaluate right) (evaluate left)
    | Node(Empty, _, _) -> Some false
  in
  evaluate tree

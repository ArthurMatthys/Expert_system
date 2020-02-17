open Library

type 'a binary_tree =
  | Empty
  | Node of 'a * 'a binary_tree * 'a binary_tree


type expr =
  | Empty
  | Leaf of string
  | Ope of (bool -> bool option -> bool)
  | Value of bool


let _filteri (func: int -> 'a -> bool) (lst:'a list): 'a list = 
  let rec loop__filteri (func: int -> 'a -> bool) (lst:'a list) (index: int): 'a list =
    match lst with
    | [] -> []
    | h::t -> if func index h
      then h :: loop__filteri func t (index + 1)
      else loop__filteri func t (index + 1)
  in
  loop__filteri func lst 0


let _ope_of_string ((ope,_):(string*int)) : (bool -> bool option -> bool) =
  match ope with
  | "^" -> let my_xor (a: bool) (b: bool option) =  a <> Option.get b in my_xor
  | "|" -> let my_or (a: bool) (b: bool option) =  a || Option.get b in my_or
  | "+" -> let my_and (a: bool) (b: bool option) =  a <> Option.get b in my_and
  | "!" -> let my_not (a: bool) (b: bool option) =  not a in my_not
  | _ -> let my_nothing a b = false in my_nothing


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
    let (ope: (bool -> bool option -> bool)) = _ope_of_string @@ List.nth facts_list split_index in
    Node (Ope ope,
          btree_of_list @@ remove_parenthesis @@ _filteri (fun index _ -> index < split_index) facts_list,
         btree_of_list @@ remove_parenthesis @@ _filteri (fun index _ -> index > split_index) facts_list)


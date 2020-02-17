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


let index_of (lst:string list) (search:string): int=
  let rec loop (str:string list) (index:int): int = match str with
    | [] -> -1
    | h::t -> if h = search
      then index
      else loop t (index+1)
  in
  loop lst 0


let explode (s:string) : string list=
    let rec exp i l =
        if i < 0 then l else exp (i - 1) (Char.escaped s.[i] :: l) in
    exp (String.length s - 1) []

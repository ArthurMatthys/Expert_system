let rec remove_parenthesis (facts_list:(string*int)list) : (string*int) list =
  match facts_list with
  | [] -> []
  | ("(", _) :: t -> remove_parenthesis t
  | (")", _) :: t -> remove_parenthesis t
  | h::t -> h :: remove_parenthesis t


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

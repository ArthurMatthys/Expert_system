let rec recreate_line (line:(string*int)list):string = match line with
  | [] -> ""
  | (h,_)::t -> h ^ (recreate_line t)

let rec _check (line:(string*int) list) (left:bool) (imply:int) (right:bool) : ((int, string) result) = match line with
  | [] -> if left && right && imply <> 0 
    then Result.ok (imply)
    else if imply = 0
      then Result.Error ("No implication symbol found")
      else if not left
        then Result.Error ("No left part")
        else Result.Error ("No right part")
  | ("<",_)::("=", _)::(">", _)::t -> if imply = 0 
    then _check t left 4 right
    else Result.Error ("Multiple implications found")
  | ("=", _)::(">", _)::t -> if imply = 0 
    then _check t left 3 right
    else Result.Error ("Multiple implications found")
  | ("=", _)::t -> if imply = 0 || left
    then _check t true 1 right
    else Result.Error ("Equal found but wrongly placed")
  | ("?", _)::t -> if imply = 0 || left
    then _check t true 2 right
    else Result.Error ("Question mark found but wrongly placed")
  | (h1,v1)::(h2,v2)::t -> if (v1 = v2 && h2 <> "!") && imply <> 1 && imply <> 2
    then Result.Error ("Two characters with same type found : \"" ^ h1 ^ "\" and\"" ^ h2 ^ "\"")
    else if v1 < 0
      then Result.Error ("Character not valid : \"" ^ h1 ^ "\"")
      else if imply > 0
        then _check ((h2,v2)::t) left imply true
        else _check ((h2,v2)::t) true imply right
  | (h,v)::t -> if v < 0
    then Result.Error ("Character not valid : \"" ^ h ^ "\"")
    else if imply > 0
      then _check t left imply true
      else _check t true imply right


let check_input (data:(string*int) list list) : ((unit, string) result) =
  let rec check_file (lines:(string*int) list list) (facts:bool) (init:bool) (search:bool) : ((unit, string) result) = match lines with
    | [] -> if init && search && facts
      then Result.Ok () 
      else if not init
        then Result.Error ("Could not find the initial facts")
        else if not search
          then Result.Error ("Could not find the queries")
          else Result.Error ("No statement was found")
    | h::t -> if List.length h = 0 
      then check_file t facts init search
      else
        let (res_check: (int, string) result) = _check h false 0 false in
        if Result.is_error res_check 
        then Result.Error ("Error in line \"" ^ (recreate_line h) ^ "\" : " ^ Result.get_error res_check)
        else let type_line = Result.get_ok res_check in
          if type_line = 1 
          then if init
            then Result.Error ("There is two lines containing initial facts")
            else check_file t facts true search

          else if type_line = 2 
            then if search
                then Result.Error ("There is two lines containing a query")
                else check_file t facts init true
          else check_file t true init search
  in
  check_file data false false false


let check_consistency (lst_fact:(string*(bool option)) list) (lst_states:(string*int)list): ((unit,string) result) = 
  let unknown_facts = List.filter (fun (fact, case) -> if case <> 1 
    then false
    else not @@ List.exists ((=) (fact, None)) lst_fact
    ) lst_states
  in
  if List.length unknown_facts = 0
  then Result.ok ()
  else Result.error (match List.nth unknown_facts 0 with (str,_) -> str)


let count_even_parenthesis (facts_list:(string*int)list) : bool =
  let rec count (facts_lst:(string*int)list) (nbr:int) : bool =
    match facts_lst with
    | [] -> nbr = 0
    | (h,_)::t -> if h = "("
      then count t (nbr+1)
      else
        if h = ")"
        then count t (nbr-1)
        else count t nbr
  in
  count facts_list 0

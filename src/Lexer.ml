open Library

let alphabet = ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";]
let implications = ["=";"?";">";"<"]
let conditions = ["^";"|";"+";"!"]


let print_lex ((read, value):(string*int)):unit =
  Printf.printf "char : %s\tvalue : %d\n" read value


let print_lexed_line (lex_line:(string*int) list):unit =
  let _ = List.map print_lex lex_line in 
  print_newline ()


let lexer (str:string): ((string*int) list)=
  let rec remove_comment (lst:string list) :string list = match lst with
    | [] -> []
    | h::t -> if h = "#" then [] else h :: remove_comment t
  in
  let (str_cleaned: string list) = explode @@ String.escaped str in
  let rec lex (depth:int) (lst:string list) : ((string*int )list) = match lst with
    | [] -> []
    | h::t -> let comp = ((=) h) in
      if h = " " 
      then lex depth t
      else if List.exists comp alphabet 
        then (h, 1) :: lex depth t
        else if List.exists comp implications
        then match t with
          | [] -> (h, 2) :: []
          | "="::">"::tl -> ("<=>", 3) :: lex depth tl
          | ">"::tl -> ("=>", 4) :: lex depth tl
          | _ -> (h, 2) :: lex depth t
          else if List.exists comp conditions
          (* then begin Printf.fprintf Stdlib.stdout "debug-lex: |%s|\n" h ; (h, (5 + 4*depth + (index_of conditions h))) :: lex depth t end  *)
          then (h, (5 + 4*depth + (index_of conditions h))) :: lex depth t 
            else if h = "("
              then (h, 5 + 4*(depth+1)) :: (lex (depth+1) t)
              else if h = ")"
                then (h, 5 + 4*depth) :: (lex (depth-1) t)
                else (h, 0) :: lex depth t
  in
  if List.exists ((=) "#") str_cleaned
  then lex 0 @@ remove_comment str_cleaned
  else lex 0 str_cleaned

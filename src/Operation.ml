let my_and (a:bool option) (b:bool option) : bool option =
  if Option.is_none a || Option.is_none b
  then None
  else Some (Option.get a && Option.get b)


let my_or (a:bool option) (b:bool option) : bool option =
  if Option.is_none a && Option.is_none b
  then None
  else 
    if Option.is_none a
    then b
    else
      if Option.is_none b
      then a
      else Some (Option.get a || Option.get b)


let my_xor (a:bool option) (b:bool option) : bool option =
  if Option.is_none a || Option.is_none b
  then None
  else Some (Option.get a <> Option.get b)


let my_not (a:bool option) : bool option =
  if Option.is_none a
  then None
  else Some (not @@ Option.get a)

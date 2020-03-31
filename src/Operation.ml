let my_and (a:((bool option),string)result) (b:((bool option),string)result) : (((bool option),string)result) =
  if Result.is_error a
    then a
  else if Result.is_error b
    then b
  else
    if Option.is_none (Result.get_ok a) || Option.is_none (Result.get_ok b)
    then Result.ok None
    else Result.ok (Some (Option.get (Result.get_ok a) && Option.get (Result.get_ok b)))


let my_or (a:((bool option),string)result) (b:((bool option),string)result) : (((bool option),string)result) =
  if Result.is_error a
    then a
  else if Result.is_error b
    then b
  else
    if Option.is_none (Result.get_ok a) && Option.is_none (Result.get_ok b)
    then Result.ok None
    else 
      if Option.is_none (Result.get_ok a)
      then b
      else
        if Option.is_none (Result.get_ok b)
        then a
        else Result.ok (Some (Option.get (Result.get_ok a) || Option.get (Result.get_ok b)))


let my_xor (a:((bool option),string)result) (b:((bool option),string)result) : (((bool option),string)result) =
  if Result.is_error a
    then a
  else if Result.is_error b
    then b
  else
    if Option.is_none (Result.get_ok a) || Option.is_none (Result.get_ok b)
    then Result.ok None
    else Result.ok (Some (Option.get (Result.get_ok a) <> Option.get (Result.get_ok b)))


let my_not (a:((bool option),string)result) : (((bool option),string)result) =
  if Result.is_error a
    then a
  else
    if Option.is_none (Result.get_ok a)
    then Result.ok None
    else Result.ok (Some (not @@ Option.get (Result.get_ok a)))

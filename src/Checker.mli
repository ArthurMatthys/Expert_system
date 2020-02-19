val check_input_mandatory : (string*int) list list -> (unit, string) result
val check_input_bonus : (string*int) list list -> (unit, string) result
val check_consistency : ((string*(bool option)) list) -> ((string*int) list) -> (unit,string) result
val count_even_parenthesis : (string*int)list -> bool
val recreate_line: (string*int)list -> string

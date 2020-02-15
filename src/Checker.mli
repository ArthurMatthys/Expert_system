val check_input : (string*int) list list -> (unit, string) result
val check_input2 : (string*int*int) list list -> (unit, string) result
val check_consistency : ((string*(bool option)) list) -> ((string*int) list) -> (unit,string) result
val check_consistency2 : ((string*(bool option)) list) -> ((string*int*int) list) -> (unit,string) result

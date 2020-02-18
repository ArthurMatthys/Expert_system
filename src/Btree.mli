type exp_ast

val print_exp_ast : exp_ast -> unit
val exp_ast_of_list : (string*int) list -> exp_ast

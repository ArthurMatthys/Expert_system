type 'a binary_tree
type expr
type exp_ast

val btree_of_list : (string*int)list -> expr binary_tree
val print_exp_ast : exp_ast -> unit
val exp_ast_of_list : (string*int) list -> exp_ast

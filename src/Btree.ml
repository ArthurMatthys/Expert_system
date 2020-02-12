type 'a binary_tree =
  | Empty
  | Node of 'a * 'a binary_tree * 'a binary_tree

type expr =
  | Empty
  | Leaf of string
  | Ope of (string -> string -> bool)


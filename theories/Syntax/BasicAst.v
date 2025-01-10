(** * LogRel.BasicAst: definitions preceding those of the AST of terms: sorts, binder annotations… *)

Inductive sort : Set :=
  | set : sort.

Definition sort_of_product (s s' : sort) := set.
Require Import Termination.Trees.
Require Import Termination.Syntax.
Require Import Termination.Tactics.

(* always 0 for non-values *)
Fixpoint tsize_semantics t: nat :=
  match t with
  | fvar _ _ => 0
  | uu => 0
  | notype_lambda t' => 0
  | pp t1 t2 => 1 + tsize_semantics t1 + tsize_semantics t2
  | ttrue => 0
  | tfalse => 0
  | zero => 0
  | succ t' =>  1 + tsize_semantics t'
  | notype_trefl => 0
  | type_abs t => 0
  | notype_tfold t => 1 + tsize_semantics t
  | tright t => 1 + tsize_semantics t
  | tleft t => 1 + tsize_semantics t
  | T => 0
  end.

From Coq Require Import List.
Import ListNotations.

(** * Some complements on [comparison] *)

Set Implicit Arguments.

(** A notation for lexicographic comparison.
    Note that [c2] might not need to be evaluated (lazyness). *)

Notation "c1 >>= c2" :=
  (match c1 with Lt => Lt | Gt => Gt | Eq => c2 end) (at level 70).

(** Lexicographic comparison on pairs *)

Section PairComp.
Variable A B : Type.
Variable cmpA : A -> A -> comparison.
Variable cmpB : B -> B -> comparison.
Definition pair_compare '(a,b) '(a',b') := cmpA a a' >>= cmpB b b'.
End PairComp.

(** Comparison on lists *)

Section ListComp.
Variable A : Type.
Variable cmp : A -> A -> comparison.
Fixpoint list_compare (l1 l2 : list A) :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | x1::l1', x2::l2' => cmp x1 x2 >>= list_compare l1' l2'
  end.
End ListComp.

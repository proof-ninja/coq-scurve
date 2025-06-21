Require Export List.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Section Prefix.
  Variable A: Type.

  Definition Prefix (pre xs: list A) := exists r, xs = pre ++ r.

  Lemma Prefix_app (pre r: list A) : Prefix pre (pre ++ r).
  Admitted.


  Lemma prefix_brothers_is_prefix (p1 p2 xs : list A) :
    Prefix p1 xs -> Prefix p2 xs ->
    Prefix p1 p2 \/ Prefix p2 p1.
  Admitted.

End Prefix.

Hint Resolve Prefix_app : core.

Fixpoint all_prefix {A:Set} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x::xs' =>
      let ps := all_prefix xs' in
      ps ++ map (fun ys => x :: ys) ps
  end.

Fixpoint all_sublists {A:Set} (xs: list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x::xs' =>
      map (fun ys => x :: ys) (all_prefix xs') ++ all_sublists xs'
  end.

Inductive sublist {A:Set} : list A -> list A -> Prop:=
| SL l xs r: sublist xs (l ++ xs ++ r).

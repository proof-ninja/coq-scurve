Require Export List.
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

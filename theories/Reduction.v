Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Open Scope R_scope.
Import ListNotations.

(* 向き *)
Inductive Direction : Set :=
| Plus : Direction
| Minus : Direction
.

(* 単位セグメントから向きへの変換 *)
Definition orn (x:PrimitiveSegment) : Direction :=
match x with
| (n, e, cx) | (s, e, cx) | (s, w, cc) | (n, w, cc) => Plus
| (s ,w, cx) | (s, e, cc) | (n, e, cc) | (n, w, cx) => Minus
end.

Definition inv (x:Direction) : Direction :=
match x with
| Plus => Minus
| Minus => Plus
end.

(* 簡約 *)
Definition reduction (xs: list Direction) : list Direction :=
match xs with
| s1 :: s2 :: s3 :: s4 :: xs'  =>
    if s1 = s3 and s3 = inv s2 then
      s1 :: s4 :: xs'
    else
    if s1 = s2 and s2 = inv s3 and inv s3 = inv s4 then
      s1 :: s4 :: xs'
    else
      xs
| _ => xs
end.

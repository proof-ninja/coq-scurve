Require Import Stdlib.Lists.List.
Require Import PrimitiveSegment.
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

(* 簡約のルール
 * r1: s1 = s3 = inv(s2) ならば σ1 s1 s2 s3 σ2 を σ1 s1 σ2 に置き換える. +−+ ⇒ +, −+− ⇒ −
 * r2: s1 = s2 = inv(s3) = inv(s4) ならば σ1 s1 s2 s3 s4 σ2 を σ1 s1 s4 σ2 に置き換える. ++−− ⇒ +−, −−++ ⇒ −+
 *)
Inductive Rule : list Direction -> list Direction -> Prop :=
| R1Plus : Rule [Plus; Minus; Plus] [Plus]
| R1Minus : Rule [Minus; Plus; Minus] [Minus]
| R2Plus : Rule [Plus; Plus; Minus; Minus] [Plus; Minus]
| R2Minus : Rule [Minus; Minus; Plus; Plus] [Minus; Plus]
.

Inductive ReduceDirStep : list Direction -> list Direction -> Prop :=
| RDS : forall (l r ds ds': list Direction), Rule ds ds' ->
    ReduceDirStep (l ++ ds ++ r) (l ++ ds' ++ r)
.

Inductive ReduceDir : list Direction -> list Direction -> Prop :=
| RDRefl : forall ds, ReduceDir ds ds
| RDTrans : forall ds ds' ds'', ReduceDirStep ds ds' -> ReduceDirStep ds' ds'' ->
    ReduceDir ds ds''
.

Definition Reduce (p p': list PrimitiveSegment): Prop :=
  ReduceDir (map orn p) (map orn p').

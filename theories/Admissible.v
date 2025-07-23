From Stdlib Require Export List.
Require Import Reduction.
From Stdlib Require Import ZArith.
Require Import PrimitiveSegment.
Import ListNotations.
Open Scope Z_scope.

Definition all_admissibles :=
[
  (* + *)
  [Plus];
  [Minus];
  (* +- *)
  [Plus; Minus];
  [Minus;Plus];
  (* ++ *)
  [Plus; Plus];
  [Minus; Minus];
  (* +++ *)
  [Plus; Plus; Plus];
  [Minus; Minus; Minus];
  (* ++- *)
  [Plus; Plus; Minus];
  [Minus; Plus; Plus];
  [Minus; Minus; Plus];
  [Plus; Minus; Minus];
  (* +++- *)
  [Plus; Plus; Plus; Minus];
  [Minus; Plus; Plus; Plus];
  [Minus; Minus; Minus; Plus];
  [Plus; Plus; Plus; Minus];
  (* -++- *)
  [Minus; Plus; Plus; Minus];
  [Plus; Minus; Minus; Plus];
  (* ++++- *)
  [Plus; Plus; Plus; Plus; Minus];
  [Minus; Plus; Plus; Plus; Plus];
  [Minus; Minus; Minus; Minus; Plus];
  [Plus; Minus; Minus; Minus; Minus];
  (* -+++- *)
  [Minus; Plus; Plus; Plus; Minus];
  [Plus; Minus; Minus; Minus; Plus];
  (* -++++- *)
  [Minus; Plus; Plus; Plus; Plus; Minus];
  [Plus; Minus; Minus; Minus; Minus; Plus];
  (* -+++++- *)
  [Minus; Plus; Plus; Plus; Plus; Plus; Minus];
  [Plus; Minus; Minus; Minus; Minus; Minus; Plus]
  ].

Parameter AdmissibleDirs : list Direction -> Prop.

Definition reduced_form ds reduced:= ReduceDir ds reduced /\ ~ CanReduceDirStep reduced. 

Lemma AdmissibleDirs_preserve ds ds': AdmissibleDirs ds -> ReduceDir ds ds' -> AdmissibleDirs ds'.
Admitted.

Axiom inadmissible_rotation_dif_four: forall ds, rotation_difference ds >= 4 -> ~ AdmissibleDirs ds.

Lemma rotate_dif_four_len_eight ds reduced: reduced_form ds reduced -> (length reduced >= 8)%nat ->rotation_difference ds >= 4.
Admitted.

Theorem reduced_admissible_form : forall ds reduced, AdmissibleDirs ds -> reduced_form ds reduced -> In reduced all_admissibles.
Admitted.
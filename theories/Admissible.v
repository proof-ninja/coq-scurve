From Stdlib Require Export List.
Require Import Reduction.
From Stdlib Require Import ZArith.
Require Import PrimitiveSegment.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Import Lia.

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
  [Plus; Minus; Minus; Minus];
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

Axiom notAdmissibleNil : ~ AdmissibleDirs [].

Lemma nil_RDS ds: ~ ReduceDirStep ds [].
Proof.
  intros RDS. inversion RDS as [l r ds0 ds1 HRule eq1 eq2].
  apply app_eq_nil in eq2. destruct eq2 as [l_nil eq2]. apply app_eq_nil in eq2. destruct eq2 as [ds1_nil r_nil]. subst.
  inversion HRule.
Qed.

Lemma nil_reduce ds: ReduceDir ds [] -> ds = [].
Proof. 
  intros RD. remember [] as ds'. induction RD as [ds|ds ds' _nil RDS RD IHRD]; try reflexivity.
  subst. contradict RDS. rewrite IHRD. exact (nil_RDS ds). reflexivity.
Qed. 

Definition reduced ds dsr:= ReduceDir ds dsr /\ ~ CanReduceDirStep dsr. 

Lemma AdmissibleDirs_preserve ds ds': AdmissibleDirs ds -> ReduceDir ds ds' -> AdmissibleDirs ds'.
Admitted.

Axiom inadmissible_rotation_dif_four: forall ds, Z.abs(rotation_difference ds) >= 4 -> ~ AdmissibleDirs ds.

Lemma repeat_dif_P n: rotation_difference (repeat Plus n) = Z.of_nat n.
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - simpl. change (Plus :: repeat Plus n) with ([Plus] ++ repeat Plus n). rewrite rotation_difference_distribution. rewrite IHn. change (rotation_difference [Plus]) with 1. now auto with zarith.
Qed.
Lemma repeat_dif_M n: rotation_difference (repeat Minus n) = - (Z.of_nat n).
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - simpl. change (Minus :: repeat Minus n) with ([Minus] ++ repeat Minus n). rewrite rotation_difference_distribution. rewrite IHn. change (rotation_difference [Minus]) with (-1). now auto with zarith.
Qed.

Lemma rotate_dif_four_len_eight ds dsr: reduced ds dsr -> (length dsr >= 8)%nat -> Z.abs(rotation_difference ds) >= 4.
Proof.
  intros [rdc cannotStep] len_eight.
  rewrite (rotation_difference_preservation ds dsr rdc).
  eapply reduced_form in cannotStep as form.
  destruct form as [l [m [n [Hl [Hn [PMP | MPM]]]]]].
  - rewrite PMP in len_eight. repeat rewrite length_app in len_eight. repeat rewrite repeat_length in len_eight. rewrite <- Nat.add_shuffle3 in len_eight. rewrite Nat.add_comm in len_eight.
    destruct l as [| [|l]], n as [| [|n]]; try lia; simpl in len_eight;
    subst; repeat rewrite rotation_difference_distribution; rewrite repeat_dif_M; repeat rewrite repeat_dif_P; lia.
  - rewrite MPM in len_eight. repeat rewrite length_app in len_eight. repeat rewrite repeat_length in len_eight. rewrite <- Nat.add_shuffle3 in len_eight. rewrite Nat.add_comm in len_eight.
    destruct l as [| [|l]], n as [| [|n]]; try lia; simpl in len_eight;
    subst; repeat rewrite rotation_difference_distribution; rewrite repeat_dif_P; repeat rewrite repeat_dif_M; lia.
Qed.

Ltac listin := repeat (try (now left);right).

Theorem reduced_admissible_form : forall ds dsr, AdmissibleDirs ds -> reduced ds dsr -> In dsr all_admissibles.
Proof.
  intros ds dsr admds [rdc cannotStep].
  eapply reduced_form in cannotStep as form.
  destruct (Nat.le_gt_cases 8 (length dsr)) as [ge8 | lt8];
  [contradict admds; apply inadmissible_rotation_dif_four; eapply rotate_dif_four_len_eight; [split;[exact rdc | exact cannotStep] | exact ge8] |]. 
  destruct form as [l [m [n [lcond [ncond [PMP | MPM]]]]]].
  - destruct l as [|[|l]], n as [|[|n]];simpl in PMP; subst.
    + destruct m as [|[|[|[|m]]]]; try now listin.
      * contradict admds. simpl in rdc. apply nil_reduce in rdc. subst. exact notAdmissibleNil.
      * contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). rewrite rotation_difference_distribution. rewrite repeat_dif_M. simpl. lia.
    + destruct m as [|[|[|[|[|m]]]]]; try now listin.
      contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). change (repeat Minus (S (S (S (S (S m)))))) with ([Minus; Minus; Minus; Minus; Minus] ++ repeat Minus m). repeat rewrite rotation_difference_distribution. rewrite repeat_dif_M. rewrite Z.add_comm. rewrite Z.add_assoc. change (rotation_difference [Plus] + rotation_difference [Minus; Minus; Minus; Minus; Minus]) with (-4). lia.
    + contradict ncond. lia.
    + destruct m as [|[|[|[|[|m]]]]]; try now listin.
      contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). simpl. rewrite app_nil_r. change (Plus :: Minus :: Minus :: Minus :: Minus :: Minus :: repeat Minus m) with ([Plus; Minus; Minus; Minus; Minus; Minus] ++ repeat Minus m). rewrite rotation_difference_distribution. rewrite repeat_dif_M. change (rotation_difference [Plus;Minus; Minus; Minus; Minus; Minus]) with (-4). lia.
    + destruct m as [|[|[|[|[|[|m]]]]]]; try now listin.
      * contradict cannotStep. simpl. exists [Plus]. change ([Plus; Minus; Plus]) with ([] ++ [Plus; Minus; Plus] ++ []). change [Plus] with ([] ++ [Plus] ++ []). now apply RDS.
      * contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). simpl. repeat rewrite app_comm_cons. change (Plus :: Minus :: Minus :: Minus :: Minus :: Minus :: Minus :: repeat Minus m) with ([Plus; Minus; Minus; Minus; Minus; Minus; Minus] ++ repeat Minus m). repeat rewrite rotation_difference_distribution. rewrite repeat_dif_M. rewrite Z.add_shuffle0. change (rotation_difference [Plus; Minus; Minus; Minus; Minus; Minus; Minus] + rotation_difference [Plus]) with (-4). lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
  - destruct l as [|[|l]], n as [|[|n]];simpl in MPM; subst.
    + destruct m as [|[|[|[|m]]]]; try now listin.
      * contradict admds. simpl in rdc. apply nil_reduce in rdc. subst. exact notAdmissibleNil.
      * contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). rewrite rotation_difference_distribution. rewrite repeat_dif_P. simpl. lia.
    + destruct m as [|[|[|[|[|m]]]]]; try now listin.
      contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). change (repeat Plus (S (S (S (S (S m)))))) with ([Plus; Plus; Plus; Plus; Plus] ++ repeat Plus m). repeat rewrite rotation_difference_distribution. rewrite repeat_dif_P. rewrite Z.add_comm. rewrite Z.add_assoc. change (rotation_difference [Minus] + rotation_difference [Plus; Plus; Plus; Plus; Plus]) with 4. lia.
    + contradict ncond. lia.
    + destruct m as [|[|[|[|[|m]]]]]; try now listin.
      contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). simpl. rewrite app_nil_r. change (Minus :: Plus :: Plus :: Plus :: Plus :: Plus :: repeat Plus m) with ([Minus; Plus; Plus; Plus; Plus; Plus] ++ repeat Plus m). rewrite rotation_difference_distribution. rewrite repeat_dif_P. change (rotation_difference [Minus; Plus; Plus; Plus; Plus; Plus]) with 4. lia.
    + destruct m as [|[|[|[|[|[|m]]]]]]; try now listin.
      * contradict cannotStep. simpl. exists [Minus]. change ([Minus; Plus; Minus]) with ([] ++ [Minus; Plus; Minus] ++ []). change [Minus] with ([] ++ [Minus] ++ []). now apply RDS.
      * contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). simpl. repeat rewrite app_comm_cons. change (Minus :: Plus :: Plus :: Plus :: Plus :: Plus :: Plus :: repeat Plus m) with ([Minus; Plus; Plus; Plus; Plus; Plus; Plus] ++ repeat Plus m). repeat rewrite rotation_difference_distribution. rewrite repeat_dif_P. rewrite Z.add_shuffle0. change (rotation_difference [Minus; Plus; Plus; Plus; Plus; Plus; Plus] + rotation_difference [Minus]) with 4. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
Qed.

Definition all_admissibles_quotient :=
[
  (* + *)
  [Plus];
  (* +- *)
  [Plus; Minus];
  (* ++ *)
  [Plus; Plus];
  (* +++ *)
  [Plus; Plus; Plus];
  (* ++- *)
  [Plus; Plus; Minus];
  (* +++- *)
  [Plus; Plus; Plus; Minus];
  (* -++- *)
  [Minus; Plus; Plus; Minus];
  (* ++++- *)
  [Plus; Plus; Plus; Plus; Minus];
  (* -+++- *)
  [Minus; Plus; Plus; Plus; Minus];
  (* -++++- *)
  [Minus; Plus; Plus; Plus; Plus; Minus];
  (* -+++++- *)
  [Minus; Plus; Plus; Plus; Plus; Plus; Minus]
  ].

Definition inv ds := map (fun x => match x with | Plus => Minus | Minus => Plus end) ds.

Inductive Equiv : list Direction -> list Direction -> Prop :=
| Equal : forall ds, Equiv ds ds
| Rev : forall ds, Equiv ds (rev ds)
| Inv : forall ds, Equiv ds (inv ds)
| RevInv : forall ds, Equiv ds (rev (inv ds))
.

Ltac try_all_list lst :=
  match eval compute in lst with
  | nil => fail "not applicable"
  | cons ?h ?t => first [now (exists h; subst; split;[try constructor| listin]) | try_all_list t ]
  end.

Lemma consist_quotient: 
forall ds, In ds all_admissibles -> exists repds, Equiv ds repds /\ In repds all_admissibles_quotient.
Proof.
  intros ds HIn. repeat destruct HIn as [Heq | HIn]
  ; try_all_list all_admissibles_quotient.
Qed.

Corollary reduced_admissible_form_quotient:
forall ds dsr, AdmissibleDirs ds -> reduced ds dsr -> exists repds, Equiv dsr repds /\ In repds all_admissibles_quotient.
Proof.
  intros ds dsr AD Reduced. apply consist_quotient. exact (reduced_admissible_form ds dsr AD Reduced).
Qed.
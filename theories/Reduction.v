Require Import ListExt.
From Stdlib Require Import ZArith.
Require Import PrimitiveSegment.
Import ListNotations.
Open Scope Z_scope.
Require Import Eq.

(* 向き *)
Inductive Direction : Set :=
| Plus : Direction
| Minus : Direction
.

Definition Direction_dec: forall (x y: Direction), {x = y} + {x <> y}.
  refine (fun x y => match x, y with
                  | Plus, Plus => left _
                  | Minus, Minus => left _
                  | _, _ => right _
                  end); now auto.
Defined.
Canonical Direction_eqDec := @Pack _ Direction_dec.

(* 単位セグメントから向きへの変換 *)
Definition orn (x:PrimitiveSegment) : Direction :=
match x with
| (n, e, cx) | (s, e, cx) | (s, w, cc) | (n, w, cc) => Plus
| (s ,w, cx) | (s, e, cc) | (n, e, cc) | (n, w, cx) => Minus
end.

Definition rotation_difference (ds: list Direction) : Z :=
  fold_right Z.add 0 (map (fun d =>
                             match d with
                             | Plus => 1
                             | Minus => -1
                             end
  ) ds).

Lemma rotation_difference_distribution:
  forall (ds ds': list Direction),
  rotation_difference (ds ++ ds') = rotation_difference ds + rotation_difference ds'.
Proof.
  intros ds ds'.
  unfold rotation_difference.
  set (F := fun d =>
              match d with
              | Plus => 1
              | Minus => -1
              end).
  induction ds as [| d ds IH]; [now simpl | simpl].
  rewrite IH. now auto with zarith.
Qed.

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
Hint Constructors Rule : core.

Lemma Rule_same_src ds ds1 ds2: Rule ds ds1 -> Rule ds ds2 -> ds1 = ds2.
Proof.
  intros rule1 rule2.
  inversion rule1; inversion rule2; subst; now try discriminate.
Qed.

Lemma rotation_difference_preservation_rule:
  forall (ds ds': list Direction), Rule ds ds' -> rotation_difference ds = rotation_difference ds'.
Proof.
  intros ds ds' H. now destruct H.
Qed.

Lemma Rule_preserve_both_ends: forall ds ds',
  Rule ds ds' -> head ds = head ds' /\ last_opt ds = last_opt ds'.
Proof.
  intros ds ds' H.
  destruct H; auto.
Qed.

Inductive ReduceDirStep : list Direction -> list Direction -> Prop :=
| RDS : forall (l r ds ds': list Direction), Rule ds ds' ->
    ReduceDirStep (l ++ ds ++ r) (l ++ ds' ++ r)
.

Lemma ReduceDirStep_length ds ds':
  ReduceDirStep ds ds' -> length ds = (2 + length ds')%nat.
Proof.
  intros H.
  induction H.
  destruct H; simpl; repeat rewrite length_app, length_cons; repeat rewrite plus_n_Sm; reflexivity.
Qed.

Lemma rotation_difference_preservation_step:
  forall (ds ds': list Direction), ReduceDirStep ds ds' -> rotation_difference ds = rotation_difference ds'.
Proof.
  intros ds ds' H.
  destruct H.
  apply rotation_difference_preservation_rule in H.
  repeat rewrite rotation_difference_distribution.
  apply Z.add_cancel_l. apply Z.add_cancel_r. now apply H.
Qed.

Lemma ReduceDirStep_preserve_both_ends: forall ds ds',
  ReduceDirStep ds ds' -> head ds = head ds' /\ last_opt ds = last_opt ds'.
Proof.
  intros ds ds' H.
  destruct H as [l r es es' rule].
  destruct (Rule_preserve_both_ends _ _ rule) as [head last].
  split.
  - destruct l; [simpl | now reflexivity].
    destruct es'; [now rewrite nil_head in head |].
    destruct es; [now discriminate | simpl].
    simpl in head. apply head.
  - repeat rewrite last_head in last.
    repeat rewrite last_head.
    repeat rewrite rev_app_distr.
    destruct (rev r); [simpl | now reflexivity].
    destruct (rev es').
    * rewrite nil_head in last.
      rewrite last.
      now reflexivity.
    * destruct (rev es); [now discriminate | now simpl].
Qed.

Inductive ReduceDir : list Direction -> list Direction -> Prop :=
| RDRefl : forall ds, ReduceDir ds ds
| RDTrans : forall ds ds' ds'', ReduceDirStep ds ds' -> ReduceDir ds' ds'' ->
    ReduceDir ds ds''
.

Lemma ReduceDir_preserve_both_ends: forall ds ds',
  ReduceDir ds ds' -> head ds = head ds' /\ last_opt ds = last_opt ds'.
Proof.
  intros ds ds' H.
  induction H; [split; reflexivity|].
  destruct (ReduceDirStep_preserve_both_ends _ _ H) as [head_eq last_eq].
  destruct IHReduceDir as [head_eq' last_eq'].
  split; [now rewrite head_eq, head_eq' | now rewrite last_eq, last_eq'].
Qed.

Definition Reduce (p p': list PrimitiveSegment): Prop :=
  ReduceDir (map orn p) (map orn p').

Definition rule_dec ds: {exists ds', Rule ds ds'} + {~ exists ds', Rule ds ds'}.
  refine (match ds with
          | [Plus; Minus; Plus] => left (ex_intro _ [Plus] _)
          | [Minus; Plus; Minus] => left (ex_intro _ [Minus] _)
          | [Plus; Plus; Minus; Minus] => left (ex_intro _ [Plus; Minus] _)
          | [Minus; Minus; Plus; Plus] => left (ex_intro _ [Minus; Plus] _)
          | _ => right _
          end);try now auto; intros H; destruct H.
Defined.

Lemma ReduceDirStep_ex_sublist ds :
  (exists ds', ReduceDirStep ds ds') <-> ex_sublists (fun ds0 => exists ds0', Rule ds0 ds0') ds.
Proof.
  split.
  - intros existsds'. destruct existsds' as [ds' HRDS]. apply all_sublists_ex. apply Exists_exists.
    inversion HRDS as [l r l0 r0 HRule _eq1 _eq2]. exists l0. split.
    + apply all_sublists_iff. now apply (SL l l0 r).
    + now exists r0.
  - intros Hex_sub. apply all_sublists_ex in Hex_sub. apply Exists_exists in Hex_sub. destruct Hex_sub as [l0 [HIn [r0 HR]]].
    apply all_sublists_iff in HIn. inversion HIn as [l _l0 r _eq _eq2]. exists (l ++ r0 ++ r). now apply (RDS l r l0 r0).
Qed.

Definition CanReduceDirStep ds := exists ds', ReduceDirStep ds ds'.

Lemma CanReduceDirStep_or ds: CanReduceDirStep ds \/ ~CanReduceDirStep ds.
Proof.
    destruct (ex_sublists_dec (fun ds0 => exists ds0', Rule ds0 ds0') rule_dec ds).
    - left. now apply ReduceDirStep_ex_sublist.
    - right. intros HCRDS. apply n. apply ReduceDirStep_ex_sublist. exact HCRDS.
Qed.

(**
 * 簡約の性質1: 強正規化性
 * 簡約は必ず停止する
 *)
Lemma termination : forall x, exists y, ReduceDir x y /\ ~ CanReduceDirStep y.
Proof.
  apply (Nat.measure_induction _ (@List.length _)).
  intros x IHx.
  destruct (CanReduceDirStep_or x) as [canReduce|].
  - destruct canReduce as [x' step]. destruct IHx with x' as [final [reduce cannnotStep]].
    + rewrite (ReduceDirStep_length x x'); auto with arith.
    + exists final. now split; [apply RDTrans with x' |].
  - exists x. now split; [constructor|].
Qed.

  (**
    * 簡約の性質2: 回転差保持
    * 簡約において +, − の個数の差は保持される.
    *)
Lemma rotation_difference_preservation:
  forall (ds ds': list Direction), ReduceDir ds ds' -> rotation_difference ds = rotation_difference ds'.
Proof.
  intros ds ds' H.
  induction H as [| ds ds']; [now reflexivity |].
  apply rotation_difference_preservation_step in H.
  rewrite H. now apply IHReduceDir.
Qed.

  (**
    * 簡約の性質3.a: reduced form
    * educeDirをこれ以上できないまで行った最終形が必ず次のような形をしている:
    * (一つまたはゼロ個の +) (一つ以上の連続する-の列) (一つまたはゼロ個の +)
    * またはその +と - を逆にしたもの
    *)
Lemma tl_cannot_reduce h tl: ~ CanReduceDirStep (h :: tl) -> ~ CanReduceDirStep tl.
Proof.
  intros notreduce reduce.
  apply notreduce. inversion reduce as [tl' HRDS]. inversion HRDS as [l r ds ds' HRule eq1 eq2].
  exists ((h :: l) ++ ds' ++ r). rewrite app_comm_cons.
  now auto.
Qed.

Lemma ReduceDir_reduced_form_PlusPlus l r:
  ~ CanReduceDirStep (l ++ [Plus;Plus] ++ r) -> r <> [] ->
  exists lst (n: nat),  r = (List.repeat Plus n) ++ [lst].
Proof.
  revert l. induction r as [|d r IHr].
  - contradiction.
  - intros l NotReduce _Hnil. clear _Hnil. destruct d.
    + destruct r as [|d r'];[now exists Plus, 0%nat|].
      assert (Heq: (l ++ [Plus; Plus] ++ Plus :: d::r') = ((l++[Plus]) ++ [Plus;Plus] ++ d :: r')).
      {
        simpl. rewrite <- app_assoc. reflexivity.
      }
      rewrite Heq in NotReduce.
      apply IHr in NotReduce;[|discriminate].
      destruct NotReduce as [lst [n _eqr]].
      rewrite _eqr. exists lst, (1+n)%nat. reflexivity.
    + destruct r as [|d r'];[now exists Minus, 0%nat|].
      destruct d.
      * contradict NotReduce. simpl. exists ((l ++ [Plus]) ++ [Plus] ++ r').
      assert(Heq: (l ++ Plus :: Plus :: Minus :: Plus :: r') = ((l ++ [Plus]) ++ [Plus ; Minus ; Plus] ++ r')).
      { rewrite <- app_assoc. reflexivity. }
      rewrite Heq. now auto.
      * contradict NotReduce. simpl. exists (l ++ [Plus; Minus] ++ r').
      change (l ++ Plus :: Plus :: Minus :: Minus :: r') with (l ++ [Plus; Plus; Minus; Minus] ++ r').
      now auto.
Qed.

Lemma ReduceDir_reduced_form_MinusMinus l r:
  ~ CanReduceDirStep (l ++ [Minus;Minus] ++ r) -> r <> [] ->
  exists lst (n: nat),  r = (List.repeat Minus n) ++ [lst].
Proof.
  revert l. induction r as [|d r IHr].
  - contradiction.
  - intros l NotReduce _Hnil. clear _Hnil. destruct d.
    + destruct r as [|d r'];[now exists Plus, 0%nat|].
      destruct d.
      * contradict NotReduce. simpl. exists (l ++ [Minus; Plus] ++ r').
      change (l ++ Minus :: Minus :: Plus :: Plus :: r') with (l ++ [Minus; Minus; Plus; Plus] ++ r').
      now auto.
      * contradict NotReduce. simpl. exists ((l ++ [Minus]) ++ [Minus] ++ r').
      assert(Heq: (l ++ Minus :: Minus :: Plus :: Minus :: r') = ((l ++ [Minus]) ++ [Minus ; Plus ; Minus] ++ r')).
      { rewrite <- app_assoc. reflexivity. }
      rewrite Heq. now auto.
    + destruct r as [|d r'];[now exists Minus, 0%nat|].
      assert (Heq: (l ++ [Minus; Minus] ++ Minus :: d::r') = ((l++[Minus]) ++ [Minus;Minus] ++ d :: r')).
      {
        simpl. rewrite <- app_assoc. reflexivity.
      }
      rewrite Heq in NotReduce.
      apply IHr in NotReduce;[|discriminate].
      destruct NotReduce as [lst [n _eqr]].
      rewrite _eqr. exists lst, (1+n)%nat. reflexivity.
Qed.

Lemma ReduceDir_reduced_form_MinusPlusRepeat: forall (n: nat) r,
  ~ CanReduceDirStep (Minus :: Plus :: (List.repeat Minus n) ++ r)
  -> n = 0%nat.
Proof.
  intros n r NotReduce. destruct n as [|n].
  - reflexivity.
  - contradiction NotReduce. simpl. 
    change (Minus :: Plus :: Minus :: repeat Minus n ++ r) with ([] ++ [Minus ; Plus; Minus] ++ (repeat Minus n ++ r)).
    exists ([] ++ [Minus] ++ repeat Minus n ++ r). now auto.
Qed.

Lemma ReduceDir_reduced_form_PlusMinusRepeat: forall (n: nat) r,
  ~ CanReduceDirStep (Plus :: Minus :: (List.repeat Plus n) ++ r)
  -> n = 0%nat.
Proof.
  intros n r NotReduce. destruct n as [|n].
  - reflexivity.
  - contradiction NotReduce. simpl. 
    change (Plus :: Minus :: Plus :: repeat Plus n ++ r) with ([] ++ [Plus ; Minus; Plus] ++ (repeat Plus n ++ r)).
    exists ([] ++ [Plus] ++ repeat Plus n ++ r). now auto.
Qed.

Lemma repeat_last_P n lst x: x = repeat Plus n ++ [lst] -> exists n' m', x = repeat Plus n' ++ repeat Minus m'.
Proof.
  destruct lst; intros ->; [exists (1 + n)%nat, O| exists n, 1%nat].
  - replace [Plus] with (repeat Plus 1); [|now auto].
    now rewrite <- repeat_app, Nat.add_comm, app_nil_r.
  - now simpl.
Qed.

Lemma repeat_last_M n lst x: x = repeat Minus n ++ [lst] -> exists n' m', x = repeat Minus n' ++ repeat Plus m'.
Proof.
  destruct lst; intros ->; [exists n, 1%nat| exists (1 + n)%nat, O].
  - now simpl.
  - replace [Minus] with (repeat Minus 1); [|now auto].
    now rewrite <- repeat_app, Nat.add_comm, app_nil_r.
Qed.

Open Scope nat_scope.
Lemma reduced_form : forall (x: list Direction), ~ CanReduceDirStep x
  ->  exists (l m n:nat), (x = (List.repeat Plus l) ++ (List.repeat Minus m) ++ (List.repeat Plus n) \/ 
                           x = (List.repeat Minus l) ++ (List.repeat Plus m) ++ (List.repeat Minus n)).
Proof.
  intros x. induction x as [|h x IHx];[exists 0, 0, 0;now left|].
  intros NotReduce. apply tl_cannot_reduce in NotReduce as NotReducex. apply IHx in NotReducex. clear IHx. destruct NotReducex as [l [m [n [PMP | MPM]]]].
    - destruct h;[exists (1+l), m, n; left; now rewrite PMP|].
      destruct l;[exists 0, (1+m), n; left; now rewrite PMP|].
      destruct l.
      + simpl in PMP. rewrite PMP in NotReduce. eapply ReduceDir_reduced_form_MinusPlusRepeat in NotReduce. subst. simpl. exists 0,1,(1+n). now left.
      + simpl in PMP. rewrite PMP in NotReduce.
        destruct ((list_eq_dec Direction_dec) (repeat Plus l ++ repeat Minus m ++ repeat Plus n) (@nil Direction)) as [e|ne]; [exists 0,1,2;left; rewrite PMP; now rewrite e|].
        change (Minus :: Plus :: Plus :: repeat Plus l ++ repeat Minus m ++ repeat Plus n) with ([Minus] ++ [Plus ; Plus] ++ repeat Plus l ++ repeat Minus m ++ repeat Plus n) in NotReduce. 
        eapply ReduceDir_reduced_form_PlusPlus in NotReduce;[|exact ne].
        destruct NotReduce as [lst [n0 eq]]. rewrite eq in PMP.
        change (Plus :: Plus :: repeat Plus n0 ++ [lst]) with (repeat Plus (2+n0) ++ [lst]) in PMP. apply repeat_last_P in PMP.
        destruct PMP as [n' [m' _eq]]. exists 1,n',m'. right. now rewrite _eq.
    - destruct h;[|exists (1+l), m, n; right; now rewrite MPM].
      destruct l;[exists 0, (1+m), n; right; now rewrite MPM|].
      destruct l; simpl in MPM; rewrite MPM in NotReduce.
      + eapply ReduceDir_reduced_form_PlusMinusRepeat in NotReduce. subst. simpl. exists 0,1,(1+n). now right.
      + 
        destruct ((list_eq_dec Direction_dec) (repeat Minus l ++ repeat Plus m ++ repeat Minus n) (@nil Direction)) as [e|ne]; [exists 0,1,2;right; rewrite MPM; now rewrite e|].
        change (Plus :: Minus :: Minus :: repeat Minus l ++ repeat Plus m ++ repeat Minus n) with ([Plus] ++ [Minus ; Minus] ++ repeat Minus l ++ repeat Plus m ++ repeat Minus n) in NotReduce. 
        eapply ReduceDir_reduced_form_MinusMinus in NotReduce;[|exact ne].
        destruct NotReduce as [lst [n0 eq]]. rewrite eq in MPM.
        change (Minus :: Minus :: repeat Minus n0 ++ [lst]) with (repeat Minus (2+n0) ++ [lst]) in MPM. apply repeat_last_M in MPM.
        destruct MPM as [n' [m' _eq]]. exists 1,n',m'. left. now rewrite _eq.
Qed.
      
Close Scope nat_scope. 



Notation have_common_reduce ds1 ds2 := (exists ds', ReduceDir ds1 ds' /\ ReduceDir ds2 ds').

Lemma non_overlap_reduction_confluence l c r ds1 ds2 ds1' ds2':
  Rule ds1 ds1' -> Rule ds2 ds2' ->
  have_common_reduce (l ++ ds1' ++ c ++ ds2 ++ r) (l ++ ds1 ++ c ++ ds2' ++ r).
Proof.
  intros. exists (l ++ ds1' ++ c ++ ds2' ++ r). split.
  - eapply RDTrans. rewrite app_assoc. rewrite app_assoc. apply RDS. now eauto. repeat (rewrite app_assoc; try now apply RDRefl).
  - eapply RDTrans. apply RDS. now eauto. repeat (rewrite app_assoc; try now apply RDRefl).
Qed.

Lemma Rule_app_inv r1 r2 ds1l ds1r ds1 ds2 ds1' ds2': (* 14パターン列挙 *)
  ds1r <> [] -> ds1 = ds1l ++ ds1r ->
  Rule ds1 ds1' ->
  Rule ds2 ds2' ->
  ds2 ++ r2 = ds1r ++ r1 ->
  (ds1l = [] /\ ds1r = ds2)
  \/ (ds1l = [Plus] /\ ds1r = [Minus; Plus] /\ ds2 = [Minus; Plus; Minus])
  \/ (ds1l = [Minus] /\ ds1r = [Plus; Minus] /\ ds2 = [Plus; Minus; Plus])
  \/ (ds1l = [Plus; Minus] /\ ds1r = [Plus] /\ ds2 = [Plus; Minus; Plus])
  \/ (ds1l = [Minus; Plus] /\ ds1r = [Minus] /\ ds2 = [Minus; Plus; Minus])
  \/ (ds1l = [Plus; Minus] /\ ds1r = [Plus] /\ ds2 = [Plus; Plus; Minus; Minus])
  \/ (ds1l = [Minus; Plus] /\ ds1r = [Minus] /\ ds2 = [Minus; Minus; Plus; Plus])
  \/ (ds1l = [Plus; Plus] /\ ds1r = [Minus; Minus] /\ ds2 = [Minus; Minus; Plus; Plus])
  \/ (ds1l = [Minus; Minus] /\ ds1r = [Plus; Plus] /\ ds2 = [Plus; Plus; Minus; Minus])
  \/ (ds1l = [Plus; Plus; Minus] /\ ds1r = [Minus] /\ ds2 = [Minus; Plus; Minus])
  \/ (ds1l = [Plus; Plus; Minus] /\ ds1r = [Minus] /\ ds2 = [Minus; Minus; Plus; Plus])
  \/ (ds1l = [Minus; Minus; Plus] /\ ds1r = [Plus] /\ ds2 = [Plus; Minus; Plus])
  \/ (ds1l = [Minus; Minus; Plus] /\ ds1r = [Plus] /\ ds2 = [Plus; Plus; Minus; Minus])
.
Proof.
  intros nonnil eds1 rule1 rule2 prefix_ds2.
  destruct ds1r as [|d ds1r]; [now auto|].
  assert (or4: ds1l = []
               \/ (exists d0, ds1l = [d0])
               \/ (exists d0 d1, ds1l = [d0; d1])
               \/ (exists d0 d1 d2, ds1l = [d0; d1; d2])
         ).
  + destruct ds1l as [|d0]; [now left|].
    destruct ds1l as [|d1]; [now right; left; exists d0|].
    destruct ds1l as [|d2]; [now right; right; left; exists d0, d1|].
    destruct ds1l as [|d3]; [now right; right; right;  exists d0, d1, d2|].
    simpl in eds1. rewrite eds1 in rule1.
    now destruct ds1l; inversion rule1.
  + destruct or4 as [|[ [d0 e0] |[ [d0 [d1 e]] | [d0 [d1 [d2 e]]]]
      ]];
      destruct rule1, rule2; subst; try inversion eds1; subst; try now auto; try tauto.
Qed.


Lemma eq_have_common_reduce ds1 ds2: ds1 = ds2 -> have_common_reduce ds1 ds2.
Proof.
  intros eq. subst. exists ds2. split; now apply RDRefl.
Qed.

Lemma ReduceDirStep_Reduce_dir ds ds': ReduceDirStep ds ds' -> ReduceDir ds ds'.
Proof.
  intros HRDS. eapply RDTrans.
  - exact HRDS.
  - now apply RDRefl.
Qed.

Lemma ReduceDir_local_confluence_aux l1 r1 ds1 ds1' l2 r2 ds2 ds2':
  Rule ds1 ds1' ->
  Rule ds2 ds2' ->
  l2 ++ ds2 ++ r2 = l1 ++ ds1 ++ r1 ->
  Prefix l1 l2 ->
  have_common_reduce (l1 ++ ds1' ++ r1) (l2 ++ ds2' ++ r2).
Proof.
  intros rule1 rule2 e prefix.
  destruct (prefix) as [l1' prefix_]. subst l2.
  rewrite <- app_assoc, app_inv_head_iff in e.
  destruct (ds1 =? l1').
  - (* ds1 = l1' の場合: rule1,2で重ならない *)
    rewrite <- app_assoc. subst l1'.
    rewrite app_inv_head_iff in e. subst r1.
    now apply (non_overlap_reduction_confluence l1 []).
  - destruct (@prefix_brothers_is_prefix _ ds1 l1' (ds1 ++ r1)) as[prefix'|prefix'].
    + now auto.
    + now rewrite <- e.
    + (* ds1 < l1' の場合: rule1,2で重ならない *)
      destruct prefix' as [l1'']. subst l1'.
      rewrite <- app_assoc, app_inv_head_iff in e. subst r1.
      repeat rewrite <- app_assoc.
      now apply non_overlap_reduction_confluence.
    + (* ds1 > l1' の場合: 重なるパターンを考える *)
      repeat rewrite <- app_assoc.
      destruct prefix' as [ds1_r ]. subst ds1.
      rewrite <- app_assoc, app_inv_head_iff in e.
      assert (nonnil: ds1_r <> []);
        [now intros enil; rewrite enil, app_nil_r in n|].
      destruct (Rule_app_inv r1 r2 l1' ds1_r (l1' ++ ds1_r) ds2 ds1' ds2' nonnil (refl_equal _) rule1 rule2 e) as
        [es|[es|[es|[es|[es|[es|[es|[es|[es|[es|[es|[es|es]]]] ]]]]]]]].
      * destruct es as [e1 e2]. subst. simpl in *.
        rewrite (Rule_same_src _ _ _ rule1 rule2).
        rewrite (app_inv_head  _ _ _ e).
        now apply eq_have_common_reduce.
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. subst. inversion rule2. subst.
        apply eq_have_common_reduce.
        do 2 f_equal. now inversion e.
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst.
        apply eq_have_common_reduce.
        do 2 f_equal. now inversion e.
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst.
        apply eq_have_common_reduce. now rewrite <- e .
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst.
        apply eq_have_common_reduce. now rewrite <- e .
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst.
        exists (l1 ++ [Plus; Minus] ++r2). rewrite <- e.
        split; apply ReduceDirStep_Reduce_dir; [now constructor|].
        change ([Plus; Minus] ++ [Plus; Minus] ++ r2) with ([Plus; Minus; Plus] ++ [Minus] ++ r2).
        now change ([Plus; Minus] ++ r2) with ([Plus] ++ [Minus] ++ r2).
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst.
        exists (l1 ++ [Minus; Plus] ++ r2). rewrite <- e.
        split; apply ReduceDirStep_Reduce_dir; [now constructor|].
        change ([Minus; Plus] ++ [Minus; Plus] ++ r2) with ([Minus; Plus; Minus] ++ [Plus] ++ r2).
        now change ([Minus; Plus] ++ r2) with ([Minus] ++ [Plus]++r2).
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst. inversion e.
        exists (l1 ++ [Plus] ++ Plus::r2).
        change ([Plus; Minus] ++ Plus :: Plus :: r2) with ([Plus; Minus; Plus] ++ Plus :: r2).
        split; apply ReduceDirStep_Reduce_dir; [now repeat constructor|].
        change ([Plus; Plus] ++ [Minus; Plus] ++ r2) with ([Plus] ++ [Plus; Minus; Plus] ++ r2).
        change (Plus :: r2) with ([Plus] ++ r2).
        now do 2 rewrite  (app_assoc l1).
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst. inversion e. subst.
        exists (l1 ++ [Minus; Minus] ++ r2). split; apply ReduceDirStep_Reduce_dir.
        -- replace (l1 ++ [Minus; Plus] ++ Minus :: Minus :: r2)
                   with ((l1 ++ [Minus;Plus;Minus] ++ ([Minus] ++ r2))); [|reflexivity].
           now change (l1 ++ [Minus; Minus] ++ r2) with (l1 ++ [Minus] ++ ([Minus] ++ r2)).
        -- replace (l1 ++ [Minus; Minus] ++ [Plus; Minus] ++ r2)
                   with ((l1 ++ [Minus]) ++ [Minus;Plus; Minus] ++ r2); [|now rewrite <- app_assoc].
           now replace (l1 ++ [Minus; Minus] ++ r2) with ((l1 ++ [Minus]) ++ [Minus] ++ r2);
             [|now rewrite <- app_assoc].
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst. inversion e. subst r1.
        exists (l1 ++ [Plus; Minus] ++ r2); split; apply ReduceDirStep_Reduce_dir.
        -- change (l1 ++ [Plus;Minus] ++ Plus :: Minus :: r2) with
             (l1 ++ [Plus;Minus;Plus]++([Minus] ++ r2)).
           now change (l1 ++ [Plus;Minus] ++ r2) with (l1 ++ [Plus] ++ ([Minus] ++ r2)).
        -- now change ([Plus;Plus;Minus] ++ [Minus] ++ r2) with
             ([Plus; Plus; Minus; Minus] ++ r2).
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst. inversion e. subst r1.
        exists ((l1 ++ [Plus]) ++ [Minus; Plus] ++ r2). split; apply ReduceDirStep_Reduce_dir.
        -- now replace (l1 ++ [Plus;Minus] ++ Minus::Plus::Plus::r2)
             with ((l1 ++ [Plus]) ++ [Minus;Minus;Plus;Plus] ++ r2);
             [|now rewrite <- app_assoc].
        -- change (l1 ++ [Plus;Plus;Minus]++[Minus; Plus] ++ r2)
             with (l1 ++ [Plus;Plus;Minus;Minus]++ ([Plus] ++ r2)).
           now replace ((l1 ++ [Plus]) ++ [Minus;Plus] ++ r2)
             with (l1 ++ [Plus;Minus] ++ ([Plus] ++ r2)); [|now rewrite <- app_assoc].
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst. inversion e; subst r1.
        exists (l1 ++ [Minus; Plus] ++ r2). split; apply ReduceDirStep_Reduce_dir.
        -- change (l1 ++ [Minus; Plus] ++ Minus:: Plus :: r2) with (l1 ++ [Minus; Plus; Minus] ++ ([Plus]++r2)).
           now change (l1 ++ [Minus; Plus] ++ r2) with (l1 ++ [Minus] ++ ([Plus] ++ r2)).
        -- now change ([Minus; Minus; Plus] ++ [Plus] ++ r2)
             with ([Minus; Minus; Plus; Plus] ++ r2).
      * destruct es as [e1 [e2 e3]]; subst.
        inversion rule1. inversion rule2. subst. inversion e. subst r1.
        exists (l1 ++ [Minus; Plus] ++ ([Minus] ++ r2)). split; apply ReduceDirStep_Reduce_dir.
        -- replace (l1 ++ [Minus; Plus] ++ Plus :: Minus:: Minus ::r2)
                   with ((l1 ++ [Minus]) ++ [Plus; Plus; Minus; Minus] ++ r2);
             [|now rewrite <- app_assoc].
           now replace (l1 ++ [Minus;Plus] ++ [Minus] ++ r2)
               with ((l1 ++ [Minus]) ++ [Plus;Minus] ++ r2); [|now rewrite <- app_assoc].
        -- now change ([Minus; Minus; Plus] ++ [Plus; Minus] ++ r2)
             with ([Minus;Minus;Plus;Plus] ++ [Minus]++r2).
Qed.


Lemma exists_iff {A:Type} (P Q : A -> Prop) :
  (forall x, P x <-> Q x) -> (exists x, P x) <-> (exists x, Q x).
Proof.
  intros pq. now split; intros [x p]; exists x; [rewrite <- pq| rewrite pq].
Qed.

Lemma ReduceDir_local_confluence src dst1 dst2:
  ReduceDirStep src dst1 ->
  ReduceDirStep src dst2 ->
  have_common_reduce dst1 dst2.
Proof.
  intros step1 step2.
  inversion step1 as [l1 r1 ds1 ds1' rule1 e1 e2].
  inversion step2 as [l2 r2 ds2 ds2' rule2 e12 e22]. subst.
  destruct (@prefix_brothers_is_prefix _ l1 l2 (l1 ++ (ds1 ++ r1))) as [prefix|prefix].
  - now auto.
  - now rewrite <- e12.
  - now apply (ReduceDir_local_confluence_aux _ _ _ _ _ _ _ _ rule1 rule2).
  - rewrite (exists_iff _ _ (fun ds => and_comm _ _)).
    now eapply (ReduceDir_local_confluence_aux _ _ _ _ _ _ _ _ rule2 rule1).
Qed.

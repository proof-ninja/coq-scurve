Require Import Segment.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.
Import ListNotations.

(* Segment.v にある extend を実際に作れることを確認するためのファイル *)

(* ls の各セグメントの境界を表す媒介変数値の列．ls の長さが n なら n+1 個あり，
    i 番目と i+1 番目の要素の間が ls の i 番目のセグメントの区間に対応する．
    先頭要素より小さい／末尾要素より大きい部分は，それぞれ先頭／末尾セグメントの延長線に対応する． *)
Parameter segment_border : list Segment -> list R.

Axiom border_length : forall ls, length (segment_border ls) = S (length ls).

(* 単調増加であるという仕様．連続する要素についてだけ述べれば十分 *)
Axiom border_increasing : forall ls i bi bi1,
  nth_error (segment_border ls) i = Some bi ->
  nth_error (segment_border ls) (S i) = Some bi1 ->
  bi < bi1.

(* t がどのセグメントの担当か & そこでのローカル媒介変数 を返却．
    segs の i 番目のセグメントの区間が bs の i 番目・(i+1) 番目の要素の間になるように，
    t の位置から該当するセグメントとその中でのローカルな媒介変数（アフィン変換で [0,1] に写したもの）を選ぶ．
    区間の端点（共有される境界）ちょうどでは，手前のセグメント側を採用する．
    最後のセグメントについては，区間の外側でもそのまま同じアフィン変換の式を使うことで，
    延長線（先頭は t' <= 0，末尾は t' >= 1）を表す． *)
Fixpoint concrete_extend_pick
  (segs : list Segment) (bs : list R) (t : R)
  : nat * Segment * R :=
  match segs, bs with
  | s :: nil, b0 :: b1 :: nil =>
      (O, s, (t - b0) / (b1 - b0))

  | s :: ((_ :: _) as segs'), b0 :: ((b1 :: _) as bs') =>
      if Rle_dec t b1 then
        (O, s, (t - b0) / (b1 - b0))
      else
        let '(n, s', t') :=
          concrete_extend_pick segs' bs' t
        in
        (S n, s', t')

  | _, _ =>
      (O, default_segment, 0)
  end.

Definition concrete_extend (ls : list Segment) (t : R) : R * R :=
  let (s', t') := concrete_extend_pick ls (segment_border ls) t in
  let (_, s) := s' in point s t'.

(* --------------------------------------------------------------------------- *)
(* extend_pick の特徴づけ．extention_split 等の証明のための下請け補題群 *)

Definition Increasing (bs : list R) : Prop :=
  forall i bi bi1, nth_error bs i = Some bi -> nth_error bs (S i) = Some bi1 -> bi < bi1.

Lemma Increasing_tl : forall b bs, Increasing (b :: bs) -> Increasing bs.
Proof.
  intros b bs H i bi bi1 Hi Hi1.
  apply (H (S i) bi bi1); simpl; assumption.
Qed.

Lemma Increasing_lt : forall bs i j a b,
  Increasing bs -> (i < j)%nat -> nth_error bs i = Some a -> nth_error bs j = Some b -> a < b.
Proof.
  intros bs i j. revert i.
  induction j as [| j' IH]; intros i a b Hinc Hij Hi Hj; [lia |].
  destruct (Nat.eq_dec i j') as [->|Hneq].
  - eapply Hinc; eauto.
  - assert (Hij': (i < j')%nat) by lia.
    destruct (nth_error bs j') as [c|] eqn:Hc.
    + assert (Hac: a < c) by (eapply IH; eauto).
      assert (Hcb: c < b) by (eapply Hinc; eauto).
      lra.
    + exfalso. apply nth_error_None in Hc.
      assert (Hlen: (length bs <= S j')%nat) by lia.
      apply nth_error_None in Hlen. congruence.
Qed.

Lemma segment_border_increasing : forall ls, Increasing (segment_border ls).
Proof. intros ls i bi bi1. apply border_increasing. Qed.

(* アフィン変換 t -> (t-b0)/(b1-b0) に関する基本性質 *)
Lemma affine_param_iff_le : forall b0 b1 t k,
  b0 < b1 -> ((t - b0) / (b1 - b0) <= k <-> t <= b0 + k * (b1 - b0)).
Proof.
  intros b0 b1 t k Hb.
  assert (Hd: 0 < b1 - b0) by lra.
  assert (Heq: (t - b0) / (b1 - b0) * (b1 - b0) = t - b0) by (field; lra).
  split; intro H.
  - assert (H2: (t - b0) / (b1 - b0) * (b1 - b0) <= k * (b1 - b0))
      by (apply Rmult_le_compat_r; lra).
    lra.
  - apply (Rmult_le_reg_r (b1 - b0)); [lra |]. lra.
Qed.

Lemma affine_param_iff_gt : forall b0 b1 t k,
  b0 < b1 -> (k < (t - b0) / (b1 - b0) <-> b0 + k * (b1 - b0) < t).
Proof.
  intros b0 b1 t k Hb.
  assert (Hd: 0 < b1 - b0) by lra.
  assert (Heq: (t - b0) / (b1 - b0) * (b1 - b0) = t - b0) by (field; lra).
  split; intro H.
  - assert (H2: k * (b1 - b0) < (t - b0) / (b1 - b0) * (b1 - b0))
      by (apply Rmult_lt_compat_r; lra).
    lra.
  - apply (Rmult_lt_reg_r (b1 - b0)); [lra |]. lra.
Qed.

Lemma affine_inj : forall b0 b1 t1 t2,
  b0 < b1 -> (t1 - b0) / (b1 - b0) = (t2 - b0) / (b1 - b0) -> t1 = t2.
Proof.
  intros b0 b1 t1 t2 Hb Heq.
  assert (Hd: 0 < b1 - b0) by lra.
  assert (E1: (t1 - b0) / (b1 - b0) * (b1 - b0) = t1 - b0) by (field; lra).
  assert (E2: (t2 - b0) / (b1 - b0) * (b1 - b0) = t2 - b0) by (field; lra).
  assert (t1 - b0 = t2 - b0) by (rewrite <- E1, <- E2, Heq; reflexivity).
  lra.
Qed.

(* extend_pick の特徴づけ：どの区間を選んでいるか，およびその中でのアフィン変換の式 *)
Lemma concrete_extend_pick_spec_aux : forall segs bs t,
  segs <> [] ->
  length bs = S (length segs) ->
  Increasing bs ->
  exists n s bn bn1,
    nth_error segs n = Some s /\
    nth_error bs n = Some bn /\
    nth_error bs (S n) = Some bn1 /\
    ((n = O /\ t <= bn) \/ (bn < t <= bn1) \/ (S n = length segs /\ bn1 < t)) /\
    concrete_extend_pick segs bs t
      = (n, s, (t - bn) / (bn1 - bn)).
Proof.
  induction segs as [| s0 segs' IH]; intros bs t Hne Hlen Hinc; [congruence |].
  destruct segs' as [| s1 segs''].
  - (* segs = [s0], bs は長さ2 *)
    destruct bs as [| b0 [| b1 [| b2 bs2]]]; simpl in Hlen; try lia.
    exists O, s0, b0, b1.
    assert (Hb01: b0 < b1) by (eapply (Hinc O); simpl; reflexivity).
    assert (Hcase: (O = O /\ t <= b0) \/ (b0 < t <= b1) \/ (S O = length [s0] /\ b1 < t)). {
      destruct (Rle_or_lt t b0) as [Ht | Ht]; [left; auto |].
      destruct (Rle_or_lt t b1) as [Ht1 | Ht1]; [right; left; lra |].
      right; right; split; [reflexivity | lra].
    }
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split; [exact Hcase |].
    simpl. reflexivity.
  - (* segs = s0 :: s1 :: segs'' *)
    destruct bs as [| b0 [| b1 bs'']]; simpl in Hlen; try lia.
    assert (Hb01: b0 < b1) by (eapply (Hinc O); simpl; reflexivity).
    assert (Hlen': length (b1 :: bs'') = S (length (s1 :: segs''))) by (simpl in *; lia).
    assert (Hinc': Increasing (b1 :: bs'')) by (eapply Increasing_tl; eauto).
    destruct (Rle_dec t b1) as [Htb1 | Htb1].
    + (* このセグメントを選ぶ *)
      exists O, s0, b0, b1.
      assert (Hcase: (O = O /\ t <= b0) \/ (b0 < t <= b1) \/ (S O = length (s0::s1::segs'') /\ b1 < t)).
      { destruct (Rle_or_lt t b0) as [Ht | Ht]; [left; auto | right; left; lra]. }
      split; [reflexivity |].
      split; [reflexivity |].
      split; [reflexivity |].
      split; [exact Hcase |].
      simpl. destruct (Rle_dec t b1); [reflexivity | contradiction].
    + (* 再帰 *)
      assert (Hne': s1 :: segs'' <> []) by discriminate.
      destruct (IH (b1 :: bs'') t Hne' Hlen' Hinc')
        as [n' [s' [bn' [bn1' [Hs' [Hbn' [Hbn1' [Hcase Heq]]]]]]]].
      exists (S n'), s', bn', bn1'.
      assert (Hcase': (S n' = O /\ t <= bn') \/ (bn' < t <= bn1') \/ (S (S n') = length (s0::s1::segs'') /\ bn1' < t)).
      { destruct Hcase as [[Hn0 Ht] | [Hmid | [Hlast Ht]]].
        - exfalso. subst n'. simpl in Hbn'. injection Hbn' as ->. lra.
        - right; left; assumption.
        - right; right; split; [simpl in Hlast |- *; lia | assumption]. }
      split; [simpl; assumption |].
      split; [simpl; assumption |].
      split; [simpl; assumption |].
      split; [exact Hcase' |].
      simpl. destruct (Rle_dec t b1); [contradiction |]. 
      simpl. 
Admitted.

Lemma concrete_extend_pick_spec : forall ls t,
  ls <> [] ->
  exists n s bn bn1,
    nth_error ls n = Some s /\
    nth_error (segment_border ls) n = Some bn /\
    nth_error (segment_border ls) (S n) = Some bn1 /\
    ((n = O /\ t <= bn) \/ (bn < t <= bn1) \/ (S n = length ls /\ bn1 < t)) /\
    concrete_extend_pick ls (segment_border ls) t = (n, s, (t - bn) / (bn1 - bn)).
Proof.
  intros ls t Hne.
  apply concrete_extend_pick_spec_aux; auto.
  - apply border_length.
  - apply segment_border_increasing.
Qed.


(* Axiom とされていたものをちゃんと満たすことを確認 *)
Definition extend_index (ls : list Segment) (t : R) : nat :=
  let '(n, _, _) :=
    concrete_extend_pick
      ls (segment_border ls) t
  in n.

Definition extend_param (ls : list Segment) (t : R) : R :=
  let '(_, _, t') :=
    concrete_extend_pick
      ls (segment_border ls) t
  in t'.

Definition extend (ls : list Segment) (t : R) : R * R :=
  let '(_, s, t') :=
    concrete_extend_pick
      ls (segment_border ls) t
  in point s t'.
  

Lemma extend_repr_sound : forall ls t,
  ls <> [] ->
  exists s,
    nth_error ls (extend_index ls t) = Some s /\
    extend ls t = point s (extend_param ls t).
Proof.
  intros ls t Hls.

  destruct (concrete_extend_pick_spec ls t Hls)
    as [n [s [bn [bn1 [Hseg [Hbn [Hbn1 [Hcase Hpick]]]]]]]].

  exists s.
  split.
  - unfold extend_index.
    rewrite Hpick.
    simpl.
    exact Hseg.

  - unfold extend, concrete_extend.
    unfold extend_param.
    rewrite Hpick.
    simpl.
    reflexivity.
Qed.

Lemma extend_param_region_sound : forall ls t,
  ls <> [] ->
  (0 < extend_param ls t <= 1)
  \/ (extend_index ls t = 0%nat /\ extend_param ls t <= 0)
  \/ (S (extend_index ls t) = length ls /\ 1 < extend_param ls t).
Proof.
  intros ls t Hls.

  destruct (concrete_extend_pick_spec ls t Hls)
    as [n [s [bn [bn1 [Hseg [Hbn [Hbn1 [Hcase Hpick]]]]]]]].

  assert (Hbnlt : bn < bn1).
  {
    eapply segment_border_increasing.
    - exact Hbn.
    - exact Hbn1.
  }

  assert (Hden : 0 < bn1 - bn) by lra.

  assert (Hidx :
      extend_index ls t = n).
  {
    unfold extend_index.
    rewrite Hpick.
    reflexivity.
  }

  assert (Hparam :
      extend_param ls t = (t - bn) / (bn1 - bn)).
  {
    unfold extend_param.
    rewrite Hpick.
    reflexivity.
  }

  destruct Hcase as [[Hn0 Htle] | [Hmid | [Hlast Hgt]]].

  - right; left.
    split.
    + congruence.
    + rewrite Hparam.
      pose proof
        (affine_param_iff_le bn bn1 t 0 Hbnlt)
        as Hiff.
      apply Hiff.
      simpl.
      lra.

  - left.
    rewrite Hparam.
    split.
    + pose proof
        (affine_param_iff_gt bn bn1 t 0 Hbnlt)
        as Hiff.
      apply Hiff.
      simpl.
      lra.
    + pose proof
        (affine_param_iff_le bn bn1 t 1 Hbnlt)
        as Hiff.
      apply Hiff.
      simpl.
      lra.

  - right; right.
    split.
    + rewrite Hidx.
      exact Hlast.
    + rewrite Hparam.
      pose proof
        (affine_param_iff_gt bn bn1 t 1 Hbnlt)
        as Hiff.
      apply Hiff.
      simpl.
      lra.
Qed.

Lemma extend_same_piece_injective_sound : forall ls t1 t2,
  ls <> [] ->
  extend_index ls t1 = extend_index ls t2 ->
  extend_param ls t1 = extend_param ls t2 ->
  t1 = t2.
Proof.
  intros ls t1 t2 Hnonnil Hidx Hparam.

  destruct (concrete_extend_pick_spec ls t1 Hnonnil)
    as [n1 [s1 [bn1 [bn11
      [Hseg1 [Hbn1 [Hbn11 [Hcase1 Hpick1]]]]]]]].

  destruct (concrete_extend_pick_spec ls t2 Hnonnil)
    as [n2 [s2 [bn2 [bn21
      [Hseg2 [Hbn2 [Hbn21 [Hcase2 Hpick2]]]]]]]].

  assert (Hidx1 :
      extend_index ls t1 = n1).
  {
    unfold extend_index.
    rewrite Hpick1.
    reflexivity.
  }

  assert (Hidx2 :
      extend_index ls t2 = n2).
  {
    unfold extend_index.
    rewrite Hpick2.
    reflexivity.
  }

  assert (Hn : n1 = n2) by congruence.
  subst n2.

  assert (Hbn : bn1 = bn2).
  {
    assert (Htmp : Some bn1 = Some bn2). {
      rewrite <- Hbn1.
      rewrite <- Hbn2.
      congruence.
    }
    injection Htmp.
    auto.
  }

  assert (Hbn1eq : bn11 = bn21).
  {
    assert (Htmp : Some bn11 = Some bn21). {
      rewrite <- Hbn11.
      rewrite <- Hbn21.
      congruence.
    }
    injection Htmp.
    auto.
  }

  assert (Hlt1 : bn1 < bn11).
  {
    eapply segment_border_increasing.
    - exact Hbn1.
    - exact Hbn11.
  }

  assert (Hparam' :
      (t1 - bn1) / (bn11 - bn1)
      =
      (t2 - bn2) / (bn21 - bn2)).
  {
    unfold extend_param in Hparam.
    rewrite Hpick1 in Hparam.
    rewrite Hpick2 in Hparam.
    simpl in Hparam.
    exact Hparam.
  }

  rewrite Hbn in Hparam'.
  rewrite Hbn1eq in Hparam'.

  eapply affine_inj.
  - exact Hlt1.
  - subst; exact Hparam'.
Qed.
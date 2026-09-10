Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import SegmentsTranslation.
Require Import ListExt.
Require Import Sparse.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.


(* --------------------------------------------------------------------------- *)
(* extend に関する補題．extend の公理は Segment.v 参照 *)

Lemma extention_split : forall t1 t2 ls,
  let p1 := extend ls t1 in let p2 := extend ls t2 in
  ls <> [] -> t1 <> t2 ->
  (exists u1 u2, u1 <= 0 /\ u2 <= 0 /\ u1 <> u2 /\ p1 = point (hd_segment ls) u1 /\ p2 = point (hd_segment ls) u2)
  \/ (exists u1 u2 s, u1 <= 0 /\ 0 < u2 <= 1 /\ In s ls /\ p1 = point (hd_segment ls) u1 /\ p2 = point s u2)
  \/ (exists u1 u2, u1 <= 0 /\ 1 < u2 /\ p1 = point (hd_segment ls) u1 /\ p2 = point (last_segment ls) u2)
  \/ (exists u1 u2 s, 0 < u1 <= 1 /\ u2 <= 0 /\ In s ls /\ p1 = point s u1 /\ p2 = point (hd_segment ls) u2)
  \/ (exists u1 u2 s, 0 < u1 <= 1 /\ 0 < u2 <= 1 /\ u1 <> u2 /\ In s ls /\ p1 = point s u1 /\ p2 = point s u2)
  \/ (exists u1 u2 s1 s2, 0 < u1 <= 1 /\ 0 < u2 <= 1 /\ In_order s1 s2 ls /\ p1 = point s1 u1 /\ p2 = point s2 u2)
  \/ (exists u1 u2 s1 s2, 0 < u1 <= 1 /\ 0 < u2 <= 1 /\ In_order s2 s1 ls /\ p1 = point s1 u1 /\ p2 = point s2 u2)
  \/ (exists u1 u2 s, 0 < u1 <= 1 /\ 1 < u2 /\ In s ls /\ p1 = point s u1 /\ p2 = point (last_segment ls) u2)
  \/ (exists u1 u2, 1 < u1 /\ u2 <= 0 /\ p1 = point (last_segment ls) u1 /\ p2 = point (hd_segment ls) u2)
  \/ (exists u1 u2 s, 1 < u1 /\ 0 < u2 <= 1 /\ In s ls /\ p1 = point (last_segment ls) u1 /\ p2 = point s u2)
  \/ (exists u1 u2, 1 < u1 /\ 1 < u2 /\ u1 <> u2 /\ p1 = point (last_segment ls) u1 /\ p2 = point (last_segment ls) u2).
Proof.
  intros t1 t2 ls p1 p2 Hne Hneq.
  destruct (extend_repr ls t1 Hne) as [s1 [N1 E1]].
  destruct (extend_repr ls t2 Hne) as [s2 [N2 E2]].
  destruct (extend_param_region ls t1 Hne) as [M1 | [[H1 H1u] | [L1 L1u]]];
  destruct (extend_param_region ls t2 Hne) as [M2 | [[H2 H2u] | [L2 L2u]]].
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [I|I].
    + do 4 right; left. subst. assert (s1 = s2) by congruence. subst s2.
      exists (extend_param ls t1), (extend_param ls t2), s1.
      assert (U : extend_param ls t1 <> extend_param ls t2). {
        intro U. apply Hneq. eapply extend_same_piece_injective; eauto. }
      assert (Hin : In s1 ls). { apply nth_error_In in N1; exact N1. }
      tauto.
    + destruct (Nat.lt_ge_cases (extend_index ls t1) (extend_index ls t2)) as [LT|GE].
      * do 5 right; left. exists (extend_param ls t1), (extend_param ls t2), s1, s2.
        assert (O : In_order s1 s2 ls) by (eapply In_order_nth; eauto).
        tauto.
      * do 6 right; left. exists (extend_param ls t1), (extend_param ls t2), s1, s2.
        assert (O : In_order s2 s1 ls) by (eapply In_order_nth; eauto; lia).
        tauto.
  - do 3 right; left. assert (SH : s2 = hd_segment ls). { rewrite H2 in N2. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    subst s2. exists (extend_param ls t1), (extend_param ls t2), s1.
    assert (Hin : In s1 ls). { apply nth_error_In in N1; exact N1. } tauto.
  - do 7 right; left. assert (SL : s2 = last_segment ls). {
      unfold last_segment. assert (K : extend_index ls t2 = (length ls - 1)%nat) by lia.
      rewrite K in N2. pose proof (@nth_error_last Segment ls default_segment Hne) as Q.
      rewrite N2 in Q. injection Q as Q. exact Q. }
    subst s2. exists (extend_param ls t1), (extend_param ls t2), s1.
    assert (Hin : In s1 ls). { apply nth_error_In in N1; exact N1. } tauto.
  - right; left. assert (SH : s1 = hd_segment ls). { rewrite H1 in N1. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    subst s1. exists (extend_param ls t1), (extend_param ls t2), s2.
    assert (Hin : In s2 ls). { apply nth_error_In in N2; exact N2. } tauto.
  - left. assert (A : s1 = hd_segment ls). { rewrite H1 in N1. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    assert (B : s2 = hd_segment ls). { rewrite H2 in N2. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    subst s1; subst s2. exists (extend_param ls t1), (extend_param ls t2).
    assert (U : extend_param ls t1 <> extend_param ls t2). { intro U. apply Hneq. eapply extend_same_piece_injective; [apply Hne | rewrite H1, H2; reflexivity | exact U]. }
    tauto.
  - do 2 right; left. assert (A : s1 = hd_segment ls). { rewrite H1 in N1. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    assert (B : s2 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t2 = (length ls - 1)%nat) by lia.
      rewrite K in N2. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N2 in Q. injection Q as Q. exact Q. }
    subst s1; subst s2. exists (extend_param ls t1), (extend_param ls t2). repeat split; assumption.
  - do 9 right; left. assert (A : s1 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t1 = (length ls - 1)%nat) by lia.
      rewrite K in N1. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N1 in Q. injection Q as Q. exact Q. }
    subst s1. exists (extend_param ls t1), (extend_param ls t2), s2.
    assert (Hin : In s2 ls). { apply nth_error_In in N2; exact N2. } tauto.
  - do 8 right; left. assert (A : s1 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t1 = (length ls - 1)%nat) by lia.
      rewrite K in N1. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N1 in Q. injection Q as Q. exact Q. }
    assert (B : s2 = hd_segment ls). { rewrite H2 in N2. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    subst s1; subst s2. exists (extend_param ls t1), (extend_param ls t2). repeat split; assumption.
  - repeat right. assert (A : s1 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t1 = (length ls - 1)%nat) by lia.
      rewrite K in N1. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N1 in Q. injection Q as Q. exact Q. }
    assert (B : s2 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t2 = (length ls - 1)%nat) by lia.
      rewrite K in N2. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N2 in Q. injection Q as Q. exact Q. }
    subst s1; subst s2. exists (extend_param ls t1), (extend_param ls t2).
    assert (I : extend_index ls t1 = extend_index ls t2) by lia.
    assert (U : extend_param ls t1 <> extend_param ls t2). { intro U. apply Hneq. eapply extend_same_piece_injective; [apply Hne | exact I | exact U]. }
    tauto.
Qed.

(* 2つ以上離れたセグメントが１点を共有していれば，それらのセグメントを含む曲線は閉 *)
Lemma two_segs_have_same_point_close : forall s1 s2 p ls,
	onSegment s1 p
	-> onSegment s2 p
	-> (exists l1 l2 l3, ls = l1 ++ s1 :: l2 ++ s2 :: l3 /\ l2 <> [])  (* 逆順は不要 *)
	-> close ls.
Proof.
Admitted.

(* 先頭と末尾の延長線が交わっていたら，同じ延長線を持つ曲線は閉 *)
Lemma head_last_cross_close : forall p ls1 ls2,
	ls2 <> []
	-> onHead_extend ls1 p
	-> onLast_extend ls1 p
	-> same_extention_head ls1 ls2
	-> same_extention_last ls1 ls2
	-> close ls2.
Proof.
Admitted.

(* 先頭の延長線が先頭以外のセグメントと交わっていたら，同じ延長線とセグメントを持つ曲線は閉 *)
Lemma head_seg_cross_close : forall p seg ls1 ls2 n,
	onHead_extend ls1 p
	-> In seg ls1
	-> onSegment' seg p
	-> same_extention_head ls1 ls2
	-> nth_error ls2 n = Some seg
	-> (n > 0)%nat
	-> close ls2.
Proof.
Admitted.

(* 末尾の延長線が末尾以外のセグメントと交わっていたら，同じ延長線とセグメントを持つ曲線は閉 *)
Lemma last_seg_cross_close : forall p seg ls1 ls2 n,
	onLast_extend ls1 p
	-> In seg ls1
	-> onSegment' seg p
	-> same_extention_last ls1 ls2
	-> nth_error ls2 n = Some seg
	-> (n < length ls2 - 1)%nat
	-> close ls2.
Proof.
Admitted.

(* １つのセグメントの中（延長部分含め）で交差は起こらない（point の満たすべき性質，仕様） *)
Lemma one_seg_not_cross : forall t1 t2 seg,
	point seg t1 = point seg t2
	-> t1 = t2.
Proof.
	intros t1 t2 seg H. exact (point_injective seg t1 t2 H).
Qed.


(* 接続点での滑らかさを課さず、指定した外側の傾きを持つ連結2セグメントが存在する *)
Definition reconnect_slope_pair
	(p q : Point) (d1 d2 : Direction) (slope_p slope_q : R) : Prop :=
	exists middle slope_left slope_right,
		in_rect (rect_between p q) middle /\
		reconnect_slope p middle d1 slope_p slope_left /\
		reconnect_slope middle q d2 slope_right slope_q.

Axiom reconnect_slope_pair_spec :
  forall p q d1 d2 slope_p slope_q,
    reconnect_slope_pair p q d1 d2 slope_p slope_q <->
    exists s1 s2,
      embed_listDir [d1; d2] [s1; s2]
      /\ init s1 = p
      /\ term s2 = q
      /\ in_rect (rect_between p q) (term s1)
      /\ slope_init s1 = slope_p
      /\ slope_term s2 = slope_q.

Definition same_init_and_term (c1 c2 : list Segment) := 
	init (hd_segment c1) = init (hd_segment c2) 
	/\ term (last_segment c1) = term (last_segment c2).
Definition same_slope_init_and_term (c1 c2 : list Segment) := 
	slope_init (hd_segment c1) = slope_init (hd_segment c2) 
	/\ slope_term (last_segment c1) = slope_term (last_segment c2).

(* 始点と始点での傾きが同じであれば，始点方向への延長線は等しい（slope_init 等の満たすべき性質，仕様） *)
Lemma same_init_then_same_extention_head : forall ls1 ls2,
	let seg1 := hd_segment ls1 in
	let seg2 := hd_segment ls2 in
	init seg1 = init seg2
	-> slope_init seg1 = slope_init seg2
	-> same_extention_head ls1 ls2.
Proof. 
	intros ls1 ls2 Hinit Hslope p.
	unfold same_extention_head, onHead_extend.
	now apply head_extension_determined_by_init_slope.
Qed.

Lemma same_term_then_same_extention_last : forall ls1 ls2,
	let seg1 := last_segment ls1 in
	let seg2 := last_segment ls2 in
	term seg1 = term seg2
	-> slope_term seg1 = slope_term seg2
	-> same_extention_last ls1 ls2.
Proof. 
	intros ls1 ls2 Hterm Hslope p.
	unfold same_extention_last, onLast_extend.
	now apply last_extension_determined_by_term_slope.
Qed.


(* --------------------------------------------------------------------------- *)
(* 許容可能性保持の証明に向けた定義と補題群 *)

Lemma is_one_way_listDir_forall : forall ds,
	is_one_way_listDir ds <-> 
		(forall sc, scurve_to_direction sc = ds -> is_one_way_scurve sc).
Proof.
	intros ds. split.
	- (* -> *) intros [sc' [Hembed Honeway]] sc Hdir.
		eapply is_one_way_same_direction; [ | eassumption].
		congruence.
	- (* <- *) intros H. 
		destruct ds as [ | d ds'].
		+ (* このままでは contradiction にならないか *)
			specialize H with (exist _ [] IsScurveNil).
			unfold scurve_to_direction, is_one_way_scurve in H.
			specialize (H eq_refl).
			simpl in H; destruct H.
			contradiction. 
		+ pose proof (Direction_to_PrimitiveSegment d default_primitive_segment) as [p [Hp _]].
			subst.
			pose proof (direction_scurve_correspondence ds' p) as [sc [_ Hdir]].
			exists sc. split; auto.
Qed. 

Lemma P_is_oneway : is_one_way_listDir [Plus].
Proof. 
	exists (scurve_from_one (n,e,cx)). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. constructor; eauto.
Qed.

Lemma PM_is_oneway : is_one_way_listDir [Plus; Minus].
Proof. 
	set (p1 := scurve_from_one (n,e,cx)).
	set (p2 := scurve_from_one (n,e,cc)).
	eexists (exist _ [(n,e,cx); (n,e,cc)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. constructor; eauto.
	Unshelve. (* scurve であることの証明 *) 
	simpl. repeat constructor.
Qed.

Lemma PMP_is_oneway : is_one_way_listDir [Plus; Minus; Plus].
Proof.
	set (p1 := scurve_from_one (n,e,cx)).
	set (p2 := scurve_from_one (n,e,cc)).
	eexists (exist _ [(n,e,cx); (n,e,cc); (n,e,cx)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. repeat constructor; eauto.
	Unshelve. (* scurve であることの証明 *) 
	simpl. repeat constructor.
Qed.

Lemma PPMM_is_oneway : is_one_way_listDir [Plus; Plus; Minus; Minus].
Proof.
	set (p1 := scurve_from_one (n,e,cx)).
	set (p2 := scurve_from_one (s,e,cx)).
	set (p3 := scurve_from_one (s,e,cc)).
	set (p4 := scurve_from_one (n,e,cc)).
	eexists (exist _ [(n,e,cx); (s,e,cx); (s,e,cc); (n,e,cc)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. repeat constructor; eauto.
	Unshelve. (* scurve であることの証明 *)
	simpl. repeat constructor.
Qed.

(* [Plus] 系 is_oneway 補題を，全ての PrimitiveSegment の cx/cc を反転させることで
		[Minus] 系に写す（v は e 側では orn に無関係なので固定のままでよい） *)
Lemma M_is_oneway : is_one_way_listDir [Minus].
Proof.
	exists (scurve_from_one (n,e,cc)). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. constructor; eauto.
Qed.

Lemma MP_is_oneway : is_one_way_listDir [Minus; Plus].
Proof.
	set (p1 := scurve_from_one (n,e,cc)).
	set (p2 := scurve_from_one (n,e,cx)).
	eexists (exist _ [(n,e,cc); (n,e,cx)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. constructor; eauto.
	Unshelve. (* scurve であることの証明 *)
	simpl. repeat constructor.
Qed.

Lemma MPM_is_oneway : is_one_way_listDir [Minus; Plus; Minus].
Proof.
	set (p1 := scurve_from_one (n,e,cc)).
	set (p2 := scurve_from_one (n,e,cx)).
	eexists (exist _ [(n,e,cc); (n,e,cx); (n,e,cc)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. repeat constructor; eauto.
	Unshelve. (* scurve であることの証明 *)
	simpl. repeat constructor.
Qed.

(* PPMM 側は (n,e,cx);(s,e,cx);(s,e,cc);(n,e,cc) を dc で繋いでいた．
		v(=n/s) と c(=cx/cc) を同時に反転（h=e は固定）させると dc の各規則
		（DXtrvN <-> DXtrvS, DIfl は自己双対）はそのまま保たれ，かつ e 側では
		orn は c のみで決まる（cx -> Plus, cc -> Minus）ので，向きは Plus/Minus が
		入れ替わる．よって (s,e,cc);(n,e,cc);(n,e,cx);(s,e,cx) が MMPP の埋め込みになる． *)
Lemma MMPP_is_oneway : is_one_way_listDir [Minus; Minus; Plus; Plus].
Proof.
	set (p1 := scurve_from_one (s,e,cc)).
	set (p2 := scurve_from_one (n,e,cc)).
	set (p3 := scurve_from_one (n,e,cx)).
	set (p4 := scurve_from_one (s,e,cx)).
	eexists (exist _ [(s,e,cc); (n,e,cc); (n,e,cx); (s,e,cx)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. repeat constructor; eauto.
	Unshelve. (* scurve であることの証明 *)
	simpl. repeat constructor.
Qed.

Lemma embedding_oneway_listDir : forall ds ls,
	embed_listDir ds ls -> is_one_way_listDir ds -> is_one_way_embedding ls.
Proof.
	intros ds ls H1 H2.
	destruct H1 as [sc [Hdir Hembed]].
	exists sc. split; auto.
	apply (is_one_way_listDir_forall ds); auto.
Qed.

Lemma embedding_one_dir : forall d ls, 
	embed_listDir [d] ls -> exists seg, ls = [seg].
Proof. 
	intros d ls H. 
	apply embedding_listDir_length_consis in H.
	destruct ls as [ | x ls']; try discriminate.
	destruct ls'; try discriminate.
	repeat eexists.
Qed.

Lemma embedding_two_dir : forall d1 d2 ls, 
	embed_listDir [d1; d2] ls -> exists seg1 seg2, ls = [seg1; seg2].
Proof. 
	intros d1 d2 ls H. 
	apply embedding_listDir_length_consis in H.
	destruct ls as [ | x1 ls1]; try discriminate.
	destruct ls1 as [ | x2 ls2]; try discriminate.
	destruct ls2; try discriminate.
	repeat eexists.
Qed.

Lemma embedding_three_dir : forall d1 d2 d3 ls, 
	embed_listDir [d1; d2; d3] ls -> exists seg1 seg2 seg3, ls = [seg1; seg2; seg3].
Proof. 
	intros d1 d2 d3 ls H. 
	apply embedding_listDir_length_consis in H.
	destruct ls as [ | x1 ls1]; try discriminate.
	destruct ls1 as [ | x2 ls2]; try discriminate.
	destruct ls2 as [ | x3 ls3]; try discriminate.
	destruct ls3; try discriminate.
	repeat eexists.
Qed.

Lemma embedding_four_dir : forall d1 d2 d3 d4 ls, 
	embed_listDir [d1; d2; d3; d4] ls -> exists seg1 seg2 seg3 seg4, ls = [seg1; seg2; seg3; seg4].
Proof.
	intros d1 d2 d3 d4 ls H. 
	apply embedding_listDir_length_consis in H.
	destruct ls as [ | x1 ls1]; try discriminate.
	destruct ls1 as [ | x2 ls2]; try discriminate.
	destruct ls2 as [ | x3 ls3]; try discriminate.
	destruct ls3 as [ | x4 ls4]; try discriminate.
	destruct ls4; try discriminate.
	repeat eexists.
Qed.

(* 単方向曲線は開 *)
Lemma oneway_then_open : forall ls, 
	is_one_way_embedding ls -> ~ close ls.
Proof.
Admitted.

(* sub_ls 周りで疎な埋め込みについて， sub_ls を矩形の中で sub_ls' に変えても疎なまま *)
(* Lemma sparse_in_rect_change : forall (ls rs sub_ls sub_ls' : list Segment), 
	sparse ls sub_ls rs
	-> (forall rr, onSegmentlist sub_ls' rr -> in_rect sub_ls rr) 
	-> same_init_and_term sub_ls sub_ls' 
	-> same_slope_init_and_term sub_ls sub_ls'
	-> sparse ls sub_ls' rs.
Proof. 
Qed. *)


(* embed_sparsely_listDir を強めたもの．PMP 部分の両端と端点傾きから，
		それらを保存する Plus セグメントを構成できるように埋め込める． *)
(* TODO：embed_sparsely_listDir に統合しても良い *)
Lemma embed_sparsely_listDir_PMP (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Plus; Minus; Plus] ++ ds2)
	-> exists l r seg1 seg2 seg3,
		reconnect_slope (init seg1) (term seg3) Plus
			(slope_init seg1) (slope_term seg3) (* 将来的にこの部分を，傾きを保存したまま１つのセグメントに変更できるように *)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Plus; Minus; Plus] ++ ds2) (l ++ [seg1; seg2; seg3] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3] ++ r)
		/\ sparse l [seg1; seg2; seg3] r.
Proof. Admitted.

(* embed_sparsely_listDir_PMP の Minus 版． *)
Lemma embed_sparsely_listDir_MPM (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Minus; Plus; Minus] ++ ds2)
	-> exists l r seg1 seg2 seg3,
		reconnect_slope (init seg1) (term seg3) Minus
			(slope_init seg1) (slope_term seg3) (* 将来的にこの部分を，傾きを保存したまま１つのセグメントに変更できるように *)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Minus; Plus; Minus] ++ ds2) (l ++ [seg1; seg2; seg3] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3] ++ r)
		/\ sparse l [seg1; seg2; seg3] r.
Proof. Admitted.

Lemma embed_sparsely_listDir_PPMM (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2)
	-> exists l r seg1 seg2 seg3 seg4, 
		reconnect_slope_pair (init seg1) (term seg4) Plus Minus
			(slope_init seg1) (slope_term seg4) (* 将来的にこの部分を，傾きを保存したまま２つのセグメントに変更できるように *)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Plus; Plus; Minus; Minus] [seg1; seg2; seg3; seg4]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2) (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ sparse l [seg1; seg2; seg3; seg4] r.
Proof. Admitted.

(* embed_sparsely_listDir_PPMM の Minus 版． *)
Lemma embed_sparsely_listDir_MMPP (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2)
	-> exists l r seg1 seg2 seg3 seg4,
		reconnect_slope_pair (init seg1) (term seg4) Minus Plus
			(slope_init seg1) (slope_term seg4) (* 将来的にこの部分を，傾きを保存したまま２つのセグメントに変更できるように *)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Minus; Minus; Plus; Plus] [seg1; seg2; seg3; seg4]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2) (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ sparse l [seg1; seg2; seg3; seg4] r.
Proof. Admitted.

(* Plus (の向きを持つ Primitive Segment) の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Minus; Plus] の埋め込みとなる３つに矩形内で分割できる *)
Lemma embedding_P_to_PMP_in_rect : forall (seg : Segment),
	embed_listDir [Plus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ in_rect_or_endpoints [seg] [seg1; seg2; seg3]
		/\ same_init_and_term [seg] [seg1; seg2; seg3]
		/\ same_slope_init_and_term [seg] [seg1; seg2; seg3].
Proof. 
	(* seg1, seg3 は十分小さくとり， seg1 の終点の傾きは 0 に， seg3 の始点の傾きは
		無限大あるいは十分大きくとる．その後端点を結ぶように seg2 をとる．
		具体的には，seg3 の始点が seg1 の終点より右上にあり，
		seg3 の始点での傾きが seg1 の終点での傾きより大きくなるようにすれば良い． *)
Admitted.

(* embedding_P_to_PMP_in_rect の Minus 版 *)
Lemma embedding_M_to_MPM_in_rect : forall (seg : Segment),
	embed_listDir [Minus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
		/\ in_rect_or_endpoints [seg] [seg1; seg2; seg3]
		/\ same_init_and_term [seg] [seg1; seg2; seg3]
		/\ same_slope_init_and_term [seg] [seg1; seg2; seg3].
Proof. Admitted.

(* [Plus; Minus] の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Plus; Minus; Minus] の埋め込みとなる4つに矩形内で分割できる *)
Lemma embedding_PM_to_PPMM_in_rect : forall (seg1 seg2 : Segment),
	embed_listDir [Plus; Minus] [seg1; seg2]
	-> exists seg1' seg2' seg3' seg4',
		embed_listDir [Plus; Plus; Minus; Minus] [seg1'; seg2'; seg3'; seg4'] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ in_rect_or_endpoints [seg1; seg2] [seg1'; seg2'; seg3'; seg4'] (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_slope_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4'].
Proof. Admitted.

(* embedding_PM_to_PPMM_in_rect の Minus 版 *)
Lemma embedding_MP_to_MMPP_in_rect : forall (seg1 seg2 : Segment),
	embed_listDir [Minus; Plus] [seg1; seg2]
	-> exists seg1' seg2' seg3' seg4',
		embed_listDir [Minus; Minus; Plus; Plus] [seg1'; seg2'; seg3'; seg4']
		/\ in_rect_or_endpoints [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_slope_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4'].
Proof. Admitted.

(* 両端で指定された傾きを実現できるなら，PMP の埋め込みを，端点と傾きを
		保存したまま矩形内の Plus の埋め込みに変更できる． *)
(* TODO : もう少し一般化しても良いかもしれない *)
Lemma embedding_PMP_to_P_in_rect : forall (seg1 seg2 seg3 : Segment),
	reconnect_slope (init seg1) (term seg3) Plus
		(slope_init seg1) (slope_term seg3)
	-> embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
	->
	exists seg,
		embed_listDir [Plus] [seg]
		/\ in_rect_or_endpoints [seg1; seg2; seg3] [seg]
		/\ same_init_and_term [seg1; seg2; seg3] [seg]
		/\ same_slope_init_and_term [seg1; seg2; seg3] [seg].
Proof.
	(* reconnect_slope_* が保証する両端の条件を同時に満たす Plus の埋め込みを取る． *)
Admitted.

(* embedding_PMP_to_P_in_rect の Minus 版． *)
Lemma embedding_MPM_to_M_in_rect : forall (seg1 seg2 seg3 : Segment),
	reconnect_slope (init seg1) (term seg3) Minus
		(slope_init seg1) (slope_term seg3)
	-> embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
	->
	exists seg,
		embed_listDir [Minus] [seg]
		/\ in_rect_or_endpoints [seg1; seg2; seg3] [seg]
		/\ same_init_and_term [seg1; seg2; seg3] [seg]
		/\ same_slope_init_and_term [seg1; seg2; seg3] [seg].
Proof. Admitted.

(* PP と MM の各部分について両端点・両端傾きを同時に実現できるなら，
		それらを矩形内の Plus，Minus セグメントへそれぞれ縮約できる． *)
Lemma embedding_PPMM_to_PM_in_rect : forall (seg1 seg2 seg3 seg4 : Segment),
	reconnect_slope_pair (init seg1) (term seg4) Plus Minus
		(slope_init seg1) (slope_term seg4)
	-> embed_listDir [Plus; Plus; Minus; Minus] [seg1; seg2; seg3; seg4]
	->
	exists seg1' seg2',
		embed_listDir [Plus; Minus] [seg1'; seg2'] 
		/\ in_rect_or_endpoints [seg1; seg2; seg3; seg4] [seg1'; seg2'] (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_slope_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2'].
Proof.
	(* 始点から中心へ，終点から中心へそれぞれ Plus, Minus の埋め込みをとり，繋げれば良さそう *)
Admitted.

(* embedding_PPMM_to_PM_in_rect の Minus 版． *)
Lemma embedding_MMPP_to_MP_in_rect : forall (seg1 seg2 seg3 seg4 : Segment),
	reconnect_slope_pair (init seg1) (term seg4) Minus Plus
		(slope_init seg1) (slope_term seg4)
	-> embed_listDir [Minus; Minus; Plus; Plus] [seg1; seg2; seg3; seg4]
	->
	exists seg1' seg2',
		embed_listDir [Minus; Plus] [seg1'; seg2']
		/\ in_rect_or_endpoints [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_slope_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2'].
Proof. Admitted.

(*  向き ds1 ++ ds2 ++ ds3 の ds2 (の向きを持つ scurve) の埋め込みを，端点の条件を満たしつつ
		ds2' の埋め込みに変えたら，向き ds1 ++ ds2' ++ ds3 の埋め込みである *)
(* TODO: 向き列を交えず scurve だけでいけばコンパクトに，もし hd_scurve 取れればきれい？ *)
Lemma embbeding_inner_change : forall sc1 sc2 ds1 ds2 ds2' ds3 ls1 ls2 ls2' ls3,
	ls2 <> []
	-> ls2' <> []
	-> embed_scurve sc1 (ls1 ++ ls2 ++ ls3) (* つまり ls1, ls2, ls3 は繋がっている *)
	-> embed_listDir ds2 ls2
	-> embed_listDir ds2' ls2'
	-> same_init_and_term ls2 ls2'
	-> scurve_to_direction sc1 = ds1 ++ ds2 ++ ds3
	-> scurve_to_direction sc2 = ds1 ++ ds2' ++ ds3
	-> hd_scurve sc1 = hd_scurve sc2
	-> embed_scurve sc2 (ls1 ++ ls2' ++ ls3).
Proof. 
	intros sc1 sc2 ds1 ds2 ds2' ds3 ls1 ls2 ls2' ls3.
	intros Hls2 Hls2' Hembed Hembed_dir1 Hembed_dir2 Hinit_term Hdir1 Hdir2 Hhead.
Admitted.

(* 【証明の本質としている補題２】 sub_ls の周りが疎な開埋め込みにおいて，端点で傾きを保ちつつ
		sub_ls をその領域に収まる開な sub_ls' に置き換えても開のまま *)
(* TODO : もうちょっと自動化できるはず．．． *)
(* TODO : 隣接セグメントが交わらないことを使い，内部で場合分けを増やす必要がある *)
Lemma seg_in_rectangle_keep_openness : forall (ls rs sub_ls sub_ls' : list Segment),
	sub_ls <> []
	-> sub_ls' <> [] 
	-> ~ close sub_ls'
	-> ~ close (ls ++ sub_ls ++ rs)
	-> sparse ls sub_ls rs
	-> in_rect_or_endpoints sub_ls sub_ls'
	-> same_init_and_term sub_ls sub_ls'
	-> same_slope_init_and_term sub_ls sub_ls'
	-> ~ close (ls ++ sub_ls' ++ rs).
(* strict 延長線と非隣接セグメントの端点込み分離により、置換後の
   sub が旧 sub の端点長方形内にある限り新しい自己交差は生じない。 *)
Admitted.


(* --------------------------------------------------------------------------- *)
(* 許容可能性保持に関する主張８つと，その系 *)

(* [+-+ => +] での簡約で，簡約元が許容可能なら簡約先も許容可能 *)
Lemma AdmissibleDirs_r1_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Plus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_PMP _ _ admds) as H.
	destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [Hcan [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]]]]];
	simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		pose proof (embedding_PMP_to_P_in_rect seg1 seg2 seg3 Hcan Hls2) as [segP [HP [Hin_rect [Hinit_term Hsame_slope]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [segP] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus; Minus; Plus] [Plus] r ls1 [seg1; seg2; seg3] [segP] ls3); 
				try assumption; try discriminate.
			(* 仮定を満たすことはほぼ作業的に示せる *)
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2; seg3] [segP]); 
				try assumption; try (symmetry; assumption); try congruence.
			(* 残った subgoal もほぼ自明 *)
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus]); try assumption.
				apply P_is_oneway.
Qed.

Lemma AdmissibleDirs_r1_Minus: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r) -> AdmissibleDirs (l ++ [Minus] ++ r).
Proof.
	intros l r admds.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_MPM _ _ admds) as H.
	destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [Hcan [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]]]]];
	simpl in *.
	assert (Hdir: hd Minus (l ++ Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Minus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		pose proof (embedding_MPM_to_M_in_rect seg1 seg2 seg3 Hcan Hls2) as [segM [HM [Hin_rect [Hinit_term Hsame_slope]]]].
		(* 欲しかった埋め込み *)
		exists (ls1 ++ [segM] ++ ls3).
		unfold admissible.
		split.
		+ (* 埋め込みになっていること *)
			apply (embbeding_inner_change sc sc' l [Minus; Plus; Minus] [Minus] r ls1 [seg1; seg2; seg3] [segM] ls3);
				try assumption; try discriminate.
			(* 仮定を満たすことはほぼ作業的に示せる *)
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *)
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2; seg3] [segM]);
				try assumption; try (symmetry; assumption); try congruence;
				try (apply in_rect_implies_or_endpoints; assumption).
			(* 残った subgoal もほぼ自明 *)
			* apply oneway_then_open. apply (embedding_oneway_listDir [Minus]); try assumption.
				apply M_is_oneway.
Qed.

(* [+-+ => +] での簡約で，簡約先が許容可能ならもともと許容可能 *)
Lemma AdmissibleDirs_r1_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds P_is_oneway) 
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
	simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: Minus :: Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}	
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Minus :: Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Plus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_one_dir Plus ls2 Hls2) as [segP HP]; subst.
		pose proof (embedding_P_to_PMP_in_rect segP Hls2) 
			as [seg1 [seg2 [seg3 [HPMP [Hin_rect [Hinit_term Hslope]]]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [seg1; seg2; seg3] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus] [Plus; Minus; Plus] r ls1 [segP] [seg1; seg2; seg3] ls3); 
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [segP] _ ); try assumption; try congruence;
				try (apply in_rect_implies_or_endpoints; assumption).
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Minus; Plus]); try assumption.
				apply PMP_is_oneway.
Qed.

Lemma AdmissibleDirs_r1_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r).
Proof.
	intros l r admds.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds M_is_oneway)
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
	simpl in *.
	assert (Hdir: hd Minus (l ++ Minus :: Plus :: Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Minus :: Plus :: Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Minus; Plus; Minus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Minus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_one_dir Minus ls2 Hls2) as [segM HM]; subst.
		pose proof (embedding_M_to_MPM_in_rect segM Hls2)
			as [seg1 [seg2 [seg3 [HMPM [Hin_rect [Hinit_term Hslope]]]]]].
		(* 欲しかった埋め込み *)
		exists (ls1 ++ [seg1; seg2; seg3] ++ ls3).
		unfold admissible.
		split.
		+ (* 埋め込みになっていること *)
			apply (embbeding_inner_change sc sc' l [Minus] [Minus; Plus; Minus] r ls1 [segM] [seg1; seg2; seg3] ls3);
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *)
			apply (seg_in_rectangle_keep_openness _ _ [segM] _ ); try assumption; try congruence;
				try (apply in_rect_implies_or_endpoints; assumption).
			* apply oneway_then_open. apply (embedding_oneway_listDir [Minus; Plus; Minus]); try assumption.
				apply MPM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_PPMM _ _ admds) as H.
	destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [seg4 [Hcan [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]]]]]];
	simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		pose proof (embedding_PPMM_to_PM_in_rect seg1 seg2 seg3 seg4 Hcan Hls2)
			as [seg1' [seg2' [HPM [Hin_rect [Hinit_term Hslope]]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [seg1'; seg2'] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus; Plus; Minus; Minus] [Plus; Minus] r ls1 [seg1; seg2; seg3; seg4] [seg1'; seg2'] ls3); 
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2; seg3; seg4] [seg1'; seg2']); 
				try assumption; try (symmetry; assumption); try congruence;
				try (apply in_rect_implies_or_endpoints; assumption).
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Minus]); try assumption.
			apply PM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Minus: forall l r,
  AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus] ++ r).
Proof.
	intros l r admds.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_MMPP _ _ admds) as H.
	destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [seg4 [Hcan [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]]]]]];
	simpl in *.
	assert (Hdir: hd Minus (l ++ Minus :: Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Minus :: Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		pose proof (embedding_MMPP_to_MP_in_rect seg1 seg2 seg3 seg4 Hcan Hls2)
			as [seg1' [seg2' [HMP [Hin_rect [Hinit_term Hslope]]]]].
		(* 欲しかった埋め込み *)
		exists (ls1 ++ [seg1'; seg2'] ++ ls3).
		unfold admissible.
		split.
		+ (* 埋め込みになっていること *)
			apply (embbeding_inner_change sc sc' l [Minus; Minus; Plus; Plus] [Minus; Plus] r ls1 [seg1; seg2; seg3; seg4] [seg1'; seg2'] ls3);
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *)
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2; seg3; seg4] [seg1'; seg2']);
				try assumption; try (symmetry; assumption); try congruence;
				try (apply in_rect_implies_or_endpoints; assumption).
			* apply oneway_then_open. apply (embedding_oneway_listDir [Minus; Plus]); try assumption.
			apply MP_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds PM_is_oneway) 
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
	simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: Plus :: Minus :: Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}	
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Plus :: Minus :: Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Plus; Minus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_two_dir Plus Minus ls2 Hls2) as [seg1 [seg2 HPM]]; subst.
		pose proof (embedding_PM_to_PPMM_in_rect _ _ Hls2) 
			as [seg1' [seg2' [seg3' [seg4' [HPPMM [Hin_rect [Hinit_term Hslope]]]]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [seg1'; seg2'; seg3'; seg4'] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus; Minus] [Plus; Plus; Minus; Minus] r ls1 [seg1; seg2] [seg1'; seg2'; seg3'; seg4'] ls3); 
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2] _ ); try assumption; try congruence;
				try (apply in_rect_implies_or_endpoints; assumption).
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Plus; Minus; Minus]); try assumption.
				apply PPMM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r).
Proof.
	intros l r admds.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds MP_is_oneway)
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
	simpl in *.
	assert (Hdir: hd Minus (l ++ Minus :: Minus :: Plus :: Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Minus :: Minus :: Plus :: Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Minus; Plus; Minus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Minus; Plus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_two_dir Minus Plus ls2 Hls2) as [seg1 [seg2 HMP]]; subst.
		pose proof (embedding_MP_to_MMPP_in_rect _ _ Hls2)
			as [seg1' [seg2' [seg3' [seg4' [HMMPP [Hin_rect [Hinit_term Hslope]]]]]]].
		(* 欲しかった埋め込み *)
		exists (ls1 ++ [seg1'; seg2'; seg3'; seg4'] ++ ls3).
		unfold admissible.
		split.
		+ (* 埋め込みになっていること *)
			apply (embbeding_inner_change sc sc' l [Minus; Plus] [Minus; Minus; Plus; Plus] r ls1 [seg1; seg2] [seg1'; seg2'; seg3'; seg4'] ls3);
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *)
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2] _ ); try assumption; try congruence;
				try (apply in_rect_implies_or_endpoints; assumption).
			* apply oneway_then_open. apply (embedding_oneway_listDir [Minus; Minus; Plus; Plus]); try assumption.
				apply MMPP_is_oneway.
Qed.

Lemma AdmissibleDirs_preserve_Rule : forall l ds ds' r,
  Rule ds ds' 
	-> (AdmissibleDirs (l ++ ds ++ r) <-> AdmissibleDirs (l ++ ds' ++ r)).
Proof.
	intros l ds ds' r Hrule. inversion Hrule as [ HPMP HP | HMPM HM | HPPMM HPM | HMMPP HMP ]; subst. 
	- (* +-+ -> + *) split. apply AdmissibleDirs_r1_Plus. apply AdmissibleDirs_r1_Plus_inv.
	- (* -+- -> - *) split. apply AdmissibleDirs_r1_Minus. apply AdmissibleDirs_r1_Minus_inv.
	- (* ++-- -> +- *) split. apply AdmissibleDirs_r2_Plus. apply AdmissibleDirs_r2_Plus_inv.
	- (* --++ -> -+ *) split. apply AdmissibleDirs_r2_Minus. apply AdmissibleDirs_r2_Minus_inv.
Qed.

Lemma AdmissibleDirs_preserve_Step : forall ds ds',
	ReduceDirStep ds ds' 
	-> (AdmissibleDirs ds <-> AdmissibleDirs ds').
Proof.
  intros ds ds' Hstep.
  inversion Hstep ; subst.
  apply AdmissibleDirs_preserve_Rule. auto.
Qed.

Corollary AdmissibleDirs_preserve  : forall ds ds',
	ReduceDir ds ds' 
	-> (AdmissibleDirs ds <-> AdmissibleDirs ds').
Proof.
  intros ds ds' Hreduce.
  induction Hreduce.
  - (* RDRefl: ds = ds なので自明 *)
    reflexivity.
  - (* RDTrans: ds -> ds' -> ds'' の場合 *)
    apply (@iff_trans _ (AdmissibleDirs ds') _); try assumption.
		apply AdmissibleDirs_preserve_Step. assumption.
Qed.

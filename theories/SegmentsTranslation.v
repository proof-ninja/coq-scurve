Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Segment.
Require Import PrimitiveSegment.
Require Import Reduction.
Require Import Embed.
Require Import Admissible.
Import ListNotations.
Open Scope R_scope.


(* ================================================================= *)
(*  セグメントの幾何変換と端点指定                                   *)
(* ================================================================= *)

Definition hd_segment (ls : list Segment) := hd default_segment ls.
Definition last_segment (ls : list Segment) := last ls default_segment.

Definition onHead_extend (ls : list Segment) (p : Point) :=
  onHead (hd_segment ls) p.

Definition onLast_extend (ls : list Segment) (p : Point) :=
  onLast (last_segment ls) p.

Definition same_extention_head (ls1 ls2 : list Segment) :=
  forall p, onHead_extend ls1 p <-> onHead_extend ls2 p.

Definition same_extention_last (ls1 ls2 : list Segment) :=
  forall p, onLast_extend ls1 p <-> onLast_extend ls2 p.

Definition x_monotone_seg (s : Segment) : Prop := init_x s < term_x s.

Definition x_monotone_segs (ls : list Segment) : Prop :=
  forall s, In s ls -> x_monotone_seg s.

Definition embed_listDir (ds : list Direction) (ls : list Segment) : Prop :=
  exists sc : scurve,
    scurve_to_direction sc = ds /\ embed_scurve sc ls.

Definition is_one_way_embedding (ls : list Segment) : Prop :=
  exists sc, embed_scurve sc ls /\ is_one_way_scurve sc.

Definition is_one_way_listDir (ds : list Direction) : Prop :=
  exists sc : scurve,
    scurve_to_direction sc = ds /\ is_one_way_scurve sc.


(* ----------------------------------------------------------------- *)
(*  90 度単位の回転                                                   *)
(* ----------------------------------------------------------------- *)

Inductive Rot : Type := R0 | R90 | R180 | R270.

Definition rot_pt (g : Rot) (p : Point) : Point :=
  match g with
  | R0   => p
  | R90  => (- snd p, fst p)
  | R180 => (- fst p, - snd p)
  | R270 => (snd p, - fst p)
  end.

Definition rot_inv (g : Rot) : Rot :=
  match g with R0 => R0 | R90 => R270 | R180 => R180 | R270 => R90 end.

Lemma rot_inv_inv : forall g, rot_inv (rot_inv g) = g.
Proof. destruct g; reflexivity. Qed.

Lemma rot_pt_inv : forall g p, rot_pt (rot_inv g) (rot_pt g p) = p.
Proof.
  intros g [x y]; destruct g; simpl; f_equal; ring.
Qed.

Parameter rot_seg : Rot -> Segment -> Segment.

(* 回転したセグメントは、各パラメータ点を同じだけ回転したもの。 *)
Axiom rot_seg_point :
  forall g s t, point (rot_seg g s) t = rot_pt g (point s t).

(* 90 度単位の回転はセグメントの Direction を保つ。 *)
Axiom rot_seg_orn :
  forall g s, orn_seg (rot_seg g s) = orn_seg s.

(* 逆回転により元のセグメントへ戻る。 *)
Axiom rot_inv_seg :
  forall g s, rot_seg (rot_inv g) (rot_seg g s) = s.

Lemma rot_seg_inv :
  forall g s, rot_seg g (rot_seg (rot_inv g) s) = s.
Proof.
  intros g s.
  pose proof (rot_inv_seg (rot_inv g) s) as H.
  now rewrite rot_inv_inv in H.
Qed.

Lemma rot_seg_init :
  forall g s, init (rot_seg g s) = rot_pt g (init s).
Proof. intros g s. unfold init. apply rot_seg_point. Qed.

Lemma rot_seg_term :
  forall g s, term (rot_seg g s) = rot_pt g (term s).
Proof. intros g s. unfold term. apply rot_seg_point. Qed.

Definition rot_segs (g : Rot) (ls : list Segment) : list Segment :=
  map (rot_seg g) ls.

Lemma rot_inv_segs : forall g ls, rot_segs (rot_inv g) (rot_segs g ls) = ls.
Proof.
  intros g ls. induction ls as [|s ls IH]; simpl; [reflexivity |].
  rewrite rot_inv_seg, IH. reflexivity.
Qed.

Lemma rot_segs_inv : forall g ls, rot_segs g (rot_segs (rot_inv g) ls) = ls.
Proof.
  intros g ls. induction ls as [|s ls IH]; simpl; [reflexivity |].
  rewrite rot_seg_inv, IH. reflexivity.
Qed.

Lemma rot_segs_app :
  forall g ls1 ls2, rot_segs g (ls1 ++ ls2) = rot_segs g ls1 ++ rot_segs g ls2.
Proof. intros. unfold rot_segs. apply map_app. Qed.

Lemma rot_segs_nonnil : forall g ls, ls <> [] -> rot_segs g ls <> [].
Proof.
  intros g [|s ls] H; [contradiction | discriminate].
Qed.

Lemma onSegment_rot :
  forall g s p, onSegment s p -> onSegment (rot_seg g s) (rot_pt g p).
Proof.
  intros g s p [t [Ht Hp]]. exists t. split; [exact Ht |].
  now rewrite rot_seg_point, Hp.
Qed.

Lemma onHead_rot :
  forall g s p, onHead s p -> onHead (rot_seg g s) (rot_pt g p).
Proof.
  intros g s p [t [Ht Hp]]. exists t. split; [exact Ht |].
  now rewrite rot_seg_point, Hp.
Qed.

Lemma onLast_rot :
  forall g s p, onLast s p -> onLast (rot_seg g s) (rot_pt g p).
Proof.
  intros g s p [t [Ht Hp]]. exists t. split; [exact Ht |].
  now rewrite rot_seg_point, Hp.
Qed.

Lemma app_nonnil_mid :
  forall (l sub r : list Segment), sub <> [] -> l ++ sub ++ r <> [].
Proof.
  intros l sub r H. destruct l as [|a l']; simpl.
  - destruct sub as [|s sub']; [contradiction | discriminate].
  - discriminate.
Qed.

(* ----------------------------------------------------------------- *)
(*  scurve（PrimitiveSegment 列）レベルでの回転                       *)
(* ----------------------------------------------------------------- *)

Definition rot_scurve (g : Rot) (sc : scurve) : scurve.
Admitted. (*TODO*)

(** 回転は向き（Plus/Minus）の列を変えない。 *)
Lemma rot_scurve_direction : forall g sc,
  scurve_to_direction (rot_scurve g sc) = scurve_to_direction sc.
Admitted.

Axiom rot_scurve_embed : forall g sc ls,
  embed_scurve sc ls <-> embed_scurve (rot_scurve g sc) (rot_segs g ls).

(* 回転はセグメント列が同じ向き列を埋め込むという性質を保存する。 *)
Lemma rot_embed :
  forall g ds ls, embed_listDir ds ls -> embed_listDir ds (rot_segs g ls).
Proof.
  intros g ds ls [sc [Hdir Hembed]].
  exists (rot_scurve g sc). split.
  - rewrite rot_scurve_direction. exact Hdir.
  - apply (rot_scurve_embed g sc ls). exact Hembed.
Qed.

(* 回転後に自己交差があれば、逆回転により元の列にも自己交差がある。 *)
Lemma rot_close :
  forall g ls, close (rot_segs g ls) -> close ls.
Admitted.

Lemma rot_open :
  forall g ls, ~ close ls -> ~ close (rot_segs g ls).
Proof. intros g ls H Hc. apply H. now apply (rot_close g). Qed.

Lemma rot_scurve_admissible : forall g sc,
  admissible sc <-> admissible (rot_scurve g sc).
Proof.
  intros g sc. split.
  - intros [ls [Hembed Hopen]]. exists (rot_segs g ls). split.
    + apply (rot_scurve_embed g sc ls). exact Hembed.
    + intros Hclose. apply Hopen. apply (rot_close g ls). exact Hclose.
  - intros [ls' [Hembed Hopen]]. exists (rot_segs (rot_inv g) ls'). split.
    + apply (rot_scurve_embed g sc (rot_segs (rot_inv g) ls')).
      rewrite rot_segs_inv. exact Hembed.
    + intros Hclose. apply Hopen. apply (rot_close (rot_inv g) ls'). exact Hclose.
Qed.

(** 向き列（Plus/Minus の列）が一致する2つの scurve は，一方をもう一方の
   回転として得られる。 *)
Lemma rot_scurve_of_same_direction :
  forall sc ps,
    scurve_to_direction sc = scurve_to_direction ps ->
    exists g, ps = rot_scurve g sc.
Admitted.

(* 単方向な埋め込みは、90 度単位の回転で x 正方向へ単調にできる。 *)
Lemma one_way_rot_exists :
  forall ls, is_one_way_embedding ls ->
    exists g : Rot, x_monotone_segs (rot_segs g ls).
Admitted.

Lemma x_monotone_embed_is_one_way_listDir :
  forall ds ls,
    embed_listDir ds ls ->
    x_monotone_segs ls ->
    is_one_way_listDir ds.
Admitted.


(* ----------------------------------------------------------------- *)
(*  単一セグメントの平行移動                                         *)
(* ----------------------------------------------------------------- *)

Definition translate_pt (v p : Point) : Point :=
  (fst p + fst v, snd p + snd v).

Definition opposite_translation (v : Point) : Point :=
  (- fst v, - snd v).

Parameter translate_seg : (R * R) -> Segment -> Segment.

(* 平行移動したセグメントの各点は、元の点を同じベクトルだけ移したもの。 *)
Axiom translate_seg_point :
  forall v s t, point (translate_seg v s) t = translate_pt v (point s t).

(* 平行移動はセグメントの向きを変えない。 *)
Axiom translate_seg_orn :
  forall v s, orn_seg (translate_seg v s) = orn_seg s.

(* 平行移動は両端で指定される延長線の傾きを変えない。 *)
Axiom translate_seg_slope_init :
  forall v s, slope_init (translate_seg v s) = slope_init s.

Axiom translate_seg_slope_term :
  forall v s, slope_term (translate_seg v s) = slope_term s.

(* 逆向きの平行移動により元のセグメントへ戻る。 *)
Axiom translate_seg_inverse :
  forall v s, translate_seg (opposite_translation v) (translate_seg v s) = s.

Lemma translate_seg_init :
  forall v s, init (translate_seg v s) = translate_pt v (init s).
Proof. intros v s. unfold init. apply translate_seg_point. Qed.

Lemma translate_seg_term :
  forall v s, term (translate_seg v s) = translate_pt v (term s).
Proof. intros v s. unfold term. apply translate_seg_point. Qed.

Lemma onSegment_translate :
  forall v s p,
    onSegment s p -> onSegment (translate_seg v s) (translate_pt v p).
Proof.
  intros v s p [t [Ht Hp]]. exists t. split; [exact Ht |].
  now rewrite translate_seg_point, Hp.
Qed.

Lemma onHead_translate :
  forall v s p,
    onHead s p -> onHead (translate_seg v s) (translate_pt v p).
Proof.
  intros v s p [t [Ht Hp]]. exists t. split; [exact Ht |].
  now rewrite translate_seg_point, Hp.
Qed.

Lemma onLast_translate :
  forall v s p,
    onLast s p -> onLast (translate_seg v s) (translate_pt v p).
Proof.
  intros v s p [t [Ht Hp]]. exists t. split; [exact Ht |].
  now rewrite translate_seg_point, Hp.
Qed.

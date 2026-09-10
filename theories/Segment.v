Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import PrimitiveSegment.
Require Import Reduction.
Require Import Stdlib.Reals.Ranalysis1.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.
Import ListNotations.

(*セグメントは[0,1]->R*Rの関数
埋め込み関係は次の条件を満たしたもの
・[0,1]で微分可能
・1要素目，2要素目の関数において，[0,1]で勾配の正負が一定．
・dy/dxが微分可能
・[0,1]において凸性が変わらない
    <=> forall t \in [0,1], d2y/dx2 = d/dt(dy/dx) * (dx/dt)の正負が一定
    <=> forall t \in [0,1], d2y/dx2 = d/dt(dy/dx)の正負が一定*)

(* R*Rの微分 *)
(* Definition derivable_pair_pt (f : R -> R * R) (t : R) : Set :=
  derivable_pt (fun t1 => fst (f t1)) t * derivable_pt (fun t1 => snd (f t1)) t.

Definition derivable_pair (f : R -> R * R) : Set :=
  forall t : R, derivable_pair_pt f t.

Definition derive_pair_fst (f : R -> R * R) (pr : derivable_pair f) (x : R) : R :=
  derive_pt (fun t => fst (f t)) x (fst (pr x)).
Definition derive_pair_snd (f : R -> R * R) (pr : derivable_pair f) (x : R) : R :=
  derive_pt (fun t => snd (f t)) x (snd (pr x)).

Definition derivable_dydx_pt (f : R -> R * R) (t : R) (pr : derivable_pair f): Set :=
  derivable_pt (fun t1 => (derive_pair_snd f pr t1) / (derive_pair_fst f pr t1)) t.

Definition derivable_dydx (f : R -> R * R) (pr : derivable_pair f): Set :=
  forall t: R, derivable_dydx_pt f t pr. *)


Definition Point := (R * R)%type.

Parameter Segment : Type.
Parameter point : Segment -> R -> Point.
Parameter default_segment : Segment.

Definition init (seg: Segment) : R * R := point seg 0.

Definition term (seg: Segment) : R * R := point seg 1.

Definition init_x (s: Segment) : R := fst (init s).
Definition init_y (s: Segment) : R := snd (init s).
Definition term_x (s: Segment) : R := fst (term s).
Definition term_y (s: Segment) : R := snd (term s).

(* Segment は一つの PrimitiveSegment の幾何学的実現である。 *)
Parameter embed : PrimitiveSegment -> Segment -> Prop.
Parameter primitive_segment : Segment -> PrimitiveSegment.
Axiom primitive_segment_embed : forall s, embed (primitive_segment s) s.

(* Segment の向きは対応する PrimitiveSegment の向きと一致する。 *)
Parameter orn_seg : Segment -> Direction.
Axiom orn_seg_primitive : forall s, orn_seg s = orn (primitive_segment s).

(* initとtermは異なる点 *)
Axiom neq_init_term_x : forall seg, init_x seg <> term_x seg.
Axiom neq_init_term_y : forall seg, init_y seg <> term_y seg.
Lemma neq_init_term : forall seg, init seg <> term seg.
Proof.
  intros seg Heq. apply (neq_init_term_x seg).
  unfold init_x, term_x. now rewrite Heq.
Qed.

(* Segment は連続，x，y軸それぞれに関して狭義単調. *)
Definition x_strictly_monotone (s : Segment) : Prop :=
  (forall t1 t2, 0 <= t1 /\ t1 < t2 /\ t2 <= 1 ->
      fst (point s t1) < fst (point s t2))
  \/
  (forall t1 t2, 0 <= t1 /\ t1 < t2 /\ t2 <= 1 ->
      fst (point s t2) < fst (point s t1)).

Definition y_strictly_monotone (s : Segment) : Prop :=
  (forall t1 t2, 0 <= t1 /\ t1 < t2 /\ t2 <= 1 ->
      snd (point s t1) < snd (point s t2))
  \/
  (forall t1 t2, 0 <= t1 /\ t1 < t2 /\ t2 <= 1 ->
      snd (point s t2) < snd (point s t1)).

Definition continuous_segment (s : Segment) : Prop :=
  continuity (fun t => fst (point s t)) /\
  continuity (fun t => snd (point s t)).

Axiom seg_continuous : forall s, continuous_segment s.
Axiom x_strictly_monotone_seg : forall s, x_strictly_monotone s.
Axiom y_strictly_monotone_seg : forall s, y_strictly_monotone s.

(* 1つのセグメントは（延長部分も含め）自己交差しない，つまり point seg は単射
    （point の満たすべき性質，仕様） *)
Axiom point_injective : forall seg t1 t2, point seg t1 = point seg t2 -> t1 = t2.

Definition head_seg (ls: list Segment) (def: Segment):= hd def ls.

Lemma nth_head: forall (l:list Segment) (d: Segment), nth 0 l d = head_seg l d.
  Proof.
    intros l d. destruct l. simpl; reflexivity. simpl;reflexivity.
  Qed.


(* セグメントの[0, 1]区間上にその座標があるかどうか *)
Definition onSegment (seg: Segment) (rr : R * R) := exists (t:R), 0 <= t <= 1 /\ point seg t = rr.
Definition onHeadSegment (seg: Segment) (rr : R * R) := exists (t:R), t <= 1 /\ point seg t = rr.
Definition onLastSegment (seg: Segment) (rr : R * R) := exists (t:R), 0 <= t /\ point seg t = rr.

(* 始点側・終点側への延長部分上にある点 *)
Definition onHead (seg : Segment) (p : Point) : Prop :=
  exists t : R, t <= 0 /\ point seg t = p.
Definition onLast (seg : Segment) (p : Point) : Prop :=
  exists t : R, 1 <= t /\ point seg t = p.

Inductive onExtendSegment : list Segment -> Segment -> R * R -> Prop :=
| OnSegHead : forall (hds: Segment) (ls: list Segment) (rr: R*R),
    onHeadSegment hds rr
    -> onExtendSegment (hds :: ls) hds rr
| OnSegMid : forall (ls: list Segment) (seg:Segment) (rr: R*R),
    ls <> []
    -> In seg ls
    -> onSegment seg rr
    -> onExtendSegment ls seg rr
| OnSegLast : forall (ls: list Segment) (rr: R*R),
    ls <> []
    -> onLastSegment (last ls default_segment) rr
    -> onExtendSegment ls (last ls default_segment) rr.

Lemma ex_exists : forall (ls: list Segment) (seg: Segment) (rr : R * R), onExtendSegment ls seg rr -> exists (t:R), point seg t = rr.
Proof.
  intros ls seg rr Honex. inversion Honex as [
    hds ls0 rr0 H0 H1 H2 H3 |
    ls0 seg0 rr0 H0 H1 H2 H3 H4 |
    ls0 rr0 H0 H1 H2 H3].
    - unfold onHeadSegment in H0. destruct H0 as [t [_ Heq]]. exists t. exact Heq.
    - unfold onSegment in H1. destruct H2 as [t [_ Heq]]. exists t. exact Heq.
    - unfold onLastSegment in H1. destruct H1 as [t [_ Heq]]. exists t. exact Heq.
Qed.


Lemma onseg_onhead : forall (seg: Segment) (rr: R*R), onSegment seg rr -> onHeadSegment seg rr.
Proof.
intros seg rr HonSeg. unfold onSegment in HonSeg. destruct HonSeg as [t [[_ Hle1] Heqsegt]]. exists t. split. now auto. now auto.
Qed.

Lemma onseg_onlast : forall (seg: Segment) (rr: R*R), onSegment seg rr -> onLastSegment seg rr.
Proof.
  intros seg rr HonSeg. unfold onSegment in HonSeg. destruct HonSeg as [t [[Hge0 _] Heqsegt]]. exists t. split. now auto. now auto.
Qed.

Lemma onInit : forall s: Segment, onSegment s (init s).
Proof. intros s. exists 0. split; [lra | reflexivity]. Qed.

Lemma onTerm : forall s: Segment, onSegment s (term s).
Proof. intros s. exists 1. split; [lra | reflexivity]. Qed.

(* 長方形とその開内部。リストに依存しない基本表現をここで定める。 *)
Record Rect := mkRect { rx0 : R; ry0 : R; rx1 : R; ry1 : R }.

Definition rect_between (p q : Point) : Rect :=
  mkRect (Rmin (fst p) (fst q)) (Rmin (snd p) (snd q))
         (Rmax (fst p) (fst q)) (Rmax (snd p) (snd q)).

Definition in_rect (Rc : Rect) (p : Point) : Prop :=
  rx0 Rc < fst p < rx1 Rc /\ ry0 Rc < snd p < ry1 Rc.

(* Segment 上の点は端点か、両端点を対角線とする開長方形の内部にある。 *)
Definition in_open_segment_rectangle (s : Segment) (p : Point) : Prop :=
  in_rect (rect_between (init s) (term s)) p.

Definition in_segment_rectangle_or_endpoints (s : Segment) (p : Point) : Prop :=
  p = init s \/ p = term s \/ in_open_segment_rectangle s p.

Axiom segment_in_rectangle_or_endpoints :
  forall s p, onSegment s p -> in_segment_rectangle_or_endpoints s p.

(* x, y とも異なる任意の二点は、ある Segment で結ばれる。 *)
Axiom segment_exists_between : forall p q : Point,
  fst p <> fst q -> snd p <> snd q ->
  exists s : Segment, init s = p /\ term s = q.

(* 二点を通る時，その間にあるx座標を取ると，そのx座標の点がセグメント上に存在する（x(t)の連続性と中間値の定理で証明） *)
Axiom exist_between_x_pos: forall (seg: Segment) (x1 x2 y1 y2 x: R),
    onSegment seg (x1, y1) -> onSegment seg (x2, y2) -> y1 <= y2 -> x1 <= x -> x <= x2 -> exists y:R, onSegment seg (x, y) /\ y1 <= y <= y2.

Axiom exist_between_x_neg: forall (seg: Segment) (x1 x2 y1 y2 x: R),
    onSegment seg (x1, y1) -> onSegment seg (x2, y2) -> y2 <= y1 -> x1 <= x -> x <= x2 -> exists y:R, onSegment seg (x, y) /\ y2 <= y <= y1.

(* x, y の双方が異なる二点は、任意の向きで再接続できる。 *)
Definition reconnectable (p q : Point) (_ : Direction) : Prop :=
  fst p <> fst q /\ snd p <> snd q.

Parameter make_seg : forall p q d,
  reconnectable p q d -> Segment.

Axiom make_seg_spec : forall p q d H,
  init (make_seg p q d H) = p
  /\ term (make_seg p q d H) = q
  /\ orn_seg (make_seg p q d H) = d.

Lemma make_seg_init : forall p q d H,
  init (make_seg p q d H) = p.
Proof. intros p q d H; exact (proj1 (make_seg_spec p q d H)). Qed.

Lemma make_seg_term : forall p q d H,
  term (make_seg p q d H) = q.
Proof. intros p q d H; exact (proj1 (proj2 (make_seg_spec p q d H))). Qed.

Lemma make_seg_orn : forall p q d H,
  orn_seg (make_seg p q d H) = d.
Proof. intros p q d H; exact (proj2 (proj2 (make_seg_spec p q d H))). Qed.

Lemma reconnectable_iff : forall p q d,
  reconnectable p q d <->
  exists s, init s = p /\ term s = q /\ orn_seg s = d.
Proof.
  intros p q d. split.
  - intros H. exists (make_seg p q d H). apply make_seg_spec.
  - intros [s [Hinit [Hterm _]]]. unfold reconnectable.
    split.
    + rewrite <- Hinit, <- Hterm. apply neq_init_term_x.
    + rewrite <- Hinit, <- Hterm. apply neq_init_term_y.
Qed.

Lemma reconnectable_segment_exists : forall p q d,
  reconnectable p q d ->
  exists s, init s = p /\ term s = q /\ orn_seg s = d.
Proof. intros p q d H. now apply reconnectable_iff. Qed.


(* 注意：傾きを想定しているが，原理上は，埋め込みの延長線を一意に定義するものであればよい *)
Parameter slope_init : Segment -> R.
Parameter slope_term : Segment -> R.

(* 始点（終点）とそこでの傾きが、対応する延長線を一意に定める。 *)
Axiom head_extension_determined_by_init_slope : forall s1 s2,
	init s1 = init s2 ->
	slope_init s1 = slope_init s2 ->
	forall p, onHead s1 p <-> onHead s2 p.

Axiom last_extension_determined_by_term_slope : forall s1 s2,
	term s1 = term s2 ->
	slope_term s1 = slope_term s2 ->
	forall p, onLast s1 p <-> onLast s2 p.

(* ２点を始点終点とする，指定された向き・傾きのセグメントが取れる *)
Parameter reconnect_slope : Point -> Point -> Direction -> R -> R -> Prop.

Axiom reconnect_slope_spec : forall p q d slope_p slope_q,
  reconnect_slope p q d slope_p slope_q <->
  exists s,
    init s = p /\ term s = q /\ orn_seg s = d
    /\ slope_init s = slope_p /\ slope_term s = slope_q.

Parameter make_seg_slope : forall p q d slope_p slope_q,
  reconnect_slope p q d slope_p slope_q -> Segment.

Axiom make_seg_slope_spec : forall p q d slope_p slope_q H,
  init (make_seg_slope p q d slope_p slope_q H) = p
  /\ term (make_seg_slope p q d slope_p slope_q H) = q
  /\ orn_seg (make_seg_slope p q d slope_p slope_q H) = d
  /\ slope_init (make_seg_slope p q d slope_p slope_q H) = slope_p
  /\ slope_term (make_seg_slope p q d slope_p slope_q H) = slope_q.

Axiom reconnect_slope_reconnectable : forall p q d slope_p slope_q,
  reconnect_slope p q d slope_p slope_q -> reconnectable p q d.

  (* onSegmentに関する述語ならばonExtendedSegmentに関する述語みたいな補題を入れると楽に示せる *)
Lemma exist_between_x_pos_ex: forall (ls: list Segment) (seg: Segment) (x1 x2 y1 y2 x: R),
    onExtendSegment ls seg (x1, y1) -> onExtendSegment ls seg (x2, y2) -> y1 <= y2 -> x1 <= x -> x <= x2 -> exists y:R, onExtendSegment ls seg (x, y) /\ y1 <= y <= y2.
Admitted.

Lemma exist_between_x_neg_ex: forall (ls: list Segment) (seg: Segment) (x1 x2 y1 y2 x: R),
    onExtendSegment ls seg (x1, y1) -> onExtendSegment ls seg (x2, y2) -> y2 <= y1 -> x1 <= x -> x <= x2 -> exists y:R, onExtendSegment ls seg (x, y) /\ y2 <= y <= y1.
Admitted.


(* [extend] は意図的に抽象化している。具体的な構成はこのインターフェースを
   満たす候補実装としてのみ残す。 *)
Parameter extend : list Segment -> R -> R * R.
(* extend した後のパラメータ t がどのセグメントを指すか．2つのセグメントの共有端点なら，先頭側を返すものとする *)
Parameter extend_index : list Segment -> R -> nat.
(* extend した後のパラメータ t に対応するセグメントの中での局所パラメータ *)
Parameter extend_param : list Segment -> R -> R.

Definition Pos := (nat * R)%type.

Definition pos_of (ls : list Segment) (t : R) : Pos :=
  (extend_index ls t, extend_param ls t).

(* 先頭だけ下限なし（先頭の延長線）、末尾だけ上限なし（末尾の延長線）*)
Definition in_range (ls : list Segment) (q : Pos) : Prop :=
  (fst q < length ls)%nat
  /\ ((fst q = 0)%nat \/ 0 < snd q)
  /\ (S (fst q) = length ls \/ snd q <= 1).

(* extend は in_range のすべての位置を実現する *)
Axiom extend_onto : forall ls q,
  ls <> [] -> in_range ls q -> exists t, pos_of ls t = q.

Axiom extend_repr : forall ls t,
  ls <> [] -> exists s,
    nth_error ls (extend_index ls t) = Some s /\
    extend ls t = point s (extend_param ls t).

Axiom extend_param_region : forall ls t,
  ls <> [] ->
  (0 < extend_param ls t <= 1)
  \/ (extend_index ls t = 0%nat /\ extend_param ls t <= 0)
  \/ (S (extend_index ls t) = length ls /\ 1 < extend_param ls t).

Axiom extend_same_piece_injective : forall ls t1 t2,
  ls <> [] ->
  extend_index ls t1 = extend_index ls t2 ->
  extend_param ls t1 = extend_param ls t2 ->
  t1 = t2.

Definition close_extended (c: R -> R * R):=
  exists (t1 t2: R), t1 <> t2 /\ c t1 = c t2.

(* close, 閉 *)
Definition close (ls: list Segment) : Prop :=  close_extended (extend ls).

Axiom x_cross_h:
    forall (ls: list Segment) (s1 s2: Segment) (xa xb y1a y1b y2a y2b: R),
    In s1 ls
    -> In s2 ls
    -> onExtendSegment ls s1 (xa, y1a)
    -> onExtendSegment ls s1 (xb, y1b)
    -> onExtendSegment ls s2 (xa, y2a)
    -> onExtendSegment ls s2 (xb, y2b)
    -> (y1a - y2a) * (y1b - y2b) < 0
    -> close ls.

Axiom x_cross_v:
    forall (ls: list Segment) (s1 s2: Segment) (ya yb x1a x1b x2a x2b: R),
    In s1 ls
    -> In s2 ls
    -> onExtendSegment ls s1 (x1a, ya)
    -> onExtendSegment ls s1 (x1b, yb)
    -> onExtendSegment ls s2 (x2a, ya)
    -> onExtendSegment ls s2 (x2b, yb)
    -> (x1a - x2a) * (x1b - x2b) < 0
    -> close ls.

(*2つの異なる点を共有していたら延長考えなくともclose*)
Lemma have_two_same_point_close s1 s2 i j p1 p2 l :
  i <> j -> List.nth_error l i = Some s1 -> List.nth_error l j = Some s2 ->
  onSegment s1 p1 -> onSegment s1 p2 -> onSegment s2 p1 -> onSegment s2 p2 ->
  p1 <> p2 ->
  close l.
Admitted.

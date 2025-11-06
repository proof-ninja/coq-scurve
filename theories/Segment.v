Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lra.
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


Definition Segment := R -> R * R.
Parameter default_segment : Segment.


Definition init (seg: Segment) : R * R := seg 0.

Definition term (seg: Segment) : R * R := seg 1.

Definition init_x (s: Segment) : R := fst (init s).
Definition init_y (s: Segment) : R := snd (init s).
Definition term_x (s: Segment) : R := fst (term s).
Definition term_y (s: Segment) : R := snd (term s).

(* initとtermは異なる点 *)
Axiom neq_init_term_x : forall seg, init_x seg <> term_x seg.
Axiom neq_init_term_y : forall seg, init_y seg <> term_y seg.
Axiom neq_init_term : forall seg, init seg <> term seg.

Definition head_seg (ls: list Segment) (def: Segment):= hd def ls.

Lemma nth_head: forall (l:list Segment) (d: Segment), nth 0 l d = head_seg l d.
  Proof.
    intros l d. destruct l. simpl; reflexivity. simpl;reflexivity.
  Qed.


(* セグメントの[0, 1]区間上にその座標があるかどうか *)
Definition onSegment (seg: Segment) (rr : R * R) := exists (t:R), 0 <= t <= 1 /\ seg t = rr.
Definition onHeadSegment (seg: Segment) (rr : R * R) := exists (t:R), t <= 1 /\ seg t = rr.
Definition onLastSegment (seg: Segment) (rr : R * R) := exists (t:R), 0 <= t /\ seg t = rr.
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

Lemma ex_exists : forall (ls: list Segment) (seg: Segment) (rr : R * R), onExtendSegment ls seg rr -> exists (t:R), seg t = rr.
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

Axiom onInit : forall s: Segment, onSegment s (init s).

Axiom onTerm : forall s: Segment, onSegment s (term s).

(* 二点を通る時，その間にあるx座標を取ると，そのx座標の点がセグメント上に存在する（x(t)の連続性と中間値の定理で証明） *)
Axiom exist_between_x_pos: forall (seg: Segment) (x1 x2 y1 y2 x: R),
    onSegment seg (x1, y1) -> onSegment seg (x2, y2) -> y1 <= y2 -> x1 <= x -> x <= x2 -> exists y:R, onSegment seg (x, y) /\ y1 <= y <= y2.

Axiom exist_between_x_neg: forall (seg: Segment) (x1 x2 y1 y2 x: R),
    onSegment seg (x1, y1) -> onSegment seg (x2, y2) -> y2 <= y1 -> x1 <= x -> x <= x2 -> exists y:R, onSegment seg (x, y) /\ y2 <= y <= y1.

  (* onSegmentに関する述語ならばonExtendedSegmentに関する述語みたいな補題を入れると楽に示せる *)
Lemma exist_between_x_pos_ex: forall (ls: list Segment) (seg: Segment) (x1 x2 y1 y2 x: R),
    onExtendSegment ls seg (x1, y1) -> onExtendSegment ls seg (x2, y2) -> y1 <= y2 -> x1 <= x -> x <= x2 -> exists y:R, onExtendSegment ls seg (x, y) /\ y1 <= y <= y2.
Admitted.

Lemma exist_between_x_neg_ex: forall (ls: list Segment) (seg: Segment) (x1 x2 y1 y2 x: R),
    onExtendSegment ls seg (x1, y1) -> onExtendSegment ls seg (x2, y2) -> y2 <= y1 -> x1 <= x -> x <= x2 -> exists y:R, onExtendSegment ls seg (x, y) /\ y2 <= y <= y1.
Admitted.


Parameter extend : list Segment -> (R -> R * R).

Definition close_extended (c: Segment):=
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

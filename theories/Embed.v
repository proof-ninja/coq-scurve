Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import PrimitiveSegment.
Require Import Segment.
From Stdlib Require Import Lra.
Open Scope R_scope.
Import ListNotations.

(*
 * 自動で生成される名前がズレてしまうので無意味な定義を入れている。
 * TODO: 証明のintros とかで名前付けをサボらない
 *)
Definition H := H.


(* [0, 1]区間で連続かどうか，向きがPrimitiveSegmentの向きか，など *)
Parameter embed : PrimitiveSegment -> Segment -> Prop.


(* 始点と終点の位置関係を示す公理 *)
Axiom n_end_relation: forall (s: Segment) (h: H) (c: C),
    embed (n, h, c) s -> snd (init s) < snd (term s).
Axiom s_end_relation: forall (s1: Segment) (h: H) (c: C),
    embed (s, h, c) s1 -> snd (term s1) < snd (init s1).
Axiom e_end_relation: forall (s: Segment) (v: V) (c: C),
    embed (v, e, c) s -> fst (init s) < fst (term s).
Axiom w_end_relation: forall (s: Segment) (v: V) (c: C),
    embed (v, w, c) s -> fst (term s) < fst (init s).

(* セグメント上にある点と始点終点の位置関係 *)
Axiom s_onseg_relation: forall (s1: Segment) (h:H) (c:C) (x y: R),
    embed (s, h, c) s1 -> onSegment s1 (x, y) -> snd (term s1) <= y /\ y <= snd (init s1).

Axiom n_onseg_relation: forall (s1: Segment) (h:H) (c:C) (x y: R),
    embed (n, h, c) s1 -> onSegment s1 (x, y) -> snd (init s1) <= y /\ y <= snd (term s1).

Axiom e_onseg_relation: forall (s1: Segment) (v:V) (c:C) (x y: R),
    embed (v, e, c) s1 -> onSegment s1 (x, y) -> fst (init s1) <= x /\ x <= fst (term s1).

Axiom w_onseg_relation: forall (s1: Segment) (v:V) (c:C) (x y: R),
    embed (v, w, c) s1 -> onSegment s1 (x, y) -> fst (term s1) <= x /\ x <= fst (init s1).

(* 始点と終点の間にあるx座標を取ると，そのx座標の点がセグメント上にあることを示す公理 *)
Lemma e_exist_y s' v c x:
  embed (v, e, c) s' -> fst (init s') <= x -> x <= fst (term s') ->
  exists y:R, onSegment s' (x, y) /\ (match v with n => init_y s' <= y <= term_y s' | s => term_y  s' <= y <= init_y s' end).
Proof.
  intros H0 Hge0 Hge1. destruct v.
  - eapply exist_between_x_pos with (x1:=fst (init s')) (y1:= snd (init s')) (x2:=fst (term s')) (y2:= snd (term s')).
    + rewrite <- surjective_pairing. now eapply onInit.
    + rewrite <- surjective_pairing. now eapply onTerm.
    + apply Rlt_le. eapply n_end_relation. now eauto.
    + exact Hge0.
    + exact Hge1.
  - eapply exist_between_x_neg with (x1:=fst (init s')) (y1:= snd (init s')) (x2:=fst (term s')) (y2:= snd (term s')).
    + rewrite <- surjective_pairing. now eapply onInit.
    + rewrite <- surjective_pairing. now eapply onTerm.
    + apply Rlt_le. eapply s_end_relation. now eauto.
    + exact Hge0.
    + exact Hge1.
Qed.

Lemma w_exist_y s' v c x:
  embed (v, w, c) s' -> fst (term s') <= x -> x <= fst (init s') ->
  exists y:R, onSegment s' (x, y) /\ (match v with n => init_y s' <= y <= term_y s' | s => term_y  s' <= y <= init_y s' end).
Proof.
  intros H0 Hge0 Hge1. destruct v.
  - eapply exist_between_x_neg with (x2:=fst (init s')) (y2:= snd (init s')) (x1:=fst (term s')) (y1:= snd (term s')).
    + rewrite <- surjective_pairing. now eapply onTerm.
    + rewrite <- surjective_pairing. now eapply onInit.
    + apply Rlt_le. eapply n_end_relation. now eauto.
    + exact Hge0.
    + exact Hge1.
  - eapply exist_between_x_pos with (x2:=fst (init s')) (y2:= snd (init s')) (x1:=fst (term s')) (y1:= snd (term s')).
    + rewrite <- surjective_pairing. now eapply onTerm.
    + rewrite <- surjective_pairing. now eapply onInit.
    + apply Rlt_le. eapply s_end_relation. now eauto.
    + exact Hge0.
    + exact Hge1.
Qed.

Lemma e_exist_y_ex: forall (ls: list Segment) (s':Segment) (v:V) (c:C) (x:R),
    embed (v, e, c) s' -> In s' ls -> ls <> [] -> fst (init s') <= x -> x <= fst (term s') -> exists y:R, onExtendSegment ls s' (x, y) /\ (match v with n => init_y s' <= y <= term_y s' | s => term_y  s' <= y <= init_y s' end).
Proof.
    intros ls s' v c x Hembed Hin Hnotnil Hge0 Hge1.
    assert(HonInitTerm: onExtendSegment ls s' (init_x s', init_y s') /\ onExtendSegment ls s' (term_x s', term_y s')).
    {
      split.
      - eapply OnSegMid. exact Hnotnil. exact Hin.
        unfold init_x, init_y. rewrite <- surjective_pairing. now eapply onInit.
      - eapply OnSegMid. exact Hnotnil. exact Hin.
        unfold term_x, term_y. rewrite <- surjective_pairing. now eapply onTerm.
    } destruct HonInitTerm as [HonInit HonTerm]. destruct v.
    - eapply exist_between_x_pos_ex.
      + exact HonInit.
      + exact HonTerm.
      + apply Rlt_le. eapply n_end_relation. now eauto.
      + exact Hge0.
      + exact Hge1.
    - eapply exist_between_x_neg_ex.
      + exact HonInit.
      + exact HonTerm.
      + apply Rlt_le. eapply s_end_relation. now eauto.
      + exact Hge0.
      + exact Hge1.
Qed.

Lemma w_exist_y_ex: forall (ls: list Segment) (s':Segment) (v:V) (c:C) (x:R),
    embed (v, w, c) s' -> In s' ls -> ls <> [] -> fst (term s') <= x -> x <= fst (init s') -> exists y:R, onExtendSegment ls s' (x, y) /\ (match v with n => init_y s' <= y <= term_y s' | s => term_y  s' <= y <= init_y s' end).
Proof.
  intros ls s' v c x Hembed Hin Hnotnil Hge0 Hge1.
  assert(HonInitTerm: onExtendSegment ls s' (init_x s', init_y s') /\ onExtendSegment ls s' (term_x s', term_y s')).
  {
    split.
    - eapply OnSegMid. exact Hnotnil. exact Hin.
      unfold init_x, init_y. rewrite <- surjective_pairing. now eapply onInit.
    - eapply OnSegMid. exact Hnotnil. exact Hin.
      unfold term_x, term_y. rewrite <- surjective_pairing. now eapply onTerm.
  } destruct HonInitTerm as [HonInit HonTerm]. destruct v.
  - eapply exist_between_x_neg_ex.
    + exact HonTerm.
    + exact HonInit.
    + apply Rlt_le. eapply n_end_relation. now eauto.
    + exact Hge0.
    + exact Hge1.
  - eapply exist_between_x_pos_ex.
    + exact HonTerm.
    + exact HonInit.
    + apply Rlt_le. eapply s_end_relation. now eauto.
    + exact Hge0.
    + exact Hge1.
Qed.



(* scurveの埋め込み．scurveとSegmentのリストの述語．
lp: scurve にps: PrimitiveSegment をくっつけたものが (s2::ls): list Segment にs1: Segment をくっつけたものとして埋め込まれる関係　*)
Inductive embed_scurve : scurve -> list Segment -> Prop :=
| EmbedScurveNil : embed_scurve (exist _ nil IsScurveNil) nil
| EmbedScurveSigle : forall (ps:PrimitiveSegment) (s:Segment),
    embed ps s
    -> embed_scurve (connect ps (exist _ nil IsScurveNil) (DcNil ps)) (s::nil)
| EmbedScurveCons : forall (ps:PrimitiveSegment) (lp: scurve) (A: dc_pseg_hd ps (proj1_sig lp)) (s1 s2: Segment) (ls: list Segment),
    embed ps s1
    -> embed_scurve lp (s2::ls)
    -> term s1 = init s2
    -> embed_scurve (connect ps lp A) (s1 :: s2 :: ls).


Lemma consist_init_term : forall (sc: scurve) (ls1 ls2: list Segment),
  embed_scurve sc (ls1 ++ ls2)
  -> ls1 <> []
  -> ls2 <> []
  -> term (last ls1 default_segment) = init (List.hd default_segment ls2).
Proof.
  intros sc ls1. revert sc. induction ls1 as [|seg ls1']; [now idtac|].
  intros sc ls2 emb _. inversion emb.
  - (* EmbedScurveSingleの場合: ls2 <> [] だからありえん *)
    now apply eq_sym, app_eq_nil in H3.
  - (* EmbedScurveConsの場合 *)
    destruct ls1' as [|seg2 ls1''].
    + (* ls1' = [] のとき *)
      intros _. simpl in H1. now rewrite <- H1.
    + (* ls1' = _::_ のとき: 帰納法の仮定IHls1'を使う *)
      intros nemp_ls2. apply (IHls1' lp); [|now auto|now auto].
      simpl. injection H1 as _es1 _els. now subst s1 s2 ls.
Qed.

Lemma scurve_length_consis: forall (sc: scurve) (ls: list Segment),
  embed_scurve sc ls -> length (proj1_sig sc) = length ls.
Proof.
  intros sc ls. revert sc. induction ls as [|a ls IHls].
  - intros sc Hembed. inversion Hembed as [_Hex | | ]. reflexivity.
  - intros sc Hembed. inversion Hembed as [ | ps s0 Hembedps Hconnect [_HHH Hnil]| ps sctl Hdc a' s2 lstl Hembedps Hembedsctl _Hconsis [Heqsc Heqa Hls]].
    + reflexivity.
    + subst. simpl. apply IHls in Hembedsctl. rewrite Hembedsctl. reflexivity.
Qed.



(* リストlsに含まれてるセグメントが同じ水平方向を向いていることを表す命題 *)
Definition all_same_h (ls: list Segment) (h: H) :=
  ls <> [] /\ Forall (fun (s:Segment) => exists (v:V) (c:C), embed (v, h, c) s) ls.

(*  最初のセグメントや最後のセグメントについて，あるx/y座標より大きい/小さい任意の座標に対して，
    そのx/y座標を持つ点がセグメント上にある
    exist_between_pos/negで証明可能？ *)
Lemma extended_segment_init_n : forall (ls: list Segment) (h: H) (y x1 y1: R),
let head := head_seg ls default_segment in
embed (n, h, cx) head -> onHeadSegment head (x1, y1) -> y <= y1 -> exists (x: R), onHeadSegment (head_seg ls default_segment) (x, y) /\ (match h with e => x <= x1 | w => x1 <= x end).
Admitted.

Lemma extended_segment_init_e_scx : forall (ls: list Segment) (x x1 y1: R),
let head := head_seg ls default_segment in
embed (s, e, cx) head -> onHeadSegment head (x1, y1) -> x <= x1 -> exists (y: R), onHeadSegment (head_seg ls default_segment) (x, y) /\ y1 <= y.
Admitted.

Lemma extended_segment_init_e_ncc : forall (ls: list Segment) (x x1 y1: R),
let head := head_seg ls default_segment in
embed (n, e, cc) head -> onHeadSegment head (x1, y1) -> x <= x1 -> exists (y: R), onHeadSegment (head_seg ls default_segment) (x, y) /\ y <= y1.
Admitted.

Lemma extended_segment_term_n : forall (ls: list Segment) (h: H) (y x1 y1: R),
let last_s := last ls default_segment in
embed (n, h, cc) last_s -> onLastSegment last_s (x1, y1) ->  y1 <= y -> exists (x: R), onLastSegment (last ls default_segment) (x, y) /\ (match h with e => x1 <= x | w => x <= x1 end).
Admitted.

Lemma extended_segment_term_w_ncx : forall (ls: list Segment) (x x1 y1: R),
let last_s := last ls default_segment in
embed (n, w, cx) last_s -> onLastSegment last_s (x1, y1) ->  x <= x1 -> exists (y: R), onLastSegment last_s (x, y) /\ y1 <= y.
Admitted.



(* (n,e,cx)から始まり右にいくらか伸びて、真ん中は自由で、最後は左に伸びたあと(n,w,_)で終わる場合
   右に行く往路と左に行く復路で共通のxに対して y復路<y往路の場合、このセグメントはどこかで交わる *)
(* s1とs2は往路と復路で共通のxをもつセグメント *)
Lemma end_nwcx_close: forall sc s_start s_end c x y1 y2 l s1 center s2 r,
  embed_scurve sc (l ++ [s1] ++ center ++ [s2] ++ r) ->
  head (l ++ [s1]) = Some s_start ->
  embed (n, e, cx) s_start ->
  last ([s2] ++ r) default_segment = s_end ->
  embed (n, w, c) s_end ->
  all_same_h (l ++ [s1]) e ->  (*往路は東に伸びる*)
  all_same_h ([s2] ++ r) w ->  (*復路は西に伸びる*)
  onSegment s1 (x, y1) ->
  onSegment s2 (x, y2) ->
  y2 < y1 ->
  close (l ++ [s1] ++ center ++ [s2] ++ r).
Proof.
Admitted.

(* n,e,cxから始まり，しばらく右に伸びている，(x1, y2)を通る．
最後のセグメントが左上で，(x1, y1)を通る．
y1<=y2の時に最後のセグメントはどこかで交わる*)
(* n,e,cxから始まり，しばらく右に伸びている，(x1, y2)を通る．
最後のセグメントが左上で，(x1, y1)を通る．
y1<=y2の時に最後のセグメントはどこかで交わる*)
Axiom end_cross_term_nw:
    forall (sc: scurve) (ls1 ls2: list Segment) (x1 y1 y2: R),
    let hd1 := head_seg ls1 default_segment in
    let tl1 := last ls1 default_segment in
    let tl2 := last ls2 default_segment in
    embed_scurve sc (ls1 ++ ls2)
    -> y1 < y2
    -> ls2 <> []
    -> embed (n, e, cx) hd1
    -> embed (n, w, cc) tl2 \/ embed (n, w, cx) tl2
    -> onExtendSegment (ls1 ++ ls2) tl2 (x1, y1)
    -> onExtendSegment (ls1 ++ ls2) tl1 (x1, y2)
    -> all_same_h ls1 e
    -> close (ls1 ++ ls2).


Axiom end_cross_init_ne:
    forall (sc: scurve) (ls1 ls2: list Segment) (x1 y1 y2: R),
    let hd2 := head_seg ls2 default_segment in
    let tl2 := last ls2 default_segment in
    let hd1 := head_seg ls1 hd2 in
    embed_scurve sc (ls1 ++ ls2)
    -> y2 < y1
    -> ls1 <> []
    -> embed (n, e, cc) hd1 \/ embed (n, e, cx) hd1
    -> embed (n, w, cc) tl2
    -> onSegment hd1 (x1, y1)
    -> onSegment hd2 (x1, y2)
    -> all_same_h (rev ls2) w
    -> close (ls1++ls2).


Lemma embed_scurve_inv_Cons sc p1 p2 ps ss:
  embed_scurve sc ss ->
  proj1_sig sc = (p1 :: p2 :: ps) ->
  exists s1 s2 rest sc',
    ss = s1 :: s2 :: rest /\ proj1_sig sc' = p2 :: ps /\ embed_scurve sc' (s2 :: rest)
    /\ embed p1 s1 /\ term s1 = init s2.
Proof.
  intros emb e_proj1. inversion emb as [esc _e| p1' s1 emb1 esc| p1' sc' A s1 s2 ss_tail emb1 emb' term_init conn e_ss] .
  - now rewrite <- esc in e_proj1.
  - now rewrite <- esc in e_proj1.
  - rewrite <- conn in e_proj1.
    injection e_proj1 as _p1' e_proj1'. subst p1'.
    now exists s1, s2, ss_tail, sc'.
Qed.

Lemma embed_scurve_inv_Single sc p ss:
  embed_scurve sc ss -> proj1_sig sc = [p] ->
  exists s, ss = [s] /\ embed p s.
Proof.
  intros emb e_proj1. inversion emb as [esc _e|p' s emb1 esc|p' sc' A s1 s2 ss' emb1 emb'].
  - now rewrite <- esc in e_proj1.
  - rewrite <- esc in e_proj1. injection e_proj1 as _ep'. subst. now exists s.
  - subst. simpl in e_proj1. inversion emb'; now subst.
Qed.


(* admissible, 許容可能 *)
Definition admissible (lp: scurve) : Prop :=
    exists ls: list Segment, (embed_scurve lp ls /\ ~ close ls).

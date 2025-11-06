Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import PrimitiveSegment.
Require Import ListExt.
Require Import Segment.
Require Import Embed.
From Stdlib Require Import Lra.

Lemma x_consis: forall s1 s2, term s1 = init s2 -> term_x s1 = init_x s2.
Proof.
  intros s1 s2 H. unfold init_x, term_x. rewrite H. reflexivity.
Qed.

Lemma y_consis: forall s1 s2, term s1 = init s2 -> term_y s1 = init_y s2.
Proof.
  intros s1 s2 H. unfold init_y, term_y. rewrite H. reflexivity.
Qed.

(* psの場合分けとn_end_relationとs_end_relationでできそう *)
Lemma neq_init_term_x : forall seg ps, embed ps seg -> init_x seg <> term_x seg.
Admitted.

(* exsit_betweenシリーズでいけそう *)
Lemma exist_between_x: forall (ls: list Segment) (seg: Segment) (ps: PrimitiveSegment) (x1 x2 y1 y2 x: R),
    onExtendSegment ls seg (x1, y1) -> onExtendSegment ls seg (x2, y2) -> embed ps seg -> x1 <= x -> x <= x2 -> exists y:R, onExtendSegment ls seg (x, y).
Admitted.

(* onExtendedSegmentのinversionでできそう
    onSegの述語ならばonExの述語みたいな定理があればより楽か？ *)
Lemma onTermEx: forall (ls: list Segment) (seg: Segment), onExtendSegment ls seg (term seg).
Admitted.
Lemma onInitEx: forall (ls: list Segment) (seg: Segment), onExtendSegment ls seg (init seg).
Admitted.

Lemma have_two_same_point_ex_close s1 s2 i j p1 p2 l ls:
  i <> j -> List.nth_error l i = Some s1 -> List.nth_error l j = Some s2 ->
  onExtendSegment ls s1 p1 -> onExtendSegment ls s1 p2 -> onExtendSegment ls s2 p1 -> onExtendSegment ls s2 p2 ->
  p1 <> p2 ->
  close l.
Admitted.

Lemma have_same_point_app_close s1 s2 s ls1 ls2 p:
  In s1 ls1 -> In s2 ls2 -> 
  onExtendSegment (ls1 ++ [s] ++ ls2) s1 p -> onExtendSegment (ls1 ++ [s] ++ ls2) s2 p ->
  close (ls1 ++ [s] ++ ls2).
Admitted.

Lemma pair_neq [A B: Type] (x1 x2: A) (y1 y2: B):
  x1 <> x2 -> (x1, y1) <> (x2, y2).
Admitted.

(* under_all_eの弱いバージョン．underはx1, y1を通り，常に右を向いているlseの一番最後尾にx1がないといけない *)
Axiom under_all_e_aux:
  forall (sc: scurve) (ls1 lse ls2 ls3: list Segment) (under: Segment) (x1 xh y1 yh yl: R),
  let ls := (ls1 ++ lse ++ ls2 ++ (under :: ls3)) in
  embed_scurve sc ls
  -> all_same_h lse e
  -> onExtendSegment ls under (x1, y1)
  -> onExtendSegment ls (head_seg lse default_segment) (xh, yh)
  -> xh < x1 < term_x (last lse default_segment) /\ xh < term_x under < term_x (last lse default_segment)
  -> onExtendSegment ls (last lse default_segment) (x1, yl) /\ y1 < yl
  -> close ls \/ exists (seg:Segment) (y2:R), In seg lse /\ onExtendSegment ls seg (term_x under, y2) /\ term_y under < y2 /\ term_x under < term_x seg.

(* auxから少し使える範囲を増やした．
  ただし，underのtermは，x1があるlse上のセグメント(segonx1)のtermの右にいけない．（term_x under < term_x segonx1）
  特徴としてはunderが西向きの場合は常に使用可能 *)
Lemma under_all_e_aux_2:
  forall (sc: scurve) (ls1 lse ls2 ls3: list Segment) (under segonx1: Segment) (x1 xh y1 yh yl: R),
  let ls := (ls1 ++ lse ++ ls2 ++ (under :: ls3)) in
  embed_scurve sc ls
  -> all_same_h lse e
  -> onExtendSegment ls under (x1, y1)
  -> onExtendSegment ls (head_seg lse default_segment) (xh, yh)
  -> xh < x1 < term_x (last lse default_segment) /\ xh < term_x under < term_x (last lse default_segment)
  -> In segonx1 lse /\ onExtendSegment ls segonx1 (x1, yl) /\ x1 < term_x segonx1 /\ y1 < yl
  -> term_x under < term_x segonx1
  -> close ls \/ exists (seg:Segment) (y2:R), In seg lse /\ onExtendSegment ls seg (term_x under, y2) /\ term_y under < y2 /\ term_x under < term_x seg.
Proof.
  intros sc ls1 lse ls2 ls3 under segonx1 x1 xh y1 yh yl ls Hembed Hh HonSegx1y1 HonSegxhyh [Hltx1 Hlttermx] Hsegonx1 Hlttermunder.
  destruct Hsegonx1 as [Hin Hsegonx1]. apply in_app_app in Hin as [lse1 [lse2 Heq]]. 
  assert (Heqls: ls1 ++ lse ++ ls2 ++ under :: ls3 = ls1 ++ (lse1 ++ [segonx1]) ++ (lse2 ++ ls2) ++ under :: ls3).
  {
    rewrite Heq. repeat rewrite app_assoc. reflexivity.
  } 
  unfold ls in Hembed. rewrite Heqls in Hembed.
  eapply under_all_e_aux with (lse:= lse1 ++ [segonx1]) (ls1 := ls1) (ls2:= (lse2 ++ ls2)) (under := under) (ls3:=ls3) in Hembed.
  {
    destruct Hembed as [Hclose | [seg [y2 [Hin Hunder]]]].
    + left. unfold ls. rewrite Heqls. exact Hclose.
    + right. exists seg, y2. split.
      - rewrite Heq. rewrite app_assoc. apply in_or_app. left. exact Hin.
      - unfold ls. rewrite Heqls. exact Hunder. 
  }
  - unfold all_same_h in *. split. unfold not. destruct lse1; discriminate. destruct Hh as [_ Hforall]. rewrite Heq in Hforall. rewrite app_assoc in Hforall. apply Forall_app in Hforall as [Hforall _]. exact Hforall.
  - unfold ls in HonSegx1y1. rewrite Heqls in HonSegx1y1. exact HonSegx1y1.
  - unfold ls in HonSegxhyh. rewrite Heqls in HonSegxhyh. assert(Hhead: head_seg (lse1 ++ [segonx1]) default_segment = head_seg lse default_segment).
    {
      rewrite Heq. destruct lse1. reflexivity. reflexivity.
    }
    rewrite Hhead. exact HonSegxhyh.
  - rewrite last_last.
    destruct Hsegonx1 as [Hsegonx1 Hlty1yl]. unfold ls in Hsegonx1. split;[split;[now apply Hltx1| now apply Hlty1yl]|split;[now apply Hlttermx| ]]. exact Hlttermunder.
  - rewrite last_last. rewrite <- Heqls. unfold ls in Hsegonx1. split. now eapply Hsegonx1. now eapply Hsegonx1. 
Qed.

(* aux_2から先述の条件を減らしたもの
  現状，example2の証明で使用しているが，この部分はaux_2で十分なため，この公理は必要ないかもしれない
  また証明可能かどうかについても少し怪しい *)
(* Axiom under_all_e:
  forall (sc: scurve) (ls1 lse ls2 ls3: list Segment) (under segonx1: Segment) (x1 xh y1 yh yl: R),
  let ls := (ls1 ++ lse ++ ls2 ++ (under :: ls3)) in
  embed_scurve sc ls ->
  onExtendSegment ls under (x1, y1) ->
  all_same_h lse e ->
  onExtendSegment ls (head_seg lse default_segment) (xh, yh) ->
  xh < x1 < term_x (last lse default_segment) /\ xh < term_x under < term_x (last lse default_segment) ->
  In segonx1 lse /\ onExtendSegment ls segonx1 (x1, yl) /\ x1 < term_x segonx1 /\ y1 < yl ->
  close ls \/ exists (seg:Segment) (y2:R), In seg lse /\ onExtendSegment ls seg (term_x under, y2) /\ term_y under < y2 /\ term_x under < term_x seg. *)

  (* under_all_eをexample3に使いやすい形にした補題，証明は少し難しいかもしれないができると思う *)
Lemma all_e_swcc:
  forall (sc: scurve) (lse ls2: list Segment) (secx_seg swcc_seg: Segment),
  let ls := (lse ++ [secx_seg; swcc_seg] ++ ls2) in
  embed_scurve sc ls
  -> embed (s,e,cx) secx_seg /\ embed (s,w,cc) swcc_seg
  -> all_same_h (lse ++ [secx_seg]) e
  -> embed (n,e,cc) (head_seg (lse ++ [secx_seg]) default_segment) (* \/ embed (n,e,cx) (head_seg (lse ++ [secx_seg]) default_segment) *)
  -> close ls \/ exists (seg:Segment) (y2:R), In seg (lse ++ [secx_seg]) /\ onExtendSegment ls seg (term_x swcc_seg, y2) /\ term_y swcc_seg < y2 /\ term_x swcc_seg < term_x seg.
Proof.
  intros sc lse ls2 secx_seg swcc_seg ls Hembedsc [Hembed1 Hembed2] Halle Hembedhd.
  assert(eqls: ls = ([] ++ (lse ++ [secx_seg]) ++ [] ++ swcc_seg::ls2)).
  {
    unfold ls. now rewrite <- app_assoc.
  }
  assert(_hd: swcc_seg = List.hd default_segment (swcc_seg :: ls2) ). { reflexivity. }
  assert(Hconsis: term secx_seg = init swcc_seg).
  {
    erewrite <- last_last with (a:=secx_seg) (l:= lse). rewrite _hd. eapply consist_init_term.
    - simpl. rewrite <- app_assoc. simpl. exact Hembedsc.
    - destruct lse as [| a tail]; discriminate.
    - discriminate.
  }
  clear _hd.
  (* secxとswxxを繋ぐ点より少しだけ左の点xs2とswcc上のxs2を通る点(xs2, ys2) *)
  assert (Heps: exists xs2 ys2: R, onExtendSegment ls swcc_seg (xs2, ys2) /\ init_x secx_seg < xs2 /\ term_x swcc_seg < xs2 < init_x swcc_seg /\ ys2 <= init_y swcc_seg).
  {
    eapply e_end_relation in Hembed1 as Hlt2. rewrite Hconsis in Hlt2. eapply w_end_relation in Hembed2 as Hlt3. apply Rexists_between in Hlt2 as [xs2' Hlt2]. apply Rexists_between in Hlt3 as [xs2'' Hlt3'].
    set (xs2 := Rmax xs2' xs2'').
    assert (Rmaxge : xs2' <= xs2 /\ xs2'' <= xs2). split;[now apply Rmax_l|now apply Rmax_r].
    eapply w_exist_y_ex in Hembed2.
    - destruct Hembed2 as [ys2 [HonSeg Hlty]]. exists xs2, ys2. split;[exact HonSeg| split;[| unfold term_x]]. unfold init_x. lra. split. Search Rmax. split. lra. apply Rmax_lub_lt;unfold init_x;now auto. lra.
    - unfold ls. apply in_or_app. right. right;left;reflexivity.
    - unfold ls. destruct lse;discriminate.
    - lra. 
    - apply Rlt_le. apply Rmax_lub_lt;unfold init_x;now auto.
  }
  destruct Heps as [xs2 [ys2 [onxs2ys2 Hlt]]].
  (* swcx上を通る点(xs2, ys2over) *)
  assert (onxs2over: exists ys2over : R, onExtendSegment ls secx_seg (xs2, ys2over) /\ term_y secx_seg <= ys2over <= init_y secx_seg).
  {
    eapply e_exist_y_ex with (ls:=ls) in Hembed1 as _H.
    - now apply _H.
    - unfold ls. apply in_or_app. right. now left.
    - unfold ls. destruct lse; discriminate.
    - unfold init_x in Hlt. apply Rlt_le. now apply Hlt.
    - apply Rlt_le. rewrite Hconsis. unfold init_x in Hlt. now apply Hlt.
  }
  destruct onxs2over as [ys2over [onxs2over Hge]].
  (* 十分左にあり，lseの先頭のセグメント上にある点(xh, yh) *)
  assert(Hxh: exists xh yh, (onExtendSegment ls (head_seg (lse ++ [secx_seg]) default_segment) (xh, yh)) /\ xh < xs2 /\ xh < term_x swcc_seg).
  {
   set (xh:=Rmin (Rmin xs2 (term_x swcc_seg)) (term_x (head_seg (lse ++ [secx_seg]) default_segment)) - 1). 
   eapply extended_segment_init_e_ncc in Hembedhd.
   - destruct Hembedhd as [xhy [HonHead _]].
     exists xh. eexists. repeat split.
     + destruct lse; apply OnSegHead; eapply HonHead.
     + unfold xh, Rmin. destruct (Rle_dec xs2 (term_x swcc_seg)), (Rle_dec xs2 (term_x swcc_seg));try lra. destruct (Rle_dec (term_x swcc_seg) (term_x (head_seg (lse ++ [secx_seg]) default_segment)));try lra.
     + unfold xh, Rmin. destruct (Rle_dec xs2 (term_x swcc_seg)), (Rle_dec xs2 (term_x swcc_seg));try lra. destruct (Rle_dec (term_x swcc_seg) (term_x (head_seg (lse ++ [secx_seg]) default_segment)));try lra.
   - exists 1. split. lra. erewrite <- surjective_pairing. reflexivity.
   - change (fst (head_seg (lse ++ [secx_seg]) default_segment 1)) with (term_x (head_seg (lse ++ [secx_seg]) default_segment)).
     unfold xh, Rmin. destruct (Rle_dec xs2 (term_x swcc_seg)), (Rle_dec xs2 (term_x swcc_seg));try lra. destruct (Rle_dec (term_x swcc_seg) (term_x (head_seg (lse ++ [secx_seg]) default_segment)));try lra.     
  }
  destruct Hxh as [xh [yh [onExxh [Hlt1 Hlt2]]]].
  rewrite eqls.
  destruct (Req_dec ys2 ys2over) as [eq | neq].
  (* ys2 = ys2overの時はterm swcxと(xs2, ys2)の二点を通り，have_two_same_point_closeで示す *)
  * left. eapply have_two_same_point_ex_close with (i:= length lse) (j:= (1 + length lse)%nat).
    - apply Nat.neq_succ_diag_r.
    - simpl. rewrite <- app_assoc. rewrite (nth_error_app2 lse ([secx_seg] ++ swcc_seg :: ls2) (le_n (length lse))). 
      rewrite (Nat.sub_diag (length lse)). reflexivity.
    - rewrite Nat.add_comm. simpl. rewrite Nat.add_comm. rewrite <- app_assoc. rewrite (nth_error_app2 lse ([secx_seg] ++ swcc_seg :: ls2) (Nat.le_add_l (length lse) 1)).
      rewrite Nat.add_sub. reflexivity. 
    - now apply (onTermEx ls secx_seg).
    - exact onxs2over.
    - rewrite Hconsis. now apply onInitEx.
    - rewrite <- eq. now auto.
    - rewrite Hconsis. rewrite (surjective_pairing (init swcc_seg)). change (fst (init swcc_seg)) with (init_x swcc_seg).
      apply pair_neq. lra.
  (* そうでない時はaux_2で証明 *)
  * eapply under_all_e_aux_2;try rewrite <- eqls;try now eauto.
    - rewrite last_last. apply x_consis in Hconsis. rewrite Hconsis. try lra.
    - repeat split.
      + apply in_or_app. right. now left.
      + exact onxs2over.
      + apply x_consis in Hconsis. lra.
      + apply y_consis in Hconsis. lra.
    - apply x_consis in Hconsis. rewrite Hconsis. eapply w_end_relation. exact Hembed2.
Qed.

(* 詳細はweeklyのhack.mdにて，証明は長そう． *)
Lemma end_e_close: forall sc l s1 le secx_seg swcc_seg lw s2 r s3 ler x y1 y2 ymid,
  let ls := (l ++ [s1] ++ le ++ lw ++ [s2] ++ r ++ ler) in
  embed_scurve sc ls ->
  last ([s1] ++ le) default_segment = secx_seg ->
  head (lw ++ [s2]) = Some swcc_seg ->
  head ler = Some s3 ->
  embed (s, e, cx) secx_seg ->
  embed (s, w, cc) swcc_seg ->
  all_same_h ([s1] ++ le) e ->  (*往路は東に伸びる*)
  all_same_h (lw ++ [s2]) w ->  (*その後西に伸びる*)
  all_same_h ler e -> (* もう一度東に伸びる *)
  onExtendSegment ls s1 (x, y1) ->
  onExtendSegment ls s2 (x, y2) ->
  onExtendSegment ls s3 (x, ymid) ->
  y2 < ymid < y1 ->
  close ls.
Admitted.

Definition example2_list: list PrimitiveSegment :=
  [(n,e,cc);(n,e,cx);(s,e,cx);(s,w,cc);(n,w,cc);(n,e,cx);(n,e,cc)].
Lemma example2_scurve : is_scurve example2_list.
Proof. repeat constructor. Qed.

Definition example2 := exist _ example2_list example2_scurve.

Lemma emb_example2 ss : embed_scurve example2 ss -> exists s1 s2 s3 s4 s5 s6 s7,
      ss = [s1;s2;s3;s4;s5;s6;s7]
      /\ embed (n,e,cc) s1 /\ embed (n,e,cx) s2 /\ embed (s,e,cx) s3
      /\ embed (s,w,cc) s4 /\ embed (n,w,cc) s5 /\ embed (n,e,cx) s6 /\ embed (n,e,cc) s7
      /\ term s1 = init s2 /\ term s2 = init s3 /\ term s3 = init s4
      /\ term s4 = init s5 /\ term s5 = init s6 /\ term s6 = init s7.
Proof.
  cut (proj1_sig example2 = example2_list); [|now idtac].
  intros e_proj1 emb.
  destruct(embed_scurve_inv_Cons _ _ _ _ _ emb e_proj1)
    as [s1 [s2 [ss' [c' [ess [e_proj1' [emb' [emb1 term_init1]]]]]]]].
  destruct(embed_scurve_inv_Cons _ _ _ _ _ emb' e_proj1')
    as [s2' [s3 [ss'' [c'' [ess' [e_proj1'' [emb'' [emb2 term_init2]]]]]]]].
  injection ess' as _es2' _ess'. subst.
  destruct(embed_scurve_inv_Cons _ _ _ _ _ emb'' e_proj1'')
    as [s3' [s4 [ss''' [c''' [ess'' [e_proj1''' [emb''' [emb3 term_init3]]]]]]]].
  injection ess'' as _es3' _ess''. subst.
  destruct(embed_scurve_inv_Cons _ _ _ _ _ emb''' e_proj1''')
    as [s4' [s5 [ss'''' [c'''' [ess''' [e_proj1'''' [emb'''' [emb4 term_init4]]]]]]]].
  injection ess''' as _es4' _ess'''. subst.
  destruct(embed_scurve_inv_Cons _ _ _ _ _ emb'''' e_proj1'''')
    as [s5' [s6 [ss''''' [c''''' [ess'''' [e_proj1''''' [emb''''' [emb5 term_init5]]]]]]]].
  injection ess'''' as _es5' _ess''''. subst.
  destruct(embed_scurve_inv_Cons _ _ _ _ _ emb''''' e_proj1''''')
    as [s6' [s7 [ss'''''' [c'''''' [ess''''' [e_proj1'''''' [emb'''''' [emb6 term_init6]]]]]]]].
  injection ess''''' as _es6' _ess'''''. subst.
  edestruct(embed_scurve_inv_Single _ _ _ emb'''''' e_proj1'''''')
             as [s7' [ess'''''' emb7]].
  injection ess'''''' as _es7' _ess''''''. subst.
  now exists s1, s2', s3', s4', s5', s6', s7'.
Qed.

Lemma example2_is_close: ~ admissible example2.
Proof.
  destruct 1 as [ds [emb nclose]].
  destruct (emb_example2 _ emb) as
    [s1 [s2 [s3 [s4 [s5 [s6 [s7 [eds [emb1 [emb2 [emb3 [emb4 [emb5 [emb6 [emb7 [terminit1 [terminit2 [terminit3 [terminit4 [terminit5 terminit6]]]]]]]]]]]]]]]]]]]].
  subst ds.
  apply nclose.
  change [s1; s2; s3; s4; s5; s6; s7] with ([s1; s2]++[s3; s4]++[s5;s6;s7]) in emb.
  assert (Halle03: all_same_h [s1; s2; s3] e).
    { constructor. discriminate. now repeat (constructor; eauto). }
  eapply all_e_swcc in emb as Hclose; try now auto.
  destruct Hclose as [Hclose | [overs4 [y2 [inseg [onseg [Hlts4y2 Hlts4over]]]]]];try now auto.
  change ([s1; s2]++[s3; s4]++[s5;s6;s7]) with ([] ++ [s1; s2; s3] ++ [s4] ++ s5::[s6;s7]) in emb.
  assert(_onExSegs5: onExtendSegment ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) s5 (term_x s4, term_y s4)).
    {simpl. unfold term_x, term_y. rewrite <- surjective_pairing. rewrite terminit4. apply OnSegMid;[discriminate | now right;right;right;right;left | apply onInit]. }
  assert (_onxhyh: exists xh yh, onExtendSegment ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) (head_seg [s1; s2; s3] default_segment) (xh,yh) /\ xh < term_x s5).
    {
      destruct (Rle_or_lt (term_x s5) (init_x s1)).
      - exists (term_x s5 - 1). change s1 with (head_seg ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) default_segment) in emb1. eapply extended_segment_init_e_ncc with (x1:= init_x s1) (y1:=init_y s1) in emb1.
        destruct emb1 as [yh [_onSeg _]]. exists yh. eapply OnSegHead in _onSeg. split;[|now lra]. eapply _onSeg. apply onseg_onhead. simpl. unfold init_x, init_y. rewrite <- surjective_pairing.  eapply onInit. now lra.
      - exists (init_x s1 - 1). change s1 with (head_seg ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) default_segment) in emb1. eapply extended_segment_init_e_ncc with (x1:= init_x s1) (y1:=init_y s1) in emb1.
        destruct emb1 as [yh [_onSeg _]]. exists yh. eapply OnSegHead in _onSeg. split;[|now lra]. eapply _onSeg. apply onseg_onhead. simpl. unfold init_x, init_y. rewrite <- surjective_pairing.  eapply onInit. now lra.
    }
  destruct _onxhyh as [xh [yh [_onxhyh Hlt]]].
  assert (_Hlts5s4s3: term_x s5 < term_x s4 < term_x (last [s1;s2;s3] default_segment)).
  {
    split.
    - erewrite x_consis with (s1:=s4). eapply w_end_relation. now eauto. now eauto.
    - simpl. erewrite x_consis with (s1:=s3). eapply w_end_relation. now eauto. now eauto.
  }
  assert (_H: In overs4 [s1; s2; s3] /\
    onExtendSegment ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) overs4 (term_x s4, y2) /\
    term_x s4 < term_x overs4 /\ term_y s4 < y2).
  {
    split;[|split; [|split]]; try now auto.
  }
  eapply under_all_e_aux_2 in emb as Hclose; try now eauto; now try lra. clear _H inseg onseg Hlts4y2 Hlts4over _onExSegs5 xh yh _onxhyh Hlt _Hlts5s4s3.
  destruct Hclose as [Hclose | [overs5 [y3 [inseg5 [onseg5 [Hlts5y3 Hlts5overs5]]]]]]; try now auto.
  (* ここからend_e_closeを使う準備 *)
  assert(overs5_e: exists v c, embed (v, e, c) overs5).
  {
    inversion Halle03 as [_notnil HForall]. eapply Forall_forall in HForall;[exact HForall|exact inseg5].
  }
  destruct overs5_e as [vs5 [cs5 overs5_e]].
  assert(Hxs5: exists xs6 ys6 ys6over ys6under, onExtendSegment ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) s6 (xs6, ys6) /\ onExtendSegment ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) overs5 (xs6, ys6over) /\ onExtendSegment ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) s5 (xs6, ys6under) /\ ys6under <= ys6 /\ xs6 <> init_x s6).
  {
    destruct (Rlt_or_le (term_x s6) (term_x overs5)) as [Hlts6 | Hltovers5].
    - destruct (Rlt_or_le (term_x s6) (init_x s5)) as [Hmins6 | Hmins5].
       (* 最小値はterm_x s6 *)
      + exists (term_x s6). 
        eapply e_exist_y_ex with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb6 as emb6';[| repeat ((try (now left)); right) |discriminate |apply Rlt_le;eapply e_end_relation;now eauto | now lra].
        destruct emb6' as [ys6 [_onExs6 Hleys6]]. exists ys6.
        eapply exist_between_x with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) (x:=term_x s6) (x1:=term_x s5) (x2:=term_x overs5) in onseg5; [|unfold term_x; erewrite <- surjective_pairing; eapply onTermEx | exact overs5_e |unfold term_x; rewrite terminit5; eapply Rlt_le; eapply e_end_relation; exact emb6 |now lra].
        destruct onseg5 as [ys6over _onExovers5]. exists ys6over.
        eapply w_exist_y_ex with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb5.
        * destruct emb5 as [y6under [_onExs5 Hley]]. exists y6under. repeat (split; try now eauto). unfold term_y in Hley. rewrite terminit5 in Hley. unfold init_y in Hleys6. now lra.  unfold not. intros Hcontra. apply eq_sym in Hcontra. eapply neq_init_term_x;[| now eauto]. now eauto.
        * repeat ((try (now left)); right).
        * discriminate.
        * rewrite terminit5. apply Rlt_le. eapply e_end_relation; exact emb6.
        * unfold term_x, init_x in Hmins6. unfold term_x. now lra.
      (* 最小値はinit_x s5 *)
      + exists (init_x s5).
        eapply e_exist_y_ex with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb6 as emb6';
          [ |
          repeat ((try (now left)); right) |
          discriminate |
          rewrite <- terminit5; apply Rlt_le; eapply w_end_relation; exact emb5 |
          unfold init_x, term_x in Hmins5; now lra].
        eapply exist_between_x with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) (x:=init_x s5) (x1:=term_x s5) (x2:=term_x overs5) in onseg5; 
          [ |
          unfold term_x; erewrite <- surjective_pairing; eapply onTermEx |
          exact overs5_e|
          unfold term_x; rewrite terminit5; eapply Rlt_le; unfold init_x; rewrite <- terminit5; eapply w_end_relation;now eauto |
          now lra].
        eapply w_exist_y_ex with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb5 as emb5'.
        * destruct emb6' as [ys6 [_onExs6 Hleys6]]. exists ys6.
          destruct onseg5 as [ys6over _onExovers5]. exists ys6over.
          destruct emb5' as [y6under [_onExs5 Hley]]. exists y6under.
          repeat (split; try now eauto). erewrite y_consis with (s2:= s6) in Hley. now lra. now auto. unfold not. intros Hcontra. apply eq_sym in Hcontra. erewrite <- x_consis in Hcontra. eapply neq_init_term_x;[| apply eq_sym; now eauto]. now eauto. now auto. 
        * repeat ((try (now left)); right).
        * discriminate.
        * apply Rlt_le. unfold init_x. eapply w_end_relation; exact emb5.
        * unfold term_x, init_x in Hmins5. unfold init_x. now lra.
    - destruct (Rlt_or_le (term_x overs5) (init_x s5)) as [Hminovers5 | Hmins5].
      (* 最小値はterm_x overs5 *)
      + exists (term_x overs5).
        eapply e_exist_y_ex with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb6 as emb6';
        [ |
        repeat ((try (now left)); right) |
        discriminate |
        unfold term_x in Hlts5overs5; rewrite terminit5 in Hlts5overs5; apply Rlt_le; exact Hlts5overs5 |
        unfold term_x in Hltovers5; now auto
        ].
        eapply w_exist_y_ex with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb5.
          * destruct emb6' as [ys6 [_onExs6 Hleys6]]. exists ys6.
            exists (term_y overs5).
            destruct emb5 as [y6under [_onExs5 Hley]]. exists y6under.
            repeat (split; try now eauto). unfold term_x, term_y. rewrite <- surjective_pairing. apply onTermEx. erewrite y_consis with (s2:= s6) in Hley. now lra. now auto. unfold init_x. rewrite <- terminit5. unfold term_x in *. now lra.
          * repeat ((try (now left)); right).
          * discriminate.
          * unfold term_x in *. now lra.
          * apply Rlt_le. unfold init_x in Hminovers5. now auto.
      (* 最小値はinit_x s5 *)
      + exists (init_x s5).
        eapply e_exist_y_ex with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb6 as emb6';
          [ |
          repeat ((try (now left)); right) |
          discriminate |
          rewrite <- terminit5; apply Rlt_le; eapply w_end_relation; exact emb5 |
          unfold init_x in Hmins5; unfold term_x in *; now lra].
        eapply exist_between_x with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) (x:=init_x s5) (x1:=term_x s5) (x2:=term_x overs5) in onseg5; 
          [ |
          unfold term_x; erewrite <- surjective_pairing; eapply onTermEx |
          exact overs5_e |
          unfold term_x; rewrite terminit5; eapply Rlt_le; unfold init_x; rewrite <- terminit5; eapply w_end_relation;now eauto |
          now lra].
        eapply w_exist_y_ex with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb5 as emb5'.
        * destruct emb6' as [ys6 [_onExs6 Hleys6]]. exists ys6.
          destruct onseg5 as [ys6over _onExovers5]. exists ys6over.
          destruct emb5' as [y6under [_onExs5 Hley]]. exists y6under.
          repeat (split; try now eauto). erewrite y_consis with (s2:= s6) in Hley. now lra. now auto. unfold not. intros Hcontra. apply eq_sym in Hcontra. erewrite <- x_consis in Hcontra. eapply neq_init_term_x;[|apply eq_sym; now eauto]. now eauto. now auto. 
        * repeat ((try (now left)); right).
        * discriminate.
        * apply Rlt_le. unfold init_x. eapply w_end_relation; exact emb5.
        * unfold term_x, init_x in Hmins5. unfold init_x. now lra.
  }
  destruct Hxs5 as [xs6 [ys6 [ys6over [ys6under Hxs5]]]].
  destruct (Rlt_or_le ys6 ys6over) as [Hltys6 | Hleys6over].
  destruct Hxs5 as [onEx1 [onEx2 [onEx3 [Hle Hneq]]]].
  destruct Hle as [Hlt | Hequnderys6].
  + eapply in_app_app in inseg5. destruct inseg5 as [l [le Heq]].
    assert(_Heq : ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) = (l ++ [overs5] ++ le ++ [s4] ++ [s5] ++ [] ++ [s6;s7])). repeat rewrite app_assoc. rewrite app_assoc in Heq. rewrite <- Heq. reflexivity.
    rewrite _Heq in emb.
    change ([s1; s2; s3; s4; s5; s6; s7]) with ([] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]).
    rewrite _Heq.
    eapply end_e_close.
    - now eauto.
    - erewrite last_app. erewrite <- Heq. reflexivity. simpl. discriminate.
    - simpl. reflexivity.
    - reflexivity.
    - exact emb3.
    - exact emb4.
    - unfold all_same_h. split;[discriminate|]. unfold all_same_h in Halle03. destruct Halle03 as [_ Halle03].
      rewrite Heq in Halle03. apply Forall_app in Halle03. now apply Halle03.
    - unfold all_same_h. split;[discriminate|]. constructor. now eauto. now eauto.
    - unfold all_same_h. split;[discriminate|]. constructor. now eauto. now eauto.
    - rewrite <- _Heq. now eauto.
    - rewrite <- _Heq. now eauto.
    - rewrite <- _Heq. now eauto.
    - now lra.
  + eapply have_two_same_point_ex_close with (i:=4%nat) (j:=5%nat).
    - discriminate.
    - reflexivity.
    - reflexivity.
    - exact onEx3.
    - eapply onTermEx.
    - rewrite Hequnderys6. exact onEx1.
    - rewrite terminit5. eapply onInitEx.
    - rewrite terminit5. unfold not. assert (_Heqinit: init s6 = (init_x s6, init_y s6)).
      {unfold init_x, init_y. rewrite <- surjective_pairing. reflexivity. }
      rewrite _Heqinit. intros Hcontra. injection Hcontra. contradiction.
  + destruct Hleys6over as [Hltys6over | Heqys6over].
    - eapply x_cross_h.
      * right;right;right;right;right;left. reflexivity.
      * change [s1; s2; s3; s4; s5; s6; s7] with ([s1;s2;s3] ++ [s4;s5;s6;s7]). apply in_or_app. left. exact inseg5.
      * erewrite <- surjective_pairing. now eapply onInitEx.
      * now apply Hxs5.
      * simpl in onseg5. unfold term_x in onseg5. rewrite terminit5 in onseg5. exact onseg5.
      * now apply Hxs5.
      * unfold term_y in Hlts5y3. rewrite terminit5 in Hlts5y3. apply Rmult_neg_pos;now lra.
    - change [s1; s2; s3; s4; s5; s6; s7] with ([s1;s2;s3] ++ [s4] ++ [s5;s6;s7]).
      eapply have_same_point_app_close.
      * exact inseg5.
      * right; now left.
      * now apply Hxs5.
      * rewrite Heqys6over. now apply Hxs5.
Qed.
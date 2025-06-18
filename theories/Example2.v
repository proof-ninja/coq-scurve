Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import PrimitiveSegment.
Require Import Main.
Require Import Lra.

Axiom x_consis: forall s1 s2, term s1 = init s2 -> term_x s1 = init_x s2.
Axiom y_consis: forall s1 s2, term s1 = init s2 -> term_y s1 = init_y s2.
Axiom neq_init_term_x : forall seg, init_x seg <> term_x seg.

Axiom exist_between_x: forall (ls: list Segment) (seg: Segment) (x1 x2 y1 y2 x: R),
    onExtendSegment ls seg (x1, y1) -> onExtendSegment ls seg (x2, y2) -> x1 <= x -> x <= x2 -> exists y:R, onExtendSegment ls seg (x, y).

Axiom onTermEx: forall (ls: list Segment) (seg: Segment), onExtendSegment ls seg (term seg).
Axiom onInitEx: forall (ls: list Segment) (seg: Segment), onExtendSegment ls seg (init seg).

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

Axiom under_all_e_aux:
  forall (sc: scurve) (ls1 lse ls2 ls3: list Segment) (under: Segment) (x1 xh y1 yh yl: R),
  let ls := (ls1 ++ lse ++ ls2 ++ (under :: ls3)) in
  embed_scurve sc ls
  -> all_same_h lse e
  -> onExtendSegment ls under (x1, y1)
  -> onExtendSegment ls (head_seg lse default_segment) (xh, yh)
  -> xh < x1 < term_x (last lse default_segment) /\ xh < term_x under < term_x (last lse default_segment)
  -> onExtendSegment ls (last lse default_segment) (x1, yl) /\ y1 < yl
  -> close ls \/ exists (seg:Segment) (y2:R), In seg lse /\ onExtendSegment ls seg (term_x under, y2) /\ term_y under < y2.


Lemma in_app_app: forall [A: Type] (ls: list A) (a: A) , In a ls -> exists ls1 ls2, ls = ls1 ++ [a] ++ ls2.
Proof.
  intros A ls. induction ls as [| a ls IHls].
  - contradiction.
  - intros a0 Hin. destruct Hin as [Heqa| Hin].
    + exists [], ls. simpl. rewrite Heqa. reflexivity.
    + apply IHls in Hin. destruct Hin as [ls1' [ls2' Heq]]. exists (a::ls1'), ls2'. rewrite Heq. reflexivity.
Qed.

Lemma last_app: forall [A:Type] (l r:list A) (d: A), r <> [] -> last r d = last (l ++ r) d.
Proof.
  intros A l r. revert l. induction r as [| a res IHr].
  - intros l d Hcontra. contradiction.
  - intros l d _. destruct res as [|a' res].
    + simpl. rewrite last_last. reflexivity.
    + assert(Heq: (l ++ a :: a' :: res) = ((l ++ [a]) ++ a' :: res )).
      { rewrite <- app_assoc. simpl. reflexivity. }
      rewrite Heq.
      assert(Heq2: last (a :: a' :: res) d = last (a' :: res) d). reflexivity.
      rewrite Heq2. apply IHr. discriminate.
Qed.

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
  -> close ls \/ exists (seg:Segment) (y2:R), In seg lse /\ onExtendSegment ls seg (term_x under, y2) /\ term_y under < y2.
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

Axiom under_all_e:
  forall (sc: scurve) (ls1 lse ls2 ls3: list Segment) (under segonx1: Segment) (x1 xh y1 yh yl: R),
  let ls := (ls1 ++ lse ++ ls2 ++ (under :: ls3)) in
  embed_scurve sc ls ->
  onExtendSegment ls under (x1, y1) ->
  all_same_h lse e ->
  onExtendSegment ls (head_seg lse default_segment) (xh, yh) ->
  xh < x1 < term_x (last lse default_segment) /\ xh < term_x under < term_x (last lse default_segment) ->
  In segonx1 lse /\ onExtendSegment ls segonx1 (x1, yl) /\ x1 < term_x segonx1 /\ y1 < yl ->
  close ls \/ exists (seg:Segment) (y2:R), In seg lse /\ onExtendSegment ls seg (term_x under, y2) /\ term_y under < y2 /\ term_x under < term_x seg.

(* example1~3に使いやすい形の補題 *)
Axiom all_e_swcc:
  forall (sc: scurve) (lse ls2: list Segment) (secx_seg swcc_seg: Segment),
  let ls := (lse ++ [secx_seg; swcc_seg] ++ ls2) in
  embed_scurve sc ls
  -> embed (s,e,cx) secx_seg /\ embed (s,w,cc) swcc_seg
  -> all_same_h (lse ++ [secx_seg]) e
  -> embed (n,e,cc) (head_seg (lse ++ [secx_seg]) default_segment) \/ embed (n,e,cx) (head_seg (lse ++ [secx_seg]) default_segment)
  -> close ls \/ exists (seg:Segment) (y2:R), In seg (lse ++ [secx_seg]) /\ onExtendSegment ls seg (term_x swcc_seg, y2) /\ term_y swcc_seg < y2 /\ term_x swcc_seg < term_x seg.


Axiom end_e_close: forall sc l s1 le secx_seg swcc_seg lw s2 r s3 ler x y1 y2 ymid,
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
  eapply under_all_e in emb as Hclose; try now eauto; now try lra. clear _H inseg onseg Hlts4y2 Hlts4over _onExSegs5 xh yh _onxhyh Hlt _Hlts5s4s3.
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
        eapply e_exist_y with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb6 as emb6';[| repeat ((try (now left)); right) |discriminate |apply Rlt_le;eapply e_end_relation;now eauto | now lra].
        destruct emb6' as [ys6 [_onExs6 Hleys6]]. exists ys6.
        eapply exist_between_x with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) (x:=term_x s6) (x1:=term_x s5) (x2:=term_x overs5) in onseg5; [|unfold term_x; erewrite <- surjective_pairing; eapply onTermEx |unfold term_x; rewrite terminit5; eapply Rlt_le; eapply e_end_relation; exact emb6 |now lra].
        destruct onseg5 as [ys6over _onExovers5]. exists ys6over.
        eapply w_exist_y with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb5.
        * destruct emb5 as [y6under [_onExs5 Hley]]. exists y6under. repeat (split; try now eauto). unfold term_y in Hley. rewrite terminit5 in Hley. unfold init_y in Hleys6. now lra.  unfold not. intros Hcontra. apply eq_sym in Hcontra. eapply neq_init_term_x. now eauto.
        * repeat ((try (now left)); right).
        * discriminate.
        * rewrite terminit5. apply Rlt_le. eapply e_end_relation; exact emb6.
        * unfold term_x, init_x in Hmins6. unfold term_x. now lra.
      (* 最小値はinit_x s5 *)
      + exists (init_x s5).
        eapply e_exist_y with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb6 as emb6';
          [ |
          repeat ((try (now left)); right) |
          discriminate |
          rewrite <- terminit5; apply Rlt_le; eapply w_end_relation; exact emb5 |
          unfold init_x, term_x in Hmins5; now lra].
        eapply exist_between_x with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) (x:=init_x s5) (x1:=term_x s5) (x2:=term_x overs5) in onseg5; 
          [ |
          unfold term_x; erewrite <- surjective_pairing; eapply onTermEx |
          unfold term_x; rewrite terminit5; eapply Rlt_le; unfold init_x; rewrite <- terminit5; eapply w_end_relation;now eauto |
          now lra].
        eapply w_exist_y with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb5.
        * destruct emb6' as [ys6 [_onExs6 Hleys6]]. exists ys6.
          destruct onseg5 as [ys6over _onExovers5]. exists ys6over.
          destruct emb5 as [y6under [_onExs5 Hley]]. exists y6under.
          repeat (split; try now eauto). erewrite y_consis with (s2:= s6) in Hley. now lra. now auto. unfold not. intros Hcontra. apply eq_sym in Hcontra. erewrite <- x_consis in Hcontra. eapply neq_init_term_x. apply eq_sym. now eauto. now auto. 
        * repeat ((try (now left)); right).
        * discriminate.
        * apply Rlt_le. unfold init_x. eapply w_end_relation; exact emb5.
        * unfold term_x, init_x in Hmins5. unfold init_x. now lra.
    - destruct (Rlt_or_le (term_x overs5) (init_x s5)) as [Hminovers5 | Hmins5].
      (* 最小値はterm_x overs5 *)
      + exists (term_x overs5).
        eapply e_exist_y with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb6 as emb6';
        [ |
        repeat ((try (now left)); right) |
        discriminate |
        unfold term_x in Hlts5overs5; rewrite terminit5 in Hlts5overs5; apply Rlt_le; exact Hlts5overs5 |
        unfold term_x in Hltovers5; now auto
        ].
        eapply w_exist_y with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb5.
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
        eapply e_exist_y with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb6 as emb6';
          [ |
          repeat ((try (now left)); right) |
          discriminate |
          rewrite <- terminit5; apply Rlt_le; eapply w_end_relation; exact emb5 |
          unfold init_x in Hmins5; unfold term_x in *; now lra].
        eapply exist_between_x with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) (x:=init_x s5) (x1:=term_x s5) (x2:=term_x overs5) in onseg5; 
          [ |
          unfold term_x; erewrite <- surjective_pairing; eapply onTermEx |
          unfold term_x; rewrite terminit5; eapply Rlt_le; unfold init_x; rewrite <- terminit5; eapply w_end_relation;now eauto |
          now lra].
        eapply w_exist_y with (ls := [] ++ [s1; s2; s3] ++ [s4] ++ [s5; s6; s7]) in emb5.
        * destruct emb6' as [ys6 [_onExs6 Hleys6]]. exists ys6.
          destruct onseg5 as [ys6over _onExovers5]. exists ys6over.
          destruct emb5 as [y6under [_onExs5 Hley]]. exists y6under.
          repeat (split; try now eauto). erewrite y_consis with (s2:= s6) in Hley. now lra. now auto. unfold not. intros Hcontra. apply eq_sym in Hcontra. erewrite <- x_consis in Hcontra. eapply neq_init_term_x. apply eq_sym. now eauto. now auto. 
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
From Stdlib Require Import Reals List.
Import ListNotations.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import Embed.

Hint Resolve onInit onTerm neq_init_term : core.
Hint Constructors is_scurve dc_pseg_hd dc: core.

Definition example3_list: list PrimitiveSegment :=
  [(n,e,cx); (s,e,cx); (s,w,cc); (n,w,cc); (n,w,cx)].
Lemma example3_scurve : is_scurve example3_list.
Proof. repeat constructor. Qed.

Definition example3 := exist _ example3_list example3_scurve.

Lemma emb_example3 ss : embed_scurve example3 ss -> exists s1 s2 s3 s4 s5,
      ss = [s1;s2;s3;s4;s5]
      /\ embed (n,e,cx) s1 /\ embed (s,e,cx) s2 /\ embed (s,w,cc) s3
      /\ embed (n,w,cc) s4 /\ embed (n,w,cx) s5
      /\ term s1 = init s2 /\ term s2 = init s3 /\ term s3 = init s4
      /\ term s4 = init s5.
Proof.
  cut (proj1_sig example3 = example3_list); [|now idtac].
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
  edestruct(embed_scurve_inv_Single _ _ _ emb'''' e_proj1'''')
             as [s5' [ess'''' emb5]].
  injection ess'''' as _es5' _ess''''. subst.
  now exists s1, s2', s3', s4', s5'.
Qed.


Lemma example3_is_close: ~ admissible example3.
Proof.
  destruct 1 as [ds [emb nclose]].
  destruct (emb_example3 _ emb) as
    [s1 [s2 [s3 [s4 [s5 [eds [emb1 [emb2 [emb3 [emb4 [emb5 [terminit1 [terminit2 [terminit3  terminit4]]]]]]]]]]]]]].
  subst ds.
  assert (ex_x: exists x y1 y2, onSegment s2 (x, y1) /\ onSegment s3 (x, y2) /\ y2 < y1).
  - destruct (init s2) as [ox oy] eqn:e_oxy. destruct (term s3) as [rx ry] eqn:e_rxy.
    destruct (e_onseg_relation _ _ _ ox oy emb2) as [le_ox1 le_ox2]; [now rewrite <- e_oxy|].
    destruct (w_onseg_relation _ _ _ rx ry emb3) as [le_rx1 le_rx2]; [now rewrite <- e_rxy |].
    destruct (Rle_or_lt ox rx) as [lex|ltx].
    + (* ox <= rx の場合: x=rx, y2=ryとする *)
      destruct (e_exist_y _ _ _ rx emb2) as [y1 [onSeg_y1 [le1 le2]]];
       [now rewrite e_oxy|now rewrite terminit2|].
      exists rx, y1, ry. rewrite <- e_rxy. repeat split; [assumption| now auto|].
        assert (eq_makes_close: ry = y1 -> close [s1; s2; s3; s4; s5]). {
           intros e_ry. apply (have_two_same_point_close s2 s3 1 2 (term s2) (rx,y1)); try now auto.
           ++ now rewrite terminit2.
           ++ now rewrite <- e_ry, <- e_rxy.
           ++ rewrite terminit2, <- e_ry, <- e_rxy. now apply neq_init_term.
        }
        destruct (Rle_lt_or_eq ry y1); try now tauto.
        apply Rle_trans with (snd (term s2)); [|now auto].
        destruct (s_onseg_relation _ _ _ rx ry emb3); [now rewrite <- e_rxy|].
        now rewrite terminit2.
    + (* ox > rx の場合: x=ox, y1=oyとする *)
      apply Rlt_le in ltx. destruct (w_exist_y _ _ _ ox emb3) as [y2 [onSeg_y2 [le1 le2]]];
        [now rewrite e_rxy|now rewrite <- terminit2|].
      exists ox, oy, y2. rewrite <- e_oxy. repeat split; [now auto|assumption |].
      assert (eq_makes_close: y2 = oy -> close [s1; s2; s3; s4; s5]). {
        intros e_oy. apply (have_two_same_point_close s2 s3 1 2 (term s2) (ox, y2)); try now auto.
        ++ now rewrite e_oy, <- e_oxy.
        ++ now rewrite terminit2.
        ++ now rewrite e_oy, <- e_oxy.
      }
      destruct (Rle_lt_or_eq y2 oy); try now tauto.
      apply Rle_trans with (snd (init s3)); [now auto |].
      destruct (s_onseg_relation _ _ _ ox oy emb2); [now rewrite<- e_oxy|].
      now rewrite <- terminit2.
  - destruct nclose. destruct ex_x as [x [y1 [y2 [onSeg2 [onSeg3 neq_y12]]]]].
    change [s1; s2; s3; s4; s5] with ([s1]++[s2]++[]++[s3]++[s4;s5]).
    eapply (end_nwcx_close example3 _ _ cx x y1 y2); try now auto.
    + (*往路は東へ行く*)
      now repeat constructor; [|exists n, cx|exists s, cx].
    + (*復路は東へ行く*)
      now repeat constructor; [| exists s, cc|exists n, cc | exists n, cx].
Qed.

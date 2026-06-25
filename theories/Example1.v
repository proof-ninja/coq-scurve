Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import Embed.
From Stdlib Require Import Lra.


Definition example1: list PrimitiveSegment := [(n,e,cx);(s,e,cx);(s,w,cc);(n,w,cc)].
Lemma example1_is_scurve: is_scurve example1.
Proof. repeat constructor. Qed.

Lemma example1_is_close: forall lp: scurve, proj1_sig lp = example1 -> ~ admissible lp.
Proof.
    intros lp.
    destruct lp as [l p].
    simpl.
    unfold example1.
    intros Hl.
    unfold admissible, not.
    intros Hclose.
    destruct Hclose as [ls [Hembed_ls Hclose]].
    destruct ls as [| s0].
    - inversion Hembed_ls as [Hnil | |]. rewrite Hl in Hnil. discriminate.
    - destruct ls as [| s1].
     -- inversion Hembed_ls as [|ps s1 Hembed0 Hcontra Hs10|]. rewrite Hl in Hcontra. discriminate.
     -- destruct ls as [| s2].
      --- inversion Hembed_ls as [| | ps0 lp H s2 s3 ls Hembed0 Hembedsc1 Hconsis01 Hps [H1 H2 H3]]. subst. inversion Hembedsc1 as [|ps1 s2 Hembed1 Hconnect1 H1|]. rewrite <- Hconnect1 in Hps. simpl in Hps. discriminate.
      --- destruct ls as [| s3].
       ---- inversion Hembed_ls as [| | ps0 lp H s3 s4 ls Hembed0 Hembedsc1 Hconsis01 Hps [H1 H2 H3]]. subst. inversion Hembedsc1 as [| | ps1 lp1 Hdc1 s3 s4 ls1 Hembed1 Hembedsc2 Hconsis12 Hconnect2 [H1 H2 H3]]. subst. inversion Hembedsc2 as [| ps2 s3 Hembed2 Hconnect2 H0|]. subst. simpl in *. discriminate.
       ---- destruct ls as [| overseg].
            * inversion Hembed_ls as [| |p0 scurve13 H s0' s1' ls Hembed0 Hembedsc13 Hconsis01 Hlcons [H1 H2 H3]]. subst.
              inversion Hembedsc13 as [| |p1 scurve23 Hdcpseg123 s1' s2' ls3 Hembed1 Hembedsc23 Hconsis12 Hconnect1 [H1 H2 H3]]. subst.
              inversion Hembedsc23 as [| |p2 scurve3 Hdcpseg23 s2' s3' ls'' Hembed2 Hembedsc3 Hconsis23 Hconnect2 [H1 H2 H3]]. subst.
              inversion Hembedsc3 as [| p3 s3' Hembed3 Hconnect3 H1| ].
              apply Hclose. subst.
              inversion Hlcons as [[H0 H1 H2 H3]].
              subst p0 p1 p2 p3.
              destruct (Rle_or_lt (fst (init s1)) (fst (term s2))) as [Hge | Hlt].
              + set (x1 := fst (init s3)).
              set (y1 := snd (init s3)).
              assert (Hxins1:fst (term s2) < fst (term s1)).
                {rewrite Hconsis12. apply w_end_relation with (s:=s2) (v:=s) (c:=cc). exact Hembed2. }
              assert (Hyins1: exists y:R, onSegment s1 (x1, y)).
                {
                    eapply e_exist_y_ex with (ls:= [s0;s1;s2;s3]) in Hembed1 as Hembed1'.
                        + destruct Hembed1' as [yy H']. exists yy. destruct H' as [HonEx _]. inversion HonEx as [headseg ls' rr _Hnotnil [_Hhead _Heqls'] Heqs1 _Hrr| ls s1' rr _Hnotnil _Hin HonSegs1 _Heq1 _Heq2 _Heq3 | ls' rr _Hnotnil _Hlast _Heq Heqs1 _Hrr]. simpl in Heqs1. eapply s_end_relation in Hembed1. rewrite <- Hconsis01 in Hembed1. rewrite Heqs1 in Hembed1. now lra. exact HonSegs1. simpl in Heqs1. eapply w_end_relation in Hembed3. eapply e_end_relation in Hembed1. rewrite Heqs1 in Hembed3. now lra.
                        + right; left; reflexivity.
                        + discriminate.
                        + unfold x1. rewrite <- Hconsis23. apply Hge.
                        + unfold x1. rewrite <- Hconsis23. apply Rlt_le. exact Hxins1.
                }
              destruct Hyins1 as [y2 HonSeg].
              eapply end_cross_term_nw with (ls1:=[s0;s1]) (x1:=x1) (y1:=y1).
                ++ simpl. exact Hembed_ls.
                ++ apply Rlt_le_trans with (r2 := snd (term s1)). unfold y1. rewrite <- Hconsis23. rewrite Hconsis12. apply s_end_relation with (s1:=s2) (h:=w) (c:=cc). apply Hembed2.
                    apply s_onseg_relation with (s1:=s1) (h:=e) (c:=cx) (x:=x1) (y:=y2). apply Hembed1. exact HonSeg.
                ++ unfold not.  intros Hcontra. discriminate.
                ++ simpl. exact Hembed0.
                ++ simpl. left. exact Hembed3.
                ++ simpl. unfold x1, y1. rewrite <- surjective_pairing with (p:=init s3). apply OnSegMid. discriminate. simpl. right;right;right;left. reflexivity. now apply onInit with (s:=s3).
                ++ simpl. apply OnSegMid. discriminate. right;left;reflexivity. exact HonSeg.
                ++ unfold all_same_h. split. unfold not; discriminate. econstructor 2. exists n,cx. exact Hembed0. econstructor 2. exists s,cx. exact Hembed1. now econstructor 1.

              + set (x1 := fst (init s1)).
              set (y1 := snd (init s1)).
              assert (Hxins1:fst (init s1) < fst (init s2)).
                {rewrite <- Hconsis12. apply e_end_relation with (s:=s1) (v:=s) (c:=cx). exact Hembed1. }
              assert (Hyins1: exists y:R, onSegment s2 (x1, y)).
                {
                    eapply w_exist_y_ex with (ls:= [s0;s1;s2;s3]) in Hembed2 as Hembed2'.
                    + destruct Hembed2' as [yy H']. exists yy. destruct H' as [HonEx _]. inversion HonEx as [ls' rr _Hnotnil _Hhead _Heq Heqs1 _Hrr| ls s1' rr _Hnotnil _Hin HonSegs1 _Heq1 _Heq2 _Heq3 | ls' rr _Hnotnil _Hlast _Heq Heqs1 _Hrr].
                      - simpl in Heqs1. eapply w_end_relation in Hembed2. eapply e_end_relation in Hembed0. rewrite <- Heqs1 in Hembed2. now lra.
                      - exact HonSegs1.
                      - simpl in Heqs1. eapply s_end_relation in Hembed2. rewrite Hconsis23 in Hembed2. rewrite Heqs1 in Hembed2. now lra.
                    + right; right; left; reflexivity.
                    + discriminate.
                    + unfold x1. apply Rlt_le. apply Hlt.
                    + unfold x1. apply Rlt_le. exact Hxins1.
                 }
              destruct Hyins1 as [y2 HonSeg].
              eapply end_cross_init_ne with (ls1 := [s0;s1]) (x1:=x1) (y1:=y1).
                ++ simpl. exact Hembed_ls.
                ++ apply Rle_lt_trans with (r2:= snd (term s1)). unfold y1. rewrite Hconsis12. apply s_onseg_relation with (s1:=s2) (h:=w) (c:=cc) (x:= x1) (y:=y2). apply Hembed2. apply HonSeg.
                    unfold y1. apply s_end_relation with (s1:=s1) (h:=e) (c:=cx). exact Hembed1.
                ++ discriminate.
                ++ simpl. right. exact Hembed0.
                ++ simpl. exact Hembed3.
                ++ simpl. unfold x1, y1. rewrite <- surjective_pairing. rewrite <- Hconsis01. now eapply onTerm.
                ++ exact HonSeg.
                ++ simpl. unfold all_same_h. split. discriminate. econstructor. exists n,cc. exact Hembed3. econstructor. exists s,cc. exact Hembed2. now auto.
            * inversion Hembed_ls as [| | ps lp H s4 s5 ls0 Hembed0 Hembedsc1 Hconsis01 Hlcons [H1 H2 H3]]. subst.
              inversion Hembedsc1 as [| | ps1 scurve2 Hdc1 s1' s2' ls0 Hembed1 Hembedsc2 Hconsis12 Hconnect1 [H1 H2 H3]]. subst.
              inversion Hembedsc2 as [| | ps2 scurve3 Hdc2 s2' s3' ls1 Hembed2 Hembedsc3 Hconsis23 Hconnect2 [H1 H2 H3]]. subst.
              inversion Hembedsc3 as [| |ps3 scurve4 Hdc3 s3' s4' ls2 Hembed3 Hembedsc4 Hconsis34 Hconnect3 [H1 H2 H3]]. subst. simpl in *.
              inversion Hlcons as [[Hps0 Hps1 Hps2 Hps3 Hsc4nil]].
              inversion Hembedsc4 as [| psov sov Hembedov Hconnectov [Hsov Hnil]| psov scov Hdcov sov' s4 ls0 Hembedov Hembedscov Hconsisov Hconnectov [H1 H2]].
            ** subst. simpl in *. discriminate.
            ** subst. discriminate.
Qed.

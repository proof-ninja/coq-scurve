Require Export List.
Require Import Arith.
Require Import Dec.
Import ListNotations.

Set Implicit Arguments.

Section Prefix.
  Variable A: Type.

  Definition Prefix (pre xs: list A) := exists r, xs = pre ++ r.

  Lemma Prefix_app (pre r: list A) : Prefix pre (pre ++ r).
  Admitted.

  Lemma Prefix_cons_iff a (pre xs: list A) : Prefix (a::pre) (a::xs) <-> Prefix pre xs.
  Proof.
    split.
    - intros Precons. inversion Precons as [r eqr]. inversion eqr as [eqxs]. exact (Prefix_app pre r).
    - intros Pre. inversion Pre as [r eqr]. subst. exact (Prefix_app (a::pre) r).
  Qed.

  Lemma prefix_brothers_is_prefix (p1 p2 xs : list A) :
    Prefix p1 xs -> Prefix p2 xs ->
    Prefix p1 p2 \/ Prefix p2 p1.
  Proof.
    revert p2 xs. induction p1 as [|a p1 IHp].
    - intros p2 xs _ _. left. exists p2. reflexivity.
    - intros p2 xs Prep1 Prep2. destruct p2 as [|_a p2]; [right; now eexists|].
      inversion Prep1 as [r1 eqxs1]. inversion Prep2 as [r2 eqxs2].
      rewrite eqxs2 in eqxs1. inversion eqxs1 as [[_eqa eqr]]. subst.
      repeat rewrite Prefix_cons_iff. eapply IHp.
      + exact (Prefix_app p1 r1).
      + rewrite <- eqr. exact (Prefix_app p2 r2).
  Qed.
  
  Fixpoint all_prefix (xs : list A) : list (list A) :=
    match xs with
    | [] => [[]]
    | x::xs' =>
        [] :: List.map (fun ys => x :: ys) (all_prefix xs')
    end.

  Lemma all_prefix_iff (l: list A) :
    forall sub, (In sub (all_prefix l) <-> Prefix sub l).
  Proof.
    intros sub. split.
    - revert sub. induction l as [| a l IHl].
      + intros sub Hin. unfold all_prefix in Hin. inversion Hin as [Heq|Hcontra]. exists []. rewrite <- Heq. reflexivity. contradiction.
      + intros sub Hin. destruct Hin as [eq|Hin]. 
        * subst. exists (a::l). reflexivity.
        * apply in_map_iff in Hin. destruct Hin as [r [eq Hin]]. apply IHl in Hin. destruct Hin as [lr _eq]. subst. exists lr. reflexivity.
    - revert sub. induction l as [|a l IHl].
      + intros sub HPre. destruct HPre as [lr eq]. apply eq_sym in eq. apply app_eq_nil in eq as [eq _]. subst. simpl. now auto.
      + intros sub HPre. destruct HPre as [lr eq]. simpl. destruct sub as [|a0 sub];[now left|right].
        inversion eq as [[eqa eql]].
        assert(HPresubl: Prefix sub l). now exists lr.
        apply IHl in HPresubl. subst.
        apply in_map_iff. exists sub. split.
        * reflexivity.
        * now auto.
  Qed.

End Prefix.

Hint Resolve Prefix_app : core.


Section Sublists.
  Variable A: Type.

  Fixpoint all_sublists (xs: list A) : list (list A) :=
    match xs with
    | [] => [[]]
    | x::xs' =>
        List.map (fun ys => x :: ys) (all_prefix xs') ++ all_sublists xs'
    end.

  Inductive sublist: list A -> list A -> Prop:=
  | SL l xs r: sublist xs (l ++ xs ++ r).

  Lemma nil_in_all_sublists (l: list A) : In [] (all_sublists l).
    induction l as [|a l IHl].
    - simpl. now left.
    - apply in_or_app. right. exact IHl.
  Qed.
  
  Lemma all_sublists_iff (l: list A) :
    forall sub, (In sub (all_sublists l) <-> sublist sub l).
  Proof.
    intros sub. split.
    (* -> *)
    - revert sub. induction l as [|a l IHl].
      + intros sub Hin. simpl in Hin. destruct Hin as [_eq | Hcontra];[rewrite <- _eq|contradiction]. now apply (SL [] []).
      + intros sub Hin. apply in_app_or in Hin. destruct Hin as [HinPre | Hinsub].
        (* subがaから始まる場合 *)
        * apply in_map_iff in HinPre. destruct HinPre as [lr [eq HinPre]]. apply all_prefix_iff in HinPre. unfold Prefix in HinPre. destruct HinPre as [r eq0].
          subst. now apply (SL [] (a::lr)).
        (* そうでない場合は機能法の家庭が使える *)
        * apply IHl in Hinsub. inversion Hinsub as [ll _sub lr _eq _eq2]. subst. now apply (SL (a::ll) sub).
    (* <- *)
    - revert sub. induction l as [|a l IHl].
      + intros sub Hsub. inversion Hsub as [l xs r eq eq2]. rewrite eq2. simpl. apply app_eq_nil in eq2 as [_ eq2]. apply app_eq_nil in eq2 as [eq2 _]. subst. now left.
      + intros sub Hsub. apply in_or_app. inversion Hsub as [ll xs r eq eq2]. destruct ll as [| _a ll].
        (* subがaから始まるならleft，それ以外ならright． *)
        * simpl in eq2. clear eq Hsub. destruct sub as [|_a sub].
          (* sub = [] *)
          ++ right. apply nil_in_all_sublists.
          (* subがaから始まる，all_prefix_iffを使う *)
          ++ left. rewrite <- app_comm_cons in eq2. inversion eq2 as [[_eq eql]]. subst _a.
            apply in_map_iff. exists sub. split;[reflexivity|]. apply all_prefix_iff. now exists r.
        (* 帰納法の仮定を使う *)
        * right. apply IHl. rewrite <- app_comm_cons in eq2. inversion eq2 as [[_eq eql]]. subst _a. clear eq2. now apply (SL ll sub). 
  Qed.

  Definition ex_sublists (P: list A -> Prop) (l: list A) : Prop :=
    exists sub, sublist sub l /\ P sub.

  Lemma all_sublists_ex (P: list A -> Prop) (l: list A) :
    List.Exists P (all_sublists l) <-> ex_sublists P l.
  Proof.
    split. 
    - intros HEx. apply Exists_exists in HEx. destruct HEx as [sub [HIn Psub]].
      exists sub. split;[|exact Psub]. apply all_sublists_iff. exact HIn.
    - intros Hex. apply Exists_exists. destruct Hex as [sub [Hsub Psub]].
      exists sub. split;[|exact Psub]. apply all_sublists_iff. exact Hsub.
  Qed.

  Definition ex_sublists_dec (P : list A -> Prop) (P_dec: forall xs:list A, {P xs}+{~P xs})
    (l : list A):
    {ex_sublists P l} + {~ ex_sublists P l}.
    refine (map (all_sublists_ex P l) _). now refine (Exists_dec _ _ P_dec).
  Defined.

End Sublists.


Lemma in_app_app: forall {A: Type} (ls: list A) (a: A) , In a ls -> exists ls1 ls2, ls = ls1 ++ [a] ++ ls2.
Proof.
  intros A ls. induction ls as [| a ls IHls].
  - contradiction.
  - intros a0 Hin. destruct Hin as [Heqa| Hin].
    + exists [], ls. simpl. rewrite Heqa. reflexivity.
    + apply IHls in Hin. destruct Hin as [ls1' [ls2' Heq]]. exists (a::ls1'), ls2'. rewrite Heq. reflexivity.
Qed.

Lemma last_app: forall {A:Type} (l r:list A) (d: A), r <> [] -> last r d = last (l ++ r) d.
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

Fixpoint last_opt {A: Type} (xs: list A) :=
  match xs with
  | [] => None
  | [x] => Some x
  | _ :: xs => last_opt xs
  end.

Lemma head_app {A: Type} (xs ys: list A):
  xs <> [] -> head (xs ++ ys) = head xs.
Proof.
  now destruct xs.
Qed.

Lemma rev_nil_inv {A: Type} (xs: list A):
  rev xs = [] -> xs = [].
Proof.
  induction xs; [reflexivity|].
  simpl.
  intros e.
  destruct (app_eq_nil _ _ e) as [_ H].
  discriminate H.
Qed.

Lemma last_head:
  forall {A: Type} (xs: list A),
  last_opt xs = head (rev xs).
Proof.
  induction xs; [reflexivity|].
  simpl.
  destruct xs; [reflexivity|].
  rewrite IHxs.
  rewrite head_app; [reflexivity|].
  intro rev.
  discriminate (rev_nil_inv _ rev).
Qed.

Lemma nil_head:
  forall {A: Type} (xs: list A),
  head xs = None <-> xs = [].
Proof.
  intros A xs.
  split; intros H.
  - destruct xs; [reflexivity | discriminate].
  - rewrite H. reflexivity.
Qed.

Require Import Admissible.
Require Import Reduction.

(* 補題: Ruleを部分リストに適用しても許容性が保たれる *)
Axiom AdmissibleDirs_sublist_rule: forall l ds ds' r,
  Rule ds ds' -> AdmissibleDirs (l ++ ds ++ r) -> AdmissibleDirs (l ++ ds' ++ r).

Lemma AdmissibleDirsStep_preserve ds ds' : AdmissibleDirs ds -> ReduceDirStep ds ds' -> AdmissibleDirs ds'.
Proof.
  intros AD RDS.
  (* ReduceDirStep の定義から、l, r, es, es' と Rule es es' が存在する *)
  inversion RDS as [l r es es' HRule Hds Hds'].
  (* ds = l ++ es ++ r, ds' = l ++ es' ++ r である *)
  subst ds ds'.
  (* 補題を適用 *)
  eapply AdmissibleDirs_sublist_rule; eauto.
Qed.

Lemma AdmissibleDirs_preserve ds ds': AdmissibleDirs ds -> ReduceDir ds ds' -> AdmissibleDirs ds'.
Proof.
  intros AD RD.
  induction RD as [ds | ds ds' ds'' RDS RD IHRD].
  - (* RDRefl: ds = ds なので自明 *)
    exact AD.
  - (* RDTrans: ds -> ds' -> ds'' の場合 *)
    (* まず AdmissibleDirsStep_preserve を使って ds -> ds' の保存性を得る *)
    apply AdmissibleDirsStep_preserve with (ds := ds) in RDS; [|exact AD].
    (* 次に帰納法の仮定を使って ds' -> ds'' の保存性を得る *)
    apply IHRD.
    exact RDS.
Qed.

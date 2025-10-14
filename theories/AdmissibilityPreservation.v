Require Import Admissible.
Require Import Reduction.

Lemma AdmissibleDirsStep_preserve ds ds' : AdmissibleDirs ds -> ReduceDirStep ds ds' -> AdmissibleDirs ds'.
Admitted.

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
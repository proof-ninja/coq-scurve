# Formalization of Admissibility of Qualitatively Represented Curves using Rocq

This repository formalizes and proves the Admissibility condition in Takahashi's theory of Qualitatively Represented Curve using the formal verification tool Rocq Prover.

## Abstract

This project formalizes definitions and corollaries/theorems on Admissibility of trajectories in QRC in Rocq's proof environment.
This gives a mechanical justification guarantee to the theory of QRC, which is spoken geometrically.

## Documentation

[HTML rendering of the source code](https://proof-ninja.github.io/rocq-scurve/) (using [`rocqnavi`](https://github.com/affeldt-aist/rocqnavi)).

## Requirement

- [opam](https://opam.ocaml.org/doc/Install.html)
- [Rocq prover](https://rocq-prover.org/install)

## How to Build

```
./configure.sh
make
```

## Correspondence with the Paper
| Term | Term in Japanese | Paper (Japanese one) | Related Rocq Code |
| ---- | ---- | ---- | ---- |
| primitive segment | 単位セグメント | Sec 2.1 | PrimitiveSegment.PrimitiveSegment |
| segment | セグメント | Sec 2.1 | Segment.Segment |
| directly connectable | 直接連結可能 | Def.2 | PrimitiveSegment.dc |
| scurve | | Sec 2.2 | PrimitiveSegment.scurve |
| embedding | 埋め込み | Def.5 | Embed.embed, Embed.embed_scurve |
| closed embedding | 閉埋め込み | Def.6 | Segment.close |
| admissible | 許容可能 | Def.7 | Embed.admissible, Admissible.AdmissibleDirs |
| orientation | 向き | Def.8 | Reduction.orn, Reduction.Reduce |
| reduction | 簡約 | Sec 3.3 | Reduction.ReduceDir |
| reduced form | 簡約形 | Def.11 | Admissible.reduced |
| termination | 簡約は停止する | Prop.2(1) | Reduction.termination |
| rotation diffrence preservation | 簡約は回転差を保つ | Prop.2(2) | Reduction.rotation_difference_preservation |
| the explicit forms of the reduced forms | 簡約形の具体的な形 | Prop.2(3) | Reduction.reduced_form |
| local confluence | 簡約は局所合流性を持つ | NOT valid (cf. Example.5) | Reduction.ReduceDir_local_confluence |
| admissibility preservation (r1) | 簡約 (r1) は許容可能性を保つ | Prop.3 | AdmissibilityPreservation.AdmissibleDirs_r1_Plus, etc. |
| admissibility preservation (r2) | 簡約 (r2) は許容可能性を保つ | Prop.4 | AdmissibilityPreservation.AdmissibleDirs_r2_Plus, etc. |
| admissibility preservation | 簡約前後で許容可能性は保存される | Th.1 | AdmissibilityPreservation.AdmissibleDirs_preserve |
| admissibility of reduced form | 各簡約形の許容可能性 | Sec 4.1-4.7 | (AdmissibilityPreservation.all_admissibles_quotient) |
| judgment of admissibility | 許容可能性の判定法 | Th.2 |  |

## References

* Takahashi, K.: "[Reasoning about the Embedded Shape of a Qualitatively Represented Curve](https://ist.ksc.kwansei.ac.jp/~ktaka/LABO/DRAFTS/SCSS2024takahashi.pdf)," SCSS 2024 WIP: 10th International Symposium on Symbolic Computation in Software Science - Work in Progress Workshop, pp.113-118, ISSN: 1613-0073, CEUR Workshop Proceedings, August, 2024.
* 高橋和子: "[曲線の定性的扱いと自己交差性の判定](https://ist.ksc.kwansei.ac.jp/~ktaka/LABO/DRAFTS/PRO2024takahashi.pdf)," 情報処理学会第149回PRO研究会資料, June, 2024. 

import Statement

/-! # The statement that comparator checks

The paper's main theorem (`paper/paper.tex`, `thm:main`, "Almost-everywhere near-cubic constant-error hardness"),
stated from `Statement.lean` and Mathlib alone: `NearCubicGates.Close.FinalStatement` says that the nine published
inputs (the fields of `NearCubicGates.Close.NineInputs`, each defined in `Statement.lean`) imply
`NearCubicGates.Target.MainStatement`.

The proof is left open on purpose. `comparator` (`make comparator`; README) checks that `Solution.lean` proves exactly
this statement. `Check.lean` does not import this file, and `make` does not build it. -/

set_option warningAsError false

theorem NearCubicGates.Close.Release.main_theorem : NearCubicGates.Close.FinalStatement :=
  sorry

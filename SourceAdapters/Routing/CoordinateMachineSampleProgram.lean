import SourceAdapters.Routing.CoordinateMachineStored

/-!
The construction in `lem:generator`: evaluate the annihilator and current coordinate row at
the next monomial basis element. Both stored-evaluator calls are actual code.
-/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open ShortPCP.Machines.FL

def sampleProgram : S :=
  .seq (.set 27 (.shl (.k 1) (.v 24)))
    (.seq (.set 35 (.add (.v 24) (.k 1)))
      (.seq (evalStored 25 28) (.seq (.set 35 (.v 24)) (evalStored 26 29))))

def sampleWrites : List Var := [27, 28, 29, 35, 40, 41, 42, 44, 45, 46]

theorem sample_wellFormed (d : ℕ) (hd : d ≤ 7) : wfS sampleProgram d = true := by
  simp [sampleProgram, evalStored, wfS, dE, CoordinateMachineEval.wellFormed_depth d hd]

theorem sample_inputFree : inputFree sampleProgram = true := by decide

theorem sample_cost_eq (G : Glob) :
    costS G sampleProgram = 2 * opc G + 174 + 2 * G.N * (7 * opc G + 57) := by
  simp only [sampleProgram, evalStored, costS, costE, CoordinateMachineEval.cost_eq]
  ring

theorem sample_cost_le (G : Glob) :
    costS G sampleProgram ≤ 15000 * (G.K + 1) ^ 3 * (G.N + 1) := by
  rw [sample_cost_eq]
  have hp : 1 ≤ (G.K + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hb : 7 * opc G + 57 ≤ 6000 * (G.K + 1) ^ 3 := by unfold opc; omega
  have hm := Nat.mul_le_mul_left (2 * G.N) hb
  unfold opc at *
  nlinarith

theorem sample_compiled {C : NearCubicGates.Close.Cells.Ctx} {G : Glob} (hg : GOk C G) :
    SOk C G sampleProgram := by
  have hc (src dst : Var) : SOk C G (evalStored src dst) :=
    seq_ok (set_ok hg _ _) (seq_ok (set_ok hg _ _) (seq_ok (set_ok hg _ _)
      (seq_ok (CoordinateMachineEval.compiled hg) (set_ok hg _ _))))
  exact seq_ok (set_ok hg _ _) (seq_ok (set_ok hg _ _)
    (seq_ok (hc 25 28) (seq_ok (set_ok hg _ _) (hc 26 29))))

end NearCubicGates.Adapters.Routing.CoordinateMachine

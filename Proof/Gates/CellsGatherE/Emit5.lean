import Proof.Gates.CellsGatherE.Emit4
import Proof.Gates.CellsSys.Asm
import Proof.Gates.Cells.Width
import Proof.Gates.Cells.CellLoop2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

def emitP (qP : St VV MM) : St VV MM :=
  .seq cstE (.seq cntE (.seq (.op (.rwM sG)) (.seq tabE (.seq qP padE))))

noncomputable def emitCost (qCost : Ctx → Call → Params → ℕ → ℕ) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  100000 * ((reqIds c p).length + wWin p ^ nDig c p + 1) * (c.n + 2) ^ 10 + qCost C c p Big

theorem emitCost_class_of (qCost : Ctx → Call → Params → ℕ → ℕ) (hq : QryClass qCost) :
    GatherPhase.EmitClass (emitCost qCost) := by
  obtain ⟨K, e, hK⟩ := hq
  refine ⟨100000 + K, 10 + e, fun C c p Big => ?_⟩
  have h := hK C c p Big
  unfold emitCost
  set A := (reqIds c p).length + wWin p ^ nDig c p + 1
  set Y := c.n + Big + C.Wd + 2
  have hY1 : 1 ≤ Y := by omega
  have h1 : (c.n + 2) ^ 10 ≤ Y ^ (10 + e) :=
    (Nat.pow_le_pow_left (by omega) 10).trans (Nat.pow_le_pow_right hY1 (by omega))
  have h2 : Y ^ e ≤ Y ^ (10 + e) := Nat.pow_le_pow_right hY1 (by omega)
  have h3 : 100000 * A * (c.n + 2) ^ 10 ≤ 100000 * A * Y ^ (10 + e) := Nat.mul_le_mul_left _ h1
  have h4 : K * A * Y ^ e ≤ K * A * Y ^ (10 + e) := Nat.mul_le_mul_left _ h2
  calc 100000 * A * (c.n + 2) ^ 10 + qCost C c p Big ≤ 100000 * A * Y ^ (10 + e) + K * A * Y ^ (10 + e) := by omega
    _ = (100000 + K) * A * Y ^ (10 + e) := by ring

theorem gs_cstT : ∀ y ∈ cstT, gScratch y := by unfold gScratch; decide
theorem gs_cntT : ∀ y ∈ cntT, gScratch y := by unfold gScratch; decide
theorem gs_tabT : ∀ y ∈ tabT, gScratch y := by unfold gScratch; decide
theorem gs_padT : ∀ y ∈ padT, gScratch y := by unfold gScratch; decide

theorem not_mem_of_gs {T : List (Fin VV)} (hT : ∀ y ∈ T, gScratch y) {x : Fin VV} (hx : ¬ gScratch x) : x ∉ T :=
  fun h => hx (hT x h)

theorem rowKeys_len (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) :
    (GatherPhase.rowKeys c p wt y).length = (rowVals c p wt y).length := by
  unfold GatherPhase.rowKeys rowVals
  simp only [List.length_flatMap, List.length_map]

end NearCubicGates.Close.Cells.RecordEmission

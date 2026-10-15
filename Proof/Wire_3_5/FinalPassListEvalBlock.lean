import Proof.Wire_3_5.FinalPassListEvalMain
import Proof.Wire_3_5.BlockCost

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block

section
variable (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (L s : ℕ)

/-- The register capacity for points of length `L`. -/
def stage5Cap : ℕ := capOf M J W row L

/-- **The stage-5 machine** (one for every table, point and state). -/
def stage5Machine : Machine (2 + 17) main.toProg.size := main.toProg.compile

/-- The evaluator's own tapes: the table word, the compared state, 15 blank registers. -/
def stage5Data : Fin 17 → List Bool := fun i =>
  if i.val = 0 then levelWord M J W row
  else if i.val = 1 then unary s
  else regTape (stage5Cap M J W row L) 0

/-- One step bound for every point of length `L`. -/
def stage5Cost : ℕ := mainCost (stage5Cap M J W row L)

/-- The description size: the table word and the point. -/
def stage5Size : ℕ := (levelWord M J W row).length + L

end

theorem enc_blank_H (inp : Fin 3 → List Bool) (cap : ℕ) (b : Bool) : (enc inp cap (blank b)).H = fun _ => 0 := by
  funext j
  simp only [enc, blank]
  split <;> rfl

theorem enc_blank_A (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) (b : Bool) :
    (enc (streams M J W row Z s) (capOf M J W row Z.length) (blank b)).A =
      (Fin.addCases (m := 2) (n := 17) ![frame Z, [b]] (stage5Data M J W row Z.length s) : Fin (2 + 17) → List Bool) := by
  funext j
  fin_cases j <;> rfl

theorem stage5_step (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (L s : ℕ)
    (hrows : ∀ j ≤ J, (row j).length = L) (hs : s ≤ M) (Z : List Bool) (b : Bool) (hZ : Z.length = L) :
    Step (stage5Machine) (stage5Cost M J W row L) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 17) ![frame Z, [b]] (stage5Data M J W row L s)) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 17) ![frame Z, [decide (reportRef M J W row Z = s)]] (stage5Data M J W row L s)) := by
  subst hZ
  have h := (RExec.exec _ _ (main_spec M J W row Z s b hrows hs)).step
  rw [enc_blank_H, enc_blank_H, enc_blank_A, enc_blank_A] at h
  exact h

/-- The step bound is cubic in the description size. -/
theorem stage5_cost_le (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (L : ℕ) :
    stage5Cost M J W row L ≤ 36450 * stage5Size M J W row L ^ 3 := by
  have hB1 : 1 ≤ (levelWord M J W row).length := by have := word_M_le M J W row; unfold wordLen at this; omega
  unfold stage5Cost mainCost stage5Cap capOf stage5Size
  generalize (levelWord M J W row).length = B at hB1
  have h9 : 4 * (B + L + 1) + 1 ≤ 9 * (B + L) := by omega
  calc 50 * (4 * (B + L + 1) + 1) * (4 * (B + L + 1) + 1) * (4 * (B + L + 1) + 1)
      ≤ 50 * (9 * (B + L)) * (9 * (B + L)) * (9 * (B + L)) := by gcongr
    _ = 36450 * (B + L) ^ 3 := by ring

/-- **The step bound is within every budget class of degree at least 3** at the description size. -/
theorem stage5_within {E : Envelope} {cls : BudgetClass} {k psi : ℕ} (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool)
    (L : ℕ) (hq : 1 ≤ stage5Size M J W row L) (hd : 3 ≤ classDeg E cls) :
    Within E cls 36450 (stage5Size M J W row L) k psi (stage5Cost M J W row L) :=
  Within.of_poly hq (stage5_cost_le M J W row L) hd

end NearCubicWires.WireExponent3_5.FinalPass.ListEval

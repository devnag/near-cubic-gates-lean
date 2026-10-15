import Proof.CaseAnalysis.FinalWorkerDockSeam

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10CallCountMajorant

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The scalar width -/

theorem sumWidth_mono (k : ℕ) {c c' : ℕ} (h : c ≤ c') :
    CompetitorSumWidth.width c k ≤ CompetitorSumWidth.width c' k := by
  unfold CompetitorSumWidth.width
  exact Nat.mul_le_mul_right _ (by omega)

/-- The join width is monotone in the call count. -/
theorem joinScalarWidth_mono (entryWidth : ℕ) {c c' : ℕ} (h : c ≤ c') :
    joinScalarWidth entryWidth c ≤ joinScalarWidth entryWidth c' := by
  unfold joinScalarWidth
  exact sumWidth_mono _ h

/-! ## §2 The stage budgets -/

theorem capacity_mono {b b' : ℕ} (h : b ≤ b') :
    CompetitorReusableDecision.capacity b ≤ CompetitorReusableDecision.capacity b' := by
  unfold CompetitorReusableDecision.capacity
  have : (b + 1) ^ 2 ≤ (b' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem sumFold_bodyBudget_mono {b b' : ℕ} (h : b ≤ b') :
    CompetitorSumFold.bodyBudget b ≤ CompetitorSumFold.bodyBudget b' := by
  unfold CompetitorSumFold.bodyBudget
  have : (b + 1) ^ 2 ≤ (b' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem sumFold_loopBudget_mono {b b' n n' : ℕ} (hb : b ≤ b') (hn : n ≤ n') :
    CompetitorSumFold.loopBudget b n ≤ CompetitorSumFold.loopBudget b' n' := by
  unfold CompetitorSumFold.loopBudget
  have hbody := sumFold_bodyBudget_mono hb
  exact Nat.add_le_add_right (Nat.mul_le_mul hn (by omega)) 3

theorem sumEntry_budget_mono {b b' n n' : ℕ} (hb : b ≤ b') (hn : n ≤ n') :
    CompetitorSumEntry.budget b n ≤ CompetitorSumEntry.budget b' n' := by
  unfold CompetitorSumEntry.budget
  have h1 := sumFold_loopBudget_mono hb hn
  have h2 := capacity_mono hb
  omega

theorem monomial_bodyBudget_mono {t t' : ℕ} (h : t ≤ t') :
    CompetitorMonomialStream.bodyBudget t ≤ CompetitorMonomialStream.bodyBudget t' := by
  unfold CompetitorMonomialStream.bodyBudget
  have : (t + 1) ^ 2 ≤ (t' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem monomial_loopBudget_mono {t t' n n' : ℕ} (ht : t ≤ t') (hn : n ≤ n') :
    CompetitorMonomialStream.loopBudget t n ≤ CompetitorMonomialStream.loopBudget t' n' := by
  unfold CompetitorMonomialStream.loopBudget
  have hbody := monomial_bodyBudget_mono ht
  exact Nat.add_le_add_right (Nat.mul_le_mul hn (by omega)) 3

theorem monomialEntry_budget_mono {t t' n n' : ℕ} (ht : t ≤ t') (hn : n ≤ n') :
    CompetitorMonomialEntry.budget t n ≤ CompetitorMonomialEntry.budget t' n' := by
  unfold CompetitorMonomialEntry.budget
  have h1 := monomial_loopBudget_mono ht hn
  have h2 := capacity_mono ht
  omega

theorem readyBudget_mono {t t' n n' : ℕ} (ht : t ≤ t') (hn : n ≤ n') :
    CompetitorMonomialEntry.readyBudget t n ≤ CompetitorMonomialEntry.readyBudget t' n' := by
  unfold CompetitorMonomialEntry.readyBudget
  have h := monomialEntry_budget_mono ht hn
  omega

/-- **The docked body's budget is monotone in the call count.** -/
theorem dockBudget_mono (entryWidth : ℕ) {c c' : ℕ} (h : c ≤ c') :
    dockBudget entryWidth c ≤ dockBudget entryWidth c' := by
  unfold dockBudget
  have hw := joinScalarWidth_mono entryWidth h
  have h1 := readyBudget_mono hw h
  have h2 := sumEntry_budget_mono hw h
  omega

/-! ## §3 The record appender's budget -/

theorem unaryProduct_budget_mono {d d' e e' : ℕ} (hd : d ≤ d') (he : e ≤ e') :
    WilliamsUnaryProduct.budget d e ≤ WilliamsUnaryProduct.budget d' e' := by
  unfold WilliamsUnaryProduct.budget
  have : d * (2 * e + 3) ≤ d' * (2 * e' + 3) := Nat.mul_le_mul hd (by omega)
  omega

theorem dimensions_budget_mono {b b' : ℕ} (h : b ≤ b') :
    CompetitorDimensions.budget b ≤ CompetitorDimensions.budget b' := by
  unfold CompetitorDimensions.budget CompetitorDimensions.bootstrapBudget
  have h1 := unaryProduct_budget_mono (d := b + 1) (d' := b' + 1) (e := b + 1) (e' := b' + 1)
    (by omega) (by omega)
  have h2 := unaryProduct_budget_mono (d := b + 1) (d' := b' + 1) (e := 2) (e' := 2)
    (by omega) (by omega)
  have hsq : (b + 1) * (b + 1) ≤ (b' + 1) * (b' + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 := unaryProduct_budget_mono (d := (b + 1) * (b + 1)) (d' := (b' + 1) * (b' + 1))
    (e := 4096) (e' := 4096) hsq (by omega)
  omega

theorem prepare_budget_mono {b b' : ℕ} (h : b ≤ b') :
    CompetitorCountRecordPrepare.budget b ≤ CompetitorCountRecordPrepare.budget b' := by
  unfold CompetitorCountRecordPrepare.budget CompetitorRationalDecision.width
  have h1 := dimensions_budget_mono h
  omega

/-- **The emitter's budget is monotone in the scalar width.** -/
theorem append_budget_mono {b b' : ℕ} (h : b ≤ b') :
    CompetitorCountRecordAppend.budget b ≤ CompetitorCountRecordAppend.budget b' := by
  unfold CompetitorCountRecordAppend.budget
  have h1 := prepare_budget_mono h
  omega

/-! ## §4 The whole body fuel -/

/-- **The body's fuel is monotone in the call count**, at every input length and
for every loader/emitter fuel.  This is the inequality `stepAtInputs_mono` needs. -/
theorem fullBodyFuel_mono (loaderFuel emitFuel : ℕ → ℕ) (entryWidth : ℕ)
    {c c' : ℕ} (h : c ≤ c') (n : ℕ) :
    fullBodyFuel loaderFuel emitFuel entryWidth c n ≤
      fullBodyFuel loaderFuel emitFuel entryWidth c' n := by
  unfold fullBodyFuel
  have h1 := dockBudget_mono entryWidth h
  have h2 := append_budget_mono (joinScalarWidth_mono entryWidth h)
  omega

theorem workerBudget_mono (onset : ℕ) (fuel fuel' : ℕ → ℕ) (len : ℕ)
    (h : fuel len ≤ fuel' len) :
    workerBudget onset fuel len ≤ workerBudget onset fuel' len := by
  unfold workerBudget
  omega

/-- **The majorant, as `stepAtInputs_mono` consumes it.**  If a `len`-determined
`K` caps the call count at every witness, then the worker's budget at the ACTUAL
call count is below the worker's budget at `K len`, which is one function of
`len` alone. -/
theorem staged_le_majorant (onset : ℕ) (loaderFuel emitFuel : ℕ → ℕ) (entryWidth : ℕ)
    (K : ℕ → ℕ) (len callCount : ℕ) (hcap : callCount ≤ K len) :
    workerBudget onset (fullBodyFuel loaderFuel emitFuel entryWidth callCount) len ≤
      workerBudget onset (fullBodyFuel loaderFuel emitFuel entryWidth (K len)) len :=
  workerBudget_mono onset _ _ len
    (fullBodyFuel_mono loaderFuel emitFuel entryWidth hcap len)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10CallCountMajorant

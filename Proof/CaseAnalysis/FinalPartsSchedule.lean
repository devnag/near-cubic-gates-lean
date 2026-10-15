import Proof.CaseAnalysis.FinalLedgerBounds
import Proof.CaseAnalysis.FinalCallFuelMono

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutFinalC10StageSeam (dockedFuel)
open RepairOrdinary.CloseoutFinalC10WorkerDock (joinScalarWidth)
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The width, and the two directions it is pinned in -/

/-- The paper's `q(N)`: the selected source's native width at the ordinary clock. -/
def widthAt (sources : EightSources) (k N : ℕ) : ℕ :=
  (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N

/-- **The schedule**: a fixed power of `q(N)+1`, i.e. the paper's `q^{O(1)}`
(`paper.tex:1384`). -/
def widthPower (sources : EightSources) (k r N : ℕ) : ℕ := (widthAt sources k N + 1) ^ r

theorem one_le_widthPower (sources : EightSources) (k r N : ℕ) :
    1 ≤ widthPower sources k r N := Nat.one_le_pow _ _ (by omega)

/-- The constant of `nativeWidth_succ_le_logScale`
(`Proof/CaseAnalysis/FinalLedgerBounds.lean`). -/
def widthConst (sources : EightSources) (k : ℕ) : ℕ :=
  ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
      (sources.hierarchy (fun n => n ^ (k + 2)) (PolynomialClock.ordinaryClock k)).hierarchy
      (padding sources k (PolynomialClock.ordinaryClock k))
    * (natBitLength
        (sources.hierarchy (fun n => n ^ (k + 2))
          (PolynomialClock.ordinaryClock k)).hierarchy.coefficient + k + 4) + 1

/-- `q(N)+1` is at most a constant times `logScale N` -- LEDGER's bridge, at the
route's own clock. -/
theorem widthAt_succ_le (sources : EightSources) (k N : ℕ) :
    widthAt sources k N + 1 ≤ widthConst sources k * logScale N :=
  C10LedgerBounds.nativeWidth_succ_le_logScale sources k (PolynomialClock.ordinaryClock k) N

/-- **The schedule is polylogarithmic in `N`.**  This is the half of
`q(N) = Theta(log N)` that `hrest` consumes. -/
theorem widthPower_le_logScale (sources : EightSources) (k r N : ℕ) :
    widthPower sources k r N ≤ widthConst sources k ^ r * logScale N ^ r := by
  unfold widthPower
  calc (widthAt sources k N + 1) ^ r ≤ (widthConst sources k * logScale N) ^ r :=
        Nat.pow_le_pow_left (widthAt_succ_le sources k N) r
    _ = widthConst sources k ^ r * logScale N ^ r := mul_pow _ _ _

/-! ## Section 2  The schedule, field by field -/

/-- `StageBlock.hthreshold`'s own demand (`Proof/CaseAnalysis/FinalStageContracts.lean`):
a closed constant of the source. -/
def thresholdFloor (sources : EightSources) : ℕ :=
  C10ThresholdWidths.thresholdWidth (constantsOf sources)

/-- The record width: the threshold floor plus a fixed power of `q(N)`. -/
def entryWidthSchedule (sources : EightSources) (k r N : ℕ) : ℕ :=
  thresholdFloor sources + widthPower sources k r N

/-- The call count, and the len-only call cap: a fixed power of `q(N)`. -/
def callCountSchedule (sources : EightSources) (k r N : ℕ) : ℕ := widthPower sources k r N

def clauseBitsSchedule (sources : EightSources) (k degree N : ℕ) : ℕ :=
  CloseoutLanguage.clauseWidth degree (widthAt sources k N)

/-- S1's call-loop budget at the scheduled prologue and per-site fuels. -/
def callFuelSchedule (sources : EightSources) (k r degree : ℕ) (_ph : Phase) (N : ℕ) : ℕ :=
  C10SupplierCall.callFuel (widthPower sources k r N) (clauseBitsSchedule sources k degree N)
    (widthPower sources k r N)

/-- The dock's join width at the schedule. -/
def joinSchedule (sources : EightSources) (k r N : ℕ) : ℕ :=
  joinScalarWidth (entryWidthSchedule sources k r N) (callCountSchedule sources k r N)

/-- The emit loader's own budget (`Proof/CaseAnalysis/FinalWorkerEmitLoader.lean`)
at the scheduled join width -- exactly `StageData.emissionFuel`
(`Proof/CaseAnalysis/FinalStageContracts.lean`) with the record count replaced by
the cap. -/
def emitFuelSchedule (sources : EightSources) (k r N : ℕ) : ℕ :=
  CloseoutFinalC10WorkerEmitLoader.emitFuel (joinSchedule sources k r N)

/-- The decision tail's own budget (`Proof/CaseAnalysis/FinalTailVerdictUniform.lean`)
at the scheduled join width -- exactly `actualFuel`'s `tbud (widthOf ...)`
(`Proof/CaseAnalysis/FinalStageContracts.lean`) at the cap. -/
def tailBudgetSchedule (sources : EightSources) (k r N : ℕ) : ℕ :=
  C10TailVerdictUniform.tbud (joinSchedule sources k r N)

/-! ## Section 3  The onset -/

def ledgerExponent (sources : EightSources) (r degree : ℕ) : ℕ :=
  6 + (fixedProjection sources).degrees.proofLog
    + C10SupplierFuel.stageExponent 560001 (4 * (r + 1)) 22 r (2 * degree + 1) + 2

/-- The coefficient of the polylogarithmic envelope of the whole residual bucket. -/
def restCoefficient (sources : EightSources) (k r : ℕ) : ℕ :=
  18600000 * widthConst sources k ^ (5 * (r + 1))

/-- The onset from which the residual bucket is under `N`, from
`SupplierCapacity.coefficient_mul_logScale_pow_eventually_le`
(`Proof/Supplier/SupplierCapacity.lean`). -/
def restOnset (sources : EightSources) (k r : ℕ) : ℕ :=
  Classical.choose (SupplierCapacity.coefficient_mul_logScale_pow_eventually_le
    (restCoefficient sources k r) (5 * (r + 1)))

theorem restOnset_spec (sources : EightSources) (k r : ℕ) :
    ∀ q, restOnset sources k r ≤ q →
      restCoefficient sources k r * logScale q ^ (5 * (r + 1)) ≤ q :=
  Classical.choose_spec (SupplierCapacity.coefficient_mul_logScale_pow_eventually_le
    (restCoefficient sources k r) (5 * (r + 1)))

/-- **The one onset.**  Three demands: A.8's `fullOnset`, the point at which
`q(N)` clears the threshold floor, and the residual bucket's own onset. -/
def partsOnset (sources : EightSources) (k r degree : ℕ) : ℕ :=
  max (2 ^ C10LogFitFull.fullOnset (ledgerExponent sources r degree))
    (max (2 ^ (thresholdFloor sources + 2)) (restOnset sources k r))

theorem two_le_partsOnset (sources : EightSources) (k r degree : ℕ) :
    2 ≤ partsOnset sources k r degree := by
  have h : (4 : ℕ) ≤ 2 ^ C10LogFitFull.fullOnset (ledgerExponent sources r degree) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (C10LogFitFull.two_le_fullOnset _)
  unfold partsOnset
  omega

theorem width_ge_floor (sources : EightSources) (k r degree N : ℕ)
    (hN : partsOnset sources k r degree ≤ N) :
    thresholdFloor sources + 2 ≤ widthAt sources k N := by
  refine C10LedgerAssembly.nativeWidth_ge sources k (PolynomialClock.ordinaryClock k) _ N ?_
  exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN

/-! ## Section 4  The schedule is under a fixed power of the width -/

/-- **The one schedule fact the four binders reduce to.**  `hdriver_of_schedule`
and `hrest` both consume exactly this. -/
theorem schedule_le_widthPower (sources : EightSources) (k r degree N : ℕ)
    (hN : partsOnset sources k r degree ≤ N) :
    entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1
      ≤ widthPower sources k (r + 1) N := by
  have hfloor := width_ge_floor sources k r degree N hN
  have hP : 1 ≤ widthPower sources k r N := one_le_widthPower sources k r N
  have hAP : thresholdFloor sources
      ≤ thresholdFloor sources * widthPower sources k r N := by
    calc thresholdFloor sources = thresholdFloor sources * 1 := (Nat.mul_one _).symm
      _ ≤ thresholdFloor sources * widthPower sources k r N := Nat.mul_le_mul_left _ hP
  have hring : (thresholdFloor sources + 3) * widthPower sources k r N
      = thresholdFloor sources * widthPower sources k r N
        + 3 * widthPower sources k r N := by ring
  calc entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1
      = thresholdFloor sources + 2 * widthPower sources k r N + 1 := by
        unfold entryWidthSchedule callCountSchedule
        ring
    _ ≤ (thresholdFloor sources + 3) * widthPower sources k r N := by
        rw [hring]
        omega
    _ ≤ (widthAt sources k N + 1) * widthPower sources k r N :=
        Nat.mul_le_mul_right _ (by omega)
    _ = widthPower sources k (r + 1) N := by
        unfold widthPower
        rw [pow_succ]
        ring

/-! ## Section 5  `hdriver`, `hrows`, `hrow` at the schedule -/

/-- S6 row 3, at the schedule.  `driverCoeff := 560001`, `driverExp := 4*(r+1)`. -/
theorem hdriver_at_schedule (sources : EightSources) (k r degree : ℕ) :
    ∀ N, partsOnset sources k r degree ≤ N →
      C10SupplierStage.driverFuel (entryWidthSchedule sources k r)
          (callCountSchedule sources k r) N
        ≤ 560001
          * ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1)
              ^ (4 * (r + 1)) :=
  C10LedgerBounds.hdriver_of_schedule sources k (PolynomialClock.ordinaryClock k)
    (entryWidthSchedule sources k r) (callCountSchedule sources k r) (r + 1)
    (partsOnset sources k r degree)
    (fun N hN => schedule_le_widthPower sources k r degree N hN)

/-- S6 row 4, at the schedule.  `rowExp := 2*degree + 1`. -/
theorem hrows_at_schedule (sources : EightSources) (k r degree : ℕ) :
    ∀ N, partsOnset sources k r degree ≤ N →
      2 ^ clauseBitsSchedule sources k degree N
        ≤ ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1)
            ^ (2 * degree + 1) :=
  C10LedgerBounds.hrows_of_clauseWidth sources k (PolynomialClock.ordinaryClock k) degree
    (partsOnset sources k r degree) (two_le_partsOnset sources k r degree)

/-- **`rowFuel` at a schedule that is a POWER of the width.**  LEDGER's
`rowFuel_le` (`Proof/CaseAnalysis/FinalLedgerBounds.lean`) is stated at
`preFuel <= q`; the schedule is `(q+1)^r`, so the same linear argument runs at
`tableExp := r`.  `rowFuel a a = 4a+18 <= 22a` for `a >= 1`. -/
theorem rowFuel_le_widthPower (sources : EightSources) (k r e N : ℕ) :
    C10SupplierCall.rowFuel (widthPower sources k r N) (widthPower sources k r N)
      ≤ 22 * (2 ^ e * (widthAt sources k N + 1) ^ r) := by
  have he : 1 ≤ (2 : ℕ) ^ e := Nat.one_le_pow _ _ (by norm_num)
  have hmul : 1 * (widthAt sources k N + 1) ^ r
      ≤ 2 ^ e * (widthAt sources k N + 1) ^ r := Nat.mul_le_mul_right _ he
  have hP : 1 ≤ widthPower sources k r N := one_le_widthPower sources k r N
  unfold C10SupplierCall.rowFuel
  simp only [widthPower] at hP ⊢
  omega

/-- S6 row 5, at the schedule.  `tableCoeff := 22`, `tableExp := r`. -/
theorem hrow_at_schedule (sources : EightSources) (k r degree kappa : ℕ) :
    ∀ (_ph : Phase) (N : ℕ), partsOnset sources k r degree ≤ N →
      C10SupplierCall.rowFuel (widthPower sources k r N) (widthPower sources k r N)
        ≤ 22
          * (2 ^ ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N
                - kappa
                  * (Nat.log 2
                      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N)
                    + 1))
            * ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1)
                ^ r) :=
  fun _ N _ => rowFuel_le_widthPower sources k r _ N

/-! ## Section 6  `hrest` -- the loader, the tail and the dock, all under `N` -/

/-- `emitFuel b = 24b + 38` (`Proof/CaseAnalysis/FinalWorkerEmitLoader.lean`). -/
theorem emitFuel_le (b : ℕ) :
    CloseoutFinalC10WorkerEmitLoader.emitFuel b ≤ 62 * (b + 1) := by
  unfold CloseoutFinalC10WorkerEmitLoader.emitFuel CompetitorRationalDecision.width
  omega

/-- `C10TailFeedUniform.budget` (`Proof/CaseAnalysis/FinalTailFeedUniform.lean`) is
quadratic: its dominant summand is `CompetitorDimensions.budget (2b+2)`. -/
theorem tailFeedBudget_le (b : ℕ) :
    C10TailFeedUniform.budget b ≤ 324000 * (b + 1) ^ 2 := by
  have hw : C10TailFeedPrep.w b = 2 * b + 2 := rfl
  have hw2 : C10TailFeedPrep.w2 b = 4 * b + 6 := by
    unfold C10TailFeedPrep.w2 C10TailFeedPrep.w CompetitorRationalDecision.width
    omega
  have hdim : CompetitorDimensions.budget (2 * b + 2) ≤ 225000 * (b + 1) ^ 2 := by
    have h := C10LedgerBounds.dimensions_budget_le (2 * b + 2)
    nlinarith [h]
  have hb : C10TailFeedUniform.budget b
      = 2000 * (C10TailFeedPrep.w2 b + 1) ^ 2 + 232 * C10TailFeedPrep.w b + 439
        + CompetitorDimensions.budget (C10TailFeedPrep.w b) := rfl
  have h1 : 2000 * (4 * b + 6 + 1) ^ 2 ≤ 98000 * (b + 1) ^ 2 := by nlinarith
  have h2 : 232 * (2 * b + 2) + 439 ≤ 903 * (b + 1) ^ 2 := by nlinarith
  rw [hb, hw2, hw]
  omega

/-- `tbud W = 3 * budget W + 12` (`Proof/CaseAnalysis/FinalTailVerdictUniform.lean`). -/
theorem tbud_le (W : ℕ) : C10TailVerdictUniform.tbud W ≤ 1000000 * (W + 1) ^ 2 := by
  have hb := tailFeedBudget_le W
  have h1 : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold C10TailVerdictUniform.tbud
  omega

theorem join_succ_le (ew cc : ℕ) : joinScalarWidth ew cc + 1 ≤ 4 * (ew + cc + 1) ^ 2 := by
  have h := C10LedgerBounds.joinScalarWidth_le ew cc
  have h1 : 1 ≤ (ew + cc + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **The loader plus the decision tail, quartic in the schedule.**  Both are
functions of the join width alone, and the join width is quadratic in
`ew + cc + 1` (`joinScalarWidth_le`). -/
theorem tailPair_le (ew cc : ℕ) :
    CloseoutFinalC10WorkerEmitLoader.emitFuel (joinScalarWidth ew cc)
        + C10TailVerdictUniform.tbud (joinScalarWidth ew cc)
      ≤ 17000000 * (ew + cc + 1) ^ 4 := by
  have hj := join_succ_le ew cc
  have he := emitFuel_le (joinScalarWidth ew cc)
  have ht := tbud_le (joinScalarWidth ew cc)
  have h2 : (joinScalarWidth ew cc + 1) ^ 2 ≤ 16 * (ew + cc + 1) ^ 4 := by
    calc (joinScalarWidth ew cc + 1) ^ 2 ≤ (4 * (ew + cc + 1) ^ 2) ^ 2 :=
          Nat.pow_le_pow_left hj 2
      _ = 16 * (ew + cc + 1) ^ 4 := by ring
  have hsq : (ew + cc + 1) ^ 2 ≤ (ew + cc + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- **The whole residual bucket is quintic in the schedule.**  `dockedFuel_le`
(`Proof/CaseAnalysis/FinalLedgerBounds.lean`) plus `tailPair_le`. -/
theorem restBucket_le (sources : EightSources) (k r N : ℕ) :
    dockedFuel (emitFuelSchedule sources k r) (entryWidthSchedule sources k r N)
          (callCountSchedule sources k r N) N
        + tailBudgetSchedule sources k r N
      ≤ 18600000
        * (entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1) ^ 5 := by
  have hd := C10LedgerBounds.dockedFuel_le (emitFuelSchedule sources k r)
    (entryWidthSchedule sources k r N) (callCountSchedule sources k r N) N
  have hpair : emitFuelSchedule sources k r N + tailBudgetSchedule sources k r N
      ≤ 17000000
        * (entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1) ^ 4 :=
    tailPair_le (entryWidthSchedule sources k r N) (callCountSchedule sources k r N)
  have h45 : (entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1) ^ 4
      ≤ (entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- **S6 row 13 (`hrest`) at the hard-coded `a := 1`, with `A := 1`.**  The
residual bucket is quintic in the schedule, the schedule is polylogarithmic in
`N`, and `SupplierCapacity.coefficient_mul_logScale_pow_eventually_le`
(`Proof/Supplier/SupplierCapacity.lean`) puts that under `N` from
`restOnset` on. -/
theorem hrest_at_schedule (sources : EightSources) (k r degree : ℕ) :
    ∀ N, partsOnset sources k r degree ≤ N →
      dockedFuel (emitFuelSchedule sources k r) (entryWidthSchedule sources k r N)
            (callCountSchedule sources k r N) N
          + tailBudgetSchedule sources k r N
        ≤ 1 * (N + 1) ^ 1 := by
  intro N hN
  have hb := restBucket_le sources k r N
  have hsched := schedule_le_widthPower sources k r degree N hN
  have hS5 : (entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1) ^ 5
      ≤ widthConst sources k ^ (5 * (r + 1)) * logScale N ^ (5 * (r + 1)) := by
    calc (entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1) ^ 5
        ≤ (widthPower sources k (r + 1) N) ^ 5 := Nat.pow_le_pow_left hsched 5
      _ ≤ (widthConst sources k ^ (r + 1) * logScale N ^ (r + 1)) ^ 5 :=
          Nat.pow_le_pow_left (widthPower_le_logScale sources k (r + 1) N) 5
      _ = (widthConst sources k ^ (r + 1)) ^ 5 * (logScale N ^ (r + 1)) ^ 5 := mul_pow _ _ _
      _ = widthConst sources k ^ (5 * (r + 1)) * logScale N ^ (5 * (r + 1)) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm (r + 1) 5]
  have hdon := restOnset_spec sources k r N
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have hfin : 18600000
      * (entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1) ^ 5 ≤ N := by
    refine le_trans ?_ hdon
    unfold restCoefficient
    calc 18600000 * (entryWidthSchedule sources k r N + callCountSchedule sources k r N + 1) ^ 5
        ≤ 18600000
          * (widthConst sources k ^ (5 * (r + 1)) * logScale N ^ (5 * (r + 1))) :=
          Nat.mul_le_mul_left _ hS5
      _ = 18600000 * widthConst sources k ^ (5 * (r + 1)) * logScale N ^ (5 * (r + 1)) := by
          rw [Nat.mul_assoc]
  have he : 1 * (N + 1) ^ 1 = N + 1 := by rw [pow_one]; ring
  omega

/-! ## Section 7  The `Parts` instance -/

/-- `budgetOf` at the scheduled stage, loader, cap and tail. -/
def budgetSchedule (sources : EightSources) (k r degree : ℕ) : ℕ → ℕ :=
  C10SupplierFuel.budgetOf (partsOnset sources k r degree)
    (C10SupplierStage.stageFuel (callFuelSchedule sources k r degree)
      (entryWidthSchedule sources k r) (callCountSchedule sources k r))
    (emitFuelSchedule sources k r) (entryWidthSchedule sources k r)
    (callCountSchedule sources k r) (tailBudgetSchedule sources k r)

def partsOfSchedule (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    C10StageSeamBridge.Parts sources k p :=
  { P with
    callFuel := callFuelSchedule sources k r p.clauseDegree
    entryWidth := entryWidthSchedule sources k r
    callCount := callCountSchedule sources k r
    budget := budgetSchedule sources k r p.clauseDegree }

theorem partsOfSchedule_entryWidth (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfSchedule sources k p r P).entryWidth = entryWidthSchedule sources k r := rfl

theorem partsOfSchedule_callCount (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfSchedule sources k p r P).callCount = callCountSchedule sources k r := rfl

theorem partsOfSchedule_callFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    (ph : Phase) (N : ℕ) :
    (partsOfSchedule sources k p r P).callFuel ph N
      = C10SupplierCall.callFuel (widthPower sources k r N)
          (clauseBitsSchedule sources k p.clauseDegree N) (widthPower sources k r N) := rfl

theorem partsOfSchedule_budget (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfSchedule sources k p r P).budget = budgetSchedule sources k r p.clauseDegree := rfl

/-- `callFuel` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) is monotone in all
three arguments. -/
theorem callFuel_mono (preFuel preFuel' clauseBits clauseBits' cost cost' : ℕ)
    (hp : preFuel ≤ preFuel') (hb : clauseBits ≤ clauseBits') (hc : cost ≤ cost') :
    C10SupplierCall.callFuel preFuel clauseBits cost
      ≤ C10SupplierCall.callFuel preFuel' clauseBits' cost' := by
  have hpow : (2 : ℕ) ^ clauseBits ≤ 2 ^ clauseBits' := Nat.pow_le_pow_right (by norm_num) hb
  have hmul : 2 ^ clauseBits * (cost + 3) ≤ 2 ^ clauseBits' * (cost' + 3) :=
    Nat.mul_le_mul hpow (by omega)
  unfold C10SupplierCall.callFuel
  omega

/-- **The schedule's `callFuel` field is reachable from S1's own step fuels.**
Whatever prologue fuel, clause width and per-site fuel the real call loop runs
at, as long as each is under the schedule the `CallsReady` lifts to the
scheduled budget by `callsReady_enlarge`
(`Proof/CaseAnalysis/FinalCallFuelMono.lean`).  This is what makes
`partsOfSchedule`'s `callFuel` a MAJORANT rather than a free choice, and it is
the `hcalls` side of `stageReady_of_stageRun`
(`Proof/CaseAnalysis/FinalStageSeamBridge.lean`). -/
theorem callsReady_at_schedule (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    {cs : ℕ} {calls : LocalBitMultitape.Machine (218 + (60 + P.extra)) cs}
    {preFuel clauseBits cost ew cc N : ℕ} (ph : Phase)
    {stream input witness : List Bool}
    (h : C10SupplierStage.CallsReady P.extra calls
      (C10SupplierCall.callFuel preFuel clauseBits cost) ew cc stream input witness)
    (hpre : preFuel ≤ widthPower sources k r N)
    (hfit : clauseBits ≤ clauseBitsSchedule sources k p.clauseDegree N)
    (hcost : cost ≤ widthPower sources k r N) :
    C10SupplierStage.CallsReady P.extra calls
      ((partsOfSchedule sources k p r P).callFuel ph N) ew cc stream input witness :=
  C10CallFuelMono.callsReady_enlarge h (callFuel_mono _ _ _ _ _ _ hpre hfit hcost)

/-! ## Section 9  The payoff -/

def runtime_of_partsSchedule (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    Runtime sources k (PolynomialClock.ordinaryClock k)
      (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfSchedule sources k p r P)).budget :=
  C10LedgerAssembly.ledger_of_parts sources k p (partsOfSchedule sources k p r P)
    (emitFuelSchedule sources k r) (callCountSchedule sources k r)
    (tailBudgetSchedule sources k r)
    (fun _ N => widthPower sources k r N) (fun _ N => widthPower sources k r N)
    (clauseBitsSchedule sources k p.clauseDegree)
    560001 (4 * (r + 1)) 22 r (2 * p.clauseDegree + 1)
    (partsOnset sources k r p.clauseDegree) 1
    (fun _ _ => rfl)
    (by
      unfold partsOnset ledgerExponent
      exact le_max_left _ _)
    (hdriver_at_schedule sources k r p.clauseDegree)
    (hrows_at_schedule sources k r p.clauseDegree)
    (hrow_at_schedule sources k r p.clauseDegree _)
    (hrest_at_schedule sources k r p.clauseDegree)
    rfl

end
end NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule

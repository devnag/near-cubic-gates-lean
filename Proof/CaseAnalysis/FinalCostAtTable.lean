import Proof.CaseAnalysis.FinalFuelEnvelope

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The residual table cell, as a per-call fuel -/

/-- **The paper's `2^q/q^sigma` (`paper.tex:3555-3557`), as a budget.**  This is
byte-for-byte the cell `ledger_of_parts`' `hrow` binder
(`Proof/CaseAnalysis/FinalLedgerAssembly.lean`) already allows for one external row, with
`kappa := ledgerExponent sources r degree` (`Proof/CaseAnalysis/FinalPartsSchedule.lean`),
which is A.8's `kappa >= h_D + sigma + c_1` (`paper.tex:2307`; 2306 is the opening `\[`). -/
def hotFuel (sources : EightSources) (k r degree N : ℕ) : ℕ :=
  2 ^ (widthAt sources k N
      - ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1))

theorem one_le_hotFuel (sources : EightSources) (k r degree N : ℕ) :
    1 ≤ hotFuel sources k r degree N := by
  unfold hotFuel
  exact Nat.one_le_pow _ 2 (by norm_num)

/-- **The new ceiling DOMINATES the old one.**  Taken from `envelope_split`
(`Proof/CaseAnalysis/FinalFuelEnvelope.lean`), which states the DEFECT (`polyFuel` never
reaches `2^q`) and the DOMINATION (`polyFuel` fits inside one residual table factor) as ONE
conjunction precisely so that no consumer can take half of it: elaborating this proof term
forces both halves.  The domination half is why the move is free -- everything already
established under the `polyFuel` pin is still under the new one; the defect half is why the
move is necessary at all. -/
theorem polyFuel_le_hotFuel (sources : EightSources) (k r degree C d N : ℕ)
    (hd : d + 1 ≤ k + 2) (hN : repinOnset sources k r degree C ≤ N) :
    polyFuel C d N ≤ hotFuel sources k r degree N := by
  unfold hotFuel
  exact (envelope_split sources k r degree C d hd).2 N hN

/-! ## Section 2  `hrow` with `cost` at the cell -/

/-- `rowFuel` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) at the split pin
`preFuel := polyFuel`, `cost := hotFuel` is `2*H + 2*P + 18 <= 4*H + 18 <= 22*H`, using
`polyFuel_le_hotFuel` for the middle step and `1 <= H` for the constant. -/
theorem rowFuel_hotCost_le (sources : EightSources) (k r degree C d N : ℕ)
    (hd : d + 1 ≤ k + 2) (hN : repinOnset sources k r degree C ≤ N) :
    C10SupplierCall.rowFuel (polyFuel C d N) (hotFuel sources k r degree N)
      ≤ 22 * hotFuel sources k r degree N := by
  have hdom := polyFuel_le_hotFuel sources k r degree C d N hd hN
  have hone := one_le_hotFuel sources k r degree N
  show 2 * hotFuel sources k r degree N + 2 * polyFuel C d N + 18
      ≤ 22 * hotFuel sources k r degree N
  omega

/-- **S6 row 5 with `cost` at the residual table cell**, in exactly the shape `ledger_of_parts`
binds (`Proof/CaseAnalysis/FinalLedgerAssembly.lean`) at `tableCoeff := 22`, `tableExp := r`.
The `(q+1)^tableExp` factor is pure slack here -- the cell alone already pays. -/
theorem hrow_at_hotCost (sources : EightSources) (k r degree C d : ℕ) (hd : d + 1 ≤ k + 2) :
    ∀ (_ph : Phase) (N : ℕ), repinOnset sources k r degree C ≤ N →
      C10SupplierCall.rowFuel (polyFuel C d N) (hotFuel sources k r degree N)
        ≤ 22
          * (2 ^ ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N
                - ledgerExponent sources r degree
                  * (Nat.log 2
                      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N)
                    + 1))
            * ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1)
                ^ r) := by
  intro _ph N hN
  have hmain := rowFuel_hotCost_le sources k r degree C d N hd hN
  have hw : 1 ≤ (widthAt sources k N + 1) ^ r := Nat.one_le_pow _ _ (by omega)
  have hfac : ∀ X Y : ℕ, 1 ≤ Y → 22 * X ≤ 22 * (X * Y) := by
    intro X Y hY
    refine Nat.mul_le_mul_left 22 ?_
    calc X = X * 1 := (Nat.mul_one _).symm
      _ ≤ X * Y := Nat.mul_le_mul_left _ hY
  exact le_trans hmain (hfac _ _ hw)

/-! ## Section 3  The `Parts` instance with `cost` at the cell -/

def callFuelHot (sources : EightSources) (k r degree C d : ℕ) (_ph : Phase) (N : ℕ) : ℕ :=
  C10SupplierCall.callFuel (polyFuel C d N) (clauseBitsSchedule sources k degree N)
    (hotFuel sources k r degree N)

/-- `budgetOf` at the new stage fuel.  `emitFuel`, `entryWidth`, `callCap`, `tailBudget` and the
onset are all exactly `budgetRepin`'s (`Proof/CaseAnalysis/FinalFuelRepin.lean`); only the
stage fuel moves, and only through `callFuel`. -/
def budgetHot (sources : EightSources) (k r degree C d : ℕ) : ℕ → ℕ :=
  C10SupplierFuel.budgetOf (repinOnset sources k r degree C)
    (C10SupplierStage.stageFuel (callFuelHot sources k r degree C d)
      (entryWidthSchedule sources k r) (callCountSchedule sources k r))
    (emitFuelSchedule sources k r) (entryWidthSchedule sources k r)
    (callCountSchedule sources k r) (tailBudgetSchedule sources k r)

def partsOfHotCost (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    C10StageSeamBridge.Parts sources k p :=
  { partsOfSchedule sources k p r P with
    callFuel := callFuelHot sources k r p.clauseDegree C d
    budget := budgetHot sources k r p.clauseDegree C d }

theorem partsOfHotCost_entryWidth (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfHotCost sources k p r C d P).entryWidth = entryWidthSchedule sources k r := rfl

theorem partsOfHotCost_callCount (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfHotCost sources k p r C d P).callCount = callCountSchedule sources k r := rfl

theorem partsOfHotCost_callFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    (ph : Phase) (N : ℕ) :
    (partsOfHotCost sources k p r C d P).callFuel ph N
      = C10SupplierCall.callFuel (polyFuel C d N)
          (clauseBitsSchedule sources k p.clauseDegree N)
          (hotFuel sources k r p.clauseDegree N) := rfl

theorem partsOfHotCost_budget (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfHotCost sources k p r C d P).budget = budgetHot sources k r p.clauseDegree C d :=
  rfl

theorem polyFuel_entryWidth_still_rfl (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfPolyFuel sources k p r C d P).entryWidth = entryWidthSchedule sources k r := rfl

theorem polyFuel_callCount_still_rfl (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfPolyFuel sources k p r C d P).callCount = callCountSchedule sources k r := rfl

/-- **The new instance's record width is the old instance's, definitionally.** -/
theorem hotCost_entryWidth_eq_polyFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfHotCost sources k p r C d P).entryWidth
      = (partsOfPolyFuel sources k p r C d P).entryWidth := rfl

/-- **The new instance's call count is the old instance's, definitionally.** -/
theorem hotCost_callCount_eq_polyFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfHotCost sources k p r C d P).callCount
      = (partsOfPolyFuel sources k p r C d P).callCount := rfl

/-! ## Section 4  Nothing already proved is lost -/

/-- **The old pin is under the new one, field to field.**  `callFuel_mono`
(`Proof/CaseAnalysis/FinalPartsSchedule.lean`) at `hpre := le_rfl`, `hb := le_rfl`,
`hc := polyFuel_le_hotFuel`. -/
theorem callFuelRepin_le_callFuelHot (sources : EightSources) (k r degree C d : ℕ)
    (hd : d + 1 ≤ k + 2) (ph : Phase) (N : ℕ) (hN : repinOnset sources k r degree C ≤ N) :
    callFuelRepin sources k degree C d ph N ≤ callFuelHot sources k r degree C d ph N :=
  callFuel_mono _ _ _ _ _ _ le_rfl le_rfl
    (polyFuel_le_hotFuel sources k r degree C d N hd hN)

theorem callsReady_of_polyFuel_pin (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (hd : d + 1 ≤ k + 2)
    (P : C10StageSeamBridge.Parts sources k p)
    {cs : ℕ} {calls : LocalBitMultitape.Machine (218 + (60 + P.extra)) cs}
    {ew cc N : ℕ} (ph : Phase) (hN : repinOnset sources k r p.clauseDegree C ≤ N)
    {stream input witness : List Bool}
    (h : C10SupplierStage.CallsReady P.extra calls
      ((partsOfPolyFuel sources k p r C d P).callFuel ph N) ew cc stream input witness) :
    C10SupplierStage.CallsReady P.extra calls
      ((partsOfHotCost sources k p r C d P).callFuel ph N) ew cc stream input witness :=
  C10CallFuelMono.callsReady_enlarge h
    (callFuelRepin_le_callFuelHot sources k r p.clauseDegree C d hd ph N hN)

/-- **The majorant seam at the new pin.**  Whatever prologue fuel, clause width and per-site
cost the real call loop runs at, as long as the prologue is under `polyFuel C d N` and the cost
is under the residual table cell, the `CallsReady` lifts into the field.  The `hcost` binder is
now `cost <= 2 ^ (q - kappa*L_q)` -- a full factor of `N/polylog(N)` above what
`callsReady_at_polyFuel` (`Proof/CaseAnalysis/FinalFuelRepin.lean`) admits, by
`envelope_defect` (`Proof/CaseAnalysis/FinalFuelEnvelope.lean`). -/
theorem callsReady_at_hotCost (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    {cs : ℕ} {calls : LocalBitMultitape.Machine (218 + (60 + P.extra)) cs}
    {preFuel clauseBits cost ew cc N : ℕ} (ph : Phase)
    {stream input witness : List Bool}
    (h : C10SupplierStage.CallsReady P.extra calls
      (C10SupplierCall.callFuel preFuel clauseBits cost) ew cc stream input witness)
    (hpre : preFuel ≤ polyFuel C d N)
    (hfit : clauseBits ≤ clauseBitsSchedule sources k p.clauseDegree N)
    (hcost : cost ≤ hotFuel sources k r p.clauseDegree N) :
    C10SupplierStage.CallsReady P.extra calls
      ((partsOfHotCost sources k p r C d P).callFuel ph N) ew cc stream input witness :=
  C10CallFuelMono.callsReady_enlarge h (callFuel_mono _ _ _ _ _ _ hpre hfit hcost)

theorem records_hotCost_eq (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    C10TailComposeUniform.records sources k p
        (C10StageSeamBridge.stageData_of_parts sources k p
          (partsOfHotCost sources k p r C d P)) x bits ph
      = C10TailComposeUniform.records sources k p
        (C10StageSeamBridge.stageData_of_parts sources k p
          (partsOfSchedule sources k p r P)) x bits ph := rfl

/-! ## Section 5  The payoff -/

def runtime_of_hotCost (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (hd : d + 1 ≤ k + 2)
    (P : C10StageSeamBridge.Parts sources k p) :
    Runtime sources k (PolynomialClock.ordinaryClock k)
      (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfHotCost sources k p r C d P)).budget :=
  C10LedgerAssembly.ledger_of_parts sources k p (partsOfHotCost sources k p r C d P)
    (emitFuelSchedule sources k r) (callCountSchedule sources k r)
    (tailBudgetSchedule sources k r)
    (fun _ N => polyFuel C d N) (fun _ N => hotFuel sources k r p.clauseDegree N)
    (clauseBitsSchedule sources k p.clauseDegree)
    560001 (4 * (r + 1)) 22 r (2 * p.clauseDegree + 1)
    (repinOnset sources k r p.clauseDegree C) 1
    (fun _ _ => rfl)
    (by
      unfold repinOnset partsOnset ledgerExponent
      exact le_trans (le_max_left _ _) (le_max_left _ _))
    (fun N hN => hdriver_at_schedule sources k r p.clauseDegree N
      (le_trans (partsOnset_le_repinOnset sources k r p.clauseDegree C) hN))
    (fun N hN => hrows_at_schedule sources k r p.clauseDegree N
      (le_trans (partsOnset_le_repinOnset sources k r p.clauseDegree C) hN))
    (hrow_at_hotCost sources k r p.clauseDegree C d hd)
    (fun N hN => hrest_at_schedule sources k r p.clauseDegree N
      (le_trans (partsOnset_le_repinOnset sources k r p.clauseDegree C) hN))
    rfl

end
end NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable

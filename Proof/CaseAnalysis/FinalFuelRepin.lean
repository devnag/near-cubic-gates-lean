import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalRecordPadding

namespace NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The padded length dominates `n + 1`.  This is the step
`CloseoutNativeWidth.input_le_envelope` (`Proof/CaseAnalysis/NativeWidthStep.lean`)
takes first, isolated. -/
theorem length_ge {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad n : ℕ) :
    n + 1 ≤ HierarchyEncode.length H Cpad n :=
  (PowerSlice.linear_length k (2 * Cpad)
    (HierarchyBinary.header (VerifierEncoding.code H.verifier).length H.coefficient) n).1

/-- The padded length's `PowerSlice` limit is its `(k+2)`-nd power --
`PowerSlice.length_degree` (`Proof/PCP/PCPPowerSlice.lean`) at the route's own
allocation. -/
theorem length_limit_eq {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad n : ℕ) :
    PowerSlice.limit (HierarchyEncode.length H Cpad n)
      = HierarchyEncode.length H Cpad n ^ (k + 2) :=
  PowerSlice.length_limit k
    (HierarchyBinary.allocation Cpad (VerifierEncoding.code H.verifier).length H.coefficient n)

/-- The aggregate clock is a power of two above `2 ^ 23` times the dyadic limit
-- `ClockEnvelope.clock_factor` (`Proof/MachineModel/ClockEnvelope.lean`) at
`UAggregateClock.offset = 23`, `UAggregateClock.exponent = 5`
(`Proof/MachineModel/UAggregateClock.lean`). -/
theorem clock_limit_le_time (M : ℕ) :
    2 ^ 23 * ClockDyadicLedger.limit M ≤ UAggregateClock.time M := by
  have hp : 1 ≤ (2 ^ ClockEnvelope.logWidth M) ^ 5 := Nat.one_le_pow _ _ (by positivity)
  have hfac : UAggregateClock.time M
      = 2 ^ 23 * ClockDyadicLedger.limit M * (2 ^ ClockEnvelope.logWidth M) ^ 5 :=
    ClockEnvelope.clock_factor 23 5 M
  rw [hfac]
  calc 2 ^ 23 * ClockDyadicLedger.limit M
      = 2 ^ 23 * ClockDyadicLedger.limit M * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ 23 * ClockDyadicLedger.limit M * (2 ^ ClockEnvelope.logWidth M) ^ 5 :=
        Nat.mul_le_mul_left _ hp

/-- The source's proof envelope dominates the clock:
`Dimensions.envelope source M = source.coefficient * T M * logScale (T M) ^ proofLog`
(`Proof/PCP/ProjectionNormalizationDimensions.lean`), and both outer factors are at
least one. -/
theorem time_le_envelope {v : OrdinaryVerifier}
    (source : ProjectionSourceAlgorithm v UAggregateClock.time) (M : ℕ) :
    UAggregateClock.time M ≤ ProjectionNormalization.Dimensions.envelope source M := by
  have hc : 1 ≤ source.coefficient := source.coefficientPositive
  have hl : 0 < logScale (UAggregateClock.time M) := Nat.clog_pos (by decide) (by omega)
  have hp : 1 ≤ logScale (UAggregateClock.time M) ^ source.degrees.proofLog :=
    Nat.one_le_pow _ _ hl
  show UAggregateClock.time M
    ≤ source.coefficient * UAggregateClock.time M
      * logScale (UAggregateClock.time M) ^ source.degrees.proofLog
  calc UAggregateClock.time M = 1 * UAggregateClock.time M * 1 := by ring
    _ ≤ source.coefficient * UAggregateClock.time M
        * logScale (UAggregateClock.time M) ^ source.degrees.proofLog :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) hp

/-- `Dimensions.width` is `natBitLength` of the envelope, so two to that power
strictly dominates the envelope. -/
theorem envelope_lt_pow_width {v : OrdinaryVerifier} {T : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v T) (M : ℕ) :
    ProjectionNormalization.Dimensions.envelope source M
      < 2 ^ ProjectionNormalization.Dimensions.width source M :=
  Nat.lt_pow_succ_log_self (by decide) _

/-- **`2 ^ q` is polynomial of degree `k + 2` in `N`.**  The four steps above,
chained. -/
theorem pow_width_ge {v : OrdinaryVerifier}
    (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad n : ℕ) :
    2 ^ 23 * (n + 1) ^ (k + 2) ≤ 2 ^ HierarchyProjection.width source H Cpad n := by
  have hn : n + 1 ≤ HierarchyEncode.length H Cpad n := length_ge H Cpad n
  have hpow : (n + 1) ^ (k + 2) ≤ HierarchyEncode.length H Cpad n ^ (k + 2) :=
    Nat.pow_le_pow_left hn _
  have hlim : HierarchyEncode.length H Cpad n ^ (k + 2)
      ≤ ClockDyadicLedger.limit (HierarchyEncode.length H Cpad n) := by
    have h := (ClockDyadicLedger.limit_bounds (HierarchyEncode.length H Cpad n) (by omega)).1
    rwa [length_limit_eq H Cpad n] at h
  calc 2 ^ 23 * (n + 1) ^ (k + 2)
      ≤ 2 ^ 23 * ClockDyadicLedger.limit (HierarchyEncode.length H Cpad n) :=
        Nat.mul_le_mul_left _ (hpow.trans hlim)
    _ ≤ UAggregateClock.time (HierarchyEncode.length H Cpad n) := clock_limit_le_time _
    _ ≤ ProjectionNormalization.Dimensions.envelope source
          (HierarchyEncode.length H Cpad n) := time_le_envelope source _
    _ ≤ 2 ^ ProjectionNormalization.Dimensions.width source
          (HierarchyEncode.length H Cpad n) := (envelope_lt_pow_width source _).le
    _ = 2 ^ HierarchyProjection.width source H Cpad n := rfl

/-- **The same statement at the route's own width.**  `widthAt sources k N` IS
`HierarchyProjection.width (fixedProjection sources) H (padding sources k clock) N`
definitionally -- the identification `nativeWidth_le_time_bits`
(`Proof/CaseAnalysis/FinalLedgerBounds.lean`) also relies on. -/
theorem pow_widthAt_ge (sources : EightSources) (k N : ℕ) :
    2 ^ 23 * (N + 1) ^ (k + 2) ≤ 2 ^ widthAt sources k N :=
  pow_width_ge (fixedProjection sources)
    (sources.hierarchy (fun n => n ^ (k + 2)) (PolynomialClock.ordinaryClock k)).hierarchy
    (padding sources k (PolynomialClock.ordinaryClock k)) N

/-! ## Section 2  Spending the residual table factor `2 ^ (q - kappa * L_q)` -/

/-- `2 ^ q` splits at `K = kappa * L_q` (A.7, `paper.tex:2183-2185`), and the
discarded half is at most `(2 * q) ^ kappa`. -/
theorem pow_split (q kappa : ℕ) (hq : 1 ≤ q) (hfit : kappa * (Nat.log 2 q + 1) ≤ q) :
    (2 : ℕ) ^ q ≤ (2 * q) ^ kappa * 2 ^ (q - kappa * (Nat.log 2 q + 1)) := by
  have hself : (2 : ℕ) ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hlog : (2 : ℕ) ^ (Nat.log 2 q + 1) ≤ 2 * q := by
    rw [pow_succ]
    omega
  have hk : (2 : ℕ) ^ (kappa * (Nat.log 2 q + 1)) ≤ (2 * q) ^ kappa := by
    rw [Nat.mul_comm kappa (Nat.log 2 q + 1), pow_mul]
    exact Nat.pow_le_pow_left hlog kappa
  calc (2 : ℕ) ^ q
      = 2 ^ (kappa * (Nat.log 2 q + 1) + (q - kappa * (Nat.log 2 q + 1))) := by
        congr 1
        omega
    _ = 2 ^ (kappa * (Nat.log 2 q + 1)) * 2 ^ (q - kappa * (Nat.log 2 q + 1)) := pow_add _ _ _
    _ ≤ (2 * q) ^ kappa * 2 ^ (q - kappa * (Nat.log 2 q + 1)) := Nat.mul_le_mul_right _ hk

/-- **The spend.**  Anything whose product with the discarded polylogarithmic
factor is under `2 ^ q` fits in the residual table factor. -/
theorem le_pow_sub (B q kappa : ℕ) (hq : 1 ≤ q)
    (hfit : kappa * (Nat.log 2 q + 1) ≤ q)
    (hB : B * (2 * q) ^ kappa ≤ 2 ^ q) :
    B ≤ 2 ^ (q - kappa * (Nat.log 2 q + 1)) := by
  have hpos : 0 < (2 * q) ^ kappa := by positivity
  have h : (2 * q) ^ kappa * B ≤ (2 * q) ^ kappa * 2 ^ (q - kappa * (Nat.log 2 q + 1)) := by
    rw [Nat.mul_comm ((2 * q) ^ kappa) B]
    exact hB.trans (pow_split q kappa hq hfit)
  exact Nat.le_of_mul_le_mul_left h hpos

/-! ## Section 3  The re-pinned fuel, its coefficient and its onset -/

/-- **The re-pinned prologue / per-site step budget**: a polynomial of degree `d`
in the input length.  `d + 1 <= k + 2` is the paper's `o(T(N))`
(`paper.tex:4316-4322`) at the route's clock `T(N) = N ^ (k+2)`. -/
def polyFuel (C d N : ℕ) : ℕ := C * (N + 1) ^ d

/-- **The re-pin is inside the clock.**  `paper.tex:4316-4322` charges all
preprocessing at `o(T(N))`; the route's `T(N)` is `N ^ (k+2)`
(`PolynomialClock.ordinaryClock k`), and this is the concrete inequality. -/
theorem polyFuel_le_clock (k C d N : ℕ) (hd : d + 1 ≤ k + 2) (hC : C ≤ N + 1) :
    polyFuel C d N ≤ (N + 1) ^ (k + 2) := by
  calc polyFuel C d N = C * (N + 1) ^ d := rfl
    _ ≤ (N + 1) * (N + 1) ^ d := Nat.mul_le_mul_right _ hC
    _ = (N + 1) ^ (d + 1) := by rw [pow_succ]; ring
    _ ≤ (N + 1) ^ (k + 2) := Nat.pow_le_pow_right (by omega) hd

/-- `rowFuel` at the re-pinned fuel: `4 * C * (N+1)^d + 18`, majorised by one
coefficient. -/
theorem rowFuel_polyFuel_le (C d N : ℕ) :
    C10SupplierCall.rowFuel (polyFuel C d N) (polyFuel C d N)
      ≤ (4 * C + 18) * (N + 1) ^ d := by
  have h1 : 1 ≤ (N + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have he : (4 * C + 18) * (N + 1) ^ d = 4 * (C * (N + 1) ^ d) + 18 * (N + 1) ^ d := by ring
  have hb : 18 ≤ 18 * (N + 1) ^ d := by
    calc (18 : ℕ) = 18 * 1 := by ring
      _ ≤ 18 * (N + 1) ^ d := Nat.mul_le_mul_left _ h1
  show 2 * polyFuel C d N + 2 * polyFuel C d N + 18 ≤ (4 * C + 18) * (N + 1) ^ d
  simp only [polyFuel]
  omega

/-- The coefficient of the polylogarithmic factor the row budget must clear:
`rowFuel`'s own `4C + 18` times the doubled width constant, to the power `hrow`'s
own `kappa`. -/
def rowCoefficient (sources : EightSources) (k r degree C : ℕ) : ℕ :=
  (4 * C + 18) * (2 * widthConst sources k) ^ ledgerExponent sources r degree

def rowOnset (sources : EightSources) (k r degree C : ℕ) : ℕ :=
  Classical.choose (SupplierCapacity.coefficient_mul_logScale_pow_eventually_le
    (rowCoefficient sources k r degree C) (ledgerExponent sources r degree))

theorem rowOnset_spec (sources : EightSources) (k r degree C : ℕ) :
    ∀ N, rowOnset sources k r degree C ≤ N →
      rowCoefficient sources k r degree C * logScale N ^ ledgerExponent sources r degree ≤ N :=
  Classical.choose_spec (SupplierCapacity.coefficient_mul_logScale_pow_eventually_le
    (rowCoefficient sources k r degree C) (ledgerExponent sources r degree))

def repinOnset (sources : EightSources) (k r degree C : ℕ) : ℕ :=
  max (partsOnset sources k r degree) (rowOnset sources k r degree C)

theorem partsOnset_le_repinOnset (sources : EightSources) (k r degree C : ℕ) :
    partsOnset sources k r degree ≤ repinOnset sources k r degree C := le_max_left _ _

/-! ## Section 4  `hrow` at the re-pinned fuel -/

/-- `2 * q(N)` is at most `2 * widthConst` times `logScale N` -- `widthAt_succ_le`
(`Proof/CaseAnalysis/FinalPartsSchedule.lean`), doubled. -/
theorem two_width_pow_le (sources : EightSources) (k kappa N : ℕ) :
    (2 * widthAt sources k N) ^ kappa
      ≤ (2 * widthConst sources k) ^ kappa * logScale N ^ kappa := by
  have h := widthAt_succ_le sources k N
  have hlin : 2 * widthAt sources k N ≤ 2 * widthConst sources k * logScale N := by
    have h2 : 2 * (widthAt sources k N + 1) ≤ 2 * (widthConst sources k * logScale N) :=
      Nat.mul_le_mul_left 2 h
    have hassoc : 2 * (widthConst sources k * logScale N)
        = 2 * widthConst sources k * logScale N := (Nat.mul_assoc _ _ _).symm
    omega
  calc (2 * widthAt sources k N) ^ kappa
      ≤ (2 * widthConst sources k * logScale N) ^ kappa := Nat.pow_le_pow_left hlin kappa
    _ = (2 * widthConst sources k) ^ kappa * logScale N ^ kappa := mul_pow _ _ _

/-- **The row budget fits in the residual table factor.**  This is the whole
re-pin: the factor `rowFuel_le` (`Proof/CaseAnalysis/FinalLedgerBounds.lean`)
discards is spent here, and it is worth a full `(N+1)^(k+2)` by
`pow_widthAt_ge`. -/
theorem rowFuel_le_table (sources : EightSources) (k r degree C d N : ℕ)
    (hd : d + 1 ≤ k + 2)
    (hN : repinOnset sources k r degree C ≤ N) :
    C10SupplierCall.rowFuel (polyFuel C d N) (polyFuel C d N)
      ≤ 2 ^ (widthAt sources k N
          - ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1)) := by
  have hP : partsOnset sources k r degree ≤ N := le_trans (le_max_left _ _) hN
  have hR : rowOnset sources k r degree C ≤ N := le_trans (le_max_right _ _) hN
  have hq2 : thresholdFloor sources + 2 ≤ widthAt sources k N :=
    width_ge_floor sources k r degree N hP
  have hq1 : 1 ≤ widthAt sources k N := by omega
  have hfullN : 2 ^ C10LogFitFull.fullOnset (ledgerExponent sources r degree) ≤ N := by
    refine le_trans ?_ hP
    unfold partsOnset
    exact le_max_left _ _
  have hfullq : C10LogFitFull.fullOnset (ledgerExponent sources r degree)
      ≤ widthAt sources k N :=
    C10LedgerAssembly.nativeWidth_ge sources k (PolynomialClock.ordinaryClock k) _ N hfullN
  have hfit : ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1)
      ≤ widthAt sources k N :=
    C10LogFitFull.hfit_full (ledgerExponent sources r degree) (widthAt sources k N) hfullq
  refine le_pow_sub _ _ _ hq1 hfit ?_
  -- the product with the discarded polylogarithmic factor is under `2 ^ q`
  have hrow := rowFuel_polyFuel_le C d N
  have hpoly := two_width_pow_le sources k (ledgerExponent sources r degree) N
  have hstep1 : C10SupplierCall.rowFuel (polyFuel C d N) (polyFuel C d N)
        * (2 * widthAt sources k N) ^ ledgerExponent sources r degree
      ≤ ((4 * C + 18) * (N + 1) ^ d)
        * ((2 * widthConst sources k) ^ ledgerExponent sources r degree
          * logScale N ^ ledgerExponent sources r degree) := Nat.mul_le_mul hrow hpoly
  have hdon := rowOnset_spec sources k r degree C N hR
  have hring : ((4 * C + 18) * (N + 1) ^ d)
        * ((2 * widthConst sources k) ^ ledgerExponent sources r degree
          * logScale N ^ ledgerExponent sources r degree)
      = (rowCoefficient sources k r degree C * logScale N ^ ledgerExponent sources r degree)
        * (N + 1) ^ d := by
    unfold rowCoefficient
    ring
  have hstep2 : (rowCoefficient sources k r degree C
        * logScale N ^ ledgerExponent sources r degree) * (N + 1) ^ d
      ≤ N * (N + 1) ^ d := Nat.mul_le_mul_right _ hdon
  have hstep3 : N * (N + 1) ^ d ≤ (N + 1) ^ (k + 2) := by
    calc N * (N + 1) ^ d ≤ (N + 1) * (N + 1) ^ d := Nat.mul_le_mul_right _ (by omega)
      _ = (N + 1) ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ (N + 1) ^ (k + 2) := Nat.pow_le_pow_right (by omega) hd
  have hstep4 : ((N : ℕ) + 1) ^ (k + 2) ≤ 2 ^ 23 * (N + 1) ^ (k + 2) := by
    calc ((N : ℕ) + 1) ^ (k + 2) = 1 * (N + 1) ^ (k + 2) := by ring
      _ ≤ 2 ^ 23 * (N + 1) ^ (k + 2) := Nat.mul_le_mul_right _ (by norm_num)
  have hstep5 : 2 ^ 23 * ((N : ℕ) + 1) ^ (k + 2) ≤ 2 ^ widthAt sources k N :=
    pow_widthAt_ge sources k N
  calc C10SupplierCall.rowFuel (polyFuel C d N) (polyFuel C d N)
        * (2 * widthAt sources k N) ^ ledgerExponent sources r degree
      ≤ ((4 * C + 18) * (N + 1) ^ d)
        * ((2 * widthConst sources k) ^ ledgerExponent sources r degree
          * logScale N ^ ledgerExponent sources r degree) := hstep1
    _ = (rowCoefficient sources k r degree C * logScale N ^ ledgerExponent sources r degree)
        * (N + 1) ^ d := hring
    _ ≤ N * (N + 1) ^ d := hstep2
    _ ≤ (N + 1) ^ (k + 2) := hstep3
    _ ≤ 2 ^ 23 * (N + 1) ^ (k + 2) := hstep4
    _ ≤ 2 ^ widthAt sources k N := hstep5

/-- **S6 row 5 at the re-pinned fuel**, in exactly the shape `ledger_of_parts`
binds (`Proof/CaseAnalysis/FinalLedgerAssembly.lean`) at `tableCoeff := 22`,
`tableExp := r`. -/
theorem hrow_at_polyFuel (sources : EightSources) (k r degree C d : ℕ)
    (hd : d + 1 ≤ k + 2) :
    ∀ (_ph : Phase) (N : ℕ), repinOnset sources k r degree C ≤ N →
      C10SupplierCall.rowFuel (polyFuel C d N) (polyFuel C d N)
        ≤ 22
          * (2 ^ ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N
                - ledgerExponent sources r degree
                  * (Nat.log 2
                      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N)
                    + 1))
            * ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1)
                ^ r) := by
  intro _ph N hN
  have hmain := rowFuel_le_table sources k r degree C d N hd hN
  have hw : 1 ≤ (widthAt sources k N + 1) ^ r := Nat.one_le_pow _ _ (by omega)
  have hfac : ∀ X Y : ℕ, 1 ≤ Y → X ≤ 22 * (X * Y) := by
    intro X Y hY
    calc X = X * 1 := (Nat.mul_one _).symm
      _ ≤ X * Y := Nat.mul_le_mul_left _ hY
      _ = 1 * (X * Y) := (Nat.one_mul _).symm
      _ ≤ 22 * (X * Y) := Nat.mul_le_mul_right _ (by norm_num)
  exact le_trans hmain (hfac _ _ hw)

/-! ## Section 5  The `Parts` instance at the re-pinned fuel -/

def callFuelRepin (sources : EightSources) (k degree C d : ℕ) (_ph : Phase) (N : ℕ) : ℕ :=
  C10SupplierCall.callFuel (polyFuel C d N) (clauseBitsSchedule sources k degree N)
    (polyFuel C d N)

def budgetRepin (sources : EightSources) (k r degree C d : ℕ) : ℕ → ℕ :=
  C10SupplierFuel.budgetOf (repinOnset sources k r degree C)
    (C10SupplierStage.stageFuel (callFuelRepin sources k degree C d)
      (entryWidthSchedule sources k r) (callCountSchedule sources k r))
    (emitFuelSchedule sources k r) (entryWidthSchedule sources k r)
    (callCountSchedule sources k r) (tailBudgetSchedule sources k r)

def partsOfPolyFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    C10StageSeamBridge.Parts sources k p :=
  { partsOfSchedule sources k p r P with
    callFuel := callFuelRepin sources k p.clauseDegree C d
    budget := budgetRepin sources k r p.clauseDegree C d }

theorem partsOfPolyFuel_entryWidth (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfPolyFuel sources k p r C d P).entryWidth = entryWidthSchedule sources k r := rfl

theorem partsOfPolyFuel_callCount (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfPolyFuel sources k p r C d P).callCount = callCountSchedule sources k r := rfl

/-- The one field that moved. -/
theorem partsOfPolyFuel_callFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    (ph : Phase) (N : ℕ) :
    (partsOfPolyFuel sources k p r C d P).callFuel ph N
      = C10SupplierCall.callFuel (polyFuel C d N)
          (clauseBitsSchedule sources k p.clauseDegree N) (polyFuel C d N) := rfl

theorem partsOfPolyFuel_budget (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    (partsOfPolyFuel sources k p r C d P).budget = budgetRepin sources k r p.clauseDegree C d :=
  rfl

/-! ## Section 6  The seam: the re-pin is a MAJORANT -/

theorem callsReady_at_polyFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    {cs : ℕ} {calls : LocalBitMultitape.Machine (218 + (60 + P.extra)) cs}
    {preFuel clauseBits cost ew cc N : ℕ} (ph : Phase)
    {stream input witness : List Bool}
    (h : C10SupplierStage.CallsReady P.extra calls
      (C10SupplierCall.callFuel preFuel clauseBits cost) ew cc stream input witness)
    (hpre : preFuel ≤ polyFuel C d N)
    (hfit : clauseBits ≤ clauseBitsSchedule sources k p.clauseDegree N)
    (hcost : cost ≤ polyFuel C d N) :
    C10SupplierStage.CallsReady P.extra calls
      ((partsOfPolyFuel sources k p r C d P).callFuel ph N) ew cc stream input witness :=
  C10CallFuelMono.callsReady_enlarge h (callFuel_mono _ _ _ _ _ _ hpre hfit hcost)

/-! ## Section 7  The payoff -/

def runtime_of_polyFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (hd : d + 1 ≤ k + 2)
    (P : C10StageSeamBridge.Parts sources k p) :
    Runtime sources k (PolynomialClock.ordinaryClock k)
      (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfPolyFuel sources k p r C d P)).budget :=
  C10LedgerAssembly.ledger_of_parts sources k p (partsOfPolyFuel sources k p r C d P)
    (emitFuelSchedule sources k r) (callCountSchedule sources k r)
    (tailBudgetSchedule sources k r)
    (fun _ N => polyFuel C d N) (fun _ N => polyFuel C d N)
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
    (hrow_at_polyFuel sources k r p.clauseDegree C d hd)
    (fun N hN => hrest_at_schedule sources k r p.clauseDegree N
      (le_trans (partsOnset_le_repinOnset sources k r p.clauseDegree C) hN))
    rfl

theorem poly_polylog_le_polyFuel (a c e C d : ℕ) (hC : 1 ≤ C) (ha : a + 1 ≤ d) :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      (N + 1) ^ a * (c * logScale N ^ e) ≤ polyFuel C d N := by
  obtain ⟨onset, honset⟩ :=
    SupplierCapacity.coefficient_mul_logScale_pow_eventually_le c e
  refine ⟨onset, fun N hN => ?_⟩
  have h1 : (N + 1) ^ a * (c * logScale N ^ e) ≤ (N + 1) ^ a * (N + 1) :=
    Nat.mul_le_mul_left _ (le_trans (honset N hN) (Nat.le_succ N))
  have h2 : (N + 1) ^ a * (N + 1) = (N + 1) ^ (a + 1) := by rw [pow_succ]
  have h3 : ((N : ℕ) + 1) ^ (a + 1) ≤ (N + 1) ^ d := Nat.pow_le_pow_right (by omega) ha
  have h4 : ((N : ℕ) + 1) ^ d ≤ C * (N + 1) ^ d := by
    calc ((N : ℕ) + 1) ^ d = 1 * (N + 1) ^ d := by ring
      _ ≤ C * (N + 1) ^ d := Nat.mul_le_mul_right _ hC
  show (N + 1) ^ a * (c * logScale N ^ e) ≤ C * (N + 1) ^ d
  omega

open C10TailComposeUniform (records StageReady pcppOf)

theorem records_repin_eq (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C d : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    records sources k p (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfPolyFuel sources k p r C d P)) x bits ph
      = records sources k p (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfSchedule sources k p r P)) x bits ph := rfl

theorem stageReady_at_polyFuel (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r m C d : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    (he : 58 ≤ (C10StageSeamBridge.stageData_of_parts sources k p
      (partsOfPolyFuel sources k p r C d P)).e)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) (Lval : ℕ)
    (hq : 1 ≤ widthAt sources k n)
    (hL : ∀ i, ((P.coordinate n x bits) i).monomials.length ≤ Lval)
    (hLfit : Lval + 1 ≤ widthPower sources k m n)
    (hfit : (pcppOf sources k p x bits).clauseBits
      ≤ clauseBitsSchedule sources k p.clauseDegree n)
    (hr : 2 * p.clauseDegree + 4 * m + 5 ≤ r)
    (hcalls : C10SupplierStage.CallsReady
      (partsOfPolyFuel sources k p r C d P).extra
      ((partsOfPolyFuel sources k p r C d P).calls ph)
      ((partsOfPolyFuel sources k p r C d P).callFuel ph n)
      ((partsOfPolyFuel sources k p r C d P).entryWidth n)
      (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfPolyFuel sources k p r C d P)) x bits ph).length
      (CloseoutRowsEstimatorCoefficients.Stream.words
        ((partsOfPolyFuel sources k p r C d P).entryWidth n)
        (records sources k p (C10StageSeamBridge.stageData_of_parts sources k p
          (partsOfPolyFuel sources k p r C d P)) x bits ph))
      (List.ofFn x) bits) :
    ∃ (bank : Fin 218 → List Bool)
      (scratch : Fin (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfPolyFuel sources k p r C d P)).e → List Bool),
      StageReady sources k p (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfPolyFuel sources k p r C d P)) he x bits ph bank scratch :=
  C10RecordPadding.stageReady_of_stageRun_cap sources k p
    (partsOfPolyFuel sources k p r C d P) he x bits ph
    (C10RecordPadding.records_length_le_callCount sources k p r m P x bits ph Lval hq hL hLfit
      hfit hr)
    hcalls

end
end NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin

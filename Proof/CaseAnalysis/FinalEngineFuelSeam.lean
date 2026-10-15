import Proof.CaseAnalysis.FinalSeedEngine
import Proof.CaseAnalysis.FinalFuelRepin
import Proof.CaseAnalysis.FinalRoundEmitter
import Proof.PCP.ProjectionDimensionsFromInputBounds
import Proof.CaseAnalysis.ScheduleClauseWidth
import Proof.CaseAnalysis.CapacityPower
import Proof.PCP.ProjectionNormalizationCounter

namespace NearCubicWires.RepairSource.CloseoutFinal.C10EngineFuelSeam

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SeedEngine
  (readerFuel engineFuel readerHier readerPad readerCode readerPad_ge widthReader
   readerIn readerQ readerIn_ne width_reader prologue_at_schedule)
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## Section 1  Two envelopes: polylogarithmic, and quasi-linear -/

/-- `f` is bounded by a fixed power of `logScale` (`Proof/Foundations/Semantics.lean`). -/
def Polylog (f : ℕ → ℕ) : Prop := ∃ c e : ℕ, ∀ N, f N ≤ c * logScale N ^ e

/-- `f` is bounded by `N` times a fixed power of `logScale` -- degree ONE, which is what
`poly_polylog_le_polyFuel` (`Proof/CaseAnalysis/FinalFuelRepin.lean`) meets at `d = 2`. -/
def LinBound (f : ℕ → ℕ) : Prop := ∃ c e : ℕ, ∀ N, f N ≤ (N + 1) * (c * logScale N ^ e)

theorem one_le_logScale (N : ℕ) : 1 ≤ logScale N :=
  Nat.clog_pos (by norm_num) (by omega)

theorem logPow_mono (N : ℕ) {e e' : ℕ} (h : e ≤ e') : logScale N ^ e ≤ logScale N ^ e' :=
  Nat.pow_le_pow_right (one_le_logScale N) h

theorem polylog_mono {f g : ℕ → ℕ} (h : ∀ N, f N ≤ g N) (hg : Polylog g) : Polylog f := by
  obtain ⟨c, e, hc⟩ := hg
  exact ⟨c, e, fun N => (h N).trans (hc N)⟩

theorem polylog_const (a : ℕ) : Polylog (fun _ => a) := by
  refine ⟨a, 0, fun N => ?_⟩
  rw [pow_zero, Nat.mul_one]

theorem polylog_add {f g : ℕ → ℕ} (hf : Polylog f) (hg : Polylog g) :
    Polylog (fun N => f N + g N) := by
  obtain ⟨c1, e1, h1⟩ := hf
  obtain ⟨c2, e2, h2⟩ := hg
  refine ⟨c1 + c2, max e1 e2, fun N => ?_⟩
  show f N + g N ≤ (c1 + c2) * logScale N ^ max e1 e2
  have k1 : c1 * logScale N ^ e1 ≤ c1 * logScale N ^ max e1 e2 :=
    Nat.mul_le_mul_left _ (logPow_mono N (le_max_left _ _))
  have k2 : c2 * logScale N ^ e2 ≤ c2 * logScale N ^ max e1 e2 :=
    Nat.mul_le_mul_left _ (logPow_mono N (le_max_right _ _))
  have hsum : (c1 + c2) * logScale N ^ max e1 e2
      = c1 * logScale N ^ max e1 e2 + c2 * logScale N ^ max e1 e2 := by ring
  have hx := h1 N
  have hy := h2 N
  omega

theorem polylog_mul {f g : ℕ → ℕ} (hf : Polylog f) (hg : Polylog g) :
    Polylog (fun N => f N * g N) := by
  obtain ⟨c1, e1, h1⟩ := hf
  obtain ⟨c2, e2, h2⟩ := hg
  refine ⟨c1 * c2, e1 + e2, fun N => ?_⟩
  show f N * g N ≤ c1 * c2 * logScale N ^ (e1 + e2)
  have hstep : f N * g N ≤ c1 * logScale N ^ e1 * (c2 * logScale N ^ e2) :=
    Nat.mul_le_mul (h1 N) (h2 N)
  have hform : c1 * logScale N ^ e1 * (c2 * logScale N ^ e2)
      = c1 * c2 * logScale N ^ (e1 + e2) := by rw [pow_add]; ring
  omega

theorem polylog_pow {f : ℕ → ℕ} (hf : Polylog f) (m : ℕ) : Polylog (fun N => f N ^ m) := by
  induction m with
  | zero => exact polylog_mono (fun N => le_of_eq (pow_zero (f N))) (polylog_const 1)
  | succ i ih => exact polylog_mono (fun N => le_of_eq (pow_succ (f N) i)) (polylog_mul ih hf)

theorem linBound_of_polylog {f : ℕ → ℕ} (hf : Polylog f) : LinBound f := by
  obtain ⟨c, e, hc⟩ := hf
  exact ⟨c, e, fun N => (hc N).trans (Nat.le_mul_of_pos_left _ (by omega))⟩

theorem linBound_mono {f g : ℕ → ℕ} (h : ∀ N, f N ≤ g N) (hg : LinBound g) : LinBound f := by
  obtain ⟨c, e, hc⟩ := hg
  exact ⟨c, e, fun N => (h N).trans (hc N)⟩

theorem linBound_add {f g : ℕ → ℕ} (hf : LinBound f) (hg : LinBound g) :
    LinBound (fun N => f N + g N) := by
  obtain ⟨c1, e1, h1⟩ := hf
  obtain ⟨c2, e2, h2⟩ := hg
  refine ⟨c1 + c2, max e1 e2, fun N => ?_⟩
  show f N + g N ≤ (N + 1) * ((c1 + c2) * logScale N ^ max e1 e2)
  have k1 : (N + 1) * (c1 * logScale N ^ e1) ≤ (N + 1) * (c1 * logScale N ^ max e1 e2) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (logPow_mono N (le_max_left _ _)))
  have k2 : (N + 1) * (c2 * logScale N ^ e2) ≤ (N + 1) * (c2 * logScale N ^ max e1 e2) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (logPow_mono N (le_max_right _ _)))
  have hsum : (N + 1) * ((c1 + c2) * logScale N ^ max e1 e2)
      = (N + 1) * (c1 * logScale N ^ max e1 e2) + (N + 1) * (c2 * logScale N ^ max e1 e2) := by
    ring
  have hx := h1 N
  have hy := h2 N
  omega

theorem linBound_mul_polylog {f g : ℕ → ℕ} (hf : LinBound f) (hg : Polylog g) :
    LinBound (fun N => f N * g N) := by
  obtain ⟨c1, e1, h1⟩ := hf
  obtain ⟨c2, e2, h2⟩ := hg
  refine ⟨c1 * c2, e1 + e2, fun N => ?_⟩
  show f N * g N ≤ (N + 1) * (c1 * c2 * logScale N ^ (e1 + e2))
  have hstep : f N * g N ≤ (N + 1) * (c1 * logScale N ^ e1) * (c2 * logScale N ^ e2) :=
    Nat.mul_le_mul (h1 N) (h2 N)
  have hform : (N + 1) * (c1 * logScale N ^ e1) * (c2 * logScale N ^ e2)
      = (N + 1) * (c1 * c2 * logScale N ^ (e1 + e2)) := by rw [pow_add]; ring
  omega

theorem linBound_linear (a : ℕ) : LinBound (fun N => a * (N + 1)) := by
  refine ⟨a, 0, fun N => ?_⟩
  have h : (N + 1) * (a * logScale N ^ 0) = a * (N + 1) := by
    rw [pow_zero, Nat.mul_one, Nat.mul_comm]
  exact le_of_eq h.symm

/-! ## Section 2  The two number-theoretic bridges -/

/-- `Nat.clog 2 m` never exceeds `m`. -/
theorem clog_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  Nat.clog_le_of_le_pow (le_of_lt Nat.lt_two_pow_self)

/-- `2 ^ Nat.clog 2 m` is within a factor two of `m`. -/
theorem two_pow_clog_le (m : ℕ) : 2 ^ Nat.clog 2 m ≤ 2 * m + 2 := by
  by_cases hm : 1 < m
  · have hlt : 2 ^ (Nat.clog 2 m - 1) < m := Nat.pow_pred_clog_lt_self (by norm_num) hm
    have hpos : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) hm
    have hsplit : 2 ^ Nat.clog 2 m = 2 ^ (Nat.clog 2 m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    omega
  · have hone : (2 : ℕ) ^ 0 = 1 := by norm_num
    have hle : m ≤ 2 ^ 0 := by omega
    have h0 : Nat.clog 2 m ≤ 0 := Nat.clog_le_of_le_pow hle
    have hmono : (2 : ℕ) ^ Nat.clog 2 m ≤ 2 ^ 0 := Nat.pow_le_pow_right (by norm_num) h0
    omega

/-- The ledger's `q` (`Proof/PCP/PCPResourceLedger.lean`) is within a factor two of `logScale`. -/
theorem q_le_logScale (N : ℕ) : PCPResourceLedger.q N ≤ 2 * logScale N := by
  have h : Nat.clog 2 (N + 1) ≤ logScale N := Nat.clog_mono_right 2 (by omega)
  have h1 := one_le_logScale N
  show Nat.clog 2 (N + 1) + 1 ≤ 2 * logScale N
  omega

theorem polylog_q : Polylog PCPResourceLedger.q := by
  refine ⟨2, 1, fun N => ?_⟩
  rw [pow_one]
  exact q_le_logScale N

/-- **`q` at a LINEARLY larger argument is still polylogarithmic in `N`.**  This is what lets the
padded hierarchy input -- linear in `N` by `PowerSlice.linear_length`
(`Proof/PCP/PCPPowerSlice.lean`) -- contribute only polylog factors. -/
theorem q_le_of_linear (A M N : ℕ) (h : M ≤ A * (N + 1)) :
    PCPResourceLedger.q M ≤ (natBitLength A + 2) * logScale N := by
  have hA : A + 1 ≤ 2 ^ natBitLength A := by
    show A + 1 ≤ 2 ^ (Nat.log 2 A + 1)
    exact Nat.lt_pow_succ_log_self (by norm_num) A
  have hN : N + 2 ≤ 2 ^ logScale N := Nat.le_pow_clog (by norm_num) (N + 2)
  have hexp : A * (N + 1) + 1 ≤ (A + 1) * (N + 2) := by nlinarith
  have hprod : (A + 1) * (N + 2) ≤ 2 ^ natBitLength A * 2 ^ logScale N := Nat.mul_le_mul hA hN
  rw [← pow_add] at hprod
  have hstep : M + 1 ≤ 2 ^ (natBitLength A + logScale N) := by omega
  have hclog : Nat.clog 2 (M + 1) ≤ natBitLength A + logScale N := Nat.clog_le_of_le_pow hstep
  have hL := one_le_logScale N
  have hmul : natBitLength A ≤ natBitLength A * logScale N :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hform : (natBitLength A + 2) * logScale N
      = natBitLength A * logScale N + logScale N + logScale N := by ring
  show Nat.clog 2 (M + 1) + 1 ≤ (natBitLength A + 2) * logScale N
  omega

/-- The padded length of the reader's own hierarchy input, as a function of `N` alone. -/
noncomputable def padLen (sources : EightSources) (k N : ℕ) : ℕ :=
  HierarchyBinary.inputLength k (readerPad sources k) (readerCode sources k).length
    (readerHier sources k).coefficient N

theorem rawInput_length (sources : EightSources) (k N : ℕ) :
    (HierarchyPadding.rawInput k (readerHier sources k).coefficient (readerPad sources k)
        (readerCode sources k) (List.replicate N false)).length = padLen sources k N := by
  have h := HierarchyPadding.raw_length k (readerHier sources k).coefficient (readerPad sources k)
    (readerCode sources k) (List.replicate N false) (readerPad_ge sources k)
  rw [List.length_replicate] at h
  exact h

/-- **The padded length is LINEAR in `N`**, with `PowerSlice.linear_length`'s own coefficient --
which is `HierarchyReduction.linearCoefficient` (`Proof/Hierarchy/HierarchyReductionTime.lean`) verbatim. -/
theorem padLen_le (sources : EightSources) (k N : ℕ) :
    padLen sources k N
      ≤ HierarchyReduction.linearCoefficient k (readerHier sources k).coefficient
          (readerPad sources k) (readerCode sources k) * (N + 1) :=
  (PowerSlice.linear_length k (2 * readerPad sources k)
    (HierarchyBinary.header (readerCode sources k).length
      (readerHier sources k).coefficient) N).2

theorem polylog_qPad (sources : EightSources) (k : ℕ) :
    Polylog (fun N => PCPResourceLedger.q (padLen sources k N)) := by
  refine ⟨natBitLength (HierarchyReduction.linearCoefficient k (readerHier sources k).coefficient
    (readerPad sources k) (readerCode sources k)) + 2, 1, fun N => ?_⟩
  rw [pow_one]
  exact q_le_of_linear _ _ _ (padLen_le sources k N)

/-- The aggregate clock's bit length is polylogarithmic: `ClockEnvelope.exponent_bound`
(`Proof/MachineModel/ClockEnvelope.lean`) through `DimensionsFromInput.clock_bitLength`
(`Proof/PCP/ProjectionDimensionsFromInputBounds.lean`). -/
theorem bitLength_time_le (M : ℕ) :
    natBitLength (UAggregateClock.time M) + 1 ≤ (5 + 23 + 4) * PCPResourceLedger.q M ^ 2 := by
  have h1 := DimensionsFromInput.clock_bitLength M
  have h2 := ClockEnvelope.exponent_bound 23 5 M
  omega

theorem ordinaryBudget_replicate (sources : EightSources) (k N : ℕ) :
    HierarchyReduction.ordinaryBudget k (readerHier sources k).coefficient (readerPad sources k)
        (readerCode sources k) (List.replicate N false)
      = HierarchyReduction.runtimeCoefficient k (readerHier sources k).coefficient
          (readerPad sources k) (readerCode sources k) * (N + 1) * PCPResourceLedger.q N ^ 2 := by
  unfold HierarchyReduction.ordinaryBudget
  rw [List.length_replicate]

theorem readerFuel_eq (sources : EightSources) (k N : ℕ) :
    readerFuel sources k N
      = HierarchyReduction.ordinaryBudget k (readerHier sources k).coefficient
            (readerPad sources k) (readerCode sources k) (List.replicate N false)
          + 1 + (4 * padLen sources k N + 4) + 1
        + DimensionsFromInput.budget (fixedProjection sources).degrees.proofLog
            (fixedProjection sources).degrees.queries (fixedProjection sources).coefficient
            (HierarchyPadding.rawInput k (readerHier sources k).coefficient (readerPad sources k)
              (readerCode sources k) (List.replicate N false)) := by
  have h := rawInput_length sources k N
  unfold readerFuel HierarchyPrefix.budget HierarchyFramedInput.budget
  rw [h]

theorem dimFromInput_le (sources : EightSources) (k N : ℕ) :
    DimensionsFromInput.budget (fixedProjection sources).degrees.proofLog
        (fixedProjection sources).degrees.queries (fixedProjection sources).coefficient
        (HierarchyPadding.rawInput k (readerHier sources k).coefficient (readerPad sources k)
          (readerCode sources k) (List.replicate N false))
      ≤ 11658 * (padLen sources k N + 1) * PCPResourceLedger.q (padLen sources k N) ^ 2 + 1
        + DimensionProducer.coefficient (fixedProjection sources).degrees.proofLog
              (fixedProjection sources).degrees.queries (fixedProjection sources).coefficient
            * (natBitLength (UAggregateClock.time (padLen sources k N)) + 1)
              ^ DimensionProducer.degree (fixedProjection sources).degrees.proofLog
                  (fixedProjection sources).degrees.queries := by
  have h := DimensionsFromInput.budget_bound (fixedProjection sources).degrees.proofLog
    (fixedProjection sources).degrees.queries (fixedProjection sources).coefficient
    (HierarchyPadding.rawInput k (readerHier sources k).coefficient (readerPad sources k)
      (readerCode sources k) (List.replicate N false))
  rwa [rawInput_length sources k N] at h

theorem linBound_readerFuel (sources : EightSources) (k : ℕ) : LinBound (readerFuel sources k) := by
  refine linBound_mono (fun N => le_of_eq (readerFuel_eq sources k N)) ?_
  have hone : LinBound (fun _ : ℕ => (1 : ℕ)) := linBound_of_polylog (polylog_const 1)
  have h1 : LinBound (fun N => HierarchyReduction.ordinaryBudget k
      (readerHier sources k).coefficient (readerPad sources k) (readerCode sources k)
      (List.replicate N false)) := by
    refine linBound_mono (fun N => le_of_eq (ordinaryBudget_replicate sources k N)) ?_
    exact linBound_mul_polylog (linBound_linear _) (polylog_pow polylog_q 2)
  have h3 : LinBound (fun N => 4 * padLen sources k N + 4) := by
    refine linBound_mono (fun N => ?_)
      (linBound_linear (4 * HierarchyReduction.linearCoefficient k
        (readerHier sources k).coefficient (readerPad sources k) (readerCode sources k) + 4))
    have hp := padLen_le sources k N
    calc 4 * padLen sources k N + 4
        ≤ 4 * (HierarchyReduction.linearCoefficient k (readerHier sources k).coefficient
            (readerPad sources k) (readerCode sources k) * (N + 1)) + 4 * (N + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 4 hp) (by omega)
      _ = (4 * HierarchyReduction.linearCoefficient k (readerHier sources k).coefficient
            (readerPad sources k) (readerCode sources k) + 4) * (N + 1) := by ring
  have h4a : LinBound (fun N => 11658 * (padLen sources k N + 1)) := by
    refine linBound_mono (fun N => ?_)
      (linBound_linear (11658 * (HierarchyReduction.linearCoefficient k
        (readerHier sources k).coefficient (readerPad sources k) (readerCode sources k) + 1)))
    have hp := padLen_le sources k N
    calc 11658 * (padLen sources k N + 1)
        ≤ 11658 * (HierarchyReduction.linearCoefficient k (readerHier sources k).coefficient
            (readerPad sources k) (readerCode sources k) * (N + 1) + (N + 1)) :=
          Nat.mul_le_mul_left 11658 (Nat.add_le_add hp (by omega))
      _ = 11658 * (HierarchyReduction.linearCoefficient k (readerHier sources k).coefficient
            (readerPad sources k) (readerCode sources k) + 1) * (N + 1) := by ring
  have h4c : Polylog (fun N =>
      DimensionProducer.coefficient (fixedProjection sources).degrees.proofLog
          (fixedProjection sources).degrees.queries (fixedProjection sources).coefficient
        * (natBitLength (UAggregateClock.time (padLen sources k N)) + 1)
          ^ DimensionProducer.degree (fixedProjection sources).degrees.proofLog
              (fixedProjection sources).degrees.queries) := by
    refine polylog_mul (polylog_const _) (polylog_pow ?_ _)
    refine polylog_mono (fun N => bitLength_time_le (padLen sources k N)) ?_
    exact polylog_mul (polylog_const _) (polylog_pow (polylog_qPad sources k) 2)
  have h4 : LinBound (fun N => DimensionsFromInput.budget
      (fixedProjection sources).degrees.proofLog (fixedProjection sources).degrees.queries
      (fixedProjection sources).coefficient
      (HierarchyPadding.rawInput k (readerHier sources k).coefficient (readerPad sources k)
        (readerCode sources k) (List.replicate N false))) := by
    refine linBound_mono (fun N => dimFromInput_le sources k N) ?_
    exact linBound_add (linBound_add
      (linBound_mul_polylog h4a (polylog_pow (polylog_qPad sources k) 2)) hone)
      (linBound_of_polylog h4c)
  exact linBound_add (linBound_add (linBound_add (linBound_add h1 hone) h3) hone) h4

/-! ## Section 4  Every other stage sees only `q(N)`, and is polylogarithmic -/

theorem polylog_widthAt (sources : EightSources) (k : ℕ) : Polylog (widthAt sources k) := by
  refine ⟨widthConst sources k, 1, fun N => ?_⟩
  rw [pow_one]
  exact le_trans (Nat.le_succ _) (widthAt_succ_le sources k N)

theorem polylog_dimPoly {f : ℕ → ℕ} (hf : Polylog f) (D C : ℕ) :
    Polylog (fun N => DimensionPolynomial.budget D C (f N)) := by
  refine polylog_mono (fun N => DimensionPolynomial.budget_bound D C (f N)) ?_
  exact polylog_mul (polylog_const _) (polylog_pow (polylog_add hf (polylog_const 2)) _)

theorem polylog_clogBudget {f : ℕ → ℕ} (hf : Polylog f) :
    Polylog (fun N => CloseoutSchedule.Clog.budget (f N)) := by
  refine polylog_mono (fun N => CloseoutSchedule.Clog.budget_bound (f N)) ?_
  exact polylog_mul (polylog_const 128) (polylog_pow (polylog_add hf (polylog_const 1)) 2)

theorem polylog_clauseWidth (sources : EightSources) (k D : ℕ) :
    Polylog (fun N => CloseoutLanguage.clauseWidth D (widthAt sources k N)) := by
  refine polylog_mono (fun N => clog_le_self ((widthAt sources k N + 2) ^ D)) ?_
  exact polylog_pow (polylog_add (polylog_widthAt sources k) (polylog_const 2)) D

theorem polylog_twoPowClauseWidth (sources : EightSources) (k D : ℕ) :
    Polylog (fun N => 2 ^ CloseoutLanguage.clauseWidth D (widthAt sources k N)) := by
  refine polylog_mono (fun N => two_pow_clog_le ((widthAt sources k N + 2) ^ D)) ?_
  exact polylog_add (polylog_mul (polylog_const 2)
      (polylog_pow (polylog_add (polylog_widthAt sources k) (polylog_const 2)) D))
    (polylog_const 2)

theorem polylog_clauseBudget (sources : EightSources) (k D : ℕ) :
    Polylog (fun N => CloseoutSchedule.Clause.budget D (widthAt sources k N)) := by
  refine polylog_mono (g := fun N => 2 * widthAt sources k N + 4 + 1
      + DimensionPolynomial.budget D 1 (widthAt sources k N + 1) + 1
      + CloseoutSchedule.Clog.budget ((widthAt sources k N + 2) ^ D))
    (fun N => le_of_eq rfl) ?_
  refine polylog_add (polylog_add (polylog_add (polylog_add ?_ (polylog_const 1)) ?_)
    (polylog_const 1)) ?_
  · exact polylog_add (polylog_mul (polylog_const 2) (polylog_widthAt sources k))
      (polylog_const 4)
  · exact polylog_dimPoly (polylog_add (polylog_widthAt sources k) (polylog_const 1)) D 1
  · exact polylog_clogBudget
      (polylog_pow (polylog_add (polylog_widthAt sources k) (polylog_const 2)) D)

/-- `Power.budget d` (`Proof/CaseAnalysis/CapacityPower.lean`) is `32d + 171 + 2^d*(16d+72)`. -/
theorem power_budget_le (d : ℕ) :
    CloseoutCapacity.Power.budget d ≤ 200 * (d + 1) * (2 ^ d + 1) := by
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
  unfold CloseoutCapacity.Power.budget MatrixScorePower.budget MatrixUnaryTemplate.budget
  nlinarith [h1, Nat.zero_le d]

theorem polylog_powerBudget {f : ℕ → ℕ} (hf : Polylog f) (hp : Polylog (fun N => 2 ^ f N)) :
    Polylog (fun N => CloseoutCapacity.Power.budget (f N)) := by
  refine polylog_mono (fun N => power_budget_le (f N)) ?_
  exact polylog_mul (polylog_mul (polylog_const 200) (polylog_add hf (polylog_const 1)))
    (polylog_add hp (polylog_const 1))

theorem polylog_counterBudget {f : ℕ → ℕ} (hf : Polylog f) :
    Polylog (fun N => Counter.budget (f N)) := by
  refine polylog_mono (g := fun N => 10 * f N + 13) (fun N => le_of_eq rfl) ?_
  exact polylog_add (polylog_mul (polylog_const 10) hf) (polylog_const 13)

/-! ## Section 5  The prologue's fuel, split into its quasi-linear and polylog halves -/

/-- Everything `engineFuel` (`Proof/CaseAnalysis/FinalSeedEngine.lean`) charges beyond the
reader's own budget. -/
noncomputable def engineRest (sources : EightSources) (k r D : ℕ) (N : ℕ) : ℕ :=
  DimensionPolynomial.budget r 1 (widthAt sources k N)
    + CloseoutSchedule.Clause.budget D (widthAt sources k N)
    + 2 * CloseoutLanguage.clauseWidth D (widthAt sources k N)
    + 2 * (widthAt sources k N + 1) ^ r
    + 4 * thresholdFloor sources
    + 19

/-- Everything `prologueFuel` (`Proof/CaseAnalysis/FinalPrologueUniform.lean`) charges beyond
the seed. -/
noncomputable def prologueRest (sources : EightSources) (k D : ℕ) (N : ℕ) : ℕ :=
  CloseoutCapacity.Power.budget (CloseoutLanguage.clauseWidth D (widthAt sources k N))
    + Counter.budget (2 ^ CloseoutLanguage.clauseWidth D (widthAt sources k N))
    + 9

noncomputable def enginePreFuel (sources : EightSources) (k r D : ℕ) : ℕ → ℕ :=
  C10PrologueUniform.prologueFuel D (widthAt sources k)
    (engineFuel r D (readerFuel sources k) (thresholdFloor sources) (widthAt sources k))

theorem engineFuel_eq (sources : EightSources) (k r D N : ℕ) :
    engineFuel r D (readerFuel sources k) (thresholdFloor sources) (widthAt sources k) N
      = readerFuel sources k N + engineRest sources k r D N := by
  unfold engineFuel engineRest
  omega

theorem enginePreFuel_eq (sources : EightSources) (k r D N : ℕ) :
    enginePreFuel sources k r D N
      = readerFuel sources k N + (engineRest sources k r D N + prologueRest sources k D N) := by
  have h := engineFuel_eq sources k r D N
  unfold enginePreFuel C10PrologueUniform.prologueFuel prologueRest
  rw [h]
  omega

theorem polylog_engineRest (sources : EightSources) (k r D : ℕ) :
    Polylog (engineRest sources k r D) := by
  refine polylog_mono (g := fun N => DimensionPolynomial.budget r 1 (widthAt sources k N)
      + CloseoutSchedule.Clause.budget D (widthAt sources k N)
      + 2 * CloseoutLanguage.clauseWidth D (widthAt sources k N)
      + 2 * (widthAt sources k N + 1) ^ r
      + 4 * thresholdFloor sources
      + 19) (fun N => le_of_eq rfl) ?_
  refine polylog_add (polylog_add (polylog_add (polylog_add (polylog_add ?_ ?_) ?_) ?_)
    (polylog_const _)) (polylog_const 19)
  · exact polylog_dimPoly (polylog_widthAt sources k) r 1
  · exact polylog_clauseBudget sources k D
  · exact polylog_mul (polylog_const 2) (polylog_clauseWidth sources k D)
  · exact polylog_mul (polylog_const 2)
      (polylog_pow (polylog_add (polylog_widthAt sources k) (polylog_const 1)) r)

theorem polylog_prologueRest (sources : EightSources) (k D : ℕ) :
    Polylog (prologueRest sources k D) := by
  refine polylog_mono (g := fun N =>
      CloseoutCapacity.Power.budget (CloseoutLanguage.clauseWidth D (widthAt sources k N))
      + Counter.budget (2 ^ CloseoutLanguage.clauseWidth D (widthAt sources k N))
      + 9) (fun N => le_of_eq rfl) ?_
  refine polylog_add (polylog_add ?_ ?_) (polylog_const 9)
  · exact polylog_powerBudget (polylog_clauseWidth sources k D)
      (polylog_twoPowClauseWidth sources k D)
  · exact polylog_counterBudget (polylog_twoPowClauseWidth sources k D)

theorem linBound_enginePreFuel (sources : EightSources) (k r D : ℕ) :
    LinBound (enginePreFuel sources k r D) := by
  refine linBound_mono (fun N => le_of_eq (enginePreFuel_eq sources k r D N)) ?_
  exact linBound_add (linBound_readerFuel sources k)
    (linBound_of_polylog (polylog_add (polylog_engineRest sources k r D)
      (polylog_prologueRest sources k D)))

/-! ## Section 6  The fit: degree TWO -/

theorem enginePreFuel_le_polyFuel (sources : EightSources) (k r D C : ℕ) (hC : 1 ≤ C) :
    ∃ onset : ℕ, ∀ N, onset ≤ N → enginePreFuel sources k r D N ≤ polyFuel C 2 N := by
  obtain ⟨c, e, hce⟩ := linBound_enginePreFuel sources k r D
  obtain ⟨onset, honset⟩ := poly_polylog_le_polyFuel 1 c e C 2 hC (by omega)
  refine ⟨onset, fun N hN => ?_⟩
  have h := honset N hN
  rw [pow_one] at h
  exact (hce N).trans h

theorem prologue_at_polyFuel (sources : EightSources) (k r D : ℕ) (hD : 1 ≤ D) (C : ℕ)
    (hC : 1 ≤ C) :
    ∃ (extra ps onset : ℕ) (pre : LocalBitMultitape.Machine (218 + (60 + extra) + 1) ps),
      C10PrologueUniform.Prologue extra (entryWidthSchedule sources k r) (widthAt sources k) D
          (enginePreFuel sources k r D) pre ∧
        ∀ N, onset ≤ N → enginePreFuel sources k r D N ≤ polyFuel C 2 N := by
  obtain ⟨onset, honset⟩ := enginePreFuel_le_polyFuel sources k r D C hC
  exact ⟨_, _, onset, _,
    prologue_at_schedule sources k r D hD (widthReader sources k) (readerIn sources k)
      (readerQ sources k) (readerIn_ne sources k) (readerFuel sources k) (width_reader sources k),
    honset⟩

/-! ## Section 7  The composition: the real call loop at the RE-PINNED field -/

theorem callsReady_at_polyFuel_of_prologue (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (r C : ℕ) (P : C10StageSeamBridge.Parts sources k p)
    (extra : ℕ) {ps bs : ℕ}
    (pre : LocalBitMultitape.Machine (218 + (60 + extra) + 1) ps)
    (body : LocalBitMultitape.Machine (218 + (60 + extra)) bs)
    (hpro : C10PrologueUniform.Prologue extra (entryWidthSchedule sources k r)
      (widthAt sources k) p.clauseDegree (enginePreFuel sources k r p.clauseDegree) pre)
    (N : ℕ) (x : BitInput N) (bits : List Bool)
    (answer : List Atom → ℕ) (denominator : ℕ) (phase : Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (callCount cost : ℕ) (ph : Phase)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hfit : pcpp.clauseBits ≤ clauseBitsSchedule sources k p.clauseDegree N)
    (hdet : C10RoundEmitter.AddressDeterminacy answer denominator phase pcpp coordinate
      systematicAtom)
    (happends : C10RoundEmitter.Appends extra body cost (entryWidthSchedule sources k r N)
      (List.ofFn x) bits
      (C10RoundEmitter.nextRecords answer denominator phase pcpp coordinate systematicAtom)
      (C10RoundEmitter.Reachable answer denominator phase pcpp coordinate systematicAtom))
    (hfuel : enginePreFuel sources k r p.clauseDegree N ≤ polyFuel C 2 N)
    (hcost : cost ≤ polyFuel C 2 N) :
    C10SupplierStage.CallsReady (extra + 2) (C10SupplierCall.callMachine extra pre body)
      ((partsOfPolyFuel sources k p r C 2 P).callFuel ph N)
      (entryWidthSchedule sources k r N) callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidthSchedule sources k r N)
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      (List.ofFn x) bits :=
  C10CallFuelMono.callsReady_enlarge
    (C10RoundEmitter.callsReady_of_appends extra pre body answer denominator phase pcpp
      coordinate systematicAtom (entryWidthSchedule sources k r N) callCount
      (enginePreFuel sources k r p.clauseDegree N) cost p.clauseDegree (widthAt sources k N)
      (List.ofFn x) bits hlen hfit hdet happends (hpro N x bits))
    (callFuel_mono _ _ _ _ _ _ hfuel le_rfl hcost)

noncomputable def runtime_at_engineDegree (sources : EightSources) (k : ℕ) (hk : 1 ≤ k) {gamma : ℝ}
    (p : Parameters sources gamma) (r C : ℕ) (P : C10StageSeamBridge.Parts sources k p) :
    Runtime sources k (PolynomialClock.ordinaryClock k)
      (C10StageSeamBridge.stageData_of_parts sources k p
        (partsOfPolyFuel sources k p r C 2 P)).budget :=
  runtime_of_polyFuel sources k p r C 2 (by omega) P

end NearCubicWires.RepairSource.CloseoutFinal.C10EngineFuelSeam

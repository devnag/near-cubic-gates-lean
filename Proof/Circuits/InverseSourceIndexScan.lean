import Proof.MachineModel.CanonicalTwoPowProgram
import Proof.MachineModel.SourceDrivenNumeralBank

/-!
# The inverse schedule's `inverseSourceIndex`, executed

`SelectorDrivenLengthStage` discharged the *fixed* schedule's length residual,
where the length is `sourceLength` of the selected source itself.  The *inverse*
schedule applies one more map — `RecoveryScheduleEnvelope.inverseSourceIndex` —
between the selected source and the source length:

```
inverseScheduleLength … target =
  sourceLength (inverseSourceIndex (inverseSelectedSource … target)).
```

`inverseSourceIndex k = Nat.findGreatest (fun j => inverseSourceMeasure j ≤ k+2)
(k+1)` with `inverseSourceMeasure j = (j+1) · logScale (j+1) = (j+1) · clog₂(j+3)`.
This module supplies the executable scan.

## The design

The predicate is a monotone threshold, so the answer is the largest `j` with
`measure j ≤ k+2`; §0 proves the two-inequality characterization that turns a
program output into `inverseSourceIndex k`, and the clog-crossing arithmetic the
loop's register discipline needs.  §1 is the loop: four data registers
`j`, `c = clog₂(j+3)`, `q = 2^c`, `prod = (j+1)·c = measure j`, advanced by
*additions only* — no inner multiply and no inner clog loop — with the crossing
test the equality `q = j+3` and `prod` updated by `prod += c` (no cross) or
`prod += c + (j+2)` (cross).  §2 assembles the inverse length program and §3
discharges `SourceDrivenNumeralBank.InverseScheduledLengthRuns`.
-/

namespace NearCubicWires.InverseSourceIndexScan

open NearCubicWires
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope

/-! ## 0. The scan is correct once it reports the threshold -/

/-- `inverseSourceMeasure` is monotone: `(j+1)·clog₂(j+3)` in both factors. -/
theorem inverseSourceMeasure_mono {left right : ℕ} (hle : left ≤ right) :
    inverseSourceMeasure left ≤ inverseSourceMeasure right :=
  Nat.mul_le_mul (by omega) (logScale_mono (by omega))

/-- **The scan's contract.**  A candidate that meets the threshold and whose
successor breaks it is exactly `inverseSourceIndex k`.  Both inputs are what the
loop reports at exit: `prod = measure v ≤ k+2` and the freeze reason
`measure (v+1) > k+2`. -/
theorem inverseSourceIndex_eq_of_threshold (k v : ℕ)
    (hle : inverseSourceMeasure v ≤ k + 2)
    (hgt : k + 2 < inverseSourceMeasure (v + 1)) :
    inverseSourceIndex k = v := by
  have hlower : v ≤ inverseSourceIndex k :=
    le_inverseSourceIndex_of_measure_le v k hle
  have hupper : inverseSourceIndex k ≤ v := by
    by_contra hnot
    have hstep : v + 1 ≤ inverseSourceIndex k := by omega
    have hmono :
        inverseSourceMeasure (v + 1) ≤
          inverseSourceMeasure (inverseSourceIndex k) :=
      inverseSourceMeasure_mono hstep
    have hspec := inverseSourceIndex_measure_le k
    omega
  omega

/-! ### clog-crossing arithmetic -/

/-- Off a power boundary the base-two ceiling logarithm is unchanged when the
argument advances by one. -/
theorem clog_succ_of_lt_pow {c m : ℕ} (hcross : m + 1 ≤ 2 ^ c)
    (hprev : Nat.clog 2 m = c) : Nat.clog 2 (m + 1) = c := by
  have hle : Nat.clog 2 (m + 1) ≤ c := Nat.clog_le_of_le_pow hcross
  have hge : c ≤ Nat.clog 2 (m + 1) := by
    rw [← hprev]; exact Nat.clog_mono_right 2 (by omega)
  omega

/-- Across a power boundary the base-two ceiling logarithm increments by one. -/
theorem clog_succ_of_eq_pow {c m : ℕ} (_hprev : Nat.clog 2 m = c)
    (hboundary : m = 2 ^ c) : Nat.clog 2 (m + 1) = c + 1 := by
  have hpos : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  have hle : Nat.clog 2 (m + 1) ≤ c + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [hboundary, pow_succ]; omega
  have hgt : c < Nat.clog 2 (m + 1) := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr
    rw [hboundary]; omega
  omega

/-! ## 1. The functional scan and its correctness

The scan is written first as a pure state transition, proved equal to
`Nat.findGreatest` — hence to `inverseSourceIndex` by definition.  §2's program
then only has to reproduce this transition register for register.
-/

theorem inverseSourceMeasure_eq (j : ℕ) :
    inverseSourceMeasure j = (j + 1) * Nat.clog 2 (j + 3) := by
  rw [inverseSourceMeasure, logScale, show j + 1 + 2 = j + 3 from rfl]

/-- The five loop registers: candidate `j`, `c = clog₂(j+3)`, `q = 2^c`,
`prod = (j+1)·c = measure j`, and `arg = j+3`. -/
structure ScanState where
  j : ℕ
  c : ℕ
  q : ℕ
  prod : ℕ
  arg : ℕ

/-- `j = 0`: `c = clog₂ 3 = 2`, `q = 4`, `prod = 2`, `arg = 3`. -/
def initialScanState : ScanState := ⟨0, 2, 4, 2, 3⟩

/-- One scan step at threshold `K`.  Cross iff `q = arg`; the successor numerals
are additions only, and the candidate advances iff the successor still meets the
threshold. -/
def scanStep (K : ℕ) (s : ScanState) : ScanState :=
  let cNext := if s.q = s.arg then s.c + 1 else s.c
  let qNext := if s.q = s.arg then s.q + s.q else s.q
  let prodNext :=
    if s.q = s.arg then s.prod + s.c + (s.arg - 1) else s.prod + s.c
  if prodNext ≤ K then ⟨s.j + 1, cNext, qNext, prodNext, s.arg + 1⟩ else s

/-- `m` scan steps at threshold `K`. -/
def scanIter (K : ℕ) : ℕ → ScanState → ScanState
  | 0, s => s
  | n + 1, s => scanStep K (scanIter K n s)

/-- The register-consistency invariant. -/
def ScanValid (s : ScanState) : Prop :=
  s.c = Nat.clog 2 (s.j + 3) ∧ s.q = 2 ^ s.c ∧
    s.prod = (s.j + 1) * s.c ∧ s.arg = s.j + 3

theorem scanValid_prod {s : ScanState} (hs : ScanValid s) :
    s.prod = inverseSourceMeasure s.j := by
  obtain ⟨hc, _, hprod, _⟩ := hs
  rw [inverseSourceMeasure_eq, hprod, hc]

theorem initialScanState_valid : ScanValid initialScanState := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The step, reduced across a power boundary. -/
theorem scanStep_cross {K : ℕ} {s : ScanState} (h : s.q = s.arg) :
    scanStep K s =
      if s.prod + s.c + (s.arg - 1) ≤ K then
        ⟨s.j + 1, s.c + 1, s.q + s.q, s.prod + s.c + (s.arg - 1), s.arg + 1⟩
      else s := by
  unfold scanStep; simp only [if_pos h]

/-- The step, reduced off a power boundary. -/
theorem scanStep_nocross {K : ℕ} {s : ScanState} (h : ¬ s.q = s.arg) :
    scanStep K s =
      if s.prod + s.c ≤ K then
        ⟨s.j + 1, s.c, s.q, s.prod + s.c, s.arg + 1⟩
      else s := by
  unfold scanStep; simp only [if_neg h]

/-- **The step reproduces `measure (j+1)` and stays valid or freezes.**  Whatever
the branch, the successor numeral computed inside `scanStep` is exactly
`inverseSourceMeasure (s.j + 1)`, and the advanced state is again valid. -/
theorem scanStep_run {K : ℕ} {s : ScanState} (hs : ScanValid s) :
    (inverseSourceMeasure (s.j + 1) ≤ K →
      ScanValid (scanStep K s) ∧ (scanStep K s).j = s.j + 1) ∧
    (¬ inverseSourceMeasure (s.j + 1) ≤ K → scanStep K s = s) := by
  obtain ⟨hc, hq, hprod, harg⟩ := hs
  have hargLe : s.arg ≤ s.q := by
    rw [hq, hc, harg]; exact Nat.le_pow_clog (by norm_num) _
  have hmeasureSucc : inverseSourceMeasure (s.j + 1) = (s.j + 2) * Nat.clog 2 (s.j + 4) := by
    rw [inverseSourceMeasure_eq, show s.j + 1 + 3 = s.j + 4 from rfl,
      show s.j + 1 + 1 = s.j + 2 from rfl]
  by_cases hcross : s.q = s.arg
  · have hbnd : s.j + 3 = 2 ^ Nat.clog 2 (s.j + 3) := by rw [← hc, ← harg, ← hq, hcross]
    have hclog : Nat.clog 2 (s.j + 4) = Nat.clog 2 (s.j + 3) + 1 :=
      clog_succ_of_eq_pow rfl hbnd
    have hval : s.prod + s.c + (s.arg - 1) = inverseSourceMeasure (s.j + 1) := by
      rw [hmeasureSucc, hclog, hprod, hc, harg, show s.j + 3 - 1 = s.j + 2 from by omega]
      ring
    have hvalidNext : ScanValid ⟨s.j + 1, s.c + 1, s.q + s.q,
        s.prod + s.c + (s.arg - 1), s.arg + 1⟩ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change s.c + 1 = Nat.clog 2 (s.j + 1 + 3)
        rw [show s.j + 1 + 3 = s.j + 4 from rfl, hclog, hc]
      · change s.q + s.q = 2 ^ (s.c + 1)
        rw [hq, pow_succ]; ring
      · change s.prod + s.c + (s.arg - 1) = (s.j + 1 + 1) * (s.c + 1)
        rw [hval, hmeasureSucc, hclog, hc]
      · change s.arg + 1 = s.j + 1 + 3
        rw [harg]
    refine ⟨fun hpass => ?_, fun hfail => ?_⟩
    · rw [scanStep_cross hcross, if_pos (by rw [hval]; exact hpass)]
      exact ⟨hvalidNext, rfl⟩
    · rw [scanStep_cross hcross, if_neg (by rw [hval]; exact hfail)]
  · have hlt : s.arg < s.q := lt_of_le_of_ne hargLe (fun h => hcross h.symm)
    have hclog : Nat.clog 2 (s.j + 4) = Nat.clog 2 (s.j + 3) :=
      clog_succ_of_lt_pow (by rw [← hc, ← hq]; omega) rfl
    have hval : s.prod + s.c = inverseSourceMeasure (s.j + 1) := by
      rw [hmeasureSucc, hclog, hprod, hc]; ring
    have hvalidNext : ScanValid ⟨s.j + 1, s.c, s.q, s.prod + s.c, s.arg + 1⟩ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change s.c = Nat.clog 2 (s.j + 1 + 3)
        rw [show s.j + 1 + 3 = s.j + 4 from rfl, hclog, hc]
      · change s.q = 2 ^ s.c
        exact hq
      · change s.prod + s.c = (s.j + 1 + 1) * s.c
        rw [hval, hmeasureSucc, hclog, hc]
      · change s.arg + 1 = s.j + 1 + 3
        rw [harg]
    refine ⟨fun hpass => ?_, fun hfail => ?_⟩
    · rw [scanStep_nocross hcross, if_pos (by rw [hval]; exact hpass)]
      exact ⟨hvalidNext, rfl⟩
    · rw [scanStep_nocross hcross, if_neg (by rw [hval]; exact hfail)]

/-- **The functional scan equals `Nat.findGreatest`.**  After `m` steps the
candidate is the greatest index in `[0, m]` meeting the threshold, and the state
is valid. -/
theorem scanIter_run (K m : ℕ) :
    ScanValid (scanIter K m initialScanState) ∧
      (scanIter K m initialScanState).j =
        Nat.findGreatest (fun j => inverseSourceMeasure j ≤ K) m := by
  induction m with
  | zero => exact ⟨initialScanState_valid, rfl⟩
  | succ n ih =>
      obtain ⟨hvalid, hj⟩ := ih
      have hstep := scanStep_run (K := K)
        (s := scanIter K n initialScanState) hvalid
      have hrec :
          Nat.findGreatest (fun j => inverseSourceMeasure j ≤ K) (n + 1) =
            if inverseSourceMeasure (n + 1) ≤ K then n + 1
            else Nat.findGreatest (fun j => inverseSourceMeasure j ≤ K) n :=
        rfl
      have hle : (scanIter K n initialScanState).j ≤ n := by
        rw [hj]; exact Nat.findGreatest_le n
      by_cases hpass :
          inverseSourceMeasure ((scanIter K n initialScanState).j + 1) ≤ K
      · obtain ⟨hvalid', hj'⟩ := hstep.1 hpass
        have hsj : (scanIter K n initialScanState).j = n := by
          by_contra hne
          have hnp :
              ¬ inverseSourceMeasure ((scanIter K n initialScanState).j + 1) ≤ K :=
            Nat.findGreatest_is_greatest
              (P := fun j => inverseSourceMeasure j ≤ K)
              (n := n) (k := (scanIter K n initialScanState).j + 1)
              (by rw [← hj]; omega) (by omega)
          exact hnp hpass
        refine ⟨by rw [scanIter]; exact hvalid', ?_⟩
        rw [scanIter, hj', hrec, hsj, if_pos (by rw [← hsj]; exact hpass)]
      · have hfreeze := hstep.2 hpass
        have hnp : ¬ inverseSourceMeasure (n + 1) ≤ K := by
          intro hcon
          exact hpass (le_trans (inverseSourceMeasure_mono (by omega)) hcon)
        refine ⟨by rw [scanIter, hfreeze]; exact hvalid, ?_⟩
        rw [scanIter, hfreeze, hrec, if_neg hnp, hj]

/-- **The functional scan computes `inverseSourceIndex`.** -/
theorem scanIter_eq_inverseSourceIndex (k : ℕ) :
    (scanIter (k + 2) (k + 1) initialScanState).j = inverseSourceIndex k :=
  (scanIter_run (k + 2) (k + 1)).2

end NearCubicWires.InverseSourceIndexScan

import Proof.Wire_3_5.RecoveryLeaf

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)

/-! ## The scan for the largest index of a downward-closed predicate -/

/-- Step `a` upward while `a < n` and `P (a+1)`. -/
def scanUp (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | fuel + 1, a => if a < n ∧ P (a + 1) then scanUp P n fuel (a + 1) else a

/-- For a downward-closed `P` (on indices `≥ 1`), the scan from `0` is `Nat.findGreatest P n`. -/
theorem scanUp_eq_findGreatest (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a b, 1 ≤ a → a ≤ b → P b → P a) (n : ℕ) :
    scanUp P n n 0 = Nat.findGreatest P n := by
  -- invariant: `a ≤ n`, `a ≠ 0 → P a`, and the fuel covers the remaining indices
  have key : ∀ fuel a, a ≤ n → n ≤ a + fuel → (a ≠ 0 → P a) →
      scanUp P n fuel a ≤ n ∧ (scanUp P n fuel a ≠ 0 → P (scanUp P n fuel a)) ∧
        ∀ b, scanUp P n fuel a < b → b ≤ n → ¬ P b := by
    intro fuel
    induction fuel with
    | zero =>
      intro a ha hf hPa
      refine ⟨ha, hPa, fun b hb hbn => ?_⟩
      simp only [scanUp] at hb
      omega
    | succ fuel ih =>
      intro a ha hf hPa
      by_cases hc : a < n ∧ P (a + 1)
      · have e : scanUp P n (fuel + 1) a = scanUp P n fuel (a + 1) := by simp only [scanUp, if_pos hc]
        rw [e]
        exact ih (a + 1) (by omega) (by omega) (fun _ => hc.2)
      · have e : scanUp P n (fuel + 1) a = a := by simp only [scanUp, if_neg hc]
        rw [e]
        refine ⟨ha, hPa, fun b hb hbn hPb => hc ⟨by omega, hP (a + 1) b (by omega) (by omega) hPb⟩⟩
  obtain ⟨h1, h2, h3⟩ := key n 0 (Nat.zero_le n) (by omega) (fun h => absurd rfl h)
  exact ((Nat.findGreatest_eq_iff).2 ⟨h1, h2, fun b hb hbn => h3 b hb hbn⟩).symm

/-! ## The slice parameters -/

section Params
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (kclk Apad dG : ℕ)

/-- The width `q(2^a)` in closed form. -/
def widthAt (a : ℕ) : ℕ := a * (kclk + 2) + Apad * Nat.clog 2 (a * (kclk + 2) + 2) + Apad

theorem widthAt_eq (a : ℕ) : widthAt kclk Apad a = nativeWidth kclk Apad (2 ^ a) :=
  (nativeWidth_two_pow kclk Apad a).symm

theorem widthAt_mono : Monotone (widthAt kclk Apad) := by
  intro a b hab
  rw [widthAt_eq, widthAt_eq]
  exact nativeWidth_mono kclk Apad (Nat.pow_le_pow_right (by norm_num) hab)

/-- The core length `m_a = (t(q)+1)·(q + ⌈d_G log₂(q+2)⌉ + 1)` at `q = q(2^a)`. -/
def coreLen (a : ℕ) : ℕ :=
  (sched ζ h0 h1 (Lq (widthAt kclk Apad a)) + 1) * addrWidth dG (widthAt kclk Apad a)

theorem coreLen_eq (a : ℕ) : coreLen h0 h1 kclk Apad dG a = (recSchedule h0 h1 kclk Apad dG).coreLength a := by
  unfold coreLen
  rw [widthAt_eq]
  rfl

theorem addrWidth_mono : Monotone (addrWidth dG) := by
  intro q q' hq
  unfold addrWidth
  have : Nat.clog 2 ((q + 2) ^ dG) ≤ Nat.clog 2 ((q' + 2) ^ dG) :=
    Nat.clog_mono_right 2 (Nat.pow_le_pow_left (by omega) dG)
  omega

theorem coreLen_mono : Monotone (coreLen h0 h1 kclk Apad dG) := by
  intro a b hab
  have hw := widthAt_mono kclk Apad hab
  have hL : Lq (widthAt kclk Apad a) ≤ Lq (widthAt kclk Apad b) := Nat.clog_mono_right 2 (by omega)
  exact Nat.mul_le_mul (by have := sched_mono h0 h1 hL; omega) (addrWidth_mono dG hw)

/-- **The source index `a(n)`** by the program's upward scan. -/
def sliceIdx (n : ℕ) : ℕ := scanUp (fun a => coreLen h0 h1 kclk Apad dG a ≤ n / 2) n n 0

/-- **The scan is the language's source index.** -/
theorem sliceIdx_eq (n : ℕ) : sliceIdx h0 h1 kclk Apad dG n = (recSchedule h0 h1 kclk Apad dG).sourceIdx n := by
  unfold sliceIdx
  rw [scanUp_eq_findGreatest _ (fun a b _ hab hb => (coreLen_mono h0 h1 kclk Apad dG hab).trans hb)]
  unfold LengthSchedule.sourceIdx
  congr 1
  funext a
  rw [coreLen_eq]

end Params

/-! ## The slice of the recovered language -/

/-- **The recovered language's slice at `n`** in terms of the computed parameters: the index `a(n)`, the width
`q = q(2^{a(n)})`, the copies `t(q) + 1`, the clause width, and the refuter's output at `2^{a(n)}`. -/
theorem recLanguageCut_eq (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (M : OrdinaryWeakMachine) (cutoff n : ℕ) :
    recLanguageCut l G kclk coef A a ha M cutoff n =
      if cutoff ≤ 2 ^ sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n then
        core (recSetup l G kclk coef A a ha).pcp (gatePCPP l)
          (selectedAmplifier l.eightSources.amplification (recOracleDeg l))
          ((recRefuter l kclk).output M (2 ^ sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n))
          (sched (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l)
            (Lq (widthAt kclk G.Apad (sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n))) + 1)
          (clauseWidth (recDG l) (widthAt kclk G.Apad (sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n)))
          n
      else fun _ => false := by
  unfold recLanguageCut recSched
  rw [recLanguage_slice, sliceIdx_eq, widthAt_eq]
  rfl

/-! ## Executable twins (`ζ = 1/4`, `k = 0`, `A_pad = 1`, `d_G = 2`) -/

-- the closed-form width at small indices
#guard (List.range 6).map (widthAt 0 1) = [2, 5, 8, 10, 13, 15]
-- the scan equals the maximum search on every length below 1500
#guard (List.range 1500).all fun n =>
  sliceIdx (ζ := 1 / 4) (by norm_num) (by norm_num) 0 1 2 n =
    Nat.findGreatest (fun a => coreLen (ζ := 1 / 4) (by norm_num) (by norm_num) 0 1 2 a ≤ n / 2) n
-- the index at lengths `250 i`
#guard (List.range 8).map (fun i => sliceIdx (ζ := 1 / 4) (by norm_num) (by norm_num) 0 1 2 (250 * i)) =
  [0, 21, 51, 81, 112, 142, 173, 204]

end NearCubicWires.WireExponent3_5.Transfer

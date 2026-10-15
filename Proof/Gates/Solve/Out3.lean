import Proof.Gates.Solve.Out2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open NearCubicWires.RepairRepresentation (natWord)

def entP : WMX NS NR := .seq entA entB

def entCost (W N C : ℕ) : ℕ := entACost W N + 1 + entBCost W C

theorem capE_out (N W : ℕ) : 8 * (W + 1) + 8 + 2 * N + 2 ≤ capE N W := by unfold capE; nlinarith

/-- The parameters of the entries loop (on its reference state). -/
structure LPar (σA : MS) (W R C m n : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (junk : List Bool) : Prop where
  mc : MatCtx σA W R C a junk
  hmR : m + n ≤ R
  hn : n < C
  hCN : C ≤ R * C + 2
  CC : σA.val rCC = C
  WL : σA.val rWL = W + 1
  R2 : σA.val rR2 = 2 * (W + 1) + 1
  SD : σA.val rSD = (decide (D < 0)).toNat
  D0 : D ≠ 0
  Dlt : D.natAbs < 2 ^ W
  bd : ∀ i < R, (a i n).natAbs < 2 ^ W

/-- The entries-loop invariant after `k` unknowns. -/
def LInv (σA : MS) (W C m n : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (v : Str → ℕ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sOUT = σA.st sOUT ++ (List.range k).flatMap (fun j => entW (a (m + j) n) D) ∧
    σ1.sh sOUT = (σ1.st sOUT).length ∧ σ1.val rIX = (m + k) * C + n ∧ σ1.val rNZ = 0 ∧ σ1.val rSY = 0 ∧
    σ1.val rLE = 0 ∧ SameExcept σA σ1 [sOUT] [rIX, rNZ, rSY, rLE, rLV] ∧ v1 wAV = v wAV ∧ v1 wZ = v wZ

theorem ent_step (cap : ℕ) {σA : MS} {W R C m n : ℕ} {a : ℕ → ℕ → ℤ} {D : ℤ} {junk : List Bool} {v : Str → ℕ}
    (hp : LPar σA W R C m n a D junk) (hcap : capE (R * C) W ≤ cap) (hDA : v wAV = D.natAbs) (k : ℕ) (hk : k < n)
    (τ : MS) (hI : LInv σA W C m n a D v k τ) :
    Runs cap entP (τ.setv rLV (n - k - 1)) (entCost W (R * C) C)
      (fun ρ => LInv σA W C m n a D v (k + 1) ρ ∧ ρ.val rLV = n - k - 1) := by
  obtain ⟨σ1, v1, h1, hO1, hOh1, hIX1, hNZ1, hSY1, hLE1, hfr1, hAV1, hZ1⟩ := hI
  have h1' := h1.setv (r := rLV) (by decide) (n - k - 1)
  set σ2 := σ1.setv rLV (n - k - 1) with hσ2
  have hfr2 : SameExcept σA σ2 [sOUT] [rIX, rNZ, rSY, rLE, rLV] := hfr1.trans (sameExcept_setv σ1 (by simp) _)
  have hc2 : MatCtx σ2 W R C a junk := hp.mc.same hfr2 (by decide)
  have hv2 : ∀ r, r ∉ [rIX, rNZ, rSY, rLE, rLV] → σ2.val r = σA.val r := fun r hr => hfr2.val hr
  have hidx : (m + k) * C + n < R * C := idx_lt (by have := hp.hmR; omega) hp.hn
  have hco := capE_out (R * C) W
  set y := a (m + k) n with hy
  refine Runs.seq (entA_spec cap h1' hc2 hcap (i := m + k) (n := n) (by have := hp.hmR; omega) hp.hn
    (by simp (config := {decide := true}) [hσ2, hIX1]) (by simp (config := {decide := true}) [hσ2, hSY1])
    (by simp (config := {decide := true}) [hσ2, hNZ1]) (by simp (config := {decide := true}) [hσ2, hLE1])
    (by rw [hv2 _ (by decide), hp.R2]) hp.D0 hp.Dlt (by rw [hAV1, hDA]) (hp.bd _ (by have := hp.hmR; omega)))
    (fun τ3 ⟨σ3, v3, h3, hQ3, hB3, hNZ3, hSY3, hLE3, hfr3, hAV3, hZ3⟩ => ?_)
  have hv3 : ∀ r, r ∉ [rNZ, rSY, rLE] → σ3.val r = σ2.val r := fun r hr => hfr3.val hr
  have hDpos : 0 < D.natAbs := Int.natAbs_pos.mpr hp.D0
  have hpw : 2 ^ W < 2 ^ (W + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hylt := hp.bd (m + k) (by have := hp.hmR; omega)
  have hQlt : v3 wQ < 2 ^ (W + 1) := by
    rw [hQ3]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hBlt : v3 wB < 2 ^ (W + 1) := by
    rw [hB3]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by have := hp.Dlt; omega)
  have hIX3 : σ3.val rIX = (m + k) * C + n := by
    rw [hv3 _ (by decide)]; simp (config := {decide := true}) [hσ2, hIX1]
  refine (entB_spec cap h3 y D (C := C) hNZ3 hSY3
    (by rw [hv3 _ (by decide), hv2 _ (by decide), hp.SD])
    (by rw [hfr3.sh (by simp), hfr3.st (by simp)]; simpa [hσ2] using hOh1)
    (by rw [hv3 _ (by decide), hv2 _ (by decide), hp.WL]) (by rw [hv3 _ (by decide), hv2 _ (by decide), hp.R2])
    (by rw [hv3 _ (by decide), hv2 _ (by decide), hp.CC]) hQ3 hB3 hQlt hBlt
    (by rw [hIX3]; have := hp.hCN; omega)).post
    (fun τ4 ⟨σ4, h4, hO4, hOh4, hNZ4, hSY4, hIX4, hfr4⟩ => ⟨⟨σ4, v3, h4, ?_, hOh4, ?_, hNZ4, hSY4, ?_, ?_, ?_, ?_⟩, ?_⟩)
  · rw [hO4, hfr3.st (by simp)]
    simp only [hσ2, WState.setv_st, hO1, List.range_succ, List.flatMap_append, List.append_assoc]
    simp [hy]
  · rw [hIX4, hIX3]; ring
  · rw [hfr4.val (by decide)]; exact hLE3
  · exact hfr2.trans ((hfr3.weaken (by simp) (by simp)).trans (hfr4.weaken (by simp) (by simp)))
  · rw [hAV3, hAV1]
  · rw [hZ3, hZ1]
  · rw [h4.val (by decide), hfr4.val (by decide), hv3 _ (by decide)]; simp [hσ2]

end NearCubicGates.Close.Solve

import Proof.Gates.Solve.Ident

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
open StablePartition.Workspace (overlay)
open NearCubicGates.Close.Interfaces.Formats (SysReq)

abbrev rLV2 : Reg := 54
abbrev rBEF : Reg := 55
abbrev rAFT : Reg := 56
abbrev rK3 : Reg := 57

/-- The records of identity row `v`. -/
def idRow (n v : ℕ) : List ℕ := List.replicate v 0 ++ [2] ++ List.replicate (n - 1 - v) 0 ++ [0]

theorem idRow_eq (s : SysReq) {v : ℕ} (hv : v < s.pts.length) :
    (List.range (s.pts.length + 1)).map (fun j => encS (amat s (s.rows.length + v) j)) = idRow s.pts.length v := by
  apply List.ext_getElem
  · simp [idRow]; omega
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, amat_id]
    simp only [idRow]
    simp only [List.length_map, List.length_range] at h1
    by_cases hjv : j < v
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_append_left (by simp; omega)]
      simp [encS]; omega
    · by_cases hjv' : j = v
      · subst hjv'
        rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
          List.getElem_append_right (by simp)]
        simp [encS, hv]
      · by_cases hjn : j < s.pts.length
        · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
          simp [encS]; omega
        · rw [List.getElem_append_right (by simp; omega)]
          simp [encS]; omega

def zeroAppend : WMX NS NR := appendRecX wZ sMAT rCS rCM

/-- The zero-append loop invariant. -/
def ZInv (σB : MS) (W : ℕ) (v : Str → ℕ) (out L0 : List Bool) (j : ℕ) (τ : MS) : Prop :=
  ∃ σ1, At σ1 τ W v ∧ OutOn σ1 sMAT rCM (out ++ recBits W (List.replicate j 0)) L0 ∧ SameExcept σB σ1 [sMAT] [rCM, rK3]

theorem zero_step (cap : ℕ) {σB : MS} {W : ℕ} {v : Str → ℕ} (hvZ : v wZ = 0) {out L0 : List Bool} {P : ℕ}
    (hcap : out.length + (P + 1) * (2 * (W + 1) + 1) + 1 ≤ cap) (j : ℕ) (hj : j < P) (τ : MS)
    (hI : ZInv σB W v out L0 j τ) :
    Runs cap zeroAppend (τ.setv rK3 (P - j - 1)) (40 * (W + 1) + 11)
      (fun ρ => ZInv σB W v out L0 (j + 1) ρ ∧ ρ.val rK3 = P - j - 1) := by
  obtain ⟨σ1, h1, hout1, hfr1⟩ := hI
  have h1' := h1.setv (r := rK3) (by decide) (P - j - 1)
  have hout1' : OutOn (σ1.setv rK3 (P - j - 1)) sMAT rCM (out ++ recBits W (List.replicate j 0)) L0 :=
    ⟨by simp [hout1.1], by simp [hout1.2.1], by simp (config := {decide := true}) [hout1.2.2]⟩
  have hlen : (out ++ recBits W (List.replicate j 0)).length + 2 * (W + 1) + 2 ≤ cap := by
    rw [List.length_append, recBits_length, List.length_replicate]
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show j + 1 ≤ P + 1 by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  refine (opAppend cap h1' (X := wZ) (O := sMAT) (CO := rCM) (by decide) (by decide) (by decide) hout1' hlen).post
    (fun ρ hρ => ⟨⟨_, hρ, ?_, ?_⟩, ?_⟩)
  · rw [hvZ]
    refine ⟨by simp [List.replicate_succ', recBits_append, recBits], by simp [List.replicate_succ', recBits_append,
      recBits], by simp (config := {decide := true}) [List.replicate_succ', recBits_append, recBits]⟩
  · refine SameExcept.trans hfr1 (SameExcept.trans (sameExcept_setv σ1 (S := [sMAT]) (Rg := [rCM, rK3]) (r := rK3)
      (by simp) (P - j - 1)) ⟨fun x hx => ?_, fun q hq => ?_, rfl⟩)
    · have : x ≠ sMAT := by simpa using hx
      simp [Function.update_of_ne this]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp [Function.update_of_ne hq.1]
  · rw [hρ.val (by decide)]; simp (config := {decide := true})

end NearCubicGates.Close.Solve

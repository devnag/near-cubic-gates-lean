import Proof.Gates.Solve.Ident2

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

def identRow : WMX NS NR :=
  .seq (WMX.dec rAFT) (.seq (addR rBEF rK3 rTa) (.seq (.whr rK3 (.seq (WMX.dec rK3) zeroAppend))
  (.seq (appendRecX wTWO sMAT rCS rCM) (.seq (addR rAFT rK3 rTa) (.seq (.whr rK3 (.seq (WMX.dec rK3) zeroAppend))
  (.seq zeroAppend (WMX.inc rBEF)))))))

def identP : WMX NS NR :=
  .seq (addR rNN rLV2 rTa) (.seq (addR rNN rAFT rTa) (.seq (.whr rLV2 (.seq (WMX.dec rLV2) identRow))
    (.wm (WM.clear rBEF))))

/-- The identity-row loop invariant after `k` rows. -/
def IInv (σB : MS) (W n : ℕ) (v : Str → ℕ) (out L0 : List Bool) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1, At σ1 τ W v ∧ OutOn σ1 sMAT rCM (out ++ recBits W ((List.range k).flatMap (idRow n))) L0 ∧
    σ1.val rBEF = k ∧ σ1.val rAFT = n - k ∧ σ1.val rK3 = 0 ∧ SameExcept σB σ1 [sMAT] [rCM, rBEF, rAFT, rK3, rLV2]

theorem idRows_len (n : ℕ) : ∀ k, k ≤ n → ((List.range k).flatMap (idRow n)).length = k * (n + 1)
  | 0, _ => by simp
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.length_append, idRows_len n k (by omega)]
    simp [idRow]; rw [Nat.add_mul]; omega

/-- The cost bound of one identity row. -/
def idRowCost (n W : ℕ) : ℕ := (2 * n + 4) * (40 * (W + 1) + 16) + 40 * n + 50

theorem ident_step (cap : ℕ) {σB : MS} {W n : ℕ} {v : Str → ℕ} (hvZ : v wZ = 0) (hvT : v wTWO = 2) {out L0 : List Bool}
    (hcap : out.length + (n + 1) * (n + 3) * (2 * (W + 1) + 1) + 4 * n + 8 ≤ cap) (k : ℕ) (hk : k < n) (τ : MS)
    (hI : IInv σB W n v out L0 k τ) :
    Runs cap identRow (τ.setv rLV2 (n - k - 1)) (idRowCost n W)
      (fun ρ => IInv σB W n v out L0 (k + 1) ρ ∧ ρ.val rLV2 = n - k - 1) := by
  obtain ⟨σ1, h1, hout1, hBEF1, hAFT1, hK31, hfr1⟩ := hI
  have h1' := h1.setv (r := rLV2) (by decide) (n - k - 1)
  set σ2 := σ1.setv rLV2 (n - k - 1) with hσ2
  set Q := 2 * (W + 1) + 1 with hQ
  set L1 := out ++ recBits W ((List.range k).flatMap (idRow n)) with hL1
  have hlenk : L1.length = out.length + k * (n + 1) * Q := by
    rw [hL1, List.length_append, recBits_length, idRows_len n k hk.le]
  have hB : out.length + k * (n + 1) * Q + (n + 2) * Q + 1 ≤ cap := by
    have h1 : k * (n + 1) + (n + 2) ≤ (n + 1) * (n + 3) := by nlinarith
    have := Nat.mul_le_mul_right Q h1
    rw [Nat.add_mul] at this; omega
  have hq1 : (k + 1) * Q ≤ (n + 2) * Q := Nat.mul_le_mul_right _ (by omega)
  have eq1 : (k + 1) * Q = k * Q + Q := by ring
  have hq2 : (n + 1) * Q ≤ (n + 2) * Q := Nat.mul_le_mul_right _ (by omega)
  have eq2 : (k + 1 + (n - k - 1 + 1)) * Q = k * Q + Q + (n - k - 1 + 1) * Q := by ring
  have eq3 : (k + 1 + (n - k - 1) + 1) * Q = k * Q + Q + (n - k - 1) * Q + (1 + 1) * Q - Q := by
    rw [show k + 1 + (n - k - 1) + 1 = k + 1 + (n - k - 1) + 1 from rfl]; ring_nf; omega
  have h2c : k + 1 + (n - k - 1 + 1) = n + 1 := by omega
  have h3c : k + 1 + (n - k - 1) + 1 + 1 = n + 2 := by omega
  have eq4 : k * Q + Q + (n - k - 1) * Q + (1 + 1) * Q = (k + 1 + (n - k - 1) + 1 + 1) * Q := by ring
  have hcost : 1 + 1 + (18 * k + 3 + 1 + ((k * (40 * (W + 1) + 11 + 4) + 1) + 1 + (40 * (W + 1) + 11 + 1 +
      (18 * (n - k - 1) + 3 + 1 + (((n - k - 1) * (40 * (W + 1) + 11 + 4) + 1) + 1 + (40 * (W + 1) + 11 + 1 + 3))))))
      ≤ idRowCost n W := by
    unfold idRowCost
    have h1 : k * (40 * (W + 1) + 11 + 4) ≤ n * (40 * (W + 1) + 16) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (n - k - 1) * (40 * (W + 1) + 11 + 4) ≤ n * (40 * (W + 1) + 16) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  refine Runs.cost ?_ hcost
  -- 1. `AFT -= 1`
  refine Runs.seq (opDecR cap h1' (r := rAFT) (by decide) (by simp (config := {decide := true}) [hσ2, hAFT1]; omega))
    (fun τ3 h3 => ?_)
  set σ3 := σ2.setv rAFT (σ2.val rAFT - 1) with hσ3

  have h3B : σ3.val rBEF = k := by simp (config := {decide := true}) [hσ3, hσ2, hBEF1]
  refine Runs.seq ((opAddR cap h3 (A := rBEF) (B := rK3) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ3, hσ2, hK31, hBEF1]; omega)).cost (show 18 * σ3.val rBEF + 3 ≤ 18 * k + 3 by
      rw [h3B])) (fun τ4 h4 => ?_)
  set σ4 := σ3.setv rK3 (σ3.val rK3 + σ3.val rBEF) with hσ4
  -- 3. `k` zeros
  have hz0 : ZInv σ4 W v L1 L0 0 τ4 := by
    refine ⟨σ4, h4, ?_, SameExcept.refl _ _ _⟩
    simpa [recBits] using OutOn.same hout1 (S := []) (Rg := [rLV2, rAFT, rK3])
      (SameExcept.trans (sameExcept_setv σ1 (by simp) _) (SameExcept.trans (sameExcept_setv _ (by simp) _)
        (sameExcept_setv _ (by simp) _))) (by simp) (by decide)
  have hl1 := Runs.count (cap := cap) (K := rK3) (body := zeroAppend) (40 * (W + 1) + 11) k (ZInv σ4 W v L1 L0)
    (by omega) (fun j hj τ hτ _ => zero_step cap hvZ (out := L1) (P := k) (by rw [hlenk, ← hQ]; omega) j hj τ hτ) τ4 hz0
    (by rw [h4.val (by decide)]; simp (config := {decide := true}) [hσ4, hσ3, hσ2, hK31, hBEF1])
  refine Runs.seq hl1 (fun τ5 ⟨⟨σ5, h5, hout5, hfr5⟩, hK5⟩ => ?_)
  -- 4. the `1`
  have hlen5 : (L1 ++ recBits W (List.replicate k 0)).length + 2 * (W + 1) + 2 ≤ cap := by
    rw [List.length_append, hlenk, recBits_length, List.length_replicate, ← hQ]; omega
  refine Runs.seq ((opAppend cap h5 (X := wTWO) (O := sMAT) (CO := rCM) (by decide) (by decide) (by decide) hout5
    hlen5)) (fun τ6 h6 => ?_)
  rw [hvT] at h6
  set L6 := L1 ++ recBits W (List.replicate k 0) ++ frame (binary (W + 1) 2) with hL6
  have hlen6 : L6.length = out.length + k * (n + 1) * Q + k * Q + Q := by
    rw [hL6, List.length_append, List.length_append, hlenk, recBits_length, List.length_replicate, frame_length,
      binary_length, ← hQ]
  set σ6 := ((σ5.sets sMAT (overlay L6 L0)).seth sMAT L6.length).setv rCM L6.length with hσ6

  have h6A : σ6.val rAFT = n - k - 1 := by
    simp (config := {decide := true}) [hσ6]; rw [hfr5.val (by decide)]
    simp (config := {decide := true}) [hσ4, hσ3, hσ2, hAFT1] <;> omega
  have h6K : σ6.val rK3 = 0 := by simp (config := {decide := true}) [hσ6]; rw [← h5.val (by decide)]; exact hK5
  refine Runs.seq ((opAddR cap h6 (A := rAFT) (B := rK3) (by decide) (by decide) (by decide)
    (by rw [h6A, h6K]; omega)).cost (show 18 * σ6.val rAFT + 3 ≤ 18 * (n - k - 1) + 3 by rw [h6A]))
    (fun τ7 h7 => ?_)
  set σ7 := σ6.setv rK3 (σ6.val rK3 + σ6.val rAFT) with hσ7
  -- 6. `n − k − 1` zeros
  have hz0' : ZInv σ7 W v L6 L0 0 τ7 := by
    refine ⟨σ7, h7, ⟨by simp [hσ7, hσ6, recBits], by simp [hσ7, hσ6, recBits],
      by simp (config := {decide := true}) [hσ7, hσ6, recBits]⟩, SameExcept.refl _ _ _⟩
  have hl2 := Runs.count (cap := cap) (K := rK3) (body := zeroAppend) (40 * (W + 1) + 11) (n - k - 1)
    (ZInv σ7 W v L6 L0) (by omega)
    (fun j hj τ hτ _ => zero_step cap hvZ (out := L6) (P := n - k - 1) (by
      rw [hlen6, ← hQ]
      have : (k + 1 + (n - k - 1 + 1)) * Q ≤ (n + 2) * Q := by rw [h2c]; exact hq2
      omega) j hj τ hτ)
    τ7 hz0' (by rw [h7.val (by decide)]; simp (config := {decide := true}) [hσ7, h6K, h6A])
  refine Runs.seq hl2 (fun τ8 ⟨⟨σ8, h8, hout8, hfr8⟩, hK8⟩ => ?_)
  -- 7. the right side `0`
  set L8 := L6 ++ recBits W (List.replicate (n - k - 1) 0) with hL8
  have hlen8 : L8.length = out.length + k * (n + 1) * Q + k * Q + Q + (n - k - 1) * Q := by
    rw [hL8, List.length_append, hlen6, recBits_length, List.length_replicate, ← hQ]
  have hcap8 : L8.length + (1 + 1) * Q + 1 ≤ cap := by
    rw [hlen8]
    have : (k + 1 + (n - k - 1) + 1 + 1) * Q = (n + 2) * Q := by rw [h3c]
    rw [← hQ] at *
    omega
  have hout8' : OutOn σ8 sMAT rCM (L8 ++ recBits W (List.replicate 0 0)) L0 := by simpa [recBits] using hout8
  have hz7 := zero_step cap hvZ (out := L8) (P := 1) hcap8 0 (by omega) τ8 ⟨σ8, h8, hout8', hfr8⟩
  have e8 : τ8.setv rK3 (1 - 0 - 1) = τ8 := by rw [show 1 - 0 - 1 = 0 by rfl, ← hK8, wsetv_same]
  rw [e8] at hz7
  refine Runs.seq hz7 (fun τ9 ⟨⟨σ9, h9, hout9, hfr9⟩, hK9⟩ => ?_)
  -- 8. `BEF += 1`
  have h9B : σ9.val rBEF = k := by
    rw [hfr9.val (by decide)]; simp (config := {decide := true}) [hσ7, hσ6]
    rw [hfr5.val (by decide)]; simp (config := {decide := true}) [hσ4, h3B]
  refine (opIncR cap h9 (r := rBEF) (by decide) (by rw [h9B]; omega)).post (fun ρ hρ => ⟨⟨_, hρ, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  · have e : (List.range (k + 1)).flatMap (idRow n) = (List.range k).flatMap (idRow n) ++ idRow n k := by
      simp [List.range_succ, List.flatMap_append]
    have e2 : recBits W (idRow n k) = recBits W (List.replicate k 0) ++ frame (binary (W + 1) 2) ++
        recBits W (List.replicate (n - k - 1) 0) ++ recBits W (List.replicate 1 0) := by
      simp [idRow, recBits_append, recBits, show n - 1 - k = n - k - 1 by omega]
    have e3 : out ++ recBits W ((List.range (k + 1)).flatMap (idRow n)) = L8 ++ recBits W (List.replicate 1 0) := by
      rw [e, recBits_append, e2, hL8, hL6, hL1]; simp [List.append_assoc]
    rw [e3]
    exact ⟨by simpa using hout9.1, by simpa using hout9.2.1, by
      rw [show (σ9.setv rBEF (σ9.val rBEF + 1)).val rCM = σ9.val rCM by simp (config := {decide := true})]
      simpa using hout9.2.2⟩
  · simp [h9B]
  · rw [show (σ9.setv rBEF (σ9.val rBEF + 1)).val rAFT = σ9.val rAFT by simp (config := {decide := true})]
    rw [hfr9.val (by decide)]; simp (config := {decide := true}) [hσ7]; rw [h6A]; omega
  · rw [show (σ9.setv rBEF (σ9.val rBEF + 1)).val rK3 = σ9.val rK3 by simp (config := {decide := true})]
    rw [← h9.val (by decide)]; exact hK9
  · refine SameExcept.trans hfr1 ?_
    have f2 : SameExcept σ1 σ2 [sMAT] [rCM, rBEF, rAFT, rK3, rLV2] := by rw [hσ2]; exact sameExcept_setv σ1 (by decide) _
    have f3 : SameExcept σ2 σ3 [sMAT] [rCM, rBEF, rAFT, rK3, rLV2] := by rw [hσ3]; exact sameExcept_setv σ2 (by decide) _
    have f4 : SameExcept σ3 σ4 [sMAT] [rCM, rBEF, rAFT, rK3, rLV2] := by rw [hσ4]; exact sameExcept_setv σ3 (by decide) _
    have f6 : SameExcept σ5 σ6 [sMAT] [rCM, rBEF, rAFT, rK3, rLV2] := by
      rw [hσ6]
      exact SameExcept.trans (sameExcept_sets σ5 (by decide) _) (SameExcept.trans (sameExcept_seth _ (by decide) _)
        (sameExcept_setv _ (by decide) _))
    have f7 : SameExcept σ6 σ7 [sMAT] [rCM, rBEF, rAFT, rK3, rLV2] := by rw [hσ7]; exact sameExcept_setv σ6 (by decide) _
    have f10 : SameExcept σ9 (σ9.setv rBEF (σ9.val rBEF + 1)) [sMAT] [rCM, rBEF, rAFT, rK3, rLV2] :=
      sameExcept_setv σ9 (by decide) _
    have w5 := hfr5.weaken (S' := [sMAT]) (Rg' := [rCM, rBEF, rAFT, rK3, rLV2]) (by simp) (by decide)
    have w9 := hfr9.weaken (S' := [sMAT]) (Rg' := [rCM, rBEF, rAFT, rK3, rLV2]) (by simp) (by decide)
    exact f2.trans (f3.trans (f4.trans (w5.trans (f6.trans (f7.trans (w9.trans f10))))))
  · rw [hρ.val (by decide)]
    simp (config := {decide := true})
    rw [hfr9.val (by decide)]; simp (config := {decide := true}) [hσ7, hσ6]
    rw [hfr5.val (by decide)]; simp (config := {decide := true}) [hσ4, hσ3, hσ2]

end NearCubicGates.Close.Solve

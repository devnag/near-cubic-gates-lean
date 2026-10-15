import Proof.Gates.Solve.Rows5

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
open NearCubicGates.Close.Interfaces.Formats (inClass)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM)

/-- The word of one row. -/
def rowW (row : ℕ × List ℕ × ℕ) : List Bool := natWord row.1 ++ Interfaces.listWord natWord row.2.1 ++ natWord row.2.2

def rowA : WMX NS NR :=
  .seq (BinW.zero wQ wZ rF rR) (.seq (CounterMachine.natRead sRAW sRUL wQ rCA rR2 rCW)
  (.seq (nzP wQ wZ rNZQ rF rR) (.seq (.wm (readNatM false sRAW rCA rCW rSLN rK2 rG))
  (.seq (addR rSLN rLS rTa) (.seq (.whr rLS (.seq (WMX.dec rLS) sgBody)) (closeOutX sSG rCSG))))))

/-- The cost bound of `rowA`. -/
def rowACost (ℓ W U : ℕ) : ℕ := 10 * U + 200 * (ℓ + 2) ^ 2 + (ℓ + 2) * (300 * (W + 2) + 4)

theorem rowA_spec (cap : ℕ) {σ0 σ : MS} {W ℓ N : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {word : List Bool}
    (hc : RawCtx σ0 W word) (q : ℕ) (σl : List ℕ) (pre rest : List Bool)
    (hword : word = pre ++ natWord q ++ Interfaces.listWord natWord σl ++ rest) (hsh : σ0.sh sRAW = pre.length)
    (hSGh : σ0.sh sSG = 0) (hz : ∀ r ∈ [rNZQ, rSLN, rLS, rCSG], σ0.val r = 0) (hq : q < 2 ^ ℓ)
    (hσb : ∀ x ∈ σl, x < 2 ^ ℓ) (hσl : σl.length ≤ ℓ) (hℓW : ℓ + 2 ≤ W) (hℓN : ℓ ≤ N)
    (hcap : (ℓ + 2) * (2 * (W + 1) + 1) + 8 * ℓ + 8 ≤ cap) :
    Runs cap rowA σ (rowACost ℓ W (ucost W N)) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sRAW = σ0.st sRAW ∧
      σ1.sh sRAW = pre.length + (natWord q ++ Interfaces.listWord natWord σl).length ∧ v1 wQ = q ∧
      σ1.val rNZQ = (decide (q ≠ 0)).toNat ∧ σ1.val rSLN = σl.length ∧ σ1.val rLS = 0 ∧ σ1.val rCSG = 0 ∧
      (∃ jS, σ1.st sSG = recStream ((sgVals σl).map (binary (W + 1))) ++ jS) ∧ σ1.sh sSG = 0 ∧
      SameExcept σ0 σ1 [sRAW, sSG] [rNZQ, rSLN, rLS, rCSG] ∧ ∀ X ∈ keepW, X ≠ wQ → v1 X = v X) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨hNZQ, hSLN, hLS, hCSG⟩ := hz
  set U := ucost W N with hU
  have hU16 := one_le_ucost W N
  have hUL := lin_le_ucost W N
  have hUN := ucost_geN W N
  have hcW : 2 * (W + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < ℓ + 2 by omega); omega
  have hc4 : 4 * (W + 1) + 4 ≤ cap := by
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show 2 ≤ ℓ + 2 by omega); omega
  have hpow : 2 ^ ℓ * 4 ≤ 2 ^ W := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcost : U + 1 + (60 * (W + 2) + 1 + (U + 1 + (readCost σl.length + 1 + (U + 1 +
      (σl.length * (300 * (W + 2) + 4) + 1 + 1 + U))))) ≤ rowACost ℓ W U := by
    unfold rowACost
    have h1 := readCost_le σl.length
    have h2 : (σl.length + 2) ^ 2 ≤ (ℓ + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : σl.length * (300 * (W + 2) + 4) ≤ (ℓ + 2) * (300 * (W + 2) + 4) := Nat.mul_le_mul_right _ (by omega)
    omega
  refine Runs.cost ?_ hcost
  -- 1. `wQ := 0`; 2. `wQ := q`
  refine Runs.seq ((opZero cap h (X := wQ) (by decide) (by decide) hcW).cost (show 41 * (W + 1) + 3 ≤ U by omega))
    (fun τ1 h1 => ?_)
  have hst1 : σ0.st sRAW = pre ++ natWord q ++ (Interfaces.listWord natWord σl ++ rest) := by
    rw [hc.raw, hword]; simp [List.append_assoc]
  refine Runs.seq (opNatRead cap h1 (X := wQ) (by decide) (by simp) q pre _ hst1 hsh hc.rul hc.rulh hc.R2
    (by rw [pow_succ]; omega) hc4) (fun τ2 h2 => ?_)
  set σ2 := σ0.seth sRAW (pre.length + (natWord q).length) with hσ2
  -- 3. `NZQ := [q ≠ 0]`
  refine Runs.seq ((opNz cap h2 (X := wQ) (NZ := rNZQ) (by decide) (by decide) (by decide)
    (by simp [hσ2, hNZQ]) (by simp; rw [pow_succ]; omega) hcW).cost (show 41 * (W + 1) + 12 ≤ U by omega))
    (fun τ3 h3 => ?_)
  simp only [Function.update_self] at h3
  set σ3 := σ2.setv rNZQ (decide (q ≠ 0)).toNat with hσ3
  -- 4. `SLN := |σ|`
  have hst3 : σ3.st sRAW = (pre ++ natWord q) ++ natWord σl.length ++ (σl.flatMap natWord ++ rest) := by
    simp [hσ3, hσ2, hc.raw, hword, Interfaces.listWord, List.append_assoc]
  have hsh3 : σ3.sh sRAW = (pre ++ natWord q).length := by simp [hσ3, hσ2]
  refine Runs.seq (opReadNat cap h3 (V := rSLN) (by decide) σl.length _ _ hst3 hsh3
    (by have := two_pow_nbl_le σl.length; simp (config := {decide := true}) [hσ3, hσ2, hSLN]; rw [pow_succ]; omega))
    (fun τ4 h4 => ?_)
  set σ4 := (σ3.seth sRAW ((pre ++ natWord q).length + (natWord σl.length).length)).setv rSLN
    (σ3.val rSLN + σl.length) with hσ4
  have h4SLN : σ4.val rSLN = σl.length := by simp (config := {decide := true}) [hσ4, hσ3, hσ2, hSLN]
  -- 5. `LS := |σ|`
  refine Runs.seq ((opAddR cap h4 (A := rSLN) (B := rLS) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ4, hσ3, hσ2, hLS, hSLN]; omega)).cost
    (show 18 * σ4.val rSLN + 3 ≤ U by rw [h4SLN]; omega)) (fun τ5 h5 => ?_)
  set σ5 := σ4.setv rLS (σ4.val rLS + σ4.val rSLN) with hσ5
  have hfr05 : SameExcept σ0 σ5 [sRAW] [rNZQ, rSLN, rLS] := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, rfl⟩
    · have : x ≠ sRAW := by simpa using hx
      simp [hσ5, hσ4, hσ3, hσ2, Function.update_of_ne this]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hσ5, hσ4, hσ3, hσ2, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2]
  have hc5 : RawCtx σ5 W word := hc.same hfr05 (by simp [hσ5, hσ4, hσ3, hσ2]) (by decide) (by decide)
  -- 6. the `σ` loop
  set v5 := Function.update (Function.update v wQ 0) wQ q with hv5
  have hI0 : SgInv σ5 W σl ((pre ++ natWord q).length + (natWord σl.length).length) (σ0.st sSG) v5 0 τ5 := by
    refine ⟨σ5, v5, h5, rfl, by simp [hσ5, hσ4], ⟨?_, ?_, ?_⟩, SameExcept.refl _ _ _, fun _ _ => rfl⟩
    · simp [hσ5, hσ4, hσ3, hσ2, sgVals, recBits, overlay]
    · simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hSGh, sgVals, recBits]
    · simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hCSG, sgVals, recBits]
  have hloop := Runs.count (cap := cap) (K := rLS) (body := sgBody) (300 * (W + 2)) σl.length
    (SgInv σ5 W σl ((pre ++ natWord q).length + (natWord σl.length).length) (σ0.st sSG) v5) (by omega)
    (fun k hk τ hτ _ => sg_step cap hc5 ⟨pre ++ natWord q ++ natWord σl.length, rest, by
      rw [hword]; simp [Interfaces.listWord, List.append_assoc], by simp; omega⟩ hσb hℓW v5 hσl (by omega) k hk τ hτ) τ5 hI0
    (by rw [h5.val (by decide)]; simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hLS, hSLN])
  refine Runs.seq hloop (fun τ6 ⟨⟨σ6, v6, h6, hraw6, hsh6, hout6, hfr6, hkeep6⟩, hK6⟩ => ?_)
  rw [List.take_length] at hsh6 hout6
  -- 7. close `SG`
  have hlen6 : (recBits W (sgVals σl)).length ≤ cap := by
    rw [recBits_length]; simp only [sgVals, List.length_map]
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show σl.length ≤ ℓ + 2 by omega); omega
  refine (opCloseOut cap h6 (O := sSG) (CO := rCSG) (by decide) (by decide) hout6 hlen6).mono
    (by
      have : 5 * (recBits W (sgVals σl)).length + 3 ≤ U := by
        rw [recBits_length]; simp only [sgVals, List.length_map]
        have h1 := closeOut_le W N
        have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show σl.length ≤ N by omega)
        omega
      exact this)
    (fun τ7 h7 => ⟨_, v6, h7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · simp (config := {decide := true}); rw [hraw6]; simp [hσ5, hσ4, hσ3, hσ2]
  · simp (config := {decide := true}); rw [hsh6]; simp [Interfaces.listWord]; ring
  · rw [hkeep6 wQ (by decide)]; simp [hv5]
  · simp (config := {decide := true}); rw [hfr6.val (by decide)]; simp (config := {decide := true}) [hσ5, hσ4, hσ3]
  · simp (config := {decide := true}); rw [hfr6.val (by decide)]; exact h4SLN
  · simp (config := {decide := true}); rw [← h6.val (by decide)]; exact hK6
  · simp
  · exact ⟨(σ0.st sSG).drop (recBits W (sgVals σl) ++ [false]).length, by simp [overlay, recStream_eq]⟩
  · simp
  · refine SameExcept.trans (hfr05.weaken (by simp) (by simp)) (SameExcept.trans (hfr6.weaken (by simp) (by simp)) ?_)
    exact SameExcept.trans (sameExcept_sets _ (by simp) _) (SameExcept.trans (sameExcept_seth _ (by simp) _)
      (sameExcept_setv _ (by simp) _))
  · intro X hX hXQ
    rw [hkeep6 X hX]; simp [hv5, Function.update_of_ne hXQ]

end NearCubicGates.Close.Solve

import Proof.Gates.Solve.Points2

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
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM)
open NearCubicWires.RepairRepresentation (natWord)

/-- The cost bound of the points phase. -/
def ptsCost (n ℓ W : ℕ) : ℕ :=
  (n + 2) * (ptCost ℓ W + 4) + 200 * (n + 2) ^ 2 + 5 * (n * ℓ * (2 * (W + 1) + 1)) + 20 * (n + 2) + 50

theorem points_spec (cap : ℕ) {σ0 σ : MS} {W ℓ n : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {word restP : List Bool}
    {pts : List (List ℤ)} (hc : RawCtx σ0 W word) (hword : word = natWord n ++ pts.flatMap ptW ++ restP)
    (hn : pts.length = n) (hpts : ∀ u ∈ pts, u.length ≤ ℓ ∧ ∀ z ∈ u, z.natAbs < 2 ^ W) (hsh : σ0.sh sRAW = 0)
    (hLL : σ0.val rLL = ℓ) (hz : ∀ q ∈ [rNN, rLP, rUL, rPAD, rSGN, rCP], σ0.val q = 0) (hZ : v wZ = 0)
    (hPT : σ0.st sPT = []) (hPTh : σ0.sh sPT = 0) (hW : 1 ≤ W) (hcap : capP n ℓ W ≤ cap) :
    Runs cap pointsP σ (ptsCost n ℓ W) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sRAW = σ0.st sRAW ∧
      σ1.sh sRAW = (natWord n ++ pts.flatMap ptW).length ∧
      σ1.st sPT = recStream ((pts.flatMap (ptVals ℓ)).map (binary (W + 1))) ∧ σ1.sh sPT = 0 ∧ σ1.val rNN = n ∧
      (∀ q ∈ [rCP, rPAD, rUL, rSGN, rLP], σ1.val q = 0) ∧
      SameExcept σ0 σ1 [sRAW, sPT] [rNN, rCP, rPAD, rUL, rSGN, rLP] ∧ v1 wZ = 0) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨hNN, hLP, hUL, hPAD, hSGN, hCP⟩ := hz
  have hcapP := hcap
  unfold capP at hcapP
  have hQ4 : 4 * (2 * (W + 1) + 1) ≤ (n + 2) * (ℓ + 2) * (2 * (W + 1) + 1) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have hnc : 4 * n + 8 ≤ cap := by
    have h1 : 4 ≤ (ℓ + 2) * (2 * (W + 1) + 1) := by nlinarith
    have h2 : (n + 2) * 4 ≤ (n + 2) * ((ℓ + 2) * (2 * (W + 1) + 1)) := Nat.mul_le_mul_left _ h1
    rw [← mul_assoc] at h2
    omega
  have hcost : readCost n + 1 + (18 * n + 3 + 1 + ((n * (ptCost ℓ W + 4) + 1) + 1 +
      (5 * (n * ℓ * (2 * (W + 1) + 1)) + 3))) ≤ ptsCost n ℓ W := by
    unfold ptsCost
    have := readCost_le n
    have e : (n + 2) * (ptCost ℓ W + 4) = n * (ptCost ℓ W + 4) + 2 * (ptCost ℓ W + 4) := by ring
    omega
  refine Runs.cost ?_ hcost
  -- 1. `NN := n`
  have hst : σ0.st sRAW = [] ++ natWord n ++ (pts.flatMap ptW ++ restP) := by rw [hc.raw, hword]; simp
  refine Runs.seq (opReadNat cap h (V := rNN) (by decide) n [] _ hst (by simpa using hsh)
    (by have := two_pow_nbl_le n; rw [hNN, pow_succ]; omega)) (fun τ1 h1 => ?_)
  set σ1 := (σ0.seth sRAW (([] : List Bool).length + (natWord n).length)).setv rNN (σ0.val rNN + n) with hσ1
  -- 2. `LP := n`
  have h1NN : σ1.val rNN = n := by simp [hσ1, hNN]
  refine Runs.seq ((opAddR cap h1 (A := rNN) (B := rLP) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ1, hLP, hNN]; omega)).cost
      (show 18 * σ1.val rNN + 3 ≤ 18 * n + 3 by rw [h1NN])) (fun τ2 h2 => ?_)
  rw [h1NN] at h2
  set σ2 := σ1.setv rLP (σ1.val rLP + n) with hσ2
  have hfr02 : SameExcept σ0 σ2 [sRAW, sPT] [rNN, rCP, rPAD, rUL, rSGN, rLP] :=
    SameExcept.trans (sameExcept_seth σ0 (by simp) _) (SameExcept.trans (sameExcept_setv _ (by simp) _)
      (sameExcept_setv _ (by simp) _))
  have hc2 : RawCtx σ2 W word := hc.same hfr02 (by simp [hσ2, hσ1]) (by decide) (by decide)
  -- 3. the point loop
  have hI0 : PInv σ2 W ℓ n pts 0 τ2 := by
    refine ⟨σ2, v, h2, rfl, by simp [hσ2, hσ1], ⟨?_, ?_, ?_⟩, by simp (config := {decide := true}) [hσ2, hσ1, hUL],
      by simp (config := {decide := true}) [hσ2, hσ1, hPAD], by simp (config := {decide := true}) [hσ2, hσ1, hSGN],
      SameExcept.refl _ _ _, hZ⟩
    · simp [hσ2, hσ1, hPT, recBits, overlay]
    · simp (config := {decide := true}) [hσ2, hσ1, hPTh, recBits]
    · simp (config := {decide := true}) [hσ2, hσ1, hCP, recBits]
  have hloop := Runs.count (cap := cap) (K := rLP) (body := pointBody) (ptCost ℓ W) n (PInv σ2 W ℓ n pts)
    (by omega) (fun k hk τ hτ _ => points_step cap hc2 hword hn hpts (by rw [hfr02.val (by decide), hLL]) hW hcap
      k hk τ hτ) τ2 hI0 (by rw [h2.val (by decide)]; simp (config := {decide := true}) [hσ2, hσ1, hLP])
  refine Runs.seq hloop (fun τ3 ⟨⟨σ3, v3, h3, hraw3, hsh3, hout3, hUL3, hPAD3, hSGN3, hfr3, hZ3⟩, hK3⟩ => ?_)

  have htake : pts.take n = pts := by rw [← hn, List.take_length]
  rw [htake] at hsh3 hout3
  have hlen : (recBits W (pts.flatMap (ptVals ℓ))).length = n * ℓ * (2 * (W + 1) + 1) := by
    rw [recBits_ptVals_length, hn]
  have hlc : n * ℓ * (2 * (W + 1) + 1) ≤ cap := by
    have : n * ℓ ≤ (n + 2) * (ℓ + 2) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) this
    omega
  refine ((opCloseOut cap h3 (O := sPT) (CO := rCP) (by decide) (by decide) hout3 (by rw [hlen]; exact hlc)).cost
    (show 5 * (recBits W (pts.flatMap (ptVals ℓ))).length + 3 ≤ 5 * (n * ℓ * (2 * (W + 1) + 1)) + 3 by
      rw [hlen])).post (fun τ4 h4 => ⟨_, v3, h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hZ3⟩)
  · simp (config := {decide := true}); rw [hraw3]; simp [hσ2, hσ1]
  · simp (config := {decide := true}); rw [hsh3]; simp [hσ2, hσ1]
  · simp [overlay, recStream_eq]
  · simp
  · simp (config := {decide := true}); rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2, hσ1, hNN]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simp
    · simp (config := {decide := true}); exact hPAD3
    · simp (config := {decide := true}); exact hUL3
    · simp (config := {decide := true}); exact hSGN3
    · simp (config := {decide := true}); rw [← h3.val (by decide)]; exact hK3
  · exact SameExcept.trans hfr02 (SameExcept.trans (hfr3.weaken (by simp) (by simp))
      (SameExcept.trans (sameExcept_sets σ3 (by simp) _) (SameExcept.trans (sameExcept_seth _ (by simp) _)
        (sameExcept_setv _ (by simp) _))))

end NearCubicGates.Close.Solve

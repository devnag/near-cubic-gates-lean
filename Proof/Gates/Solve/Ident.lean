import Proof.Gates.Solve.Rows8

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
open NearCubicGates.Close.Interfaces.Formats (inClass SysReq)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM)

def rowsP : WMX NS NR :=
  .seq (.wm (readNatM false sRAW rCA rCW rMM rK2 rG)) (.seq (addR rMM rLR rTa)
    (.whr rLR (.seq (WMX.dec rLR) (.seq rowA rowB))))

/-- The cost bound of the rows phase. -/
def rowsCost (m n ℓ W U : ℕ) : ℕ := (m + 2) * (rowCost n ℓ W U + 4) + 200 * (m + 2) ^ 2 + 20 * (m + 2)

theorem rows_spec (cap : ℕ) {σ0 σ : MS} {W ℓ : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {word : List Bool}
    (hc : RawCtx σ0 W word) (s : SysReq) (hrb : ReqBound s ℓ) {pre0 rest0 : List Bool}
    (hword : word = pre0 ++ natWord s.rows.length ++ s.rows.flatMap rowW ++ rest0) (hsh : σ0.sh sRAW = pre0.length)
    {jP : List Bool} (hPT : σ0.st sPT = recStream ((s.pts.flatMap (ptVals ℓ)).map (binary (W + 1))) ++ jP)
    (hPTh : σ0.sh sPT = 0) (hNN : σ0.val rNN = s.pts.length) (hLL : σ0.val rLL = ℓ) (hSGh : σ0.sh sSG = 0)
    (hz : ∀ r ∈ rMM :: rLR :: rLS :: rCSG :: rowRegs, σ0.val r = 0) (hvZ : v wZ = 0) (hvT : v wTWO = 2)
    {L0 : List Bool} (hout : OutOn σ0 sMAT rCM [] L0) (hℓW : ℓ + 2 ≤ W) (hℓ1 : 1 ≤ ℓ)
    (hcap : capC (s.pts.length * ℓ + ℓ) W ≤ cap)
    (hcapO : (s.rows.length + 1) * (s.pts.length + 2) * (2 * (W + 1) + 1) + (ℓ + 2) * (2 * (W + 1) + 1) + 8 * ℓ + 8 ≤ cap)
    (hcapm : 4 * s.rows.length + 8 ≤ cap) :
    Runs cap rowsP σ (rowsCost s.rows.length s.pts.length ℓ W (ucost W (s.pts.length * ℓ + ℓ))) (fun τ =>
      ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sRAW = σ0.st sRAW ∧
        σ1.sh sRAW = pre0.length + (natWord s.rows.length ++ s.rows.flatMap rowW).length ∧
        OutOn σ1 sMAT rCM (recBits W (matV s.rows.length (s.pts.length + 1) (amat s))) L0 ∧
        σ1.val rMM = s.rows.length ∧ (∀ r ∈ rLR :: rLS :: rCSG :: rowRegs, σ1.val r = 0) ∧ σ1.sh sSG = 0 ∧
        SameExcept σ0 σ1 [sRAW, sSG, sMAT] (rCM :: rMM :: rLR :: rLS :: rCSG :: rowRegs) ∧ v1 wZ = 0 ∧ v1 wTWO = 2) := by
  set m := s.rows.length with hm
  have hMM : σ0.val rMM = 0 := hz rMM (by decide)
  have hLR : σ0.val rLR = 0 := hz rLR (by decide)
  have hcost : readCost m + 1 + (18 * m + 3 + 1 + (m * (rowCost s.pts.length ℓ W (ucost W (s.pts.length * ℓ + ℓ)) + 4)
      + 1)) ≤ rowsCost m s.pts.length ℓ W (ucost W (s.pts.length * ℓ + ℓ)) := by
    unfold rowsCost
    have := readCost_le m
    have e : (m + 2) * (rowCost s.pts.length ℓ W (ucost W (s.pts.length * ℓ + ℓ)) + 4) =
        m * (rowCost s.pts.length ℓ W (ucost W (s.pts.length * ℓ + ℓ)) + 4) +
          2 * (rowCost s.pts.length ℓ W (ucost W (s.pts.length * ℓ + ℓ)) + 4) := by ring
    omega
  refine Runs.cost ?_ hcost
  -- 1. `MM := m`
  have hst : σ0.st sRAW = pre0 ++ natWord m ++ (s.rows.flatMap rowW ++ rest0) := by
    rw [hc.raw, hword]; simp [List.append_assoc]
  refine Runs.seq (opReadNat cap h (V := rMM) (by decide) m pre0 _ hst hsh
    (by have := two_pow_nbl_le m; rw [hMM, pow_succ]; omega)) (fun τ1 h1 => ?_)
  set σ1 := (σ0.seth sRAW (pre0.length + (natWord m).length)).setv rMM (σ0.val rMM + m) with hσ1
  have h1MM : σ1.val rMM = m := by simp [hσ1, hMM]
  -- 2. `LR := m`
  refine Runs.seq ((opAddR cap h1 (A := rMM) (B := rLR) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ1, hLR, hMM]; omega)).cost
    (show 18 * σ1.val rMM + 3 ≤ 18 * m + 3 by rw [h1MM])) (fun τ2 h2 => ?_)
  set σ2 := σ1.setv rLR (σ1.val rLR + σ1.val rMM) with hσ2
  have hfr02 : SameExcept σ0 σ2 [sRAW] [rMM, rLR] :=
    SameExcept.trans (sameExcept_seth σ0 (by simp) _) (SameExcept.trans (sameExcept_setv _ (by simp) _)
      (sameExcept_setv _ (by simp) _))
  have hc2 : RawCtx σ2 W word := hc.same hfr02 (by simp [hσ2, hσ1]) (by decide) (by decide)
  -- 3. the rows
  have hout2 : OutOn σ2 sMAT rCM [] L0 := OutOn.same hout hfr02 (by decide) (by decide)
  have hI0 : RInv σ2 W s (pre0 ++ natWord m).length L0 0 τ2 := by
    refine ⟨σ2, v, h2, rfl, by simp [hσ2, hσ1], by simpa [matV, flat, recBits] using hout2, fun r hr => ?_, ?_, ?_, ?_,
      SameExcept.refl _ _ _, hvZ, hvT⟩
    · have : r ∉ [rMM, rLR] := by
        simp only [rowRegs, cellRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hfr02.val this]; exact hz r (by simp only [List.mem_cons] at hr ⊢; tauto)
    · rw [hfr02.val (by decide)]; exact hz rLS (by decide)
    · rw [hfr02.val (by decide)]; exact hz rCSG (by decide)
    · rw [hfr02.sh (by decide)]; exact hSGh
  have hloop := Runs.count (cap := cap) (K := rLR) (body := .seq rowA rowB)
    (rowCost s.pts.length ℓ W (ucost W (s.pts.length * ℓ + ℓ))) m (RInv σ2 W s (pre0 ++ natWord m).length L0)
    (by omega) (fun i hi τ hτ _ => rows_step cap hc2 s hrb (pre0 := pre0 ++ natWord m) (rest0 := rest0)
      (by rw [hword]) (by rw [hfr02.st (by decide), hPT]) (by rw [hfr02.sh (by decide), hPTh])
      (by rw [hfr02.val (by decide), hNN]) (by rw [hfr02.val (by decide), hLL]) hℓW hℓ1 hcap hcapO i hi τ hτ) τ2 hI0
    (by rw [h2.val (by decide)]; simp (config := {decide := true}) [hσ2, hσ1, hLR, hMM])
  refine hloop.post (fun τ3 ⟨⟨σ3, v3, h3, hraw3, hsh3, hout3, hz3, hLS3, hCSG3, hSGh3, hfr3, hZ3, hT3⟩, hK3⟩ =>
    ⟨σ3, v3, h3, ?_, ?_, ?_, ?_, ?_, hSGh3, ?_, hZ3, hT3⟩)
  · rw [hraw3]; simp [hσ2, hσ1]
  · rw [hsh3, List.take_length]; simp; omega
  · simpa using hout3
  · rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2, hσ1, hMM]
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · rw [← h3.val (by decide)]; exact hK3
    · exact hLS3
    · exact hCSG3
    · exact hz3 r hr
  · refine SameExcept.trans (hfr02.weaken (by simp) (by simp)) (hfr3.weaken (by simp) (fun r hr => ?_))
    simp only [List.mem_cons] at hr ⊢; tauto

end NearCubicGates.Close.Solve

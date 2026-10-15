import Proof.Gates.Solve.Build3

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
open NearCubicGates.Close.Interfaces.Formats (SysReq sysWord)

/-- The cost bound of the second part of the build. -/
def buildBCost (m n ℓ W : ℕ) : ℕ := 100 * (m + n + ℓ + 2) + 50 * (W + 2)

theorem buildB_spec (cap : ℕ) {σ0 σ : MS} {W m n ℓ : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (hRR : σ0.val rRR = 0)
    (hCC : σ0.val rCC = 0) (hT1 : σ0.val rT1 = 0) (hNN : σ0.val rNN = n) (hMM : σ0.val rMM = m) (hLL : σ0.val rLL = ℓ)
    (hRAWh : σ0.sh sRAW ≤ ℓ) (hcap : m + n + ℓ + 2 + 2 * (W + 1) + 1 ≤ cap) :
    Runs cap buildB σ (buildBCost m n ℓ W) (fun τ => ∃ σ1, At σ1 τ W (Function.update v wDD (v wTWO)) ∧
      σ1.sh sRAW = 0 ∧ σ1.val rRR = m + n ∧ σ1.val rCC = n + 1 ∧ σ1.val rT1 = 0 ∧
      SameExcept σ0 σ1 [sRAW] [rRR, rCC, rT1]) := by
  have hcost : 18 * m + 3 + 1 + (18 * n + 3 + 1 + (18 * n + 3 + 1 + (3 + 1 + (41 * (W + 1) + 3 + 1 +
      (18 * ℓ + 3 + 1 + (5 * ℓ + 1)))))) ≤ buildBCost m n ℓ W := by unfold buildBCost; omega
  refine Runs.cost ?_ hcost
  refine Runs.seq ((opAddR cap h (A := rMM) (B := rRR) (by decide) (by decide) (by decide) (by rw [hRR, hMM]; omega)).cost
    (show 18 * σ0.val rMM + 3 ≤ 18 * m + 3 by rw [hMM])) (fun τ1 h1 => ?_)
  set σ1 := σ0.setv rRR (σ0.val rRR + σ0.val rMM) with hσ1
  refine Runs.seq ((opAddR cap h1 (A := rNN) (B := rRR) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ1, hRR, hMM, hNN]; omega)).cost
    (show 18 * σ1.val rNN + 3 ≤ 18 * n + 3 by simp (config := {decide := true}) [hσ1, hNN])) (fun τ2 h2 => ?_)
  set σ2 := σ1.setv rRR (σ1.val rRR + σ1.val rNN) with hσ2
  refine Runs.seq ((opAddR cap h2 (A := rNN) (B := rCC) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ2, hσ1, hCC, hNN]; omega)).cost
    (show 18 * σ2.val rNN + 3 ≤ 18 * n + 3 by simp (config := {decide := true}) [hσ2, hσ1, hNN])) (fun τ3 h3 => ?_)
  set σ3 := σ2.setv rCC (σ2.val rCC + σ2.val rNN) with hσ3
  have h3CC : σ3.val rCC < cap := by simp (config := {decide := true}) [hσ3, hσ2, hσ1, hCC, hNN]; omega
  refine Runs.seq (opIncR cap h3 (r := rCC) (by decide) h3CC) (fun τ4 h4 => ?_)
  set σ4 := σ3.setv rCC (σ3.val rCC + 1) with hσ4
  refine Runs.seq (opCopy cap h4 (X := wDD) (Y := wTWO) (by decide) (by decide) (by decide) (by omega)) (fun τ5 h5 => ?_)
  have h4LL : σ4.val rLL = ℓ := by simp (config := {decide := true}) [hσ4, hσ3, hσ2, hσ1, hLL]
  refine Runs.seq ((opAddR cap h5 (A := rLL) (B := rT1) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ4, hσ3, hσ2, hσ1, hT1, hLL]; omega)).cost
    (show 18 * σ4.val rLL + 3 ≤ 18 * ℓ + 3 by rw [h4LL])) (fun τ6 h6 => ?_)
  set σ6 := σ4.setv rT1 (σ4.val rT1 + σ4.val rLL) with hσ6
  have h6T1 : σ6.val rT1 = ℓ := by simp (config := {decide := true}) [hσ6, hσ4, hσ3, hσ2, hσ1, hT1, hLL]
  have e := wrewind_spec (cap := cap) sRAW rT1 ℓ τ6 (by rw [h6.val (by decide), h6T1]) (by
    rw [h6.val (by decide), h6T1]; omega)
  refine Runs.of (WXExec.wm e) ⟨(σ6.setv rT1 0).seth sRAW (σ6.sh sRAW - ℓ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h6.sh (by decide)]; exact (h6.setv (by decide) 0).sethO (by decide) _
  · simp (config := {decide := true}) [hσ6, hσ4, hσ3, hσ2, hσ1]; omega
  · simp (config := {decide := true}) [hσ6, hσ4, hσ3, hσ2, hσ1, hRR, hMM, hNN]
  · simp (config := {decide := true}) [hσ6, hσ4, hσ3, hσ2, hσ1, hCC, hNN]
  · simp (config := {decide := true})
  · refine ⟨fun x hx => ?_, fun r hr => ?_, rfl⟩
    · have : x ≠ sRAW := by simpa using hx
      simp [hσ6, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne this]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hσ6, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2]

def buildCost (m n ℓ W : ℕ) : ℕ := buildACost m n ℓ W + 1 + buildBCost m n ℓ W

theorem build_spec (cap : ℕ) {σS σ : MS} {W ℓ : ℕ} {v : Str → ℕ} (h : At σS σ W v) (s : SysReq)
    (hc : RawCtx σS W (sysWord s)) (hrb : ReqBound s ℓ) (hsh : ∀ X, σS.sh X = 0) (hLL : σS.val rLL = ℓ)
    (hz : ∀ r ∈ bRegs, σS.val r = 0) (hZ : v wZ = 0) (hPT : σS.st sPT = []) (hMAT : σS.st sMAT = [])
    (hℓW : ℓ + 2 ≤ W) (hℓ1 : 1 ≤ ℓ) (hℓs : (sysWord s).length ≤ ℓ) (hcap : capB s.rows.length s.pts.length ℓ W ≤ cap) :
    Runs cap buildP σ (buildCost s.rows.length s.pts.length ℓ W) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      σ1.st sMAT = recStream ((matV (s.rows.length + s.pts.length) (s.pts.length + 1) (amat s)).map (binary (W + 1))) ∧
      (∀ X, X ∉ wset → σ1.sh X = 0) ∧ σ1.val rNN = s.pts.length ∧ σ1.val rMM = s.rows.length ∧
      σ1.val rRR = s.rows.length + s.pts.length ∧ σ1.val rCC = s.pts.length + 1 ∧ σ1.val rCM = 0 ∧
      SameExcept σS σ1 [sRAW, sPT, sSG, sMAT] bRegs ∧ v1 wZ = 0 ∧ v1 wDD = 2) := by
  have hcapB := hcap
  unfold capB at hcapB
  refine Runs.seq (buildA_spec cap h s hc hrb hsh hLL hz hZ hPT hMAT hℓW hℓ1 hℓs hcap) (fun τ1 ⟨σ1, v1, h1, hmat1,
    hmath1, hCM1, hraw1, hsh1, hpt1, hsg1, hNN1, hMM1, hfr1, hZ1, hT1⟩ => ?_)
  have hB := buildB_spec cap h1 (m := s.rows.length) (n := s.pts.length) (ℓ := ℓ)
    (by rw [hfr1.val (by decide)]; exact hz rRR (by decide)) (by rw [hfr1.val (by decide)]; exact hz rCC (by decide))
    (by rw [hfr1.val (by decide)]; exact hz rT1 (by decide)) hNN1 hMM1 (by rw [hfr1.val (by decide), hLL])
    (by rw [hsh1]; exact hℓs) (by
      have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < ℓ + 2 by omega); omega)
  refine hB.post (fun τ2 ⟨σ2, h2, hRAW2, hRR2, hCC2, hT12, hfr2⟩ => ⟨σ2, _, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · rw [hfr2.st (by decide), hmat1]
  · intro X hX
    by_cases h1 : X = sRAW
    · subst h1; exact hRAW2
    · rw [hfr2.sh (by simpa using h1)]
      by_cases h2 : X = sMAT
      · subst h2; exact hmath1
      · by_cases h3 : X = sPT
        · subst h3; exact hpt1
        · by_cases h4 : X = sSG
          · subst h4; exact hsg1
          · rw [hfr1.sh (by simp [h1, h2, h3, h4])]; exact hsh X
  · rw [hfr2.val (by decide)]; exact hNN1
  · rw [hfr2.val (by decide)]; exact hMM1
  · exact hRR2
  · exact hCC2
  · rw [hfr2.val (by decide)]; exact hCM1
  · exact SameExcept.trans (hfr1.weaken (by simp) (by simp [bRegsA, bRegs])) (hfr2.weaken (by simp) (by simp [bRegs]))
  · simp (config := {decide := true}) [hZ1]
  · simp [hT1]

end NearCubicGates.Close.Solve

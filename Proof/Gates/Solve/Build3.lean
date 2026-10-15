import Proof.Gates.Solve.Build2

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
open NearCubicWires.RepairRepresentation (natWord)

theorem rows_regs_mem {r : Reg} (hr : r ∈ rMM :: rLR :: rLS :: rCSG :: rowRegs) (hne : r ≠ rSGN) :
    r ∉ [rNN, rCP, rPAD, rUL, rSGN, rLP] ∧ r ∈ bRegs := by
  simp only [rowRegs, cellRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | decide | exact absurd rfl hne

theorem ident_regs_mem {r : Reg} (hr : r ∈ [rLV2, rBEF, rAFT, rK3]) :
    r ∉ rCM :: rMM :: rLR :: rLS :: rCSG :: rowRegs ∧ r ∉ [rNN, rCP, rPAD, rUL, rSGN, rLP] ∧ r ∈ bRegs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

theorem pts_regs_mem {q : Reg} (hq : q ∈ [rNN, rLP, rUL, rPAD, rSGN, rCP]) : q ∈ bRegs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The cap of the build. -/
def capB (m n ℓ W : ℕ) : ℕ :=
  capP n ℓ W + capC (n * ℓ + ℓ) W + (m + 1) * (n + 2) * (2 * (W + 1) + 1) + (ℓ + 2) * (2 * (W + 1) + 1) +
    m * (n + 1) * (2 * (W + 1) + 1) + (n + 1) * (n + 3) * (2 * (W + 1) + 1) +
    (m + n) * (n + 1) * (2 * (W + 1) + 1) + 8 * ℓ + 4 * m + 4 * n + 100

/-- The cost bound of the first part of the build. -/
def buildACost (m n ℓ W : ℕ) : ℕ :=
  ptsCost n ℓ W + rowsCost m n ℓ W (ucost W (n * ℓ + ℓ)) + identCost n W +
    5 * ((m + n) * (n + 1) * (2 * (W + 1) + 1)) + 200 * (W + 2) + 10

theorem buildA_spec (cap : ℕ) {σS σ : MS} {W ℓ : ℕ} {v : Str → ℕ} (h : At σS σ W v) (s : SysReq)
    (hc : RawCtx σS W (sysWord s)) (hrb : ReqBound s ℓ) (hsh : ∀ X, σS.sh X = 0) (hLL : σS.val rLL = ℓ)
    (hz : ∀ r ∈ bRegs, σS.val r = 0) (hZ : v wZ = 0) (hPT : σS.st sPT = []) (hMAT : σS.st sMAT = [])
    (hℓW : ℓ + 2 ≤ W) (hℓ1 : 1 ≤ ℓ) (hℓs : (sysWord s).length ≤ ℓ) (hcap : capB s.rows.length s.pts.length ℓ W ≤ cap) :
    Runs cap buildA σ (buildACost s.rows.length s.pts.length ℓ W) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      σ1.st sMAT = recStream ((matV (s.rows.length + s.pts.length) (s.pts.length + 1) (amat s)).map (binary (W + 1))) ∧
      σ1.sh sMAT = 0 ∧ σ1.val rCM = 0 ∧ σ1.st sRAW = σS.st sRAW ∧ σ1.sh sRAW = (sysWord s).length ∧
      σ1.sh sPT = 0 ∧ σ1.sh sSG = 0 ∧ σ1.val rNN = s.pts.length ∧ σ1.val rMM = s.rows.length ∧
      SameExcept σS σ1 [sRAW, sPT, sSG, sMAT] bRegsA ∧ v1 wZ = 0 ∧ v1 wTWO = 2) := by
  have hcapB := hcap
  unfold capB at hcapB
  unfold buildACost
  set m := s.rows.length with hm
  set n := s.pts.length with hn
  set Q := 2 * (W + 1) + 1 with hQ
  have hpowW : 2 ^ ℓ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzr : ∀ r ∈ bRegs, σS.val r = 0 := hz
  have hp4 : 4 ≤ 2 ^ (W + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcW : Q ≤ cap := by
    have := Nat.le_mul_of_pos_left Q (show 0 < ℓ + 2 by omega); omega
  have hcost : ptsCost n ℓ W + 1 + (50 * (W + 2) + 1 + (50 * (W + 2) + 1 + (50 * (W + 2) + 1 +
      (rowsCost m n ℓ W (ucost W (n * ℓ + ℓ)) + 1 + (identCost n W + 1 + (5 * ((m + n) * (n + 1) * Q) + 3)))))) ≤
      ptsCost n ℓ W + rowsCost m n ℓ W (ucost W (n * ℓ + ℓ)) + identCost n W +
      5 * ((m + n) * (n + 1) * Q) + 200 * (W + 2) + 10 := by omega
  refine Runs.cost ?_ hcost
  -- 1. points
  have hP := points_spec cap h (n := n) (restP := natWord m ++ s.rows.flatMap rowW) hc (sysWord_eq s) rfl
    (fun u hu => ⟨(hrb.pts u hu).1, fun z hz' => lt_of_lt_of_le ((hrb.pts u hu).2 z hz') hpowW⟩) (hsh sRAW) hLL
    (fun q hq => hzr q (pts_regs_mem hq)) hZ hPT (hsh sPT) (by omega) (by omega)
  refine Runs.seq hP (fun τ1 ⟨σ1, v1, h1, hraw1, hsh1, hpt1, hpth1, hNN1, hz1, hfr1, hZ1⟩ => ?_)
  -- 2. `wTWO := 2`
  refine Runs.seq ((opZero cap h1 (X := wTWO) (by decide) (by decide) hcW).cost (show 41 * (W + 1) + 3 ≤ 50 * (W + 2) by
    omega)) (fun τ2 h2 => ?_)
  refine Runs.seq ((opInc cap h2 (X := wTWO) (by decide) (by decide) (by simp <;> omega) hcW).cost
    (show 41 * (W + 1) + 7 ≤ 50 * (W + 2) by omega)) (fun τ3 h3 => ?_)
  refine Runs.seq ((opInc cap h3 (X := wTWO) (by decide) (by decide) (by simp <;> omega) hcW).cost
    (show 41 * (W + 1) + 7 ≤ 50 * (W + 2) by omega)) (fun τ4 h4 => ?_)
  set v4 := Function.update (Function.update (Function.update v1 wTWO 0) wTWO (Function.update v1 wTWO 0 wTWO + 1))
    wTWO (Function.update (Function.update v1 wTWO 0) wTWO (Function.update v1 wTWO 0 wTWO + 1) wTWO + 1) with hv4
  have hv4T : v4 wTWO = 2 := by simp [hv4]
  have hv4Z : v4 wZ = 0 := by simp (config := {decide := true}) [hv4, hZ1]
  -- 3. rows
  have hc1 : RawCtx σ1 W (sysWord s) := hc.same hfr1 hraw1 (by decide) (by decide)
  have hR := rows_spec cap h4 hc1 s hrb (pre0 := natWord n ++ s.pts.flatMap ptW) (rest0 := [])
    (by rw [sysWord_eq]; simp [List.append_assoc] <;> rfl) (by rw [hsh1]) (jP := []) (by rw [hpt1]; simp) hpth1 hNN1
    (by rw [hfr1.val (by decide), hLL]) (by rw [hfr1.sh (by decide), hsh sSG])
    (fun r hr => by
      by_cases hrS : r = rSGN
      · subst hrS; exact hz1 rSGN (by decide)
      · rw [hfr1.val (rows_regs_mem hr hrS).1]; exact hzr r (rows_regs_mem hr hrS).2)
    hv4Z hv4T (outOn_start σ1 sMAT rCM (by rw [hfr1.sh (by decide), hsh sMAT])
      (by rw [hfr1.val (by decide)]; exact hzr rCM (by simp [bRegs]))) hℓW hℓ1
    (by (try simp only [← hn, ← hm, ← hQ]); omega) (by (try simp only [← hn, ← hm, ← hQ]); omega)
    (by (try simp only [← hn, ← hm, ← hQ]); omega)
  refine Runs.seq hR (fun τ5 ⟨σ5, v5, h5, hraw5, hsh5, hout5, hMM5, hz5, hSG5, hfr5, hZ5, hT5⟩ => ?_)
  -- 4. identity rows
  have hlen5 : (recBits W (matV m (n + 1) (amat s))).length = m * (n + 1) * Q := by
    rw [recBits_length, matV_length]
  have hI := ident_spec cap h5 hZ5 hT5 (n := n) (by rw [hfr5.val (by decide), hNN1])
    (fun r hr => by
      rw [hfr5.val (ident_regs_mem hr).1, hfr1.val (ident_regs_mem hr).2.1]; exact hzr r (ident_regs_mem hr).2.2)
    hout5 (by rw [hlen5]; (try simp only [← hn, ← hm, ← hQ]); omega)
  refine Runs.seq hI (fun τ6 ⟨σ6, h6, hout6, hz6, hfr6⟩ => ?_)
  -- 5. close `MAT`
  have hmat6 : recBits W (matV m (n + 1) (amat s)) ++ recBits W ((List.range n).flatMap (idRow n)) =
      recBits W (matV (m + n) (n + 1) (amat s)) := by rw [matV_amat s, recBits_append]
  rw [hmat6] at hout6
  have hlen6 : (recBits W (matV (m + n) (n + 1) (amat s))).length = (m + n) * (n + 1) * Q := by
    rw [recBits_length, matV_length]
  refine ((opCloseOut cap h6 (O := sMAT) (CO := rCM) (by decide) (by decide) hout6 (by rw [hlen6]; omega)).cost
    (show 5 * (recBits W (matV (m + n) (n + 1) (amat s))).length + 3 ≤ 5 * ((m + n) * (n + 1) * Q) + 3 by
      rw [hlen6])).post (fun τ7 h7 => ⟨_, v5, h7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hZ5, hT5⟩)
  · simp (config := {decide := true}) [overlay, recStream_eq]; rw [hfr1.st (by decide), hMAT]; simp
  · simp (config := {decide := true})
  · simp (config := {decide := true})
  · simp (config := {decide := true}); rw [hfr6.st (by decide), hraw5, hraw1]
  · simp (config := {decide := true}); rw [hfr6.sh (by decide), hsh5, sysWord_eq]; simp; (try simp only [← hn, ← hm]); omega
  · simp (config := {decide := true}); rw [hfr6.sh (by decide), hfr5.sh (by decide)]; exact hpth1
  · simp (config := {decide := true}); rw [hfr6.sh (by decide)]; exact hSG5
  · simp (config := {decide := true}); rw [hfr6.val (by decide), hfr5.val (by decide)]; exact hNN1
  · simp (config := {decide := true}); rw [hfr6.val (by decide)]; exact hMM5
  · refine SameExcept.trans (hfr1.weaken (by simp) (by simp [bRegsA])) (SameExcept.trans (hfr5.weaken (by simp)
      (by simp [rowRegs, cellRegs, bRegsA])) (SameExcept.trans (hfr6.weaken (by simp) (by simp [bRegsA])) ?_))
    exact SameExcept.trans (sameExcept_sets σ6 (by simp) _) (SameExcept.trans (sameExcept_seth _ (by simp) _)
      (sameExcept_setv _ (by simp [bRegsA]) _))

end NearCubicGates.Close.Solve

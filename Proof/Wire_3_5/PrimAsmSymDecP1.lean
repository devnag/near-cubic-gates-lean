import Proof.Wire_3_5.PrimAsmSymDecPre
import Proof.Wire_3_5.PrimAsmCellLoopD

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.CellState

section P1
variable (cap : ℕ) (x : ℕ)

/-- The decode's first stage. -/
def p1W : WM (LNS x) LNR :=
  .seq (preAW x) (.seq (reqParseW x) (.seq (preBW x) (.seq (carW x) (countsW x))))

/-- The first stage's needs. -/
structure P1Need (w : List Bool) (n : ℕ) (codes ccs cx cy : List ℕ) (Kb Cmax : ℕ) : Prop where
  cW : 2 * w.length + 2 ≤ cap
  cP : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength ccs.length + 1) +
    Kb + n + codes.length + 1 ≤ cap
  cX : cx.sum + cx.length + 4 ≤ cap
  cC : cx.length + cy.sum + Cmax + 1 ≤ cap

/-- **The decode's first stage.** -/
theorem p1_spec (w out : List Bool) (j n : ℕ) (codes ccs : List ℕ) (tl : List Bool) (cx cy : List ℕ) (Kb Cmax : ℕ)
    (hw : w = Data.reqW n false codes ccs tl) (hccs : ccs.length = cx.length) (hcx : cx.length ≤ 2)
    (hcy : cy.length ≤ 4) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hC : ∀ c ∈ cx ++ cy, c ≤ Cmax)
    (hN : P1Need cap w n codes ccs cx cy Kb Cmax) :
    ∃ τ c, WExec cap (p1W x) (CellLoopD.blankCellD x w out j (Data.unaryList (cx ++ cy))) τ c ∧
      τ.val dN = n ∧ τ.val dA = codes.length ∧ τ.val dNC = cx.length ∧
      τ.val dM0 = cy.getD 0 0 ∧ τ.val dM1 = cy.getD 1 0 ∧ τ.val dM2 = cy.getD 2 0 ∧ τ.val dM3 = cy.getD 3 0 ∧
      τ.val dMS = cy.sum ∧ τ.val XA = cx.getD 0 0 ∧ τ.val XB = cx.getD 1 0 ∧
      (∀ r : Fin LNR, r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ dM0 → r ≠ dM1 → r ≠ dM2 → r ≠ dM3 → r ≠ dMS → r ≠ LEN →
        r ≠ XA → r ≠ XB → τ.val r = 0) ∧ τ.val LEN = w.length ∧
      τ.st = (CellLoopD.blankCellD x w out j (Data.unaryList (cx ++ cy))).st ∧
      (∀ s, s ≠ sk x 113 → τ.sh s = (CellLoopD.blankCellD x w out j (Data.unaryList (cx ++ cy))).sh s) ∧
      τ.cell = false ∧
      c ≤ 4 * UnaryPow.sq cap + 1 + (reqParseCost n codes.length ccs.length Kb + 1 + (5 * UnaryPow.sq cap + 1 +
        (30 * UnaryPow.sq cap + 1 + countsCost cx.length Cmax cy.sum))) := by
  set σ0 := CellLoopD.blankCellD x w out j (Data.unaryList (cx ++ cy)) with hσ0
  have n01 : sk x 0 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n0B : sk x 0 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have nB1 : sk x 113 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have z0 : ∀ r, σ0.val r = 0 := fun r => by simp [hσ0, CellLoopD.blankCellD, blankCell]
  have s0 : σ0.st (sk x 0) = frame w := by simp [hσ0, CellLoopD.blankCellD, blankCell, n0B]
  have sh0 : σ0.sh (sk x 0) = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, n01]
  have s113 : σ0.st (sk x 113) = Data.unaryList (cx ++ cy) := by simp [hσ0, CellLoopD.blankCellD]
  have sh113 : σ0.sh (sk x 113) = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, nB1]
  -- A: measure, rewind
  have eA := preA_spec cap x w σ0 s0 sh0 (z0 _) (z0 _) (z0 _) hN.cW
  set σ1 := σ0.setv LEN w.length with hσ1
  have z1 : ∀ r, r ≠ LEN → σ1.val r = 0 := fun r h => by rw [hσ1]; simp [Function.update_apply, h, z0]
  have s1 : σ1.st = σ0.st := by rw [hσ1]; rfl
  have sh1 : σ1.sh = σ0.sh := by rw [hσ1]; rfl
  -- the parse
  obtain ⟨τ2, c2, eP, v2N, v2A, v2NC, v2F, v2C, v2P, v2T, v2K, k2, s2, sh2, cl2, c2le, hh2⟩ :=
    reqParse_spec2 cap x n false codes ccs tl Kb hKb σ1 (by rw [s1, s0, hw]) (by rw [sh1, sh0])
      (z1 _ (by decide)) (z1 _ (by decide)) (z1 _ (by decide)) (z1 _ (by decide))
      (z1 _ (by decide)) (z1 _ (by decide)) (z1 _ (by decide)) (z1 _ (by decide)) hN.cP
  have z2 : ∀ r, r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ dK → r ≠ LEN → τ2.val r = 0 := fun r a b c d e => by
    rw [k2 r a b c d]; exact z1 r e
  have vL2 : τ2.val LEN = w.length := by rw [k2 _ (by decide) (by decide) (by decide) (by decide), hσ1]; simp
  -- B: rewind
  have eB := preB_spec cap x w.length τ2 vL2 (z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [← hw, frame_length] at hh2; exact hh2) hN.cW
  set σ3 := τ2.seth (sk x 0) 0 with hσ3
  have v3 : σ3.val = τ2.val := by rw [hσ3]; rfl
  have s3 : σ3.st = σ0.st := by rw [hσ3]; simp only [WState.seth_st]; rw [s2, s1]
  have sh3 : ∀ i, i ≠ sk x 0 → σ3.sh i = σ0.sh i := fun i h => by
    rw [hσ3]; simp [Function.update_apply, h, sh2 i h, sh1]
  -- the carriers
  have eC := car_spec cap x cx cy hcx σ3 (by rw [s3, s113]) (by rw [sh3 _ n0B.symm, sh113])
    (by rw [v3, v2NC, hccs])
    (by rw [v3]; exact z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v3]; exact z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v3]; exact z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v3]; exact z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v3]; exact z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hN.cX
  set σ4 := (σ3.setv XA (cx.getD 0 0)).setv XB (cx.getD 1 0) with hσ4
  have k4 : ∀ r, r ≠ XA → r ≠ XB → σ4.val r = τ2.val r := fun r a b => by
    rw [hσ4, ← v3]; simp [Function.update_apply, a, b]
  have s4 : σ4.st = σ0.st := by rw [hσ4]; simp only [WState.setv_st]; exact s3
  have sh4 : ∀ i, i ≠ sk x 0 → σ4.sh i = σ0.sh i := fun i h => by rw [hσ4]; simp only [WState.setv_sh]; exact sh3 i h
  have z4 : ∀ r, r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ dK → r ≠ LEN → r ≠ XA → r ≠ XB → σ4.val r = 0 :=
    fun r a b c d e f g => by rw [k4 r f g]; exact z2 r a b c d e
  -- the counts
  obtain ⟨τ5, c5, eK, v5M0, v5M1, v5M2, v5M3, v5MS, v5K, v5T, k5, s5, sh5, cl5, c5le⟩ :=
    counts_spec cap x cx cy hcy Cmax hC σ4 (by rw [s4, s113])
      (by rw [sh4 _ (fun e => absurd (sk_inj x e) (by decide)), sh113])
      (by rw [k4 _ (by decide) (by decide), v2NC, hccs])
      (by rw [k4 _ (by decide) (by decide), v2K]) (by rw [k4 _ (by decide) (by decide), v2T])
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      hN.cC
  refine ⟨τ5, _, WExec.seq eA (WExec.seq eP (WExec.seq eB (WExec.seq eC eK))), ?_, ?_, ?_, v5M0, v5M1, v5M2, v5M3,
    v5MS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k4 _ (by decide) (by decide), v2N]
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k4 _ (by decide) (by decide), v2A]
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k4 _ (by decide) (by decide), v2NC,
      hccs]
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hσ4]
    simp [Function.update_apply, (by decide : XA ≠ XB)]
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hσ4]; simp
  · intro r n7 n8 n9 n1 n2 n3 n4 n5 hL hA hB
    by_cases n6 : r = dK
    · subst n6; exact v5K
    rw [k5 r n1 n2 n3 n4 n5 n6]; exact z4 r n7 n8 n9 n6 hL hA hB
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k4 _ (by decide) (by decide), vL2]
  · rw [s5, s4]
  · intro s hs
    rw [sh5 s hs]
    by_cases h0 : s = sk x 0
    · subst h0; rw [hσ4, hσ3]; simp [sh0]
    · exact sh4 s h0
  · rw [cl5, hσ4, hσ3]; simp [cl2, hσ1, hσ0, CellLoopD.blankCellD, blankCell]
  · have := c2le; have := c5le; omega

end P1

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec

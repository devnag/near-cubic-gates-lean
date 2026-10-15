import Proof.Wire_3_5.PrimAsmSymDecP1

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

theorem out_G (i : Fin 64) : Outside (G i) := by simp only [Outside, G_val]; omega
theorem out_H (k : Fin 40) : Outside (H k) := by simp only [Outside, H_val]; omega

section P2
variable (cap : ℕ) (x : ℕ)

/-- The decode's second stage. -/
def p2W (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM (LNS x) LNR :=
  .seq (starCapW x cr fe ζ Cδ C) (.seq (symNumsW x) (idxW x))

/-- **The unit index split** in the block `H`: unit `j`, entry `j / EU` (cell row, state `t`, gap seed, list seed,
joint state), position `w = j % EU` in the entry, printed row `r`, position `v` in the row, target `s = v − 1`, the
flags `[j < TOT]`, `[w < EU − 1]`, `[v < M + 2]`, `[r < |carriers|]`. -/
structure HVals (τ : WState (LNS x) LNR) (j TOT EU M N2 nSt nFlat nc : ℕ) : Prop where
  h0 : τ.val (H 0) = j
  h1 : τ.val (H 1) = 0
  h2 : τ.val (H 2) = if j < TOT then 1 else 0
  h3 : τ.val (H 3) = j % EU
  h4 : τ.val (H 4) = j / EU
  h5 : τ.val (H 5) = EU - 1
  h6 : τ.val (H 6) = if j % EU < EU - 1 then 1 else 0
  h7 : τ.val (H 7) = (j % EU - 1) % (M + 3)
  h8 : τ.val (H 8) = M + 3
  h9 : τ.val (H 9) = (j % EU - 1) / (M + 3)
  h10 : τ.val (H 10) = M + 3 - 1
  h11 : τ.val (H 11) = if (j % EU - 1) % (M + 3) < M + 3 - 1 then 1 else 0
  h12 : τ.val (H 12) = (j % EU - 1) % (M + 3) - 1
  h13 : τ.val (H 13) = j / EU % N2
  h14 : τ.val (H 14) = j / EU / N2
  h15 : τ.val (H 15) = j / EU / N2 % nSt
  h16 : τ.val (H 16) = j / EU / N2 / nSt
  h17 : τ.val (H 17) = j / EU / N2 / nSt % nFlat
  h18 : τ.val (H 18) = j / EU / N2 / nSt / nFlat
  h19 : τ.val (H 19) = if (j % EU - 1) / (M + 3) < nc then 1 else 0
  hz : ∀ k : Fin 40, 20 ≤ k.val → τ.val (H k) = 0

/-- **The decode's second stage.** -/
theorem p2_spec (cr fe : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (σ : WState (LNS x) LNR)
    (a nc M m0 m1 m2 m3 j capS err L kh : ℕ)
    (hcapS : capS = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (herr : err = fe * Ledger.Lq P.n) (hL : L = Ledger.Lq P.n) (hkh : kh = P.s * (P.r / 2))
    (vN : σ.val dN = P.n) (vA : σ.val dA = a) (vNC : σ.val dNC = nc) (v0 : σ.val dM0 = m0) (v1 : σ.val dM1 = m1)
    (v2 : σ.val dM2 = m2) (v3 : σ.val dM3 = m3) (vM : σ.val dMS = M)
    (hSG : ∀ i, σ.val (SGb i) = 0) (hGb : ∀ i, σ.val (Gb i) = 0) (hHb : ∀ i, σ.val (Hb i) = 0) (hx : σ.val xT = 0)
    (hG : ∀ i, σ.val (G i) = 0) (hH : ∀ k, σ.val (H k) = 0)
    (hs2 : σ.st (sk x 2) = List.replicate j true) (hh2 : σ.sh (sk x 2) = 0)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : CapNeed C .sym P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap)
    (hN : NumsNeed cap P.n capS err M nc L kh a m0 m1 m2 m3)
    (hI : j + totV P.n capS err M nc L kh a m0 m1 m2 m3 + euV M nc a + 2 * M + 2 ^ (2 * kh) + stV m0 m1 m2 m3 +
      2 ^ FlatNums.fbv M (bV nc capS) (L + 5) + nc + 20 ≤ cap) :
    ∃ τ c, WExec cap (p2W x cr fe ζ Cδ C) σ τ c ∧
      (∀ i, τ.val (G i) = numsVec P.n capS err M nc L kh a m0 m1 m2 m3 i) ∧
      HVals x τ j (totV P.n capS err M nc L kh a m0 m1 m2 m3) (euV M nc a) M (2 ^ (2 * kh)) (stV m0 m1 m2 m3)
        (2 ^ FlatNums.fbv M (bV nc capS) (L + 5)) nc ∧
      (∀ r, Outside r → (∀ i, G i ≠ r) → (∀ k, H k ≠ r) → τ.val r = σ.val r) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧
      c ≤ starCapCost P.n cr fe (Ledger.rowBt h0 h1 P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) (Ledger.Lq P.n) cap + 1 +
        (500 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap)) := by
  have oN : Outside dN := by unfold Outside; decide
  have oA : Outside dA := by unfold Outside; decide
  have oNC : Outside dNC := by unfold Outside; decide
  have oM0 : Outside dM0 := by unfold Outside; decide
  have oM1 : Outside dM1 := by unfold Outside; decide
  have oM2 : Outside dM2 := by unfold Outside; decide
  have oM3 : Outside dM3 := by unfold Outside; decide
  have oMS : Outside dMS := by unfold Outside; decide
  obtain ⟨τ1, c1, e1, q1, -, -, -, -, q8, -, q10, -, q13, k1, st1, sh1, cl1, c1le⟩ :=
    starCap_spec cap x cr fe h0 h1 Cδ C P hrP σ vN hSG hGb hHb hx hcS hcP hcC
  have hz1 : ∀ i, τ1.val (G i) = 0 := fun i => by rw [k1 _ (out_G i)]; exact hG i
  have e2 := symNums_spec x cap τ1 P.n capS err M nc L kh a m0 m1 m2 m3 (by rw [q13, hcapS]) (by rw [k1 _ oN, vN])
    (by rw [q10, herr]) (by rw [k1 _ oMS, vM]) (by rw [k1 _ oNC, vNC]) (by rw [q1, hL]) (by rw [q8, hkh])
    (by rw [k1 _ oA, vA]) (by rw [k1 _ oM0, v0]) (by rw [k1 _ oM1, v1]) (by rw [k1 _ oM2, v2]) (by rw [k1 _ oM3, v3])
    hz1 hN
  set τ2 := numsOut x τ1 P.n capS err M nc L kh a m0 m1 m2 m3 with hτ2
  have g2 : ∀ i, τ2.val (G i) = numsVec P.n capS err M nc L kh a m0 m1 m2 m3 i :=
    fun i => numsOut_val x τ1 P.n capS err M nc L kh a m0 m1 m2 m3 hz1 i
  have k2 : ∀ r, (∀ i, G i ≠ r) → τ2.val r = τ1.val r :=
    fun r hr => numsOut_other x τ1 P.n capS err M nc L kh a m0 m1 m2 m3 r hr
  have st2 : τ2.st = τ1.st := numsOut_st x τ1 P.n capS err M nc L kh a m0 m1 m2 m3
  have sh2 : τ2.sh = τ1.sh := numsOut_sh x τ1 P.n capS err M nc L kh a m0 m1 m2 m3
  have cl2 : τ2.cell = τ1.cell := numsOut_cell x τ1 P.n capS err M nc L kh a m0 m1 m2 m3
  have hz2 : ∀ k, τ2.val (H k) = 0 := fun k => by rw [k2 _ (fun i => GH i k), k1 _ (out_H k)]; exact hH k
  have pN2 : 1 ≤ 2 ^ (2 * kh) := Nat.one_le_two_pow
  have pFl : 1 ≤ 2 ^ FlatNums.fbv M (bV nc capS) (L + 5) := Nat.one_le_two_pow
  have pSt : 1 ≤ stV m0 m1 m2 m3 := by
    have : 0 < stV m0 m1 m2 m3 := by unfold stV; positivity
    omega
  have pEU : 2 ≤ euV M nc a := by unfold euV; omega
  obtain ⟨τ3, e3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, az, k3, st3, sh3a, sh3, cl3⟩ :=
    idxA_spec x cap τ2 j (totV P.n capS err M nc L kh a m0 m1 m2 m3) (euV M nc a) M
      (by rw [st2, st1, hs2]) (by rw [sh2, sh1, hh2]) (by rw [g2]; rfl) (by rw [g2]; rfl) (by rw [g2]; rfl) hz2 pEU
      (by omega)
  simp only [Nat.zero_add] at a0 a2 a3 a4 a6 a7 a9
  have hv : (j % euV M nc a - 1) % (M + 3) < M + 3 := Nat.mod_lt _ (by omega)
  have hw : j % euV M nc a < euV M nc a := Nat.mod_lt _ (by omega)
  have hr : (j % euV M nc a - 1) / (M + 3) ≤ j % euV M nc a - 1 := Nat.div_le_self _ _
  have he : j / euV M nc a ≤ j := Nat.div_le_self _ _
  obtain ⟨τ4, e4, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, kLow, bz, k4, st4, sh4, cl4⟩ :=
    idxB_spec x cap τ3 (j / euV M nc a) ((j % euV M nc a - 1) % (M + 3)) ((j % euV M nc a - 1) / (M + 3)) M
      (2 ^ (2 * kh)) (stV m0 m1 m2 m3) (2 ^ FlatNums.fbv M (bV nc capS) (L + 5)) nc a4 a7 a8 a9
      (by rw [k3 _ (fun k => HG 53 k), g2]; rfl) (by rw [k3 _ (fun k => HG 52 k), g2]; rfl)
      (by rw [k3 _ (fun k => HG 41 k), g2]; rfl)
      (by rw [k3 _ (fun k => (ndNC_H k).symm), k2 _ (fun i => (ndNC i).symm), k1 _ oNC, vNC]) az pN2 pSt pFl
      (by omega)
  refine ⟨τ4, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), fun i => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, bz⟩, fun r hO hGr hHr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [k4 _ (fun k => HG i k), k3 _ (fun k => HG i k), g2]
  · rw [kLow 0 (by decide)]; exact a0
  · rw [kLow 1 (by decide)]; exact a1
  · rw [kLow 2 (by decide)]; exact a2
  · rw [kLow 3 (by decide)]; exact a3
  · rw [kLow 4 (by decide)]; exact a4
  · rw [kLow 5 (by decide)]; exact a5
  · rw [kLow 6 (by decide)]; exact a6
  · rw [kLow 7 (by decide)]; exact a7
  · rw [kLow 8 (by decide)]; exact a8
  · rw [kLow 9 (by decide)]; exact a9
  · rw [k4 r hHr, k3 r hHr, k2 r hGr, k1 r hO]
  · rw [st4, st3, st2, st1]
  · funext s
    rw [sh4]
    by_cases hs : s = sk x 2
    · subst hs; rw [sh3a, hh2]
    · rw [sh3 s hs, sh2, sh1]
  · rw [cl4, cl3, cl2, cl1]
  · omega

end P2

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec

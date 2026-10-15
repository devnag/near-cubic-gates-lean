import Proof.Wire_3_5.PrimAsmHashDec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.FinalPass.Filt

section HB
variable (cap : ℕ) (x : ℕ)

/-- The aux bank's registers: length, cap, error exponent, seed index, `r4 = 4·cell`, pool size, slice length. -/
def hbAW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (G 1) fsLen TM) (.seq (FinalPass.Hash4.wcopyR (G 0) fsCap TM)
  (.seq (FinalPass.Hash4.wcopyR (G 2) fsErr TM) (.seq (FinalPass.Hash4.wcopyR (H 13) fsSeed TM)
  (.seq (FinalPass.Hash4.wcopyR (H 14) fsR4 TM) (.seq (dbl fsR4 TM) (.seq (dbl fsR4 TM)
  (.seq (FinalPass.Hash4.wcopyR (G 7) fsG TM) (FinalPass.Hash4.wcopyR (G 1) fsL TM))))))))

/-- The exit state of `hbAW`. -/
def hbAOut (σ : WState (LNS x) LNR) (len capA err g row pool : ℕ) : WState (LNS x) LNR :=
  (((((((((σ.setv fsLen len).setv fsCap capA).setv fsErr err).setv fsSeed g).setv fsR4 row).setv fsR4 (2 * row)).setv
    fsR4 (2 * (2 * row))).setv fsG pool).setv fsL len)

theorem hbA_run (σ : WState (LNS x) LNR) (len capA err g row pool : ℕ) (g0 : σ.val (G 0) = capA)
    (g1 : σ.val (G 1) = len) (g2 : σ.val (G 2) = err) (h13 : σ.val (H 13) = g) (h14 : σ.val (H 14) = row)
    (g7 : σ.val (G 7) = pool) (zTM : σ.val TM = 0)
    (zfs : ∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → σ.val q = 0) (hB : ∀ q, σ.val q ≤ cap)
    (c4 : 4 * row ≤ cap) :
    WExec cap (hbAW x) σ (hbAOut x σ len capA err g row pool) (20 * UnaryPow.sq cap) := by
  have z0 := zfs fsLen (by decide) (by decide); have z1 := zfs fsCap (by decide) (by decide)
  have z2 := zfs fsErr (by decide) (by decide); have z3 := zfs fsSeed (by decide) (by decide)
  have z4 := zfs fsR4 (by decide) (by decide); have z5 := zfs fsG (by decide) (by decide)
  have z7 := zfs fsL (by decide) (by decide)
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have b0 := hB (G 0); have b1 := hB (G 1); have b2 := hB (G 2); have b13 := hB (H 13); have b7 := hB (G 7)
  rw [g0] at b0; rw [g1] at b1; rw [g2] at b2; rw [h13] at b13; rw [g7] at b7
  unfold hbAW hbAOut
  exact (seqD cap 20 1 (copy1 cap (G 1) fsLen TM (by decide) (by decide) (by decide) len _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) b1) (by omega) (by omega)
    (seqD cap _ 1 (copy1 cap (G 0) fsCap TM (by decide) (by decide) (by decide) capA _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) b0) (by omega) (by omega)
    (seqD cap _ 1 (copy1 cap (G 2) fsErr TM (by decide) (by decide) (by decide) err _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) b2) (by omega) (by omega)
    (seqD cap _ 1 (copy1 cap (H 13) fsSeed TM (by decide) (by decide) (by decide) g _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) b13) (by omega) (by omega)
    (seqD cap _ 1 (copy1 cap (H 14) fsR4 TM (by decide) (by decide) (by decide) row _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by omega)) (by omega) (by omega)
    (seqD cap _ 1 (dbl1 cap fsR4 TM (by decide) row _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by omega)) (by omega) (by omega)
    (seqD cap _ 1 (dbl1 cap fsR4 TM (by decide) (2 * row) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by omega)) (by omega) (by omega)
    (seqD cap _ 1 (copy1 cap (G 7) fsG TM (by decide) (by decide) (by decide) pool _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) b7) (by omega) (by omega)
    (endD cap _ 1 (copy1 cap (G 1) fsL TM (by decide) (by decide) (by decide) len _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, rv_TM, G_val, H_val, g0, g1, g2, h13, h14, g7, zTM, z0, z1, z2, z3, z4, z5, z7]) b1) rfl (by omega) (by omega))))))))))

theorem hbAOut_st (σ : WState (LNS x) LNR) (len capA err g row pool : ℕ) :
    (hbAOut x σ len capA err g row pool).st = σ.st := by unfold hbAOut; simp
theorem hbAOut_sh (σ : WState (LNS x) LNR) (len capA err g row pool : ℕ) :
    (hbAOut x σ len capA err g row pool).sh = σ.sh := by unfold hbAOut; simp
theorem hbAOut_cell (σ : WState (LNS x) LNR) (len capA err g row pool : ℕ) :
    (hbAOut x σ len capA err g row pool).cell = σ.cell := by unfold hbAOut; simp

theorem hbAOut_val (σ : WState (LNS x) LNR) (len capA err g row pool : ℕ) :
    (hbAOut x σ len capA err g row pool).val fsLen = len ∧ (hbAOut x σ len capA err g row pool).val fsCap = capA ∧
    (hbAOut x σ len capA err g row pool).val fsErr = err ∧ (hbAOut x σ len capA err g row pool).val fsSeed = g ∧
    (hbAOut x σ len capA err g row pool).val fsR4 = 2 * (2 * row) ∧
    (hbAOut x σ len capA err g row pool).val fsG = pool ∧ (hbAOut x σ len capA err g row pool).val fsL = len := by
  unfold hbAOut
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr,
    rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL]

theorem hbAOut_other (σ : WState (LNS x) LNR) (len capA err g row pool : ℕ) (q : Fin LNR)
    (h : q.val < 400 ∨ 408 ≤ q.val ∨ q.val = 406) :
    (hbAOut x σ len capA err g row pool).val q = σ.val q := by
  have n0 : q.val ≠ 400 := by omega
  have n1 : q.val ≠ 401 := by omega
  have n2 : q.val ≠ 402 := by omega
  have n3 : q.val ≠ 403 := by omega
  have n4 : q.val ≠ 404 := by omega
  have n5 : q.val ≠ 405 := by omega
  have n7 : q.val ≠ 407 := by omega
  unfold hbAOut
  simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsL, n0, n1,
    n2, n3, n4, n5, n7]

end HB

section HBDock
variable (cap : ℕ) (W : WalkBankProducer)

/-- **The HASH bank**: the aux parameters, the clearing of `G`, `H`, the FILTER setup. -/
def hbW (F : FiltSetupSpec5 W) : WM (LNS W.x) LNR := .seq (hbAW W.x) (.seq (clrsW ghList) F.prog)

/-- The bank's cost before the FILTER setup. -/
def hbCost (c : ℕ) : ℕ := 20 * UnaryPow.sq c + 1 + (104 * (3 * c + 2) + 1)

/-- **The HASH bank, run**: from the decoded state (the unit's streams as at the entry, the registers below `250` and
`400 … 407` zero, the aux parameters in `G 0 … G 2`, the seed's index in `H 13`, the cell in `H 14`, the pool size in
`G 7`), `DecOK`'s FILTER disjunct with the aux row's body at the seed `e`, slice offset `0`, length `P.len`. -/
theorem hb_spec (F : FiltSetupSpec5 W) (σ : WState (LNS W.x) LNR) (w out u : List Bool) (j : ℕ) (P : GapParams)
    (e : GapSeed P) (row pool : ℕ)
    (hst : σ.st = (CellLoopD.blankCellD W.x w out j u).st)
    (hsh : ∀ s, s ≠ sk W.x 113 → σ.sh s = (CellLoopD.blankCellD W.x w out j u).sh s) (hcl : σ.cell = false)
    (hzl : ∀ q : Fin LNR, q.val < 250 → σ.val q = 0) (zfs : ∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → σ.val q = 0)
    (zTM : σ.val TM = 0) (hB : ∀ q, σ.val q ≤ cap)
    (g0 : σ.val (G 0) = P.cap) (g1 : σ.val (G 1) = P.len) (g2 : σ.val (G 2) = P.errExp)
    (h13 : σ.val (H 13) = (Enum.gapSeedEquiv P e : ℕ)) (h14 : σ.val (H 14) = row) (g7 : σ.val (G 7) = pool)
    (c4 : 4 * row ≤ cap) (hU : 1 ≤ P.cap)
    (hneed : F.need P.len P.cap P.errExp P.len (2 * (2 * row)) pool 0 (Fintype.card (GapSeed P)) ≤ cap) :
    ∃ τ m, WExec cap (hbW W F) σ τ m ∧ m ≤ hbCost cap + F.bound cap ∧
      DecOK cap W τ out ((filtRefC (filterTable P e P.len) (SupplierWalk.majorityThreshold P.walkLen)
        P.len true (sliceLabs (2 * (2 * row)) pool 0 P.len)).flatMap (fun t => true :: ListMachine.Rec.termWord t))
        (filtPipeBound P e P.len (2 * (2 * row)) pool 0 (rulerW P) (rulerW P)) ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 := by
  have eA := hbA_run cap W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row pool g0 g1 g2 h13 h14 g7 zTM zfs hB c4
  set σA := hbAOut W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row pool with hσA
  obtain ⟨a0, a1, a2, a3, a4, a5, a7⟩ := hbAOut_val W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row pool
  have kA : ∀ q : Fin LNR, q.val < 400 → σA.val q = σ.val q :=
    fun q h => hbAOut_other W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row pool q (Or.inl h)
  have kOff : σA.val fsOff = 0 := by
    rw [hσA, hbAOut_other W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row pool fsOff (Or.inr (Or.inr rfl))]
    exact zfs _ (by decide) (by decide)
  have hBA : ∀ q, σA.val q ≤ cap := wexec_le cap eA hB
  have eC := clrs_spec cap ghList σA hBA
  set σC := zeroOut σA ghList with hσC
  have vC : ∀ q : Fin LNR, q.val < 408 → σC.val q = σA.val q := fun q h => by
    rw [hσC, zeroOut_val, if_neg (not_mem_gh q h)]
  have stC : σC.st = (CellLoopD.blankCellD W.x w out j u).st := by
    rw [hσC, zeroOut_st, hσA, hbAOut_st, hst]
  have shC : ∀ s, s ≠ sk W.x 113 → σC.sh s = (CellLoopD.blankCellD W.x w out j u).sh s := fun s hs => by
    rw [hσC, zeroOut_sh, hσA, hbAOut_sh, hsh s hs]
  have n0B : sk W.x 0 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n1B : sk W.x 1 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n2B : sk W.x 2 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n01 : sk W.x 0 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have n21 : sk W.x 2 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have n20 : sk W.x 2 ≠ sk W.x 0 := fun e => absurd (sk_inj W.x e) (by decide)
  have hFs : FsIn2 W.x σC w out j u P.len P.cap P.errExp (Enum.gapSeedEquiv P e) (2 * (2 * row)) pool 0 P.len :=
    { s0 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n0B]
      s1 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm]
      h1 := by rw [shC _ n1B]; simp [CellLoopD.blankCellD, blankCell]
      s2 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21]
      h2 := by rw [shC _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]
      s113 := by rw [stC]; simp [CellLoopD.blankCellD]
      blank := fun k k0 k1 k2 k3 => by
        have m0 : sk W.x k ≠ sk W.x 0 := fun e => k0 (by rw [sk_inj W.x e]; rfl)
        have m1 : sk W.x k ≠ sk W.x 1 := fun e => k1 (by rw [sk_inj W.x e]; rfl)
        have m2 : sk W.x k ≠ sk W.x 2 := fun e => k2 (by rw [sk_inj W.x e]; rfl)
        have m3 : sk W.x k ≠ sk W.x 113 := fun e => k3 (by rw [sk_inj W.x e]; rfl)
        refine ⟨?_, ?_⟩
        · rw [stC]; simp [CellLoopD.blankCellD, blankCell, m0, m1, m2, m3]
        · rw [shC _ m3]; simp [CellLoopD.blankCellD, blankCell, m1]
      blankT := fun k => by
        have m0 : sT W.x k ≠ sk W.x 0 := (sk_ne_sT W.x 0 k).symm
        have m1 : sT W.x k ≠ sk W.x 1 := (sk_ne_sT W.x 1 k).symm
        have m2 : sT W.x k ≠ sk W.x 2 := (sk_ne_sT W.x 2 k).symm
        have m3 : sT W.x k ≠ sk W.x 113 := (sk_ne_sT W.x 113 k).symm
        refine ⟨?_, ?_⟩
        · rw [stC]; simp [CellLoopD.blankCellD, blankCell, m0, m1, m2, m3]
        · rw [shC _ m3]; simp [CellLoopD.blankCellD, blankCell, m1]
      cell := by rw [hσC, zeroOut_cell, hσA, hbAOut_cell, hcl]
      vLen := by rw [vC _ (by decide)]; exact a0
      vCap := by rw [vC _ (by decide)]; exact a1
      vErr := by rw [vC _ (by decide)]; exact a2
      vSeed := by rw [vC _ (by decide)]; exact a3
      vR4 := by rw [vC _ (by decide)]; exact a4
      vG := by rw [vC _ (by decide)]; exact a5
      vOff := by rw [vC _ (by decide)]; exact kOff
      vL := by rw [vC _ (by decide)]; exact a7
      zLow := fun q hq => by
        rw [vC _ (by omega), kA _ (by omega)]; exact hzl q hq
      zHigh := fun q hq => by rw [hσC, zeroOut_val, if_pos (mem_gh q hq)]
      h0 := by rw [shC _ n0B]; simp [CellLoopD.blankCellD, blankCell, n01] }
  obtain ⟨τ, m, eF, hm, hdec, k0, k2, k2h⟩ := SymDecFilt.filt_dock W F cap P e P.len (2 * (2 * row)) pool 0
    w out u j σC hU (sliceLabs_length _ _ _ _) hneed hFs
  refine ⟨τ, _, WExec.seq eA (WExec.seq eC eF), ?_, hdec, k0, k2, k2h⟩
  unfold hbCost; rw [gh_length]; omega

end HBDock

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec

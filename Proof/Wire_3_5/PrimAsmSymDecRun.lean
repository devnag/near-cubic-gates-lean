import Proof.Wire_3_5.PrimAsmSymDecFB

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
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.FinalPass.Filt

theorem nv {r q : Fin LNR} (h : r.val ≠ q.val) : r ≠ q := fun e => h (congrArg Fin.val e)
theorem rv_dN : dN.val = 320 := rfl
theorem rv_dA : dA.val = 321 := rfl
theorem rv_dNC : dNC.val = 322 := rfl
theorem rv_dM0 : dM0.val = 330 := rfl
theorem rv_dM1 : dM1.val = 331 := rfl
theorem rv_dM2 : dM2.val = 332 := rfl
theorem rv_dM3 : dM3.val = 333 := rfl
theorem rv_LEN : LEN.val = 369 := rfl

/-- **The decoded unit state**: the entry's streams and cell, the unit's indices (`HVals`), the call's numbers
(`numsVec`), the call's counts, the pipeline registers (below `250`, `400 … 407`, `TM`) zero, every register within
the capacity. -/
structure Decoded (x cap : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (n a nc M m0 m1 m2 m3 xa xb capS err L kh : ℕ) : Prop where
  st : σ.st = (CellLoopD.blankCellD x w out j u).st
  sh : ∀ s, s ≠ sk x 113 → σ.sh s = (CellLoopD.blankCellD x w out j u).sh s
  cell : σ.cell = false
  hv : HVals x σ j (totV n capS err M nc L kh a m0 m1 m2 m3) (euV M nc a) M (2 ^ (2 * kh)) (stV m0 m1 m2 m3)
    (2 ^ FlatNums.fbv M (bV nc capS) (L + 5)) nc
  gv : ∀ i, σ.val (G i) = numsVec n capS err M nc L kh a m0 m1 m2 m3 i
  vN : σ.val dN = n
  vA : σ.val dA = a
  vNC : σ.val dNC = nc
  v0 : σ.val dM0 = m0
  v1 : σ.val dM1 = m1
  v2 : σ.val dM2 = m2
  v3 : σ.val dM3 = m3
  vM : σ.val dMS = M
  vXA : σ.val XA = xa
  vXB : σ.val XB = xb
  zl : ∀ q : Fin LNR, q.val < 250 → σ.val q = 0
  zfs : ∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → σ.val q = 0
  zTM : σ.val TM = 0
  bd : ∀ q, σ.val q ≤ cap

section Run
variable (cap : ℕ) (x : ℕ)

/-- **The decode's two stages, run** from the unit's entry to a `Decoded` state. -/
theorem decode_run (cr fe : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w out : List Bool) (j : ℕ) (codes ccs : List ℕ)
    (tl : List Bool) (cx cy : List ℕ) (Kb Cmax capS err L kh : ℕ)
    (hw : w = Data.reqW P.n false codes ccs tl) (hccs : ccs.length = cx.length) (hcx : cx.length ≤ 2)
    (hcy : cy.length ≤ 4) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hC : ∀ c ∈ cx ++ cy, c ≤ Cmax)
    (hN1 : P1Need cap w P.n codes ccs cx cy Kb Cmax)
    (hcapS : capS = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (herr : err = fe * Ledger.Lq P.n) (hL : L = Ledger.Lq P.n) (hkh : kh = P.s * (P.r / 2))
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : CapNeed C .sym P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap)
    (hN2 : NumsNeed cap P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
      (cy.getD 3 0))
    (hI : j + totV P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
      (cy.getD 3 0) + euV cy.sum cx.length codes.length + 2 * cy.sum + 2 ^ (2 * kh) +
      stV (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0) + 2 ^ FlatNums.fbv cy.sum (bV cx.length capS) (L + 5) +
      cx.length + 20 ≤ cap) :
    ∃ σ c, WExec cap (.seq (p1W x) (p2W x cr fe ζ Cδ C)) (CellLoopD.blankCellD x w out j (Data.unaryList (cx ++ cy)))
        σ c ∧
      Decoded x cap σ w out j (Data.unaryList (cx ++ cy)) P.n codes.length cx.length cy.sum (cy.getD 0 0) (cy.getD 1 0)
        (cy.getD 2 0) (cy.getD 3 0) (cx.getD 0 0) (cx.getD 1 0) capS err L kh ∧
      c ≤ 4 * UnaryPow.sq cap + 1 + (reqParseCost P.n codes.length ccs.length Kb + 1 + (5 * UnaryPow.sq cap + 1 +
        (30 * UnaryPow.sq cap + 1 + countsCost cx.length Cmax cy.sum))) + 1 +
        (starCapCost P.n cr fe (Ledger.rowBt h0 h1 P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) (Ledger.Lq P.n) cap + 1 +
        (500 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap))) := by
  obtain ⟨τ1, c1, e1, v1N, v1A, v1NC, v1M0, v1M1, v1M2, v1M3, v1MS, v1XA, v1XB, z1, v1L, s1, sh1, cl1, c1le⟩ :=
    p1_spec cap x w out j P.n codes ccs tl cx cy Kb Cmax hw hccs hcx hcy hKb hC hN1
  have zP1 : ∀ r : Fin LNR, (r.val < 320 ∨ (323 ≤ r.val ∧ r.val < 330) ∨ (335 ≤ r.val ∧ r.val < 369) ∨
      372 ≤ r.val) → τ1.val r = 0 := fun r h =>
    z1 r (nv (by rw [rv_dN]; omega)) (nv (by rw [rv_dA]; omega)) (nv (by rw [rv_dNC]; omega))
      (nv (by rw [rv_dM0]; omega)) (nv (by rw [rv_dM1]; omega)) (nv (by rw [rv_dM2]; omega))
      (nv (by rw [rv_dM3]; omega)) (nv (by rw [rv_dMS]; omega)) (nv (by rw [rv_LEN]; omega))
      (nv (by rw [rv_XA]; omega)) (nv (by rw [rv_XB]; omega))
  have n2B : sk x 2 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n20 : sk x 2 ≠ sk x 0 := fun e => absurd (sk_inj x e) (by decide)
  have n21 : sk x 2 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  obtain ⟨τ2, c2, e2, gv, hv, k2, st2, sh2, cl2, c2le⟩ :=
    p2_spec cap x cr fe h0 h1 Cδ C P hrP τ1 codes.length cx.length cy.sum (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
      (cy.getD 3 0) j capS err L kh hcapS herr hL hkh v1N v1A v1NC v1M0 v1M1 v1M2 v1M3 v1MS
      (fun i => zP1 _ (by rw [SGb_val]; have := i.isLt; omega)) (fun i => zP1 _ (by rw [Gb_val]; have := i.isLt; omega))
      (fun i => zP1 _ (by rw [Hb_val]; have := i.isLt; omega)) (zP1 _ (by decide))
      (fun i => zP1 _ (by rw [G_val]; omega)) (fun k => zP1 _ (by rw [H_val]; omega))
      (by rw [s1]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21])
      (by rw [sh1 _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]) hcS hcP hcC hN2 hI
  have k2' : ∀ r : Fin LNR, (r.val < 250 ∨ (320 ≤ r.val ∧ r.val < 337) ∨ (369 ≤ r.val ∧ r.val < 408)) →
      τ2.val r = τ1.val r := fun r h =>
    k2 r (by unfold Outside; omega) (fun i e => by have := congrArg Fin.val e; rw [G_val] at this; omega)
      (fun k e => by have := congrArg Fin.val e; rw [H_val] at this; omega)
  have e12 := WExec.seq e1 e2
  refine ⟨τ2, _, e12, ⟨by rw [st2, s1], fun s hs => by rw [sh2, sh1 s hs], by rw [cl2, cl1], hv, gv,
    by rw [k2' _ (by rw [rv_dN]; omega)]; exact v1N, by rw [k2' _ (by rw [rv_dA]; omega)]; exact v1A,
    by rw [k2' _ (by rw [rv_dNC]; omega)]; exact v1NC, by rw [k2' _ (by rw [rv_dM0]; omega)]; exact v1M0,
    by rw [k2' _ (by rw [rv_dM1]; omega)]; exact v1M1, by rw [k2' _ (by rw [rv_dM2]; omega)]; exact v1M2,
    by rw [k2' _ (by rw [rv_dM3]; omega)]; exact v1M3, by rw [k2' _ (by rw [rv_dMS]; omega)]; exact v1MS,
    by rw [k2' _ (by rw [rv_XA]; omega)]; exact v1XA, by rw [k2' _ (by rw [rv_XB]; omega)]; exact v1XB,
    fun q hq => by rw [k2' q (Or.inl hq)]; exact zP1 q (Or.inl (by omega)),
    fun q hq1 hq2 => by rw [k2' q (by omega)]; exact zP1 q (by omega),
    by rw [k2' _ (by rw [rv_TM]; omega)]; exact zP1 _ (by rw [rv_TM]; omega),
    wexec_le cap e12 (fun q => by simp [CellLoopD.blankCellD, blankCell])⟩, by omega⟩

end Run

section Dec
variable (cap : ℕ) (W : WalkBankProducer)

/-- **The SYM unit's decode.** -/
def decW (F : FiltSetupSpec5 W) (pb : WM (LNS W.x) LNR) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) :
    WM (LNS W.x) LNR :=
  .seq (.seq (p1W W.x) (p2W W.x cr fe ζ Cδ C)) (brW W (fbW W F) pb)

theorem dec_run (F : FiltSetupSpec5 W) (pb : WM (LNS W.x) LNR) (cr fe : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)
    (Cδ : ℕ) (C : Ledger.CapParams) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w out : List Bool)
    (j : ℕ) (codes ccs : List ℕ) (tl : List Bool) (cx cy : List ℕ) (Kb Cmax capS err L kh Bb BP : ℕ)
    (hw : w = Data.reqW P.n false codes ccs tl) (hccs : ccs.length = cx.length) (hcx : cx.length ≤ 2)
    (hcy : cy.length ≤ 4) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hC : ∀ c ∈ cx ++ cy, c ≤ Cmax)
    (hN1 : P1Need cap w P.n codes ccs cx cy Kb Cmax)
    (hcapS : capS = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (herr : err = fe * Ledger.Lq P.n) (hL : L = Ledger.Lq P.n) (hkh : kh = P.s * (P.r / 2))
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : CapNeed C .sym P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap)
    (hN2 : NumsNeed cap P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
      (cy.getD 3 0))
    (hI : j + totV P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
      (cy.getD 3 0) + euV cy.sum cx.length codes.length + 2 * cy.sum + 2 ^ (2 * kh) +
      stV (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0) + 2 ^ FlatNums.fbv cy.sum (bV cx.length capS) (L + 5) +
      cx.length + 20 ≤ cap)
    (FP : GapParams) (hF0 : FP.cap = capS) (hF1 : FP.len = 2 * (P.n + 1) ^ 26) (hF2 : FP.errExp = err)
    (hU : 1 ≤ FP.cap) (hcF : 4 * 2 ^ (2 * kh) + 2 * (cx.getD 0 0 + cx.getD 1 0) + cy.sum ≤ cap)
    (hFc : fbCost cap + F.bound cap ≤ Bb) (rq : ℕ → ℕ → ℕ → List Bool)
    (hfs : ∀ e r s, r < cx.length → s ≠ 0 → rq e r s = [])
    (hFrq : IsFiltU (totV P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
        (cy.getD 3 0)) (cx.length + 2 * codes.length) cy.sum cx.length j →
      ∃ eg : GapSeed FP, (Enum.gapSeedEquiv FP eg : ℕ) = j / ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) /
          2 ^ (2 * kh) / stV (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0) /
          2 ^ FlatNums.fbv cy.sum (bV cx.length capS) (L + 5) ∧
        rq (j / ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2))
            ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) 0 =
          (filtRefC (filterTable FP eg (fbL ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) /
            (cy.sum + 3)) (cx.getD 0 0) (cx.getD 1 0))) (SupplierWalk.majorityThreshold FP.walkLen)
            (fbL ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) (cx.getD 0 0)
              (cx.getD 1 0)) true
            (sliceLabs (2 * (2 * (j / ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) % 2 ^ (2 * kh))))
              (2 * (cx.getD 0 0 + cx.getD 1 0) + cy.sum)
              (fbOff ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) (cx.getD 0 0))
              (fbL ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) (cx.getD 0 0)
                (cx.getD 1 0)))).flatMap (fun t => true :: ListMachine.Rec.termWord t) ∧
        F.need FP.len FP.cap FP.errExp
            (fbL ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) (cx.getD 0 0)
              (cx.getD 1 0))
            (2 * (2 * (j / ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) % 2 ^ (2 * kh))))
            (2 * (cx.getD 0 0 + cx.getD 1 0) + cy.sum)
            (fbOff ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) (cx.getD 0 0))
            (Fintype.card (GapSeed FP)) ≤ cap ∧
        filtPipeBound FP eg
            (fbL ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) (cx.getD 0 0)
              (cx.getD 1 0))
            (2 * (2 * (j / ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) % 2 ^ (2 * kh))))
            (2 * (cx.getD 0 0 + cx.getD 1 0) + cy.sum)
            (fbOff ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) (cx.getD 0 0))
            (rulerW FP) (rulerW FP) ≤ BP)
    (hP : ∀ σ : WState (LNS W.x) LNR, Decoded W.x cap σ w out j (Data.unaryList (cx ++ cy)) P.n codes.length cx.length
        cy.sum (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0) (cx.getD 0 0) (cx.getD 1 0) capS err L kh →
      IsPopU (totV P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
        (cy.getD 3 0)) (cx.length + 2 * codes.length) cy.sum cx.length j →
      ∃ τ c, WExec cap pb σ τ c ∧
        DecOK cap W τ out (rq (j / ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2))
          ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3))
          ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) % (cy.sum + 3) - 1)) BP ∧
        τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧ c ≤ Bb) :
    ∃ σD m, WExec cap (decW W F pb cr fe ζ Cδ C) (CellLoopD.blankCellD W.x w out j (Data.unaryList (cx ++ cy))) σD m ∧
      DecOK cap W σD out (unitE (totV P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0)
        (cy.getD 2 0) (cy.getD 3 0)) (cx.length + 2 * codes.length) cy.sum rq j) BP ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      m ≤ 4 * UnaryPow.sq cap + 1 + (reqParseCost P.n codes.length ccs.length Kb + 1 + (5 * UnaryPow.sq cap + 1 +
        (30 * UnaryPow.sq cap + 1 + countsCost cx.length Cmax cy.sum))) + 1 +
        (starCapCost P.n cr fe (Ledger.rowBt h0 h1 P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) (Ledger.Lq P.n) cap + 1 +
        (500 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap))) + 1 + (Bb + 12) := by
  obtain ⟨σ, c, e, hD, cle⟩ := decode_run cap W.x cr fe h0 h1 Cδ C P hrP w out j codes ccs tl cx cy Kb Cmax capS err L
    kh hw hccs hcx hcy hKb hC hN1 hcapS herr hL hkh hcS hcP hcC hN2 hI
  have hEU : euV cy.sum cx.length codes.length = (cx.length + 2 * codes.length) * (cy.sum + 3) + 2 := by
    unfold euV; ring
  have hv := hD.hv
  rw [hEU] at hv
  have n0B : sk W.x 0 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n1B : sk W.x 1 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n2B : sk W.x 2 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n01 : sk W.x 0 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have n21 : sk W.x 2 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have n20 : sk W.x 2 ≠ sk W.x 0 := fun e => absurd (sk_inj W.x e) (by decide)
  have nfB : ∀ k : Fin 161, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 113 → σ.st (sk W.x k) = [] ∧ σ.sh (sk W.x k) = 0 := by
    intro k k0 k1 k2 k3
    have m0 : sk W.x k ≠ sk W.x 0 := fun e => k0 (sk_inj W.x e)
    have m1 : sk W.x k ≠ sk W.x 1 := fun e => k1 (sk_inj W.x e)
    have m2 : sk W.x k ≠ sk W.x 2 := fun e => k2 (sk_inj W.x e)
    have m3 : sk W.x k ≠ sk W.x 113 := fun e => k3 (sk_inj W.x e)
    refine ⟨?_, ?_⟩
    · rw [hD.st]; simp [CellLoopD.blankCellD, blankCell, m0, m1, m2, m3]
    · rw [hD.sh _ m3]; simp [CellLoopD.blankCellD, blankCell, m1]
  have f150 := nfB 150 (by decide) (by decide) (by decide) (by decide)
  have f151 := nfB 151 (by decide) (by decide) (by decide) (by decide)
  have hpow : 0 < 2 ^ (2 * kh) := by positivity
  obtain ⟨τ, c', eB, d, k0, k2, k2h, cB⟩ := br_spec cap W (fbW W F) pb σ out w j
    (totV P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0))
    (cx.length + 2 * codes.length) cy.sum (2 ^ (2 * kh)) (stV (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0))
    (2 ^ FlatNums.fbv cy.sum (bV cx.length capS) (L + 5)) cx.length Bb BP rq hv
    (by rw [hD.st]; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm])
    (by rw [hD.sh _ n1B]; simp [CellLoopD.blankCellD, blankCell]) f150.1 f150.2 f151.1 f151.2
    (by rw [hD.st]; simp [CellLoopD.blankCellD, blankCell, n0B])
    (by rw [hD.st]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21])
    (by rw [hD.sh _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]) hfs
    (fun hf => by
      obtain ⟨eg, hg, hbody, hneed, hpipe⟩ := hFrq hf
      have hr : (j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3) ≤ 1 := by
        have := hf.2.2.2.2.2.1; omega
      have hrow : j / ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) % 2 ^ (2 * kh) < 2 ^ (2 * kh) :=
        Nat.mod_lt _ hpow
      obtain ⟨τ, m, eF, hm, hdec, k0, k2, k2h⟩ := fb_spec cap W F σ w out (Data.unaryList (cx ++ cy)) j FP eg
        (j / ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) % 2 ^ (2 * kh)) (cx.getD 0 0) (cx.getD 1 0) cy.sum
        ((j % ((cx.length + 2 * codes.length) * (cy.sum + 3) + 2) - 1) / (cy.sum + 3)) hr hD.st hD.sh hD.cell hD.zl
        hD.zfs hD.zTM hD.bd (by rw [hD.gv 0, hF0]; rfl) (by rw [hD.gv 1, hF1]; rfl) (by rw [hD.gv 2, hF2]; rfl)
        (by rw [hv.h18, hg]) hv.h13 hv.h9 hD.vXA hD.vXB hD.vM (by omega) (by omega) (by omega) (by omega) hU hneed
      exact ⟨τ, m, eF, by rw [hbody]; exact decOK_mono cap W hdec hpipe, k0, k2, k2h, by omega⟩)
    (fun hp => hP σ hD hp)
  exact ⟨τ, _, WExec.seq e eB, d, k0, k2, k2h, by omega⟩

end Dec

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec

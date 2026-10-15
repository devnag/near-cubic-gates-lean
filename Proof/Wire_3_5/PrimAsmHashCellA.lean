import Proof.Wire_3_5.PrimAsmHashNum
import Proof.Wire_3_5.PrimAsmEmit
import Proof.Wire_3_5.PrimAsmDataSetup
import Proof.Wire_3_5.PrimAsmUnaryArith
import Proof.Wire_3_5.PrimAsmNumsX

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

section Gen
variable {ns nr : ℕ} (cap : ℕ)

/-- A register's value `A` as a fresh unary stream `O` (head back at `0`, `A` kept, `OP`, `K`, `T` back at `0`). -/
def wrU (O : Fin (ns + 1)) (OP A K T : Fin nr) : WM ns nr :=
  .seq (Emit.repRegW O OP A K T [true]) (Data.rewindW O OP)

theorem wrU_spec (O : Fin (ns + 1)) (OP A K T : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T)
    (hKO : K ≠ OP) (hAO : A ≠ OP) (σ : WState ns nr) (hO : σ.st O = []) (hOh : σ.sh O = 0) (hP : σ.val OP = 0)
    (hK : σ.val K = 0) (hT : σ.val T = 0) (hc : σ.val A ≤ cap) :
    WExec cap (wrU O OP A K T) σ (σ.sets O (List.replicate (σ.val A) true)) (40 * σ.val A + 10) := by
  have h1 := Emit.repRegW_spec cap O OP A K T hAK hAT hKT hKO [true] σ hK hT (by rw [hO, hOh]; rfl) hc
    (by rw [hP]; simpa using hc)
  rw [NumsX.reps_single] at h1
  have h2 := Data.rewindW_spec cap O OP (σ.val A) (appendO σ O OP (List.replicate (σ.val A) true))
    (by simp [hOh]) (by simp [hP]) hc
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
  apply WState.eq
  · funext s
    by_cases hs : s = O
    · rw [hs]; simp [hOh]
    · simp [Function.update_apply, hs]
  · funext s
    by_cases hs : s = O
    · rw [hs]; simp [hO]
    · simp [Function.update_apply, hs]
  · funext r
    by_cases hr : r = OP
    · rw [hr]; simp [hP]
    · simp [Function.update_apply, hr]
  · simp

end Gen

/-! ## The scratch registers (below `250`, off the populations loop's `0 … 54`) -/

def rO : Fin LNR := ⟨60, by decide⟩
def rK : Fin LNR := ⟨61, by decide⟩
def rT : Fin LNR := ⟨62, by decide⟩
def rS : Fin LNR := ⟨70, by decide⟩
def rP : Fin LNR := ⟨71, by decide⟩
def rQ : Fin LNR := ⟨72, by decide⟩
def rW : Fin LNR := ⟨73, by decide⟩

theorem nPS : rP ≠ rS := by decide
theorem nSP : rS ≠ rP := by decide
theorem nOS : rO ≠ rS := by decide
theorem nOP : rO ≠ rP := by decide
theorem nKS : rK ≠ rS := by decide
theorem nKP : rK ≠ rP := by decide
theorem nTS : rT ≠ rS := by decide
theorem nTP : rT ≠ rP := by decide

/-- `pow2W`'s registers `(s, p, t, w)`. -/
def pR : Fin 4 ↪ Fin LNR := ⟨![rS, rP, rQ, rW], by decide⟩

section Cell
variable (cap : ℕ) (x : ℕ)

/-- `N = 2^{k_h}` from `SGb 8 = k_h`, written as `1^N` on stream `156`. -/
def nW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (SGb 8) rS rQ) (.seq (UnaryArith.pow2W pR)
    (.seq (wrU (sk x 156) rO rP rK rT) (.seq (WM.clear rS) (WM.clear rP))))

theorem nW_spec (σ : WState (LNS x) LNR) (kh : ℕ) (h8 : σ.val (SGb 8) = kh)
    (hz : ∀ r : Fin LNR, r.val < 250 → σ.val r = 0) (hO : σ.st (sk x 156) = []) (hOh : σ.sh (sk x 156) = 0)
    (hkh : 2 ^ (kh + 1) ≤ cap) :
    WExec cap (nW x) σ (σ.sets (sk x 156) (List.replicate (2 ^ kh) true)) (30 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hk1 : kh < 2 ^ kh := Nat.lt_two_pow_self
  have hk2 : 2 ^ (kh + 1) = 2 * 2 ^ kh := by rw [pow_succ]; ring
  have zS : σ.val rS = 0 := hz rS (by decide)
  have zP : σ.val rP = 0 := hz rP (by decide)
  have zQ : σ.val rQ = 0 := hz rQ (by decide)
  have zW : σ.val rW = 0 := hz rW (by decide)
  have zO : σ.val rO = 0 := hz rO (by decide)
  have zK : σ.val rK = 0 := hz rK (by decide)
  have zT : σ.val rT = 0 := hz rT (by decide)
  have nQS : rQ ≠ rS := by decide
  have nWS : rW ≠ rS := by decide
  have e1 := FinalPass.Hash4.wcopyR_spec cap (SGb 8) rS rQ (by decide) (by decide) (by decide) σ zS zQ (by omega)
  rw [h8] at e1
  have e2 := UnaryArith.pow2W_spec cap pR (σ.setv rS kh)
    (by simp [pR, Function.update_apply, nPS, zP]) (by simp [pR, Function.update_apply, nQS, zQ])
    (by simp [pR, Function.update_apply, nWS, zW]) (by simpa [pR] using hkh)
  have hv0 : (σ.setv rS kh).val (pR 0) = kh := by simp [pR]
  have hp1 : pR 1 = rP := by simp [pR]
  rw [hv0, hp1] at e2
  set σ2 := (σ.setv rS kh).setv rP (2 ^ kh) with hσ2
  have e3 := wrU_spec cap (sk x 156) rO rP rK rT (by decide) (by decide) (by decide) (by decide) (by decide) σ2
    (by simp [σ2, hO]) (by simp [σ2, hOh]) (by simp [σ2, Function.update_apply, nOS, nOP, zO])
    (by simp [σ2, Function.update_apply, nKS, nKP, zK]) (by simp [σ2, Function.update_apply, nTS, nTP, zT])
    (by simp [σ2]; omega)
  have hv1 : σ2.val rP = 2 ^ kh := by simp [σ2]
  rw [hv1] at e3
  set σ3 := σ2.sets (sk x 156) (List.replicate (2 ^ kh) true) with hσ3
  have e4 := wclear_spec cap rS kh σ3 (by simp [σ3, σ2, Function.update_apply, nSP])
    (by simp [σ3, σ2, Function.update_apply, nSP]; omega)
  have e5 := wclear_spec cap rP (2 ^ kh) (σ3.setv rS 0) (by simp [σ3, σ2, Function.update_apply, nPS])
    (by simp [σ3, σ2, Function.update_apply, nPS]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ ?_
  · apply WState.eq
    · rfl
    · rfl
    · funext r
      simp only [σ3, σ2, WState.setv_val, WState.sets_val, Function.update_apply]
      by_cases hr1 : r = rP
      · subst hr1; simp [nPS, zP]
      · by_cases hr2 : r = rS
        · subst hr2; simp [nSP, zS]
        · simp [hr1, hr2]
    · rfl
  · have m1 : kh * (18 * 2 ^ kh + 7) ≤ cap * (18 * cap + 7) :=
      Nat.mul_le_mul (by omega) (by omega)
    have m2 : cap * (18 * cap + 7) ≤ 18 * UnaryPow.sq cap := by unfold UnaryPow.sq; nlinarith
    omega

/-- The cell's part A: the HASH decode's phases and the unary counts. -/
def cAW (cr : ℕ) : WM (LNS x) LNR :=
  .seq (.seq (hAW x cr) (.seq (hC1W x) (hC2W x)))
    (.seq (wrU (sk x 153) rO (Hb 0) rK rT) (.seq (wrU (sk x 154) rO (Hb 1) rK rT) (.seq (nW x)
      (.seq (.seq (hD1W x) (.seq (hGW x) (hD3W x)))
        (.seq (wrU (sk x 155) rO (G 7) rK rT) (wrU (sk x 157) rO (G 53) rK rT))))))

/-- Part A's steps. -/
def cACost (n wl cr : ℕ) : ℕ := hACost n wl cr cap + 260 * UnaryPow.sq cap + 20

/-- **The cell after part A**: the entry's streams with the five unary counts, every head but the data tape's at `0`,
the aux filter's cap and length, `|thrPool|` and `nE` in `G 0`, `G 1`, `G 7`, `G 53`, every register below `250` at
`0`, every register within the capacity. -/
structure CAOut (τ : WState (LNS x) LNR) (w : List Bool) (V : ℕ) (u : List Bool) (nc capT kh nP nE aC aL : ℕ) : Prop
    where
  st : τ.st = Function.update (Function.update (Function.update (Function.update (Function.update
    (CellLoopD.blankCellD x w [] V u).st (sk x 153) (List.replicate nc true)) (sk x 154) (List.replicate capT true))
    (sk x 156) (List.replicate (2 ^ kh) true)) (sk x 155) (List.replicate nP true)) (sk x 157) (List.replicate nE true)
  sh : ∀ s, s ≠ sk x 113 → τ.sh s = 0
  cell : τ.cell = false
  g0 : τ.val (G 0) = aC
  g1 : τ.val (G 1) = aL
  g7 : τ.val (G 7) = nP
  g53 : τ.val (G 53) = nE
  low : ∀ r : Fin LNR, r.val < 250 → τ.val r = 0
  bd : ∀ r, τ.val r ≤ cap

theorem bcD_st (w : List Bool) (V : ℕ) (u : List Bool) (k : Fin 161) (h0 : k.val ≠ 0) (h1 : k.val ≠ 1)
    (h2 : k.val ≠ 2) (h3 : k.val ≠ 113) : (CellLoopD.blankCellD x w [] V u).st (sk x k) = [] := by
  have n0 : sk x k ≠ sk x 0 := fun e => h0 (by have := congrArg Fin.val e; simpa [sk_val] using this)
  have n1 : sk x k ≠ sk x 1 := fun e => h1 (by have := congrArg Fin.val e; simpa [sk_val] using this)
  have n2 : sk x k ≠ sk x 2 := fun e => h2 (by have := congrArg Fin.val e; simpa [sk_val] using this)
  have n3 : sk x k ≠ sk x 113 := fun e => h3 (by have := congrArg Fin.val e; simpa [sk_val] using this)
  simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n0, n1, n2, n3]

theorem bcD_sh (w : List Bool) (V : ℕ) (u : List Bool) (s : Fin (LNS x + 1)) :
    (CellLoopD.blankCellD x w [] V u).sh s = 0 := by
  simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]

theorem skne (a b : Fin 161) (h : a.val ≠ b.val) : sk x a ≠ sk x b := fun e => h (by
  have := congrArg Fin.val e; simpa [sk_val] using this)

/-- **Part A, run** from the fresh cell. -/
theorem cA_run (cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w : List Bool) (V : ℕ)
    (codes cc : List ℕ) (tl : List Bool) (hw : w = Data.reqW P.n true codes cc tl)
    (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2) (h0v : hs.getD 0 0 = xs.length)
    (Pa : GapParams) (hPl : Pa.len = 2 * xs.sum) (hPc : Pa.cap = (xs.length + 1) * 4096 * hs.getD 1 0)
    (hPe : Pa.errExp = hs.getD 13 0) (hPc1 : 1 ≤ Pa.cap)
    (hc1 : 2 * w.length + 2 ≤ cap) (hc2 : 2 ^ (natBitLength P.n + 1) ≤ cap)
    (hc3 : (0 + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap)
    (hcD1 : hs.getD 13 0 + 2 * xs.sum + (xs.length + 1) * 4096 * hs.getD 1 0 + (xs.length + 1) * 4096 +
      hs.getD 1 0 + 10 ≤ cap)
    (hcG1 : Pa.cap * 32 + 2 ≤ cap) (hcG2 : Pa.len + 8 ≤ cap) (hcG3 : Pa.errExp + 4 ≤ cap)
    (hcG4 : 2 ^ (Pa.seedBits + 1) ≤ cap) (hcG5 : Pa.labelBits + Pa.fieldBits + Pa.walkLen + 512 ≤ cap)
    (hcD3 : 2 * xs.sum + hs.getD 8 0 + 2 ^ Pa.seedBits + 2 ^ (2 * (P.s * (P.r / 2)) + 1) +
      2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 10 ≤ cap)
    (hkh : 2 ^ (P.s * (P.r / 2) + 1) ≤ cap) :
    ∃ τ c, WExec cap (cAW x cr) (CellLoopD.blankCellD x w [] V (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ cACost cap P.n w.length cr ∧
      CAOut cap x τ w V (Data.unaryList (hs ++ (xs ++ [tg]))) xs.length (hs.getD 1 0) (P.s * (P.r / 2))
        (2 * xs.sum + hs.getD 8 0) (2 ^ Pa.seedBits) Pa.cap Pa.len := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  obtain ⟨τ1, c1, e1, c1le, t0, t1, t8m, t13, tA, tB, t8, tz, st1, sh1, cl1, bd1⟩ :=
    hAC_run cap x cr P hrP w [] V codes cc tl hw hs xs tg hhs hxs h0v hc1 hc2 hc3 hcl hcs
  have z1 : ∀ r : Fin LNR, r.val < 250 → τ1.val r = 0 := fun r hr => tz r (Or.inl hr)
  have hst1 : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → τ1.st (sk x k) = [] := by
    intro k a0 a1 a2 a3
    rw [st1]
    exact bcD_st x w V _ k a0 a1 a2 a3
  have hsh1 : ∀ s, s ≠ sk x 113 → τ1.sh s = 0 := by
    intro s hs
    rw [sh1 s hs]
    exact bcD_sh x w V _ s
  -- 153
  have e2 := wrU_spec cap (sk x 153) rO (Hb 0) rK rT (by decide) (by decide) (by decide) (by decide) (by decide) τ1
    (hst1 153 (by decide) (by decide) (by decide) (by decide)) (hsh1 _ (skne x 153 113 (by decide)))
    (z1 rO (by decide)) (z1 rK (by decide)) (z1 rT (by decide)) (bd1 _)
  rw [t0] at e2
  set τ2 := τ1.sets (sk x 153) (List.replicate xs.length true) with hτ2
  -- 154
  have s154 : τ2.st (sk x 154) = [] := by
    simp only [τ2, WState.sets_st]
    rw [Function.update_of_ne (skne x 154 153 (by decide))]
    exact hst1 154 (by decide) (by decide) (by decide) (by decide)
  have e3 := wrU_spec cap (sk x 154) rO (Hb 1) rK rT (by decide) (by decide) (by decide) (by decide) (by decide) τ2
    s154 (hsh1 _ (skne x 154 113 (by decide))) (z1 rO (by decide)) (z1 rK (by decide)) (z1 rT (by decide)) (bd1 _)
  have ht1 : τ2.val (Hb 1) = hs.getD 1 0 := t1
  rw [ht1] at e3
  set τ3 := τ2.sets (sk x 154) (List.replicate (hs.getD 1 0) true) with hτ3
  -- 156
  have s156 : τ3.st (sk x 156) = [] := by
    simp only [τ3, τ2, WState.sets_st]
    rw [Function.update_of_ne (skne x 156 154 (by decide)), Function.update_of_ne (skne x 156 153 (by decide))]
    exact hst1 156 (by decide) (by decide) (by decide) (by decide)
  have e4 := nW_spec cap x τ3 (P.s * (P.r / 2)) t8 z1 s156 (hsh1 _ (skne x 156 113 (by decide))) hkh
  set τ4 := τ3.sets (sk x 156) (List.replicate (2 ^ (P.s * (P.r / 2))) true) with hτ4
  have v4 : τ4.val = τ1.val := rfl
  -- the aux numbers
  obtain ⟨τ5, e5, g0, g1, g2, g7, g56, g55, g32, g53, g52, g41, gNC, gH, gz, st5, sh5, cl5⟩ :=
    hD_run cap x τ4 xs.length (hs.getD 1 0) (hs.getD 13 0) xs.sum (hs.getD 8 0) (P.s * (P.r / 2)) Pa
      t0 t1 t13 tA t8m t8 tz hPl hPc hPe hPc1 hcD1 hcG1 hcG2 hcG3 hcG4 hcG5 hcD3
  have z5 : ∀ r : Fin LNR, r.val < 250 → τ5.val r = 0 := fun r hr => gz r (Or.inl hr)
  have bd5 : ∀ r, τ5.val r ≤ cap := wexec_le cap e5 bd1
  have hst5 : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → k.val ≠ 153 → k.val ≠ 154 →
      k.val ≠ 156 → τ5.st (sk x k) = [] := by
    intro k a0 a1 a2 a3 a4 a5 a6
    rw [st5]
    simp only [τ4, τ3, τ2, WState.sets_st]
    rw [Function.update_of_ne (skne x k 156 a6), Function.update_of_ne (skne x k 154 a5),
      Function.update_of_ne (skne x k 153 a4)]
    exact hst1 k a0 a1 a2 a3
  have hsh5 : ∀ s, s ≠ sk x 113 → τ5.sh s = 0 := by
    intro s hs
    rw [sh5]
    exact hsh1 s hs
  -- 155
  have e6 := wrU_spec cap (sk x 155) rO (G 7) rK rT (by decide) (by decide) (by decide) (by decide) (by decide) τ5
    (hst5 155 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hsh5 _ (skne x 155 113 (by decide))) (z5 rO (by decide)) (z5 rK (by decide)) (z5 rT (by decide)) (bd5 _)
  rw [g7] at e6
  set τ6 := τ5.sets (sk x 155) (List.replicate (2 * xs.sum + hs.getD 8 0) true) with hτ6
  -- 157
  have s157 : τ6.st (sk x 157) = [] := by
    simp only [τ6, WState.sets_st]
    rw [Function.update_of_ne (skne x 157 155 (by decide))]
    exact hst5 157 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e7 := wrU_spec cap (sk x 157) rO (G 53) rK rT (by decide) (by decide) (by decide) (by decide) (by decide) τ6
    s157 (hsh5 _ (skne x 157 113 (by decide))) (z5 rO (by decide)) (z5 rK (by decide)) (z5 rT (by decide))
    (bd5 _)
  have hg53 : τ6.val (G 53) = 2 ^ Pa.seedBits := g53
  rw [hg53] at e7
  have b1 : xs.length ≤ cap := by rw [← t0]; exact bd1 _
  have b2 : hs.getD 1 0 ≤ cap := by rw [← t1]; exact bd1 _
  have b3 : 2 * xs.sum + hs.getD 8 0 ≤ cap := by rw [← g7]; exact bd5 _
  have b4 : 2 ^ Pa.seedBits ≤ cap := by rw [← g53]; exact bd5 _
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))), ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold cACost
    omega
  · simp only [τ6, WState.sets_st]
    rw [st5]
    simp only [τ4, τ3, τ2, WState.sets_st]
    rw [st1]
  · intro s hs
    exact hsh5 s hs
  · show τ5.cell = false
    rw [cl5]
    show τ1.cell = false
    exact cl1
  · exact g0
  · exact g1
  · exact g7
  · exact g53
  · exact z5
  · exact bd5

end Cell

end NearCubicWires.WireExponent3_5.PrimAsm.HashCell

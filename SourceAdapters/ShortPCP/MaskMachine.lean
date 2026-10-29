import SourceAdapters.ShortPCP.MaskMachineMain
import SourceAdapters.ShortPCP.Machines.UnaryPrefix
import SourceAdapters.Code.Composition
import Proof.Gates.CounterMachine.PrefixFinal
import Proof.Foundations.OrdinaryMachine

/-!
# The mask machine: `MaskMachine` holds

 (Step 3 of `thm:short-pcp-ours`): "Choosing `m` uses only integer comparisons; constructing the field
and listing the multiset also take `poly(n, log T)` time." The consumer is `OracleCircuitPCP.MaskMachine`
(`Field6.lean`): for fixed `K1, b1`, one ordinary word function maps `maskWord (f, n) = natWord f ++ natWord n` to
`listWord frame (masksOf (r0f f) f n K1 b1)` within `K·(f + n + 1)^e` steps.

The word function is `composeFramed` (W `Code/Composition.lean`) of
1. the width prefix `w ↦ frame (1^{size |w|} 0 ++ w)` (`UnaryPrefix.prefixWF`, `ShortPCP/Machines/UnaryPrefix.lean`), and
2. the cell program `maskP K1 b1` (`MaskMachineMain`) packaged by `Cells.wordFunction_of_lang` with width
   `2^s·(b1 + K1 + 16)` (`s` the unary prefix), every value of the run fitting by `wBig_lt`;
its budget is a polynomial in `f + n + 1` (`PolyOn`, `Field6.lean`): the run costs `poly(f, 4^m, r0)` cell steps
with `4^m ≤ 4·r0²·n·K1·f^{b1} + 1` and `r0 ≤ 4f`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5 NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee lang_le leadOnes_rep)

/-! ## The width -/

theorem wBig_lt (K1 b1 f n W : ℕ)
    (hW : (2 * natBitLength f + 2 * natBitLength n + 3) * (b1 + K1 + 16) ≤ W) : wBig K1 b1 f n < 2 ^ W := by
  set a := natBitLength f with ha
  set c := natBitLength n with hc
  have hP : f + 1 ≤ 2 ^ a := lt_natBitLength f
  have hQ : n + 1 ≤ 2 ^ c := lt_natBitLength n
  have hr : rOf f + 1 ≤ 4 * 2 ^ a := by have := r0f_le f; unfold rOf; omega
  have hK : K1 + 1 ≤ 2 ^ K1 := Nat.lt_two_pow_self
  have hb : b1 + 1 ≤ 2 ^ b1 := Nat.lt_two_pow_self
  have hP1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hQ1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  have hK1 : 1 ≤ 2 ^ K1 := Nat.one_le_two_pow
  have hb1 : 1 ≤ 2 ^ b1 := Nat.one_le_two_pow
  set G := (2 ^ a) ^ (b1 + 2) * 2 ^ c * 2 ^ K1 * 2 ^ b1 with hG
  have hPb : 1 ≤ (2 ^ a) ^ b1 := Nat.one_le_pow _ _ hP1
  have hPG : 2 ^ a ≤ (2 ^ a) ^ (b1 + 2) := Nat.le_self_pow (by omega) _
  have hG1 : (2 ^ a) ^ (b1 + 2) ≤ G := by
    have : 1 ≤ 2 ^ c * 2 ^ K1 * 2 ^ b1 := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc (2 ^ a) ^ (b1 + 2) = (2 ^ a) ^ (b1 + 2) * 1 := by ring
      _ ≤ (2 ^ a) ^ (b1 + 2) * (2 ^ c * 2 ^ K1 * 2 ^ b1) := Nat.mul_le_mul_left _ this
      _ = G := by rw [hG]; ring
  have hGc : 2 ^ c ≤ G := by
    have : 1 ≤ (2 ^ a) ^ (b1 + 2) * 2 ^ K1 * 2 ^ b1 := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc 2 ^ c = 2 ^ c * 1 := by ring
      _ ≤ 2 ^ c * ((2 ^ a) ^ (b1 + 2) * 2 ^ K1 * 2 ^ b1) := Nat.mul_le_mul_left _ this
      _ = G := by rw [hG]; ring
  have hGK : 2 ^ K1 ≤ G := by
    have : 1 ≤ (2 ^ a) ^ (b1 + 2) * 2 ^ c * 2 ^ b1 := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc 2 ^ K1 = 2 ^ K1 * 1 := by ring
      _ ≤ 2 ^ K1 * ((2 ^ a) ^ (b1 + 2) * 2 ^ c * 2 ^ b1) := Nat.mul_le_mul_left _ this
      _ = G := by rw [hG]; ring
  have hGb : 2 ^ b1 ≤ G := by
    have : 1 ≤ (2 ^ a) ^ (b1 + 2) * 2 ^ c * 2 ^ K1 := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc 2 ^ b1 = 2 ^ b1 * 1 := by ring
      _ ≤ 2 ^ b1 * ((2 ^ a) ^ (b1 + 2) * 2 ^ c * 2 ^ K1) := Nat.mul_le_mul_left _ this
      _ = G := by rw [hG]; ring
  have hnB : nBig (rOf f) n K1 b1 f ≤ 16 * G := by
    unfold nBig
    calc (rOf f + 1) ^ 2 * (n + 1) * (K1 + 1) * (f + 1) ^ b1
        ≤ (4 * 2 ^ a) ^ 2 * 2 ^ c * 2 ^ K1 * (2 ^ a) ^ b1 := by gcongr
      _ = 16 * ((2 ^ a) ^ (b1 + 2) * 2 ^ c * 2 ^ K1) := by ring
      _ ≤ 16 * G := by
        have : (2 ^ a) ^ (b1 + 2) * 2 ^ c * 2 ^ K1 * 1 ≤ G := Nat.mul_le_mul_left _ hb1
        omega
  have hGE : G = 2 ^ (a * (b1 + 2) + c + K1 + b1) := by rw [hG, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
  have hE : a * (b1 + 2) + c + K1 + b1 + 11 ≤ W := by
    have ha1 : 1 ≤ a := natBitLength_pos f
    have hc1 : 1 ≤ c := natBitLength_pos n
    nlinarith
  unfold wBig
  calc 64 * (nBig (rOf f) n K1 b1 f + K1 + b1 + f + n + 8) ≤ 64 * (16 * G + G + G + G + G + 8 * G) := by
        have : 1 ≤ G := le_trans hb1 hGb
        have : f ≤ G := by omega
        have : n ≤ G := by omega
        omega
    _ < 2 ^ 11 * G := by have : 1 ≤ G := le_trans hb1 hGb; omega
    _ = 2 ^ (a * (b1 + 2) + c + K1 + b1 + 11) := by rw [hGE, ← pow_add]; ring_nf
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hE

/-! ## The cell program as an ordinary word function -/

/-- The cell sizes: width `2^s·(b1 + K1 + 16)`, no calls. -/
def maskSz (K1 b1 : ℕ) : Sz := ⟨b1 + K1 + 16, 1, 0, 0, 0, 0⟩

/-- The input of the cell program: `1^{size |w|} 0 ++ w` for `w = maskWord (f, n)`. -/
def cellInput (q : ℕ × ℕ) : List Bool := UnaryPrefix.prefixWord (maskWord q)

def cellCost (K1 b1 : ℕ) (q : ℕ × ℕ) : ℕ :=
  preCost (Nat.size (maskWord q).length) q.1 q.2 + phaseBCost K1 b1 q.1 q.2 + 1

theorem cellInput_eq (q : ℕ × ℕ) :
    cellInput q = List.replicate (Nat.size (maskWord q).length) true ++ false :: (natWord q.1 ++ natWord q.2) := rfl

theorem maskWord_length (q : ℕ × ℕ) :
    (maskWord q).length = 2 * natBitLength q.1 + 2 * natBitLength q.2 + 2 := by
  simp only [maskWord, List.length_append, NearCubicGates.Close.Cells.natWord_length]; ring

theorem ctx_wd (K1 b1 : ℕ) (q : ℕ × ℕ) :
    (ctxOf noCallee (maskSz K1 b1) (cellInput q)).Wd = 2 ^ (1 * Nat.size (maskWord q).length) * (b1 + K1 + 16) := by
  simp only [ctxOf, maskSz, Sz.W, cellInput_eq, leadOnes_rep]

/-- **The cell program** `maskP K1 b1` on `1^s 0 ++ maskWord (f, n)` prints `listWord frame (masksOf …)`. -/
noncomputable def cellWF (K1 b1 : ℕ) : RepairOrdinary.WordFunction (ℕ × ℕ) cellInput
    (fun q => listWord RepairOrdinary.frame (masksOf (r0f q.1) q.1 q.2 K1 b1))
    (fun q => langBudget noCallee (maskSz K1 b1) VV MM (cellInput q) (cellCost K1 b1 q)) :=
  wordFunction_of_lang cellInput (fun q => listWord RepairOrdinary.frame (masksOf (r0f q.1) q.1 q.2 K1 b1))
    noCallee (maskSz K1 b1) (maskP K1 b1) (cellCost K1 b1) (fun q => by
      have hw := ctx_wd K1 b1 q
      have hL := maskWord_length q
      have hs : (maskWord q).length < 2 ^ Nat.size (maskWord q).length := Nat.lt_size_self _
      rw [Nat.one_mul] at hw
      have hW : ((maskWord q).length + 1) * (b1 + K1 + 16) ≤ (ctxOf noCallee (maskSz K1 b1) (cellInput q)).Wd := by
        rw [hw]; exact Nat.mul_le_mul_right _ hs
      have hW1 : (maskWord q).length + 1 ≤ (ctxOf noCallee (maskSz K1 b1) (cellInput q)).Wd :=
        le_trans (Nat.le_mul_of_pos_right _ (by omega)) hW
      obtain ⟨b, k, hex, hout, hk⟩ := maskP_run (ctxOf noCallee (maskSz K1 b1) (cellInput q)) K1 b1
        (Nat.size (maskWord q).length) q.1 q.2 (cellInput_eq q) (by omega) (by omega) (by omega)
        (wBig_lt K1 b1 q.1 q.2 _ (by rw [hL] at hW; exact hW))
      exact ⟨b, k, hex, hout, hk⟩)
    (fun q => by simp only [maskSz, Sz.W]; exact Nat.one_le_iff_ne_zero.2 (by positivity))

/-- The width prefix on the request `(f, n)` (`UnaryPrefix.prefixWF` at `w = maskWord (f, n)`). -/
noncomputable def prefixMaskWF : RepairOrdinary.WordFunction (ℕ × ℕ) maskWord
    (fun q => RepairOrdinary.frame (cellInput q)) (fun q => 200 * ((maskWord q).length + 1) ^ 2) where
  program := UnaryPrefix.prefixWF.program
  realizes q := UnaryPrefix.prefixWF.realizes (maskWord q)

/-- **The mask machine for `K1`, `b1`** (Step 3). -/
noncomputable def maskWF (K1 b1 : ℕ) := Code.composeFramed prefixMaskWF (cellWF K1 b1)

/-! ## The budget is a polynomial in `f + n + 1` -/

theorem two_pow_size_le (x : ℕ) : 2 ^ Nat.size x ≤ 2 * x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have h1 : 0 < Nat.size x := Nat.size_pos.2 hx
    have h2 : 2 ^ (Nat.size x - 1) ≤ x := Nat.lt_size.1 (by omega)
    have : 2 ^ Nat.size x = 2 * 2 ^ (Nat.size x - 1) := by rw [← pow_succ']; congr 1; omega
    omega

theorem size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.2 Nat.lt_two_pow_self

theorem budget_poly (K1 b1 : ℕ) : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1)
    (fun q => 2 * (200 * ((maskWord q).length + 1) ^ 2) + 2 + 1 +
      (2 * langBudget noCallee (maskSz K1 b1) VV MM (cellInput q) (cellCost K1 b1 q) + 2)) := by
  have hB : ∀ q : ℕ × ℕ, True → 1 ≤ q.1 + q.2 + 1 := fun q _ => by omega
  have hf : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => q.1) :=
    PolyOn.base.mono (fun q _ => by omega)
  have hn : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => q.2) :=
    PolyOn.base.mono (fun q _ => by omega)
  have hnf : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => natBitLength q.1) :=
    (PolyOn.add hB hf (PolyOn.const 1)).mono (fun q _ => natBitLength_le_self _)
  have hnn : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => natBitLength q.2) :=
    (PolyOn.add hB hn (PolyOn.const 1)).mono (fun q _ => natBitLength_le_self _)
  have hL : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => (maskWord q).length) := by
    refine PolyOn.mono (h := fun q => 2 * natBitLength q.1 + 2 * natBitLength q.2 + 2) ?_
      (fun q _ => (maskWord_length q).le)
    repeat (first | with_reducible assumption | with_reducible exact PolyOn.const _ |
      with_reducible apply PolyOn.add hB | with_reducible apply PolyOn.mul | with_reducible apply PolyOn.pow)
  have hs : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => Nat.size (maskWord q).length) :=
    hL.mono (fun q _ => size_le_self _)
  have h2s : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1)
      (fun q => 2 ^ Nat.size (maskWord q).length) :=
    (PolyOn.add hB (PolyOn.mul (PolyOn.const 2) hL) (PolyOn.const 1)).mono (fun q _ => two_pow_size_le _)
  have hr : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => rOf q.1) :=
    (PolyOn.mul (PolyOn.const 4) hf).mono (fun q _ => r0f_le q.1)
  have hN : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => nOf K1 b1 q.1 q.2) := by
    unfold nOf
    repeat (first | with_reducible assumption | with_reducible exact PolyOn.const _ |
      with_reducible apply PolyOn.add hB | with_reducible apply PolyOn.mul | with_reducible apply PolyOn.pow)
  have h4 : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => 4 ^ mOf K1 b1 q.1 q.2) :=
    (PolyOn.add hB (PolyOn.mul (PolyOn.const 4) hN) (PolyOn.const 1)).mono (fun q _ => four_pow_mDeg_le _)
  have hZ : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => 2 ^ mOf K1 b1 q.1 q.2) :=
    h4.mono (fun q _ => Nat.pow_le_pow_left (by norm_num) _)
  have hm : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1) (fun q => mOf K1 b1 q.1 q.2) :=
    hZ.mono (fun q _ => Nat.lt_two_pow_self.le)
  have hnb : PolyOn (fun _ : ℕ × ℕ => True) (fun q => q.1 + q.2 + 1)
      (fun q => natBitLength (4 ^ mOf K1 b1 q.1 q.2)) :=
    (PolyOn.add hB h4 (PolyOn.const 1)).mono (fun q _ => natBitLength_le_self _)
  refine PolyOn.mono (h := fun q => 2 * (200 * ((maskWord q).length + 1) ^ 2) + 2 + 1 +
      (2 * (10 ^ 6 * ((cellCost K1 b1 q + 1) * (2 ^ Nat.size (maskWord q).length * (b1 + K1 + 16) +
        Nat.size (maskWord q).length + (Nat.size (maskWord q).length + 1 + (maskWord q).length) +
        (b1 + K1 + 16) + 1 + TSK noCallee + 1) ^ 2)) + 2)) ?_ (fun q _ => ?_)
  · simp only [cellCost, preCost, phaseBCost, tableCost, tabPass, bigCost, numCost, mdegCost, srchCost, srchPass,
      perCost, perPass, lfsrCost, xorCost, allCost, allPass, rowCost, rowPass, sigCost, sigPass, dotCost, fmulCost,
      mulPass]
    repeat (first | with_reducible assumption | with_reducible exact PolyOn.const _ |
      with_reducible apply PolyOn.add hB | with_reducible apply PolyOn.mul | with_reducible apply PolyOn.pow)
  · have hl := lang_le noCallee (b1 + K1 + 16) 1 (cellInput q) (cellCost K1 b1 q)
    have hlead : leadOnes (cellInput q) = Nat.size (maskWord q).length := leadOnes_rep _ _
    have hlen : (cellInput q).length = Nat.size (maskWord q).length + 1 + (maskWord q).length := by
      simp only [cellInput, UnaryPrefix.prefixWord, List.length_append, List.length_replicate, List.length_cons]; omega
    rw [hlead, hlen, Nat.one_mul] at hl
    simp only [maskSz]
    omega

/-- **`MaskMachine` holds** (Step 3 of the proof of `thm:short-pcp-ours`). -/
theorem maskMachine : MaskMachine := by
  intro K1 b1
  obtain ⟨K, e, h⟩ := budget_poly K1 b1
  exact ⟨K, e, ⟨(maskWF K1 b1).enlargeBudget (fun q => h q trivial)⟩⟩

end NearCubicGates.Adapters.ShortPCP.MaskMachine

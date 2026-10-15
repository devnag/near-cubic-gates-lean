import Proof.Wire_3_5.PrimAsmGapNums

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GapNums
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.SparseNum NearCubicWires.WireExponent3_5.PrimAsm.FiltNum
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ} (cap : ℕ)

/-- Part B at `len = 0`: `K 5 := 4`, `K 4 := K 3`. -/
def gB0 (K : Fin 32 ↪ Fin nr) : WM ns nr :=
  .seq (StarNums.incN (K 5) 4) (FinalPass.Hash4.wcopyR (K 3) (K 4) (K 14))

/-- **The filter's numbers at an empty population.** -/
def gapNums0W (K : Fin 32 ↪ Fin nr) : WM ns nr := .seq (filtA K) (.seq (gB0 K) (.seq (filtC K) (gS K)))

theorem gapNums0_spec (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (P : Filters.GapParams) (hB0 : σ.val (K 0) = P.cap)
    (hM0 : P.len = 0) (hE0 : σ.val (K 2) = P.errExp) (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (K i) = 0)
    (hB1 : 1 ≤ P.cap) (hc1 : 1 ≤ cap) (hBc : P.cap * 32 + 2 ≤ cap)
    (hEc : P.errExp + 4 ≤ cap) (hsc : 2 ^ (P.seedBits + 1) ≤ cap)
    (hlc : P.labelBits + P.fieldBits + P.walkLen + 512 ≤ cap) :
    WExec cap (gapNums0W K) σ ((((((σ.setv (K 3) P.prefixBits).setv (K 4) P.labelBits).setv (K 5) P.fieldBits).setv
      (K 6) P.walkLen).setv (K 20) P.seedBits).setv (K 21) (2 ^ P.seedBits)) (110 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨PB, hPB⟩ : ∃ v, v = Nat.clog 2 (32 * P.cap) := ⟨_, rfl⟩
  have ePB : P.prefixBits = PB := hPB.symm
  have eLB : P.labelBits = PB := by
    show max (Nat.clog 2 (32 * P.cap)) (Nat.clog 2 P.len) = PB
    rw [hM0, ← hPB]; simp
  have eFB : P.fieldBits = 4 := by
    show Nat.clog 2 P.len + 4 = 4
    rw [hM0]; simp
  have eWL : P.walkLen = 2 * (P.errExp / 4) + 1 := rfl
  have hPc : PB ≤ cap := by rw [eLB] at hlc; omega
  have hPB1 : 1 ≤ PB := by rw [hPB]; exact Nat.clog_pos (by norm_num) (by omega)
  have hA := filtA_spec cap K σ P.cap hB0 hz hB1 hBc
  rw [← hPB] at hA
  have hB1' := incN0 cap (K 5) 4 (σ.setv (K 3) PB) (by simp [Function.update_apply, hz 5 (by decide)]) (by omega)
  have hB2 := copy1 cap (K 3) (K 4) (K 14) (by simp) (by simp) (by simp) PB ((σ.setv (K 3) PB).setv (K 5) 4)
    (by simp) (by simp [Function.update_apply, hz 4 (by decide)]) (by simp [Function.update_apply, hz 14 (by decide)])
    hPc
  have hB : WExec cap (gB0 K) (σ.setv (K 3) PB) (((σ.setv (K 3) PB).setv (K 5) 4).setv (K 4) PB)
      (UnaryPow.sq cap + 1 + UnaryPow.sq cap) := WExec.seq hB1' hB2
  have hC := filtC_spec cap K (((σ.setv (K 3) PB).setv (K 5) 4).setv (K 4) PB) P.errExp 0 (by simp [hE0])
    (by simp [Function.update_apply, hz 7 (by decide)]) (by simp [Function.update_apply, hz 6 (by decide)])
    (fun i hi => by
      have hn3 : i ≠ 3 := by intro h; subst h; simp at hi
      have hn5 : i ≠ 5 := by intro h; subst h; simp at hi
      have hn4 : i ≠ 4 := by intro h; subst h; simp at hi
      simp [Function.update_apply, hn3, hn5, hn4, hz i (by omega)]) hc1 hEc (by omega)
  have hS := gS_run cap K (((((σ.setv (K 3) PB).setv (K 5) 4).setv (K 4) PB).setv (K 6) (2 * (P.errExp / 4) + 1)).setv
      (K 7) 0) PB 4 (2 * (P.errExp / 4) + 1)
    (by simp) (by simp) (by simp) hPB1 (by omega)
    (fun i hi => by
      have hn3 : i ≠ 3 := by intro h; subst h; simp at hi
      have hn7 : i ≠ 7 := by intro h; subst h; simp at hi
      have hn5 : i ≠ 5 := by intro h; subst h; simp at hi
      have hn4 : i ≠ 4 := by intro h; subst h; simp at hi
      have hn6 : i ≠ 6 := by intro h; subst h; simp at hi
      rcases hi with hi | hi
      · simp [Function.update_apply, hn3, hn7, hn5, hn4, hn6, hz i (by omega)]
      · simp [Function.update_apply, hn3, hn7, hn5, hn4, hn6, hz i (by omega)])
    hc1 (by have h := hsc; rw [seedBits_eq, eLB, eFB, eWL] at h; exact h)
    (by have h := hlc; rw [eLB, eFB, eWL] at h; exact h)
  refine WExec.cast cap (WExec.seq hA (WExec.seq hB (WExec.seq hC hS))) ?_ (by omega)
  rw [ePB, eLB, eFB, eWL, seedBits_eq, eLB, eFB, eWL]
  clear hA hB hB1' hB2 hC hS hB0 hE0 hB1 hc1 hBc hEc hPc hsq hPB hsc hlc ePB eLB eFB eWL
  have hb0 := setv_base K σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

end NearCubicWires.WireExponent3_5.PrimAsm.GapNums

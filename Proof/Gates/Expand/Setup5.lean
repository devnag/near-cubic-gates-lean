import Proof.Gates.Expand.Setup4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp readNatM readNatM_spec enc_length)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

def walkEnd : WMX NS NR := .whs (U 0) (.seq (WMX.fwd (U 0)) (WMX.fwd (U 0)))

def readV : WMX NS NR :=
  .seq (.wm (readNatM true (U 0) (R 7) (R 8) (RF 10) (R 9) (R 10))) (.seq walkEnd (repK (Y 0) (Y 1) (WMX.bwd (U 0))))

def readVCost (V L : ℕ) : ℕ :=
  (natBitLength V + 2) * (40 * 2 ^ natBitLength V + 40) + 1 + ((L * (3 + 2) + 1) + 1 +
    ((2 * L + 1) * (1 + 8) + 7 * (2 * L + 1) + 3))

theorem readV_spec (cap : ℕ) (r : FormulaReq) (σ : WState NS NR) (hst : σ.st (U 0) = frame (formulaWord r))
    (hsh : σ.sh (U 0) = 0) (hR : ∀ j, σ.val (R j) = 0) (hV : σ.val (RF 10) = 0)
    (hY0 : σ.val (Y 0) = 2 * (formulaWord r).length + 1) (hY1 : σ.val (Y 1) = 0)
    (hcap : 2 ^ (natBitLength r.1 + 1) + 2 * (2 * (formulaWord r).length + 1) ≤ cap) :
    Runs cap readV σ (readVCost r.1 (formulaWord r).length)
      (fun τ => SameExcept σ τ [] [RF 10] ∧ τ.val (RF 10) = r.1) := by
  set w := formulaWord r with hw
  set L := w.length with hL
  have hrN : ∀ {i j : Fin 12}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have hRF : ∀ j : Fin 12, R j ≠ RF 10 := fun j => rne (by have := j.isLt; simp; omega)
  have hfw := frame_formulaWord r
  set rest := enc true (natWord (toks r.2).length) ++ enc true ((toks r.2).flatMap tokWord) ++ [false] with hrest
  have hst' : σ.st (U 0) = [] ++ enc true (natWord r.1) ++ rest := by
    rw [hst, hfw, hrest]; simp [List.append_assoc]
  have e1 := readNatM_spec (cap := cap) true (U 0) (R 7) (R 8) (RF 10) (R 9) (R 10) (hrN (by decide)) (hRF 7)
    (hrN (by decide)) (hrN (by decide)) (hRF 8) (hrN (by decide)) (hrN (by decide)) (hRF 9) (hrN (by decide))
    (hRF 10).symm r.1 [] rest σ hst' (by simp [hsh]) (hR 7) (hR 8) (hR 9) (hR 10)
    (by rw [hV]; omega)
  set a := (natWord r.1).length with ha
  have hc2 : 2 * (2 * L + 1) ≤ cap := by have := Nat.two_pow_pos (natBitLength r.1 + 1); omega
  have haL : a ≤ L := by
    rw [ha, hL, hw, formulaWord, List.length_append]; omega
  simp only [List.length_nil, zero_add, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp, if_true, hV] at e1
  set σ1 := (σ.seth (U 0) (2 * a)).setv (RF 10) r.1 with hσ1
  refine Runs.seqE (WXExec.wm e1) ?_
  -- walk to the end
  let Inv : ℕ → WState NS NR → Prop := fun k τ => k ≤ L - a ∧ SameExcept σ1 τ [U 0] [] ∧
    τ.st (U 0) = frame w ∧ τ.sh (U 0) = 2 * (L - k)
  have hwk : Runs cap walkEnd σ1 ((L - a) * (3 + 2) + 1) (Inv 0) := by
    refine Runs.whs Inv 3 (Inv 0) (fun τ h => ⟨?_, h⟩) (fun k τ h => ⟨?_, ?_⟩) (L - a) σ1
      ⟨le_rfl, SameExcept.refl _ _ _, by simp [hσ1, hst], by simp [hσ1]; omega⟩
    · obtain ⟨_, _, hs0, hs⟩ := h
      unfold wbit; rw [hs0, hs, Nat.sub_zero]; exact frame_end_gen w
    · obtain ⟨hk, _, hs0, hs⟩ := h
      unfold wbit; rw [hs0, hs]; exact frame_mark_lt w _ (by omega)
    · obtain ⟨hk, f, hs0, hs⟩ := h
      refine Runs.of (WXExec.seq (WXExec.fwd cap (U 0) τ) (WXExec.fwd cap (U 0) _)) ⟨by omega, ?_, ?_, ?_⟩
      · exact f.trans ((sameExcept_seth _ (by simp) _).trans (sameExcept_seth _ (by simp) _))
      · simpa using hs0
      · simp [hs]; omega
  refine Runs.seq (hwk.cost (by have := Nat.mul_le_mul_right (3 + 2) (Nat.sub_le L a); omega))
    (fun τ2 ⟨_, f2, hs02, hs2⟩ => ?_)
  simp only [Nat.sub_zero] at hs2
  -- rewind by 2L + 1
  have hY0' : τ2.val (Y 0) = 2 * L + 1 := by
    rw [f2.val (by simp), hσ1]; simp [Function.update_of_ne (rne (by simp) : Y 0 ≠ RF 10), hY0]
  have hY1' : τ2.val (Y 1) = 0 := by
    rw [f2.val (by simp), hσ1]; simp [Function.update_of_ne (rne (by simp) : Y 1 ≠ RF 10), hY1]
  let Inv2 : ℕ → WState NS NR → Prop := fun k τ => SameExcept τ2 τ [U 0] [Y 0, Y 1] ∧ τ.st (U 0) = frame w ∧
    τ.sh (U 0) = 2 * L - k
  refine (Runs.rep (cap := cap) (K := Y 0) (K2 := Y 1) (body := WMX.bwd (U 0)) (rne (by simp)) 1 (2 * L + 1) Inv2
    (by omega)
    (fun k τ v ⟨h1, h2, h3⟩ => ⟨h1.trans (sameExcept_setv _ (by simp) _), by simpa using h2, by simpa using h3⟩)
    (fun k τ v ⟨h1, h2, h3⟩ => ⟨h1.trans (sameExcept_setv _ (by simp) _), by simpa using h2, by simpa using h3⟩)
    (fun k _ τ ⟨h1, h2, h3⟩ => Runs.of (WXExec.bwd cap (U 0) τ) ⟨⟨h1.trans (sameExcept_seth _ (by simp) _),
      by simpa using h2, by simp [h3]; omega⟩, by simp, by simp⟩)
    τ2 ⟨SameExcept.refl _ _ _, hs02, by simp [hs2]⟩ hY0' hY1').post (fun τ ⟨⟨f3, hs03, hs3⟩, hy0, hy1⟩ => ⟨?_, ?_⟩)
  · refine ⟨fun x _ => ?_, fun q hq => ?_, ?_⟩
    · by_cases e : x = U 0
      · subst e; refine ⟨by rw [hs03, hst], by rw [hs3, hsh]; omega⟩
      · have hx : x ∉ [U 0] := by simp [e]
        rw [f3.st hx, f3.sh hx, f2.st hx, f2.sh hx, hσ1]; simp [Function.update_of_ne e]
    · by_cases e0 : q = Y 0
      · subst e0; rw [hy0, hY0]
      · by_cases e1 : q = Y 1
        · subst e1; rw [hy1, hY1]
        · rw [f3.val (by simp [e0, e1]), f2.val (by simp), hσ1]
          simp only [List.mem_singleton] at hq
          simp [Function.update_of_ne hq]
    · rw [f3.cell, f2.cell, hσ1]; simp
  · rw [f3.val (by simp [(rne (by simp) : RF 10 ≠ Y 0), (rne (by simp) : RF 10 ≠ Y 1)]), f2.val (by simp), hσ1]; simp

end NearCubicGates.Close.Expand.Layout

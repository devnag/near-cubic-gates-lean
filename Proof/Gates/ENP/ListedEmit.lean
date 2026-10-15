import Proof.Gates.CheckedPCPP.EmitNat
import Proof.Gates.WordPrograms.Hoare
import Proof.Gates.WordPrograms.OutX
import Proof.Gates.ENP.ListedFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.EmitNat

variable {ns nr : ℕ} {cap : ℕ}

/-- The marked bits of a framed word: `frame l = pairs l ++ [false]`. -/
def pairs (l : List Bool) : List Bool := l.flatMap fun b => [true, b]

theorem frame_eq_pairs (l : List Bool) : RepairOrdinary.frame l = pairs l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [RepairOrdinary.frame, pairs, ih]

theorem pairs_cons (b : Bool) (l : List Bool) : pairs (b :: l) = [true, b] ++ pairs l := by
  simp [pairs]

/-- The emitter's registers are pairwise distinct. -/
structure ERegs (X Y B CO : Fin nr) : Prop where
  xy : X ≠ Y
  xb : X ≠ B
  yb : Y ≠ B
  xc : X ≠ CO
  yc : Y ≠ CO
  bc : B ≠ CO

/-- One halving step: halve `X`, append the bit pair `[true, X mod 2]` to `O`. -/
def bitOut (X Y B CO : Fin nr) (O : Fin (ns + 1)) : WMX ns nr :=
  .seq (halve X Y B) (.seq (emitO O CO true) (.seq (.ifr B (emitO O CO true) (emitO O CO false))
    (.seq (.ifr B (WMX.dec B) WMX.skip) (.wm (WM.move Y X)))))

theorem outOn_setv {σ : WState ns nr} {O : Fin (ns + 1)} {CO : Fin nr} {out L0 : List Bool}
    (h : OutOn σ O CO out L0) (r : Fin nr) (hr : r ≠ CO) (v : ℕ) : OutOn (σ.setv r v) O CO out L0 :=
  ⟨by simpa using h.1, by simpa using h.2.1, by simp [Function.update_of_ne hr.symm, h.2.2]⟩

theorem bitOut_exec (X Y B CO : Fin nr) (O : Fin (ns + 1)) (hr : ERegs X Y B CO) (u : ℕ) (σ : WState ns nr)
    (out L0 : List Bool) (hX : σ.val X = u) (hY : σ.val Y = 0) (hB : σ.val B = 0) (hO : OutOn σ O CO out L0)
    (hu : u ≤ cap) (hc : out.length + 2 < cap) :
    WXExec cap (bitOut X Y B CO O) σ (outSt (σ.setv X (u / 2)) O CO (out ++ [true, decide (u % 2 = 1)]) L0)
      (13 * u + 50) := by
  obtain ⟨hxy, hxb, hyb, hxc, hyc, hbc⟩ := hr
  have h1 := halve_exec (cap := cap) X Y B hxy hxb hyb u σ hX hB (by omega) hu (by omega)
  set σ1 := ((σ.setv X 0).setv Y (σ.val Y + u / 2)).setv B (u % 2) with hσ1
  have hO1 : OutOn σ1 O CO out L0 := outOn_setv (outOn_setv (outOn_setv hO X hxc 0) Y hyc _) B hbc _
  have h2 := emitO_spec cap σ1 out L0 true hO1 (by omega)
  set σ2 := outSt σ1 O CO (out ++ [true]) L0 with hσ2
  have hO2 : OutOn σ2 O CO (out ++ [true]) L0 := outOn_outSt _ _ _ _ _
  have hB2 : σ2.val B = u % 2 := by simp [hσ2, hσ1, outSt, Function.update_of_ne hbc]
  have h3 : WXExec cap (.ifr B (emitO O CO true) (emitO O CO false)) σ2
      (outSt σ2 O CO (out ++ [true] ++ [decide (u % 2 = 1)]) L0) 8 := by
    by_cases hm : u % 2 = 1
    · have := emitO_spec cap σ2 (out ++ [true]) L0 true hO2 (by simp; omega)
      simpa [hm] using WXExec.ifrT (Q := emitO O CO false) (by rw [hB2]; omega) this
    · have := emitO_spec cap σ2 (out ++ [true]) L0 false hO2 (by simp; omega)
      simpa [hm] using WXExec.ifrF (P := emitO O CO true) (by rw [hB2]; omega) this
  set σ3 := outSt σ2 O CO (out ++ [true] ++ [decide (u % 2 = 1)]) L0 with hσ3
  have hB3 : σ3.val B = u % 2 := by simp [hσ3, outSt, Function.update_of_ne hbc, hB2]
  have h4 : WXExec cap (.ifr B (WMX.dec B) WMX.skip) σ3 (σ3.setv B 0) 2 := by
    by_cases hm : u % 2 = 1
    · have := WXExec.ifrT (Q := WMX.skip) (by rw [hB3]; omega) (WXExec.dec cap B σ3 (by rw [hB3]; omega))
      refine WXExec.cast cap this ?_ le_rfl
      rw [hB3, hm]
    · have hm0 : u % 2 = 0 := by omega
      have := WXExec.ifrF (P := WMX.dec B) (by rw [hB3]; omega) (WXExec.skip cap σ3)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      conv_lhs => rw [← wsetv_same σ3 B]
      rw [hB3, hm0]
  set σ4 := σ3.setv B 0 with hσ4
  have hY4 : σ4.val Y = u / 2 := by
    simp [hσ4, hσ3, hσ2, hσ1, outSt, Function.update_of_ne hyb, Function.update_of_ne hyc, hY]
  have hX4 : σ4.val X = 0 := by
    simp [hσ4, hσ3, hσ2, hσ1, outSt, Function.update_of_ne hxb, Function.update_of_ne hxc,
      Function.update_of_ne hxy]
  have h5 := WXExec.wm (cap := cap) (wmove_spec (cap := cap) Y X hxy.symm (u / 2) σ4 hY4 (by rw [hY4]; omega)
    (by rw [hY4, hX4]; omega))
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 h5)))) ?_
    le_rfl) (by omega)
  rw [hX4, hY4]
  apply WState.eq
  · funext j
    simp only [hσ4, hσ3, hσ2, hσ1, outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> simp_all
  · funext j
    simp only [hσ4, hσ3, hσ2, hσ1, outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all
  · funext j
    simp only [hσ4, hσ3, hσ2, hσ1, outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

/-- Append `frame (Nat.bits v)` for the value `v` of `X` (consumed; `Y`, `B` scratch, left `0`). -/
def emitBits (X Y B CO : Fin nr) (O : Fin (ns + 1)) : WMX ns nr :=
  .seq (.whr X (bitOut X Y B CO O)) (emitO O CO false)

/-- Cost of `emitBits` at value `v`. -/
def emitBitsCost (v : ℕ) : ℕ := (v + 1) * (13 * v + 52) + 10

theorem bits_length_le (v : ℕ) : v.bits.length ≤ v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp
    · rw [bits_eq_cons v (by omega), List.length_cons]
      have := ih (v / 2) (by omega)
      omega

/-- **`emitBits`**: appends `frame (Nat.bits v)` to `O`, sets `X` to `0`, changes nothing else. -/
theorem emitBits_exec (X Y B CO : Fin nr) (O : Fin (ns + 1)) (hr : ERegs X Y B CO) (v : ℕ) (σ : WState ns nr)
    (out L0 : List Bool) (hX : σ.val X = v) (hY : σ.val Y = 0) (hB : σ.val B = 0) (hO : OutOn σ O CO out L0)
    (hcap : out.length + 2 * v + 3 + v < cap) :
    WXExec cap (emitBits X Y B CO O) σ (outSt (σ.setv X 0) O CO (out ++ RepairOrdinary.frame v.bits) L0)
      (emitBitsCost v) := by
  let S : ℕ → List Bool → WState ns nr := fun u P => outSt (σ.setv X u) O CO (out ++ P) L0
  have hS0 : S v [] = σ := by
    apply WState.eq
    · funext j; simp only [S, outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp [hO.2.1]
    · funext j; simp only [S, outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp [hO.1]
    · funext j; simp only [S, outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [hO.2.2]
    · rfl
  let Inv : ℕ → WState ns nr → Prop := fun k τ =>
    ∃ u P, τ = S u P ∧ u.bits.length = k ∧ u ≤ v ∧ P ++ pairs u.bits = pairs v.bits
  have hloop := Runs.whr (cap := cap) (r := X) (P := bitOut X Y B CO O) Inv (13 * v + 50)
    (fun τ => τ = S 0 (pairs v.bits))
    (by
      rintro τ ⟨u, P, rfl, hk, _, hP⟩
      have hu : u = 0 := by
        by_contra hne
        rw [bits_eq_cons u hne] at hk
        simp at hk
      subst hu
      refine ⟨by simp [S, outSt, Function.update_of_ne hr.xc], ?_⟩
      have h0 : Nat.bits 0 = [] := rfl
      rw [h0] at hP
      simp only [pairs, List.flatMap_nil, List.append_nil] at hP
      simp only [pairs]
      rw [← hP])
    (by
      rintro k τ ⟨u, P, rfl, hk, huv, hP⟩
      have hu0 : u ≠ 0 := by
        rintro rfl
        simp at hk
      have hlen : (P ++ pairs u.bits).length = 2 * v.bits.length := by
        rw [hP]; simp [pairs]; omega
      have hPl : P.length ≤ 2 * v := by
        have := bits_length_le v
        simp at hlen
        omega
      refine ⟨by simpa [S, outSt, Function.update_of_ne hr.xc] using hu0, ?_⟩
      have hb := bitOut_exec (cap := cap) X Y B CO O hr u (S u P) (out ++ P) L0 (by simp [S, outSt, Function.update_of_ne hr.xc])
        (by simp [S, outSt, Function.update_of_ne hr.yc, Function.update_of_ne hr.xy.symm, hY])
        (by simp [S, outSt, Function.update_of_ne hr.bc, Function.update_of_ne hr.xb.symm, hB])
        (outOn_outSt _ _ _ _ _) (by omega) (by simp; omega)
      refine ⟨_, WXExec.mono hb (by omega), u / 2, P ++ [true, decide (u % 2 = 1)], ?_, ?_, by omega, ?_⟩
      · apply WState.eq
        · funext j; simp only [S, outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
          split_ifs <;> simp_all
        · funext j; simp only [S, outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
          split_ifs <;> simp_all
        · funext j; simp only [S, outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
          split_ifs <;> subst_vars <;> simp_all
        · rfl
      · rw [bits_eq_cons u hu0, List.length_cons] at hk; omega
      · rw [← hP, bits_eq_cons u hu0, pairs_cons]; simp)
    v.bits.length σ ⟨v, [], hS0.symm, rfl, le_rfl, by simp⟩
  obtain ⟨τ, e1, rfl⟩ := hloop
  have hlenP : (pairs v.bits).length ≤ 2 * v := by
    have := bits_length_le v
    simp [pairs]; omega
  have h2 := emitO_spec cap (S 0 (pairs v.bits)) (out ++ pairs v.bits) L0 false (outOn_outSt _ _ _ _ _)
    (by simp; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 h2) ?_ le_rfl) ?_
  · apply WState.eq
    · funext j; simp only [S, outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> simp_all [frame_eq_pairs]
    · funext j; simp only [S, outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> simp_all [frame_eq_pairs]
    · funext j; simp only [S, outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [frame_eq_pairs]
    · rfl
  · have := bits_length_le v
    unfold emitBitsCost
    nlinarith

end NearCubicGates.Close.ENP

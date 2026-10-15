import Proof.Gates.Expand.OpsF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)

variable {ns nr : ℕ}

/-- One value record against the current set: the accumulator's update. -/
def mobStep (Mw MH TMv sM pS acc v : ℕ) : ℕ :=
  if (v &&& MH) = (v &&& MH) &&& sM then
    if (v &&& TMv) = pS then (acc + (v &&& Mw)) &&& Mw else (acc + (Mw - (v &&& Mw) + 1)) &&& Mw
  else acc

section Prog
variable (MB : Fin 18 ↪ Fin (ns + 1)) (F R : Fin nr)

def termAdd : WMX ns nr :=
  .seq (BinW.copy (MB 7) (MB 1) F R) (.seq (andX (MB 7) (MB 11) F R) (.seq (BinW.copy (MB 8) (MB 1) F R)
    (.seq (andX (MB 8) (MB 12) F R) (.seq (BinW.eq (MB 7) (MB 3) F R)
      (.ifr F (.seq (WMX.dec F) (.seq (BinW.add (MB 4) (MB 8) F R) (andX (MB 4) (MB 12) F R)))
        (.seq (BinW.copy (MB 6) (MB 12) F R) (.seq (BinW.sub (MB 6) (MB 8) F R) (.seq (BinW.inc (MB 6) (MB 14) F R)
          (.seq (BinW.add (MB 4) (MB 6) F R) (andX (MB 4) (MB 12) F R))))))))))

def mobInner : WMX ns nr :=
  .seq (BinW.copy (MB 5) (MB 1) F R) (.seq (andX (MB 5) (MB 10) F R) (.seq (BinW.copy (MB 6) (MB 5) F R)
    (.seq (andX (MB 6) (MB 2) F R) (.seq (BinW.eq (MB 5) (MB 6) F R)
      (.ifr F (.seq (WMX.dec F) (termAdd MB F R)) WMX.skip)))))

end Prog

def termAddCost (Wb : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 7) + 1 +
    ((205 * Wb + 29) + 1)))))

def mobInnerCost (Wb : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 7) + 1 +
    ((1 + 1 + termAddCost Wb) + 1)))))

section Spec
variable {MB : Fin 18 ↪ Fin (ns + 1)} {F R : Fin nr}

/-- What the Möbius loops keep on the block's values. -/
structure MOK (Wb : ℕ) (v : Fin 18 → ℕ) : Prop where
  lt : ∀ i, v i < 2 ^ Wb
  mw : 2 * (v 12 + 1) ≤ 2 ^ Wb
  acc : v 4 ≤ v 12
  one : v 14 = 1

theorem MOK.upd {Wb : ℕ} {v : Fin 18 → ℕ} (h : MOK Wb v) (i : Fin 18) (hi : i ≠ 4 ∧ i ≠ 12 ∧ i ≠ 14) (x : ℕ)
    (hx : x < 2 ^ Wb) : MOK Wb (Function.update v i x) := by
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩
  · by_cases e : j = i
    · subst e; simpa using hx
    · rw [Function.update_of_ne e]; exact h.lt j
  · rw [Function.update_of_ne (Ne.symm hi.2.1)]; exact h.mw
  · rw [Function.update_of_ne (Ne.symm hi.1), Function.update_of_ne (Ne.symm hi.2.1)]; exact h.acc
  · rw [Function.update_of_ne (Ne.symm hi.2.2)]; exact h.one

theorem and_lt {x y W : ℕ} (hy : y < 2 ^ W) : x &&& y < 2 ^ W := lt_of_le_of_lt Nat.and_le_right hy

theorem termAdd_spec (cap Wb : ℕ) (σ : WState ns nr) (v : Fin 18 → ℕ) (h : MV MB Wb v σ) (hok : MOK Wb v)
    (hFR : F ≠ R) (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (termAdd MB F R) σ (termAddCost Wb) (fun τ => ∃ w, MV MB Wb w τ ∧ MOK Wb w ∧
      w 4 = (if (v 1 &&& v 11) = v 3 then (v 4 + (v 1 &&& v 12)) &&& v 12
        else (v 4 + (v 12 - (v 1 &&& v 12) + 1)) &&& v 12) ∧
      (∀ i : Fin 18, i ≠ 4 → i ≠ 6 → i ≠ 7 → i ≠ 8 → w i = v i) ∧ τ.val F = 0 ∧ τ.val R = 0 ∧
      SameExcept σ τ [MB 4, MB 6, MB 7, MB 8] [F]) := by
  have hc := hcap
  refine Runs.seq (mCopy cap Wb 7 1 (by decide) hFR h hF hR hc) (fun τ1 ⟨h1, f1⟩ => ?_)
  have ok1 := hok.upd 7 (by decide) (v 1) (hok.lt 1)
  refine Runs.seq (mAnd cap Wb 7 11 (by decide) hFR h1 (by rw [f1.val (by simp)]; exact hF)
    (by rw [f1.val (by simp)]; exact hR) hc) (fun τ2 ⟨h2, f2⟩ => ?_)
  set v2 := Function.update (Function.update v 7 (v 1)) 7 (Function.update v 7 (v 1) 7 &&& Function.update v 7 (v 1) 11)
    with hv2
  have ok2 : MOK Wb v2 := ok1.upd 7 (by decide) _ (and_lt (by simpa using hok.lt 11))
  have f12 : SameExcept σ τ2 [MB 7] [] := SameExcept.trans f1 f2
  refine Runs.seq (mCopy cap Wb 8 1 (by decide) hFR h2 (by rw [f12.val (by simp)]; exact hF)
    (by rw [f12.val (by simp)]; exact hR) hc) (fun τ3 ⟨h3, f3⟩ => ?_)
  have ok3 := ok2.upd 8 (by decide) (v2 1) (ok2.lt 1)
  refine Runs.seq (mAnd cap Wb 8 12 (by decide) hFR h3 (by rw [f3.val (by simp), f12.val (by simp)]; exact hF)
    (by rw [f3.val (by simp), f12.val (by simp)]; exact hR) hc) (fun τ4 ⟨h4, f4⟩ => ?_)
  set v4 := Function.update (Function.update v2 8 (v2 1)) 8 (Function.update v2 8 (v2 1) 8 &&& Function.update v2 8 (v2 1) 12)
    with hv4
  have ok4 : MOK Wb v4 := ok3.upd 8 (by decide) _ (and_lt (by simpa [hv2] using hok.lt 12))
  have f14 : SameExcept σ τ4 [MB 7, MB 8] [] := SameExcept.trans (SameExcept.trans (se_sub f12 (by simp) (by simp))
    (se_sub f3 (by simp) (by simp))) (se_sub f4 (by simp) (by simp))
  have hF4 : τ4.val F = 0 := by rw [f14.val (by simp)]; exact hF
  have hR4 : τ4.val R = 0 := by rw [f14.val (by simp)]; exact hR
  have e7 : v4 7 = v 1 &&& v 11 := by simp [hv4, hv2]
  have e8 : v4 8 = v 1 &&& v 12 := by simp [hv4, hv2]
  have e3 : v4 3 = v 3 := by simp [hv4, hv2]
  have e4 : v4 4 = v 4 := by simp [hv4, hv2]
  have e12 : v4 12 = v 12 := by simp [hv4, hv2]
  have e14 : v4 14 = v 14 := by simp [hv4, hv2]
  refine Runs.seq (mEq cap Wb 7 3 (by decide) hFR h4 hF4 hR4 (ok4.lt 7) (ok4.lt 3) hc)
    (fun τ5 ⟨h5, hF5, f5⟩ => ?_)
  have hR5 : τ5.val R = 0 := by rw [f5.val (by simp [Ne.symm hFR])]; exact hR4
  have hmw : 2 * (v 12 + 1) ≤ 2 ^ Wb := hok.mw
  have hf8 : v 1 &&& v 12 ≤ v 12 := Nat.and_le_right
  refine Runs.ifr (fun hne => ?_) (fun h0 => ?_)
  · -- same parity: ACC := (ACC + FV) mod M
    have heq : (v 1 &&& v 11) = v 3 := by
      by_contra hc'; rw [hF5, e7, e3] at hne; simp [hc'] at hne
    refine (Runs.seq (c2 := (41 * Wb + 3) + 1 + (41 * Wb + 3))
      (fDec1 (r := F) cap τ5 (by rw [hF5, e7, e3]; simp [heq]) (by omega)) (fun τ6 ⟨hF6, f6⟩ => ?_)).cost (by omega)
    have hR6 : τ6.val R = 0 := by rw [f6.val (by simp [Ne.symm hFR])]; exact hR5
    have h6 := h5.frame f6
    refine Runs.seq (mAdd cap Wb 4 8 (by decide) hFR h6 hF6 hR6 (by rw [e4, e8]; have := hok.acc; omega) hc)
      (fun τ7 ⟨h7, f7⟩ => ?_)
    refine (mAnd cap Wb 4 12 (by decide) hFR h7 (by rw [f7.val (by simp)]; exact hF6)
      (by rw [f7.val (by simp)]; exact hR6) hc).post (fun τ8 ⟨h8, f8⟩ => ⟨_, h8, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · refine ⟨fun j => ?_, by simpa [hv4, hv2] using hmw, ?_, by simp [hv4, hv2, hok.one]⟩
      · by_cases e : j = 4
        · subst e; simp only [Function.update_self]; exact and_lt (by simpa [hv4, hv2] using hok.lt 12)
        · rw [Function.update_of_ne e]; by_cases e' : j = 4
          · exact absurd e' e
          · rw [Function.update_of_ne e']; exact ok4.lt j
      · simp only [Function.update_self, Function.update_of_ne (by decide : (12 : Fin 18) ≠ 4)]
        exact Nat.and_le_right
    · simp [e4, e8, e12, heq]
    · intro i i4 i6 i7 i8
      simp [Function.update_of_ne i4, hv4, hv2, Function.update_of_ne i7, Function.update_of_ne i8]
    · rw [f8.val (by simp)]; rw [f7.val (by simp)]; exact hF6
    · rw [f8.val (by simp), f7.val (by simp)]; exact hR6
    · exact SameExcept.trans (SameExcept.trans (SameExcept.trans (SameExcept.trans (se_sub f14 (by simp [List.cons_subset])
        (by simp)) (se_sub f5 (by simp) (by simp))) (se_sub f6 (by simp) (by simp)))
        (se_sub f7 (by simp [List.cons_subset]) (by simp))) (se_sub f8 (by simp [List.cons_subset]) (by simp))
  · -- different parity: ACC := (ACC + (M − FV)) mod M
    have hne : ¬ (v 1 &&& v 11) = v 3 := by
      intro hc'; rw [hF5, e7, e3] at h0; simp [hc'] at h0
    have h50 : τ5.val F = 0 := h0
    refine (Runs.seq (c2 := (41 * Wb + 9) + 1 + ((41 * Wb + 7) + 1 + ((41 * Wb + 3) + 1 + (41 * Wb + 3))))
      (mCopy cap Wb 6 12 (by decide) hFR h5 h50 hR5 hc) (fun τ6 ⟨h6, f6⟩ => ?_)).cost (by omega)
    refine Runs.seq (mSub cap Wb 6 8 (by decide) hFR h6 (by rw [f6.val (by simp)]; exact h50)
      (by rw [f6.val (by simp)]; exact hR5) (by simp [e8, e12]; exact hf8) (by simp [e12]; omega) hc)
      (fun τ7 ⟨h7, f7⟩ => ?_)
    have f67 : SameExcept τ5 τ7 [MB 6] [] := SameExcept.trans f6 f7
    refine Runs.seq (mInc cap Wb 6 14 (by decide) hFR h7 (by rw [f67.val (by simp)]; exact h50)
      (by rw [f67.val (by simp)]; exact hR5) (by simp [e8, e12]; omega) hc) (fun τ8 ⟨h8, f8⟩ => ?_)
    have f68 : SameExcept τ5 τ8 [MB 6] [] := SameExcept.trans f67 f8
    refine Runs.seq (mAdd cap Wb 4 6 (by decide) hFR h8 (by rw [f68.val (by simp)]; exact h50)
      (by rw [f68.val (by simp)]; exact hR5) (by simp [e4, e8, e12]; have := hok.acc; omega) hc)
      (fun τ9 ⟨h9, f9⟩ => ?_)
    refine (mAnd cap Wb 4 12 (by decide) hFR h9 (by rw [f9.val (by simp), f68.val (by simp)]; exact h50)
      (by rw [f9.val (by simp), f68.val (by simp)]; exact hR5) hc).post (fun τ10 ⟨h10, f10⟩ => ⟨_, h10, ?_, ?_, ?_, ?_, ?_,
        ?_⟩)
    · refine ⟨fun j => ?_, by simpa [hv4, hv2] using hmw, ?_, by simp [hv4, hv2, hok.one]⟩
      · by_cases e : j = 4
        · subst e; simp only [Function.update_self]; exact and_lt (by simpa [hv4, hv2] using hok.lt 12)
        · rw [Function.update_of_ne e]
          by_cases e6 : j = 6
          · subst e6; simp [e8, e12]; omega
          · simp only [Function.update_of_ne e, Function.update_of_ne e6]; exact ok4.lt j
      · simp only [Function.update_self, Function.update_of_ne (by decide : (12 : Fin 18) ≠ 4),
          Function.update_of_ne (by decide : (12 : Fin 18) ≠ 6)]
        exact Nat.and_le_right
    · simp [e4, e8, e12, hne]
    · intro i i4 i6 i7 i8
      simp [Function.update_of_ne i4, Function.update_of_ne i6, hv4, hv2, Function.update_of_ne i7,
        Function.update_of_ne i8]
    · rw [f10.val (by simp), f9.val (by simp), f68.val (by simp)]; exact h50
    · rw [f10.val (by simp), f9.val (by simp), f68.val (by simp)]; exact hR5
    · exact SameExcept.trans (SameExcept.trans (SameExcept.trans (se_sub f14 (by simp [List.cons_subset]) (by simp))
        (se_sub f5 (by simp) (by simp))) (se_sub f68 (by simp [List.cons_subset]) (by simp)))
        (SameExcept.trans (se_sub f9 (by simp [List.cons_subset]) (by simp)) (se_sub f10 (by simp [List.cons_subset]) (by simp)))

/-- **One value record** against the current set. -/
theorem mobInner_spec (cap Wb : ℕ) (σ : WState ns nr) (v : Fin 18 → ℕ) (h : MV MB Wb v σ) (hok : MOK Wb v)
    (hFR : F ≠ R) (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (mobInner MB F R) σ (mobInnerCost Wb) (fun τ => ∃ w, MV MB Wb w τ ∧ MOK Wb w ∧
      w 4 = mobStep (v 12) (v 10) (v 11) (v 2) (v 3) (v 4) (v 1) ∧
      (∀ i : Fin 18, i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 8 → w i = v i) ∧ τ.val F = 0 ∧ τ.val R = 0 ∧
      SameExcept σ τ [MB 4, MB 5, MB 6, MB 7, MB 8] [F]) := by
  have hc := hcap
  refine Runs.seq (mCopy cap Wb 5 1 (by decide) hFR h hF hR hc) (fun τ1 ⟨h1, f1⟩ => ?_)
  have ok1 := hok.upd 5 (by decide) (v 1) (hok.lt 1)
  refine Runs.seq (mAnd cap Wb 5 10 (by decide) hFR h1 (by rw [f1.val (by simp)]; exact hF)
    (by rw [f1.val (by simp)]; exact hR) hc) (fun τ2 ⟨h2, f2⟩ => ?_)
  set v2 := Function.update (Function.update v 5 (v 1)) 5 (Function.update v 5 (v 1) 5 &&& Function.update v 5 (v 1) 10)
    with hv2
  have ok2 : MOK Wb v2 := ok1.upd 5 (by decide) _ (and_lt (by simpa using hok.lt 10))
  have f12 : SameExcept σ τ2 [MB 5] [] := SameExcept.trans f1 f2
  refine Runs.seq (mCopy cap Wb 6 5 (by decide) hFR h2 (by rw [f12.val (by simp)]; exact hF)
    (by rw [f12.val (by simp)]; exact hR) hc) (fun τ3 ⟨h3, f3⟩ => ?_)
  have ok3 := ok2.upd 6 (by decide) (v2 5) (ok2.lt 5)
  refine Runs.seq (mAnd cap Wb 6 2 (by decide) hFR h3 (by rw [f3.val (by simp), f12.val (by simp)]; exact hF)
    (by rw [f3.val (by simp), f12.val (by simp)]; exact hR) hc) (fun τ4 ⟨h4, f4⟩ => ?_)
  set v4 := Function.update (Function.update v2 6 (v2 5)) 6 (Function.update v2 6 (v2 5) 6 &&& Function.update v2 6 (v2 5) 2)
    with hv4
  have ok4 : MOK Wb v4 := ok3.upd 6 (by decide) _ (and_lt (by simpa [hv2] using hok.lt 2))
  have f14 : SameExcept σ τ4 [MB 5, MB 6] [] := SameExcept.trans (SameExcept.trans (se_sub f12 (by simp) (by simp))
    (se_sub f3 (by simp) (by simp))) (se_sub f4 (by simp) (by simp))
  have hF4 : τ4.val F = 0 := by rw [f14.val (by simp)]; exact hF
  have hR4 : τ4.val R = 0 := by rw [f14.val (by simp)]; exact hR
  have e5 : v4 5 = v 1 &&& v 10 := by simp [hv4, hv2]
  have e6 : v4 6 = (v 1 &&& v 10) &&& v 2 := by simp [hv4, hv2]
  have eo : ∀ i : Fin 18, i ≠ 5 → i ≠ 6 → v4 i = v i := by
    intro i i5 i6; simp [hv4, hv2, Function.update_of_ne i5, Function.update_of_ne i6]
  refine Runs.seq (mEq cap Wb 5 6 (by decide) hFR h4 hF4 hR4 (ok4.lt 5) (ok4.lt 6) hc)
    (fun τ5 ⟨h5, hF5, f5⟩ => ?_)
  have hR5 : τ5.val R = 0 := by rw [f5.val (by simp [Ne.symm hFR])]; exact hR4
  refine Runs.ifr (fun hne => ?_) (fun h0 => ?_)
  · have heq : (v 1 &&& v 10) = (v 1 &&& v 10) &&& v 2 := by
      by_contra hc'; rw [hF5, e5, e6] at hne; simp [hc'] at hne
    refine Runs.seq (fDec1 (r := F) cap τ5 (by rw [hF5, e5, e6, decide_eq_true heq]; rfl) (by omega))
      (fun τ6 ⟨hF6, f6⟩ => ?_)
    have hR6 : τ6.val R = 0 := by rw [f6.val (by simp [Ne.symm hFR])]; exact hR5
    refine (termAdd_spec cap Wb τ6 v4 (h5.frame f6) ok4 hFR hF6 hR6 hc).post (fun τ7 ⟨w, hw, okw, hw4, hwo, hF7, hR7, f7⟩ =>
      ⟨w, hw, okw, ?_, ?_, hF7, hR7, ?_⟩)
    · rw [hw4]; unfold mobStep
      rw [if_pos heq]
      simp only [eo 1 (by decide) (by decide), eo 11 (by decide) (by decide), eo 3 (by decide) (by decide),
        eo 4 (by decide) (by decide), eo 12 (by decide) (by decide)]
    · intro i i4 i5 i6 i7 i8; rw [hwo i i4 i6 i7 i8, eo i i5 i6]
    · exact SameExcept.trans (SameExcept.trans (SameExcept.trans (se_sub f14 (by simp [List.cons_subset]) (by simp))
        (se_sub f5 (by simp) (by simp))) (se_sub f6 (by simp) (by simp))) (se_sub f7 (by simp [List.cons_subset]) (by simp))
  · have hne : ¬ (v 1 &&& v 10) = (v 1 &&& v 10) &&& v 2 := by
      intro hc'; rw [hF5, e5, e6, decide_eq_true hc'] at h0; simp at h0
    refine (Runs.of (WXExec.skip cap τ5) ⟨v4, h5, ok4, ?_, ?_, h0, hR5, ?_⟩).cost (by omega)
    · rw [eo 4 (by decide) (by decide)]; unfold mobStep; rw [if_neg hne]
    · intro i i4 i5 i6 i7 i8; exact eo i i5 i6
    · exact SameExcept.trans (se_sub f14 (by simp [List.cons_subset]) (by simp)) (se_sub f5 (by simp) (by simp))

end Spec

end NearCubicGates.Close.Expand

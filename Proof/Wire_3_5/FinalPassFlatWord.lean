import Proof.Wire_3_5.FinalPassWordAux

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

variable {ns nr : ℕ} (cap : ℕ)

/-- One bit: step onto the bits, copy, step onto the next markers, count `B`'s two cells. -/
def fcStep (A B : Fin (ns + 1)) (C PC : Fin nr) : WM ns nr :=
  .seq (.fwd B) (.seq (.inc PC) (.seq (.fwd A) (.seq (.ifs B (.wr A true) (.wr A false)) (.seq (.fwd B)
    (.seq (.inc PC) (.seq (.fwd A) (.dec C)))))))

/-- Copy `C` bits of `B` onto `A`. -/
def fcLoop (A B : Fin (ns + 1)) (C PC : Fin nr) : WM ns nr := .whr C (fcStep A B C PC)

theorem frameP_append' (l l' : List Bool) : frameP (l ++ l') = frameP l ++ frameP l' := by
  simp [frameP, List.flatMap_append]

/-- **The counted copy**: the first `n` bits of `A`'s word (after `preA`) become `B`'s next `n` bits. -/
theorem fcLoop_spec (A B : Fin (ns + 1)) (C PC : Fin nr) (hAB : A ≠ B) (hCP : C ≠ PC) :
    ∀ (n : ℕ) (ws bs preA preB restA restB : List Bool) (σ : WState ns nr),
      σ.val C = n → n ≤ ws.length → n ≤ bs.length →
      σ.st A = preA ++ frameP ws ++ restA → σ.sh A = preA.length →
      σ.st B = preB ++ frameP bs ++ restB → σ.sh B = preB.length →
      σ.val PC + 2 * n ≤ cap → n ≤ cap →
      ∃ τ, WExec cap (fcLoop A B C PC) σ τ (22 * n + 1) ∧
        τ.st A = preA ++ frameP (bs.take n ++ ws.drop n) ++ restA ∧ τ.sh A = preA.length + 2 * n ∧
        τ.st B = σ.st B ∧ τ.sh B = preB.length + 2 * n ∧ τ.val PC = σ.val PC + 2 * n ∧ τ.val C = 0 ∧
        WFrame (fun i => i = A ∨ i = B) (fun r => r = C ∨ r = PC) σ τ
  | 0, ws, bs, preA, preB, restA, restB, σ, hC, _, _, hA, hhA, _, hhB, _, _ => by
    refine ⟨σ, WExec.whrF hC, by simpa using hA, by simpa using hhA, rfl, by simp [hhB], by simp, hC,
      WFrame.refl _ _ σ⟩
  | n + 1, ws, bs, preA, preB, restA, restB, σ, hC, hw, hb, hA, hhA, hB, hhB, hP, hn => by
    obtain ⟨b0, bs', rfl⟩ : ∃ b0 bs', bs = b0 :: bs' := by
      cases bs with
      | nil => simp at hb
      | cons b0 bs' => exact ⟨b0, bs', rfl⟩
    obtain ⟨w0, ws', rfl⟩ : ∃ w0 ws', ws = w0 :: ws' := by
      cases ws with
      | nil => simp at hw
      | cons w0 ws' => exact ⟨w0, ws', rfl⟩
    simp only [List.length_cons] at hb hw
    have hAB' := Ne.symm hAB
    have hCP' := Ne.symm hCP
    -- forward on B, count
    have s1 := WExec.fwd (cap := cap) B σ
    have s2 := WExec.inc (cap := cap) PC (σ.seth B (σ.sh B + 1)) (by simp; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr, τ = (σ.seth B (preB.length + 1)).setv PC (σ.val PC + 1) := ⟨_, rfl⟩
    have s2' : WExec cap (.inc PC) (σ.seth B (σ.sh B + 1)) σ2 3 := by rw [hσ2, ← hhB]; simpa using s2
    -- forward on A
    have s3 := WExec.fwd (cap := cap) A σ2
    obtain ⟨σ3, hσ3⟩ : ∃ τ : WState ns nr, τ = σ2.seth A (preA.length + 1) := ⟨_, rfl⟩
    have s3' : WExec cap (.fwd A) σ2 σ3 1 := by
      rw [hσ3]
      have e : σ2.sh A = preA.length := by rw [hσ2]; simp [Function.update_of_ne hAB, hhA]
      rw [← e]; exact s3
    -- copy the bit
    have hread : wbit σ3 B = b0 := by
      unfold wbit
      have e1 : σ3.st B = (preB ++ [true]) ++ b0 :: (frameP bs' ++ restB) := by
        rw [hσ3, hσ2]; simp [hB]
      have e2 : σ3.sh B = (preB ++ [true]).length := by
        rw [hσ3, hσ2]; simp [Function.update_of_ne hAB']
      rw [e1, e2, readTapeBit_mid]
    have hA3 : σ3.st A = (preA ++ [true]) ++ w0 :: (frameP ws' ++ restA) := by rw [hσ3, hσ2]; simp [hA]
    have hhA3 : σ3.sh A = (preA ++ [true]).length := by rw [hσ3]; simp
    obtain ⟨σ4, hσ4⟩ : ∃ τ : WState ns nr, τ = σ3.sets A ((preA ++ [true]) ++ b0 :: (frameP ws' ++ restA)) := ⟨_, rfl⟩
    have s4 : WExec cap (.ifs B (.wr A true) (.wr A false)) σ3 σ4 2 := by
      have hw' := WExec.wr (cap := cap) A b0 σ3
      rw [hA3, hhA3, writeTapeBit_mid', ← hσ4] at hw'
      cases b0
      · exact WExec.ifsF hread hw'
      · exact WExec.ifsT hread hw'
    -- forward on B, count
    have s5 := WExec.fwd (cap := cap) B σ4
    have s6 := WExec.inc (cap := cap) PC (σ4.seth B (σ4.sh B + 1)) (by rw [hσ4, hσ3, hσ2]; simp; omega)
    obtain ⟨σ6, hσ6⟩ : ∃ τ : WState ns nr, τ = (σ4.seth B (preB.length + 2)).setv PC (σ.val PC + 2) := ⟨_, rfl⟩
    have s6' : WExec cap (.inc PC) (σ4.seth B (σ4.sh B + 1)) σ6 3 := by
      have e1 : σ4.sh B = preB.length + 1 := by rw [hσ4, hσ3, hσ2]; simp [Function.update_of_ne hAB']
      have e2 : σ4.val PC = σ.val PC + 1 := by rw [hσ4, hσ3, hσ2]; simp
      rw [hσ6]; simpa [e1, e2] using s6
    -- forward on A, count down
    have s7 := WExec.fwd (cap := cap) A σ6
    obtain ⟨σ7, hσ7⟩ : ∃ τ : WState ns nr, τ = σ6.seth A (preA.length + 2) := ⟨_, rfl⟩
    have s7' : WExec cap (.fwd A) σ6 σ7 1 := by
      have e : σ6.sh A = preA.length + 1 := by rw [hσ6, hσ4, hσ3]; simp [Function.update_of_ne hAB]
      rw [hσ7, show preA.length + 2 = σ6.sh A + 1 by omega]; exact s7
    have s8 := WExec.dec (cap := cap) C σ7 (by rw [hσ7, hσ6, hσ4, hσ3, hσ2]; simp [Function.update_of_ne hCP]; omega)
    obtain ⟨σ8, hσ8⟩ : ∃ τ : WState ns nr, τ = σ7.setv C n := ⟨_, rfl⟩
    have s8' : WExec cap (.dec C) σ7 σ8 1 := by
      have e : σ7.val C = n + 1 := by rw [hσ7, hσ6, hσ4, hσ3, hσ2]; simp [Function.update_of_ne hCP, hC]
      rw [hσ8]; simpa [e] using s8
    -- the rest of the copy
    obtain ⟨τ, hτ, h1, h2, h3, h4, h5, h6, hf⟩ := fcLoop_spec A B C PC hAB hCP n ws' bs' (preA ++ [true, b0])
      (preB ++ [true, b0]) restA restB σ8 (by rw [hσ8]; simp) (by omega) (by omega)
      (by rw [hσ8, hσ7, hσ6, hσ4]; simp)
      (by rw [hσ8, hσ7]; simp)
      (by rw [hσ8, hσ7, hσ6, hσ4, hσ3, hσ2]; simp [Function.update_of_ne hAB', hB])
      (by rw [hσ8, hσ7, hσ6]; simp [Function.update_of_ne hAB'])
      (by rw [hσ8, hσ7, hσ6]; simp [Function.update_of_ne hCP']; omega) (by omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2' (WExec.seq s3' (WExec.seq s4
      (WExec.seq s5 (WExec.seq s6' (WExec.seq s7' s8'))))))) hτ) (by omega), ?_, ?_, ?_, ?_, ?_, h6, ?_⟩
    · rw [h1]; simp [List.take_succ_cons, List.drop_succ_cons]
    · rw [h2]; simp; omega
    · rw [h3, hσ8, hσ7, hσ6, hσ4, hσ3, hσ2]; simp [Function.update_of_ne hAB']
    · rw [h4]; simp; omega
    · rw [h5, hσ8, hσ7, hσ6]; simp [Function.update_of_ne hCP']; omega
    · refine WFrame.trans ?_ hf
      refine ⟨fun i hi => ?_, fun r hr => ?_, ?_⟩
      · have hiA : i ≠ A := fun h => hi (Or.inl h)
        have hiB : i ≠ B := fun h => hi (Or.inr h)
        rw [hσ8, hσ7, hσ6, hσ4, hσ3, hσ2]
        simp [Function.update_of_ne hiA, Function.update_of_ne hiB]
      · have hrC : r ≠ C := fun h => hr (Or.inl h)
        have hrP : r ≠ PC := fun h => hr (Or.inr h)
        rw [hσ8, hσ7, hσ6, hσ4, hσ3, hσ2]
        simp [Function.update_of_ne hrC, Function.update_of_ne hrP]
      · rw [hσ8, hσ7, hσ6, hσ4, hσ3, hσ2]; rfl

/-- A state that agrees with `σ` off two streams and two registers is the update of `σ` on them. -/
theorem wframe_eq (σ τ : WState ns nr) (A B : Fin (ns + 1)) (C PC : Fin nr) (hAB : A ≠ B) (hCP : C ≠ PC)
    (sa sb : List Bool) (ha hb vc vp : ℕ) (hf : WFrame (fun i => i = A ∨ i = B) (fun r => r = C ∨ r = PC) σ τ)
    (h1 : τ.st A = sa) (h2 : τ.sh A = ha) (h3 : τ.st B = sb) (h4 : τ.sh B = hb) (h5 : τ.val C = vc)
    (h6 : τ.val PC = vp) :
    τ = (((((σ.sets A sa).sets B sb).seth A ha).seth B hb).setv C vc).setv PC vp := by
  refine WState.eq ?_ ?_ ?_ ?_
  · funext i
    simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    by_cases hB : i = B
    · subst hB; simp [h4]
    · by_cases hA : i = A
      · subst hA; simp [hB, h2]
      · simp only [hA, hB, if_false]
        exact (hf.1 i (by rintro (h | h) <;> contradiction)).2
  · funext i
    simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    by_cases hB : i = B
    · subst hB; simp [h3]
    · by_cases hA : i = A
      · subst hA; simp [hB, h1]
      · simp only [hA, hB, if_false]
        exact (hf.1 i (by rintro (h | h) <;> contradiction)).1
  · funext r
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases hP : r = PC
    · subst hP; simp [h6]
    · by_cases hC : r = C
      · subst hC; simp [hP, h5]
      · simp only [hC, hP, if_false]
        exact hf.2.1 r (by rintro (h | h) <;> contradiction)
  · simp [hf.2.2]

end NearCubicWires.WireExponent3_5.FinalPass.Tm

import Proof.Gates.Codec.FieldGate

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Codec

variable {ns nr : ℕ} {cap : ℕ}

/-- While `T ≠ 0`: decrement `T`, then decrement `D` if it is nonzero, else increment `F`. -/
def ltSubLoop (D F T : Fin nr) : WM ns nr := .whr T (.seq (.dec T) (.ifr D (.dec D) (.inc F)))

theorem ltSubLoop_spec (D F T : Fin nr) (hDF : D ≠ F) (hDT : D ≠ T) (hFT : F ≠ T) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val T = m → m ≤ cap → σ.val F + m ≤ cap → σ.val D ≤ cap →
      WExec cap (ltSubLoop D F T) σ
        (((σ.setv T 0).setv D (σ.val D - m)).setv F (σ.val F + (m - σ.val D))) (8 * m + 1)
  | 0, σ, h0, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    apply WState.eq <;> try rfl
    funext r; simp only [WState.setv_val, Function.update_apply]
    split_ifs with h1 h2 h3 <;> subst_vars <;> simp [h0]
  | m + 1, σ, hm, hc, hF, hDc => by
    have e1 := WExec.dec (cap := cap) T σ (by omega)
    set σ1 := σ.setv T (σ.val T - 1) with hσ1
    have hD1 : σ1.val D = σ.val D := by simp [hσ1, Function.update_of_ne hDT]
    by_cases hD : σ.val D = 0
    · have e2 := WExec.inc (cap := cap) F σ1 (by simp [hσ1, Function.update_of_ne hFT]; omega)
      set σ2 := σ1.setv F (σ1.val F + 1) with hσ2
      have hrest := ltSubLoop_spec D F T hDF hDT hFT m σ2
        (by simp [hσ2, hσ1, Function.update_apply, hFT, Ne.symm hFT]; omega) (by omega)
        (by simp [hσ2, hσ1, Function.update_apply, hFT, Ne.symm hFT]; omega)
        (by simp [hσ2, hσ1, Function.update_apply, hDF, hDT]; omega)
      refine WExec.cast cap (WExec.whrT (by omega)
        (WExec.seq e1 (WExec.ifrF (by rw [hD1]; exact hD) e2)) hrest) ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r
      simp only [hσ2, hσ1, WState.setv_val, Function.update_apply]
      by_cases hr : r = F
      · subst hr; simp [hDF, Ne.symm hDF, hFT, Ne.symm hFT, hDT, Ne.symm hDT, hD]; omega
      by_cases hr' : r = D
      · subst hr'; simp [hDF, hDT, hD]
      by_cases hr'' : r = T
      · subst hr''; simp [hr, hr', Ne.symm hDT, Ne.symm hFT]
      · simp [hr, hr', hr'']
    · have e2 := WExec.dec (cap := cap) D σ1 (by rw [hD1]; exact hDc)
      set σ2 := σ1.setv D (σ1.val D - 1) with hσ2
      have hrest := ltSubLoop_spec D F T hDF hDT hFT m σ2
        (by simp [hσ2, hσ1, Function.update_apply, hDT, Ne.symm hDT]; omega) (by omega)
        (by simp [hσ2, hσ1, Function.update_apply, hDF, Ne.symm hDF, hFT, Ne.symm hFT]; omega)
        (by simp [hσ2, hσ1, Function.update_apply, hDT]; omega)
      refine WExec.cast cap (WExec.whrT (by omega)
        (WExec.seq e1 (WExec.ifrT (by rw [hD1]; exact hD) e2)) hrest) ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r
      simp only [hσ2, hσ1, WState.setv_val, Function.update_apply]
      by_cases hr : r = F
      · subst hr; simp [hDF, Ne.symm hDF, hFT, Ne.symm hFT, hDT, Ne.symm hDT, hD]; omega
      by_cases hr' : r = D
      · subst hr'; simp [hDF, hDT, hD]; omega
      by_cases hr'' : r = T
      · subst hr''; simp [hr, hr', Ne.symm hDT, Ne.symm hFT]
      · simp [hr, hr', hr'']

/-- `D := A − B`, `F := B − A` (truncated); `A`, `B` kept; scratch `T`, `X` at `0` before and after. -/
def ltSubW (A B D F T X : Fin nr) : WM ns nr :=
  .seq (dupR A D X) (.seq (dupR B T X) (ltSubLoop D F T))

theorem ltSubW_spec (A B D F T X : Fin nr) (hr : [A, B, D, F, T, X].Nodup) (σ : WState ns nr)
    (hD : σ.val D = 0) (hF : σ.val F = 0) (hT : σ.val T = 0) (hX : σ.val X = 0)
    (hc : σ.val A + σ.val B ≤ cap) :
    WExec cap (ltSubW A B D F T X) σ ((σ.setv D (σ.val A - σ.val B)).setv F (σ.val B - σ.val A))
      (18 * σ.val A + 3 + 1 + (18 * σ.val B + 3 + 1 + (8 * σ.val B + 1))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hr
  obtain ⟨⟨hAB, hAD, hAF, hAT, hAX⟩, ⟨hBD, hBF, hBT, hBX⟩, ⟨hDF, hDT, hDX⟩, ⟨hFT, hFX⟩, hTX, -⟩ := hr
  have e1 := dupR_spec cap A D X hAD hAX hDX σ hX (by omega)
  set σ1 := σ.setv D (σ.val D + σ.val A) with hσ1
  have e2 := dupR_spec cap B T X hBT hBX hTX σ1 (by simp [hσ1, Function.update_of_ne (Ne.symm hDX), hX])
    (by simp [hσ1, Function.update_of_ne hBD, Function.update_of_ne (Ne.symm hDT), hT]; omega)
  set σ2 := σ1.setv T (σ1.val T + σ1.val B) with hσ2
  have hB1 : σ1.val B = σ.val B := by rw [hσ1, WState.setv_val]; exact Function.update_of_ne hBD _ _
  have e3 := ltSubLoop_spec (cap := cap) D F T hDF hDT hFT (σ.val B) σ2
    (by rw [hσ2, WState.setv_val, Function.update_self, hB1, hσ1, WState.setv_val,
      Function.update_of_ne (Ne.symm hDT), hT, zero_add]) (by omega)
    (by simp [hσ2, hσ1, Function.update_of_ne hFT, Function.update_of_ne (Ne.symm hDF), hF]; omega)
    (by simp [hσ2, hσ1, Function.update_of_ne hDT, hD]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by rw [hB1])
  apply WState.eq <;> try rfl
  funext r
  simp only [hσ2, hσ1, WState.setv_val, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

end NearCubicGates.Close.Worker

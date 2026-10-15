import Proof.Gates.WordPrograms.Hoare

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TEmit

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

theorem repX {ns nr cap : ℕ} {K K2 : Fin nr} {body : WMX ns nr} {α : Type} (hKK : K ≠ K2) (c n : ℕ)
    (st : ℕ → α → WState ns nr) (a0 : α) (hcap : 2 * n ≤ cap)
    (hK : ∀ k a, (st k a).val K = (st 0 a0).val K) (hK2 : ∀ k a, (st k a).val K2 = (st 0 a0).val K2)
    (hstep : ∀ k < n, ∀ (a : α) (v1 v2 : ℕ), ∃ a' : α,
      WXExec cap body (((st k a).setv K v1).setv K2 v2) (((st (k + 1) a').setv K v1).setv K2 v2) c)
    (h0K : (st 0 a0).val K = n) (h0K2 : (st 0 a0).val K2 = 0) :
    ∃ a : α, WXExec cap (repK K K2 body) (st 0 a0) (st n a) (n * (c + 8) + 7 * n + 3) := by
  let Inv : ℕ → WState ns nr → Prop := fun k τ => ∃ (a : α) (v1 v2 : ℕ), τ = ((st k a).setv K v1).setv K2 v2
  have hsv : ∀ (τ : WState ns nr) (r : Fin nr), τ.setv r (τ.val r) = τ := fun τ r => wsetv_same τ r
  obtain ⟨τ, e, ⟨a, v1, v2, hτ⟩, hKτ, hK2τ⟩ := Runs.rep (cap := cap) (body := body) hKK c n Inv hcap
    (by
      rintro k τ v ⟨a, v1, v2, rfl⟩
      refine ⟨a, v, v2, ?_⟩
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all)
    (by
      rintro k τ v ⟨a, v1, v2, rfl⟩
      refine ⟨a, v1, v, ?_⟩
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all)
    (by
      rintro k hk τ ⟨a, v1, v2, rfl⟩
      obtain ⟨a', h⟩ := hstep k hk a v1 v2
      refine ⟨_, h, ⟨a', v1, v2, rfl⟩, ?_, ?_⟩
      · simp [Function.update_of_ne hKK]
      · simp)
    (st 0 a0) ⟨a0, (st 0 a0).val K, (st 0 a0).val K2, by rw [hsv, hsv]⟩ h0K h0K2
  refine ⟨a, ?_⟩
  have e2 : τ = st n a := by
    rw [hτ]
    have h1 : v1 = (st n a).val K := by
      have := hKτ; rw [hτ] at this; simp [Function.update_of_ne hKK] at this; rw [hK n a, h0K]; exact this
    have h2 : v2 = (st n a).val K2 := by
      have := hK2τ; rw [hτ] at this; simp at this; rw [hK2 n a, h0K2]; exact this
    rw [h1, h2, hsv, hsv]
  rw [e2] at e
  exact e

end NearCubicGates.Close.ENP.TEmit

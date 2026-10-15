import Proof.Gates.Worker.Classify

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Codec

variable {ns nr : ℕ} {cap : ℕ}

/-- `Z := Z + (if F ≠ 0 then A else B)`, scratch `T`. -/
def selW (F A B Z T : Fin nr) : WM ns nr := .ifr F (dupR A Z T) (dupR B Z T)

theorem selW_spec (F A B Z T : Fin nr) (hAZ : A ≠ Z) (hAT : A ≠ T) (hBZ : B ≠ Z) (hBT : B ≠ T) (hZT : Z ≠ T)
    (σ : WState ns nr) (hT : σ.val T = 0) (hc : σ.val A + σ.val B + σ.val Z ≤ cap) :
    WExec cap (selW F A B Z T) σ
      (σ.setv Z (σ.val Z + if σ.val F ≠ 0 then σ.val A else σ.val B))
      (18 * (if σ.val F ≠ 0 then σ.val A else σ.val B) + 4) := by
  by_cases hF : σ.val F = 0
  · have e := dupR_spec cap B Z T hBZ hBT hZT σ hT (by omega)
    simp only [hF, ne_eq, not_true_eq_false, if_false]
    exact WExec.ifrF hF e
  · have e := dupR_spec cap A Z T hAZ hAT hZT σ hT (by omega)
    simp only [hF, ne_eq, not_false_eq_true, if_true]
    exact WExec.ifrT hF e

/-- Load a literal operand: `N := sNeg`, `Y := sFlag`, `Z := sV` if `sFlag ≠ 0` else `sD`; scratch `T`. -/
def loadLit (sNeg sFlag sV sD N Y Z T : Fin nr) : WM ns nr :=
  .seq (dupR sNeg N T) (.seq (dupR sFlag Y T) (selW sFlag sV sD Z T))

theorem loadLit_spec (sNeg sFlag sV sD N Y Z T : Fin nr) (hr : [sNeg, sFlag, sV, sD, N, Y, Z, T].Nodup)
    (σ : WState ns nr) (hN : σ.val N = 0) (hY : σ.val Y = 0) (hZ : σ.val Z = 0) (hT : σ.val T = 0)
    (hc : σ.val sNeg + σ.val sFlag + σ.val sV + σ.val sD ≤ cap) :
    WExec cap (loadLit sNeg sFlag sV sD N Y Z T) σ
      (((σ.setv N (σ.val sNeg)).setv Y (σ.val sFlag)).setv Z (if σ.val sFlag ≠ 0 then σ.val sV else σ.val sD))
      (18 * σ.val sNeg + 3 + 1 + (18 * σ.val sFlag + 3 + 1 +
        (18 * (if σ.val sFlag ≠ 0 then σ.val sV else σ.val sD) + 4))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hr
  obtain ⟨⟨h12, h13, h14, h1N, h1Y, h1Z, h1T⟩, ⟨h23, h24, h2N, h2Y, h2Z, h2T⟩, ⟨h34, h3N, h3Y, h3Z, h3T⟩,
    ⟨h4N, h4Y, h4Z, h4T⟩, ⟨hNY, hNZ, hNT⟩, ⟨hYZ, hYT⟩, hZT, -⟩ := hr
  have e1 := dupR_spec cap sNeg N T h1N h1T hNT σ hT (by omega)
  set σ1 := σ.setv N (σ.val N + σ.val sNeg) with hσ1
  have v1 : ∀ r, r ≠ N → σ1.val r = σ.val r := fun r hr => by
    rw [hσ1, WState.setv_val]; exact Function.update_of_ne hr _ _
  have e2 := dupR_spec cap sFlag Y T h2Y h2T hYT σ1 (by rw [v1 T (Ne.symm hNT)]; exact hT)
    (by rw [v1 sFlag h2N, v1 Y (Ne.symm hNY)]; omega)
  set σ2 := σ1.setv Y (σ1.val Y + σ1.val sFlag) with hσ2
  have v2 : ∀ r, r ≠ N → r ≠ Y → σ2.val r = σ.val r := fun r hrN hrY => by
    rw [hσ2, WState.setv_val, Function.update_of_ne hrY]; exact v1 r hrN
  have e3 := selW_spec (cap := cap) sFlag sV sD Z T h3Z h3T h4Z h4T hZT σ2 (by rw [v2 T (Ne.symm hNT) (Ne.symm hYT)]; exact hT)
    (by rw [v2 sV h3N h3Y, v2 sD h4N h4Y, v2 Z (Ne.symm hNZ) (Ne.symm hYZ)]; omega)
  rw [v2 sFlag h2N h2Y, v2 sV h3N h3Y, v2 sD h4N h4Y] at e3
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by rw [v1 sFlag h2N])
  apply WState.eq <;> try rfl
  funext r
  simp only [hσ2, hσ1, WState.setv_val, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

def loadHelper (PB A Z T : Fin nr) : WM ns nr := .seq (dupR PB Z T) (dupR A Z T)

theorem loadHelper_spec (PB A Z T : Fin nr) (hr : [PB, A, Z, T].Nodup) (σ : WState ns nr) (hZ : σ.val Z = 0)
    (hT : σ.val T = 0) (hc : σ.val PB + σ.val A ≤ cap) :
    WExec cap (loadHelper PB A Z T) σ (σ.setv Z (σ.val PB + σ.val A))
      (18 * σ.val PB + 3 + 1 + (18 * σ.val A + 3)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hr
  obtain ⟨⟨hPA, hPZ, hPT⟩, ⟨hAZ, hAT⟩, hZT, -⟩ := hr
  have e1 := dupR_spec cap PB Z T hPZ hPT hZT σ hT (by omega)
  set σ1 := σ.setv Z (σ.val Z + σ.val PB) with hσ1
  have hA1 : σ1.val A = σ.val A := by rw [hσ1, WState.setv_val]; exact Function.update_of_ne hAZ _ _
  have e2 := dupR_spec cap A Z T hAZ hAT hZT σ1
    (by rw [hσ1, WState.setv_val]; rw [Function.update_of_ne (Ne.symm hZT)]; exact hT)
    (by rw [hA1, hσ1, WState.setv_val, Function.update_self]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by rw [hA1])
  apply WState.eq <;> try rfl
  funext r
  simp only [hσ1, WState.setv_val, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

end NearCubicGates.Close.Worker

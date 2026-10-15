import Proof.Gates.Codec.ParityW
import Proof.Gates.Worker.Meaning

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces (bitWord outputWord)

variable {ns nr : ℕ}

/-- The raw mean of an exact entry: `1/2` when the flag is set. -/
def halfIf (h : Bool) : ℚ := if h then 1 / 2 else 0

/-- **The exact-entry writer.** -/
def exactEntryW (o : Fin (ns + 1)) (OP F H : Fin nr) : WMX ns nr :=
  .seq (.ifr F (.wm (Codec.emitMarks o OP (bitWord true))) (.wm (Codec.emitMarks o OP (bitWord false))))
    (.ifr H (.wm (Codec.emitMarks o OP (outputWord (1 / 2, 0)))) (.wm (Codec.emitMarks o OP (outputWord (0, 0)))))

theorem bitWord_len (b : Bool) : (bitWord b).length = 3 := by cases b <;> rfl

theorem half_num : ((1 : ℚ) / 2).num = 1 := by norm_num
theorem half_den : ((1 : ℚ) / 2).den = 2 := by norm_num

theorem outputWord_half_len : (outputWord ((1 : ℚ) / 2, 0)).length = 20 := by
  simp only [outputWord, NearCubicGates.Close.Interfaces.ratWord, List.length_append, half_num, half_den]; rfl

theorem outputWord_zero_len : (outputWord ((0 : ℚ), 0)).length = 18 := by rfl

/-- **STATEMENT `exactEntryW_spec`**: append `marks (bitWord [F ≠ 0] ++ outputWord (halfIf [H ≠ 0], 0))`. -/
theorem exactEntryW_spec (cap : ℕ) (o : Fin (ns + 1)) (OP F H : Fin nr) (hOH : OP ≠ H)
    (σ : WState ns nr) (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + 46 ≤ cap) :
    WXExec cap (exactEntryW o OP F H) σ
      (appendO σ o OP (marks (bitWord (decide (σ.val F ≠ 0)) ++ outputWord (halfIf (decide (σ.val H ≠ 0)), 0))))
      400 := by
  have hb : ∀ b : Bool, WXExec cap (.ifr F (.wm (Codec.emitMarks o OP (bitWord true)))
      (.wm (Codec.emitMarks o OP (bitWord false)))) σ (appendO σ o OP (marks (bitWord (decide (σ.val F ≠ 0))))) 49 :=
    fun _ => by
      by_cases hF : σ.val F = 0
      · have e := Codec.emitMarks_spec cap o OP (bitWord false) σ ho (by rw [bitWord_len]; omega)
        rw [bitWord_len] at e
        simpa [hF] using (WXExec.ifrF hF (WXExec.wm e)).mono (by omega)
      · have e := Codec.emitMarks_spec cap o OP (bitWord true) σ ho (by rw [bitWord_len]; omega)
        rw [bitWord_len] at e
        simpa [hF] using (WXExec.ifrT hF (WXExec.wm e)).mono (by omega)
  set τ := appendO σ o OP (marks (bitWord (decide (σ.val F ≠ 0)))) with hτ
  have hτo : τ.sh o = (τ.st o).length := by simp [hτ, appendO, ho]
  have hτH : τ.val H = σ.val H := by simp [hτ, appendO, Function.update_of_ne (Ne.symm hOH)]
  have hτc : τ.val OP = σ.val OP + 6 := by
    simp [hτ, appendO, Codec.marks_length, bitWord_len]
  have e2 : WXExec cap (.ifr H (.wm (Codec.emitMarks o OP (outputWord (1 / 2, 0))))
      (.wm (Codec.emitMarks o OP (outputWord (0, 0))))) τ
      (appendO τ o OP (marks (outputWord (halfIf (decide (σ.val H ≠ 0)), 0)))) 330 := by
    by_cases hH : σ.val H = 0
    · have e := Codec.emitMarks_spec cap o OP (outputWord (0, 0)) τ hτo (by rw [outputWord_zero_len]; omega)
      rw [outputWord_zero_len] at e
      simpa [hH, halfIf] using (WXExec.ifrF (by rw [hτH]; exact hH) (WXExec.wm e)).mono (by omega)
    · have e := Codec.emitMarks_spec cap o OP (outputWord (1 / 2, 0)) τ hτo (by rw [outputWord_half_len]; omega)
      rw [outputWord_half_len] at e
      simpa [hH, halfIf] using (WXExec.ifrT (by rw [hτH]; exact hH) (WXExec.wm e)).mono (by omega)
  refine (WXExec.seq (hb true) e2).cast cap ?_ (by omega)
  rw [hτ, appendO_append, Codec.marksApp]

/-! ## Value lemmas -/

open NearCubicGates.Close.Gadget in
theorem canonList_ne_nil_iff {q : ℕ} (S : Finset (Fin q)) : (canonList S).map Fin.val ≠ [] ↔ S.Nonempty := by
  rw [Ne, List.map_eq_nil_iff]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨i, (mem_canonList S i).1 hi⟩
  · rintro ⟨i, hi⟩ h
    have := (mem_canonList S i).2 hi
    rw [h] at this; simp at this

open NearCubicGates.Close.Gadget in
theorem canonList_inj {q : ℕ} (S T : Finset (Fin q)) : (canonList S).map Fin.val = (canonList T).map Fin.val ↔ S = T := by
  constructor
  · intro h
    have h' : canonList S = canonList T := List.map_injective_iff.2 Fin.val_injective h
    ext i; rw [← mem_canonList S i, ← mem_canonList T i, h']
  · rintro rfl; rfl

theorem parityMean_halfIf {q : ℕ} (S : Finset (Fin q)) :
    Worker.parityMean S = halfIf (decide S.Nonempty) := by
  unfold Worker.parityMean halfIf; by_cases h : S.Nonempty <;> simp [h]

theorem symmDiff_nonempty_iff {α : Type} [DecidableEq α] (S T : Finset α) : (symmDiff S T).Nonempty ↔ S ≠ T := by
  rw [Finset.nonempty_iff_ne_empty, Ne, Ne, ← Finset.bot_eq_empty, symmDiff_eq_bot]

end NearCubicGates.Close.WorkerArith

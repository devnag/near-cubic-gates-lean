import Proof.Wire_3_5.UnionMachineEntryAcc

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Sched
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine

section Layout
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- The estimator's tape count. -/
noncomputable abbrev TE : ℕ := (estRW P).program.tapeCount

/-- The ambient tape count. -/
noncomputable abbrev NA : ℕ := 31 + TE P

/-- A fixed tape. -/
noncomputable def fx (k : Fin 31) : Fin (NA P) := Fin.castAdd (TE P) k

/-- **The estimator's slots.** -/
noncomputable def es : Fin (TE P) → Fin (NA P) := Fin.natAdd 31

/-- The estimator's output and input tapes. -/
noncomputable abbrev eOut : Fin (TE P) := (estRW P).program.outputTape
noncomputable abbrev eIn : Fin (TE P) := C10WordFunctionDock.inSlot (estRW P).program

/-- **The rounding bank's slots**: its stream `0` is the estimator's output tape. -/
noncomputable def rs : Fin (2 + 2 + 14) → Fin (NA P) :=
  fun k => if h : k.val = 0 then es P (eOut P) else fx P ⟨k.val, by omega⟩

/-- The entry bank's registers among the fixed tapes. -/
def ebReg : Fin 15 → Fin 31 := ![18, 19, 20, 21, 22, 23, 14, 15, 24, 25, 26, 27, 28, 29, 30]

/-- **The entry bank's slots**: its stream `1` is the estimator's input tape. -/
noncomputable def eb : Fin (1 + 2 + 15) → Fin (NA P) :=
  fun k => if k.val = 0 then fx P 0 else if k.val = 1 then fx P 1 else if k.val = 2 then es P (eIn P)
    else fx P (ebReg ⟨k.val - 3, by omega⟩)

theorem fx_val (k : Fin 31) : (fx P k).val = k.val := rfl
theorem es_val (j : Fin (TE P)) : (es P j).val = 31 + j.val := by simp [es]

theorem es_inj : Function.Injective (es P) := by
  intro a b h; have := congrArg Fin.val h; simp [es] at this; exact Fin.ext this

theorem fx_inj : Function.Injective (fx P) := by
  intro a b h; have := congrArg Fin.val h; simp [fx] at this; exact Fin.ext this

theorem fx_ne_es (k : Fin 31) (j : Fin (TE P)) : fx P k ≠ es P j := by
  intro h; have := congrArg Fin.val h; rw [fx_val, es_val] at this; omega

theorem ebReg_inj : Function.Injective ebReg := by decide

theorem ebReg_ge (r : Fin 15) : 14 ≤ (ebReg r).val := by fin_cases r <;> decide

theorem rs_zero : rs P 0 = es P (eOut P) := by simp [rs]

theorem rs_pos (k : Fin (2 + 2 + 14)) (hk : k.val ≠ 0) : rs P k = fx P ⟨k.val, by omega⟩ := by
  simp [rs, hk]

theorem rs_inj : Function.Injective (rs P) := by
  intro a b h
  by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
  · exact Fin.ext (by omega)
  · rw [show a = 0 from Fin.ext ha, rs_zero, rs_pos P b hb] at h; exact absurd h.symm (fx_ne_es P _ _)
  · rw [show b = 0 from Fin.ext hb, rs_zero, rs_pos P a ha] at h; exact absurd h (fx_ne_es P _ _)
  · rw [rs_pos P a ha, rs_pos P b hb] at h
    have := congrArg Fin.val (fx_inj P h); exact Fin.ext this

theorem rs_es_disj (j : Fin (TE P)) (k : Fin (2 + 2 + 14)) (h : es P j = rs P k) : k = 0 := by
  by_contra hk
  have hk' : k.val ≠ 0 := fun h0 => hk (Fin.ext h0)
  rw [rs_pos P k hk'] at h
  exact fx_ne_es P _ _ h.symm

theorem eb_val_fixed (k : Fin (1 + 2 + 15)) (hk : k.val ≠ 2) : ∃ m : Fin 31, eb P k = fx P m := by
  unfold eb
  split_ifs <;> first | exact ⟨_, rfl⟩ | omega

theorem eb_two : eb P 2 = es P (eIn P) := by simp [eb]

theorem eb_inj : Function.Injective (eb P) := by
  intro a b h
  have hv := congrArg Fin.val h
  unfold eb at hv
  apply Fin.ext
  split_ifs at hv with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 <;>
    simp only [fx_val, es_val, Fin.isValue] at hv <;> (try omega) <;>
    (first
      | (have := ebReg_ge ⟨a.val - 3, by omega⟩; simp at hv; omega)
      | (have := ebReg_ge ⟨b.val - 3, by omega⟩; simp at hv; omega)
      | (have := ebReg_inj (Fin.ext hv : ebReg ⟨a.val - 3, by omega⟩ = ebReg ⟨b.val - 3, by omega⟩)
         simp [Fin.ext_iff] at this; omega)
      | (have e1 := es_val P (eIn P); omega))

end Layout

end NearCubicWires.WireExponent3_5.UnionMachine.Sched

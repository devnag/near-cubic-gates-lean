import Proof.Gates.TabMachine.Rest

/-! # One variable occurrence of a monomial (the cut machine's inner step)

Proof of lem:print, one variable of a monomial at the inner point `c`: restrict the variable's gate to `c`
(`restrictP`), hand its outer weights and strict target to the exact-test compiler (lem:exact, `compileP`), split
the children into fields (`explode`), put every child before every current tuple (`tupleStep`), and make the new
tuples the current ones. **`occStep_spec`**: the tuple stream goes from `tf` to `newT (o.kids c) tf`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## Value level -/

theorem compileL_length (ws : List ℤ) (t : ℤ) : ∀ c ∈ compileL ws t, c.length = ws.length + 1 := by
  intro c hc
  unfold compileL at hc
  split_ifs at hc
  · simp at hc; subst hc; simp [zeroL]
  · simp at hc; subst hc; simp [zeroL]
  · simp only [List.mem_flatMap, List.mem_filterMap] at hc
    obtain ⟨bit, _, i, _, hi⟩ := hc
    split_ifs at hi
    simp at hi; subst hi; simp [childL]

theorem compRecs_stream (W : ℕ) (ws : List ℤ) (t : ℤ) :
    compRecs W ws t ++ [false] = recStream ((compileL ws t).map (recBits W)) := by
  unfold compRecs recStream; rw [List.flatMap_map]

theorem overlay_closed (out L0 : List Bool) : ∃ junk, overlay out L0 = out ++ junk := ⟨_, rfl⟩

/-- An occurrence block's length. -/
def occLen (o : Occ) : ℕ := 2 + o.inW.length + o.outW.length

theorem occRecs_length (o : Occ) : (occRecs o).length = occLen o := by
  simp [occRecs, occLen]; omega

theorem occRecs_take (o : Occ) : (occRecs o).take (2 + o.inW.length) = [o.ref.toNat, encS o.thr] ++ o.inW.map encS := by
  unfold occRecs
  rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp; omega)]

theorem occRecs_drop (o : Occ) : (occRecs o).drop (2 + o.inW.length) = o.outW.map encS := by
  unfold occRecs
  have h : ([o.ref.toNat, encS o.thr] ++ o.inW.map encS).length = 2 + o.inW.length := by simp; omega
  rw [← h, List.drop_left]

section OccA
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

/-- Restriction, outer weights into the compiler's input, the compiler (child records on `KD`). -/
def occA : WMX ns nr :=
  .seq (restrictP (zA Z) (yB Y))
  (.seq (copyN (Z 46) (Z 47) (Z 0) (Y 75) (Y 76) (Y 77) (Y 78) (Y 87) (Y 88) (Y 89) (Y 90))
  (.seq (closeOutX (Z 0) (Y 88))
  (.seq (compileP (zS Z) (yR Y)) (closeOutX (Z 2) (Y 14)))))

/-- The stream indices `occA` may change. -/
def occAIdx : List (Fin 64) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 47, 48, 49, 50, 51, 52]

/-- The streams `occA` may change. -/
def occAStreams : List (Fin (ns + 1)) := occAIdx.map Z

theorem map_subset {α β : Type} (f : α → β) (is js : List α) (h : ∀ i ∈ is, i ∈ js) :
    ∀ x ∈ is.map f, x ∈ js.map f := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨i, h i hi, rfl⟩

theorem drop_take_seg (xs : List ℕ) (p : ℕ) (o : Occ) (hblk : (xs.drop p).take (occLen o) = occRecs o) :
    (xs.drop p).take (2 + o.inW.length) = [o.ref.toNat, encS o.thr] ++ o.inW.map encS ∧
      (xs.drop (p + (2 + o.inW.length))).take o.outW.length = o.outW.map encS ∧
      p + occLen o ≤ xs.length := by
  have hl : ((xs.drop p).take (occLen o)).length = occLen o := by rw [hblk, occRecs_length]
  rw [List.length_take, List.length_drop] at hl
  have h2 : 2 ≤ occLen o := by unfold occLen; omega
  refine ⟨?_, ?_, by omega⟩
  · rw [← occRecs_take, ← hblk, List.take_take, min_eq_left (by unfold occLen; omega)]
  · rw [← occRecs_drop, ← hblk, List.drop_take, ← List.drop_drop]
    congr 1; unfold occLen; omega

end OccA

end NearCubicGates.Close.TabMachine

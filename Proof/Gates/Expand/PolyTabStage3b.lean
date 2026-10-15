import Proof.Gates.Expand.PolyTabStage3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)

/-! ## Positions in the terms word -/

section Terms
variable {V : ℕ} (P : Terms V)

def posT (k : ℕ) : ℕ := 1 + ((P.take k).map fun t => (monoN t).length).sum
def cmx (k : ℕ) : ℕ := ((P.take k).map fun t => natBitLength t.2.natAbs).foldr max 0

theorem monoN_length (t : Finset (Fin V) × ℤ) :
    (monoN t).length = ((t.1.sort (· ≤ ·)).map Fin.val).length + 3 := by simp [monoN, intN]

theorem termsN_split (k : ℕ) (hk : k < P.length) :
    termsN P = ((P.length :: (P.take k).flatMap monoN) ++ monoN P[k]) ++ (P.drop (k + 1)).flatMap monoN := by
  have e2 : P.flatMap monoN = (P.take k ++ P[k] :: P.drop (k + 1)).flatMap monoN := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  simp only [termsN, e2, List.flatMap_append, List.flatMap_cons, List.cons_append, List.append_assoc]

theorem posT_eq (k : ℕ) : (P.length :: (P.take k).flatMap monoN).length = posT P k := by
  simp [posT, List.length_flatMap]; ring

theorem getElem?_mid' {α : Type} (A B C : List α) (j : ℕ) (hj : j < B.length) :
    ((A ++ B) ++ C)[A.length + j]? = B[j]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj]

theorem termsN_at (k j : ℕ) (hk : k < P.length) (hj : j < (monoN P[k]).length) :
    (termsN P)[posT P k + j]? = (monoN P[k])[j]? := by
  rw [termsN_split P k hk, ← posT_eq]
  exact getElem?_mid' _ _ _ j hj

theorem posT_succ (k : ℕ) (hk : k < P.length) :
    posT P (k + 1) = posT P k + ((P[k].1.sort (· ≤ ·)).map Fin.val).length + 3 := by
  unfold posT
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, monoN_length]
  ring

theorem termsN_length : (termsN P).length = posT P P.length := by
  simp [termsN, posT, List.length_flatMap]; ring

theorem foldr_max_append (l : List ℕ) (x : ℕ) : (l ++ [x]).foldr max 0 = max (l.foldr max 0) x := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, List.foldr_cons, ih]; omega

theorem cmx_succ (k : ℕ) (hk : k < P.length) : cmx P (k + 1) = max (cmx P k) (natBitLength P[k].2.natAbs) := by
  unfold cmx
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
  exact foldr_max_append _ _

theorem foldr_max_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem cmx_le (k : ℕ) : cmx P k ≤ (termsWord P).length := by
  unfold cmx
  refine foldr_max_le _ _ fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have ht' := List.mem_of_mem_take ht
  have h1 : natBitLength t.2.natAbs + 1 ≤ (natWord t.2.natAbs).length := natBitLength_le_word _
  have h2 : t.2.natAbs ∈ termsN P := by
    simp only [termsN, List.mem_cons, List.mem_flatMap]
    right; exact ⟨t, ht', by simp [monoN, intN]⟩
  have h3 := flatMap_natWord_ge (termsN P) _ h2
  rw [← termsWord_eq] at h3
  omega

end Terms

end NearCubicGates.Close.Expand.PolyTab

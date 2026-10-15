import Proof.Gates.Cells.CellBody

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

section S
variable {n : ℕ} (I : Finset (Fin n))

theorem outer_nodup : (outerCoords I).Nodup := Finset.sort_nodup _ _

theorem mem_outer (x : Fin n) : x ∈ outerCoords I ↔ x ∉ I := by
  simp [outerCoords, Finset.mem_sort]

theorem card_cells : Fintype.card (Cells I) = 2 ^ cellBits I := by
  rw [Fintype.card_fun, Fintype.card_bool]
  congr 1
  unfold cellBits outerCoords
  rw [Finset.length_sort, Fintype.card_subtype]

theorem cellOf_inj {j j' : ℕ} (hj : j < 2 ^ cellBits I) (hj' : j' < 2 ^ cellBits I)
    (h : cellOf I j = cellOf I j') : j = j' := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < cellBits I
  · have hk' : k < (outerCoords I).length := hk
    set x := (outerCoords I)[k] with hx
    have hxI : x ∉ I := (mem_outer I x).1 (List.getElem_mem hk')
    have hidx : (outerCoords I).idxOf x = k := by rw [hx]; exact (outer_nodup I).idxOf_getElem k hk'
    have := congrFun h ⟨x, hxI⟩
    simp only [cellOf] at this
    rw [hidx] at this
    exact this
  · push Not at hk
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hk)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj' (Nat.pow_le_pow_right (by norm_num) hk))]

theorem sum_cells {β : Type} [AddCommMonoid β] (f : Cells I → β) :
    ∑ y, f y = ∑ j ∈ Finset.range (2 ^ cellBits I), f (cellOf I j) := by
  have hinj : Set.InjOn (cellOf I) (Finset.range (2 ^ cellBits I)) := by
    intro j hj j' hj' h
    exact cellOf_inj I (Finset.mem_range.mp hj) (Finset.mem_range.mp hj') h
  have himg : (Finset.range (2 ^ cellBits I)).image (cellOf I) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, card_cells]
  rw [← himg, Finset.sum_image hinj]

end S

end NearCubicGates.Close.Cells

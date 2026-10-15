import Mathlib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open Finset

variable {N L : ℕ}

/-- The next vertex slot around the cycle. -/
def nextSlot (hL : 0 < L) (k : Fin L) : Fin L := ⟨(k.val + 1) % L, Nat.mod_lt _ hL⟩

/-- The matrix cell read by edge slot `k`: `(row, column)`, rows on even slots (`EEᵀ` alternation). -/
def cellOf (hL : 0 < L) (w : Fin L → Fin N) (k : Fin L) : Fin N × Fin N :=
  if k.val % 2 = 0 then (w k, w (nextSlot hL k)) else (w (nextSlot hL k), w k)

/-- A walk is consistent with the grouping when every edge reads the same cell as its representative. -/
def Consistent (hL : 0 < L) (rep : Fin L → Fin L) (w : Fin L → Fin N) : Prop :=
  ∀ k, cellOf hL w k = cellOf hL w (rep k)

theorem nextSlot_val (hL : 0 < L) (k : Fin L) (hk : k.val + 1 < L) : (nextSlot hL k).val = k.val + 1 := by
  simp [nextSlot, Nat.mod_eq_of_lt hk]

/-- Determination: two consistent walks with the same first vertex and the same "new" vertices agree. -/
theorem walk_determined (hL : 0 < L) (rep : Fin L → Fin L) (hrep : ∀ k, rep k ≤ k)
    (w w' : Fin L → Fin N) (hw : Consistent hL rep w) (hw' : Consistent hL rep w')
    (h0 : w ⟨0, hL⟩ = w' ⟨0, hL⟩)
    (hnew : ∀ k : Fin L, rep k = k → ∀ hk : k.val + 1 < L, w ⟨k.val + 1, hk⟩ = w' ⟨k.val + 1, hk⟩) :
    w = w' := by
  have key : ∀ j (hj : j < L), w ⟨j, hj⟩ = w' ⟨j, hj⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases j with _ | k
      · exact h0
      · set kk : Fin L := ⟨k, by omega⟩
        by_cases hfirst : rep kk = kk
        · exact hnew kk hfirst hj
        · have hlt : (rep kk).val < k := lt_of_le_of_ne (hrep kk) (fun h => hfirst (Fin.ext h))
          have hr1 : (rep kk).val + 1 < L := by omega
          -- the representative's cell is already determined
          have hA : w (rep kk) = w' (rep kk) := ih _ (by omega) _
          have hB : w (nextSlot hL (rep kk)) = w' (nextSlot hL (rep kk)) := by
            have hv := nextSlot_val hL (rep kk) hr1
            have := ih ((rep kk).val + 1) (by omega) (by omega)
            have e : nextSlot hL (rep kk) = ⟨(rep kk).val + 1, by omega⟩ := Fin.ext hv
            rw [e]; exact this
          have hcellR : cellOf hL w (rep kk) = cellOf hL w' (rep kk) := by
            unfold cellOf; rw [hA, hB]
          have hcell : cellOf hL w kk = cellOf hL w' kk := by rw [hw kk, hw' kk, hcellR]
          have hnext : nextSlot hL kk = ⟨k + 1, hj⟩ := Fin.ext (nextSlot_val hL kk (by simp [kk]; omega))
          unfold cellOf at hcell
          rw [hnext] at hcell
          split_ifs at hcell
          · exact (Prod.ext_iff.mp hcell).2
          · exact (Prod.ext_iff.mp hcell).1
  funext j; exact key j.val j.isLt

/-- The walk count: at most `N^{1 + #first edges}` consistent walks. -/
theorem card_consistent_le (hL : 0 < L) (rep : Fin L → Fin L) (hrep : ∀ k, rep k ≤ k)
    [DecidablePred (Consistent (N := N) hL rep)] :
    (univ.filter (Consistent (N := N) hL rep)).card ≤ N ^ (1 + (univ.filter fun k : Fin L => rep k = k).card) := by
  classical
  set G := univ.filter fun k : Fin L => rep k = k
  let code : (Fin L → Fin N) → Fin N × (G → Fin N) := fun w =>
    (w ⟨0, hL⟩, fun k => w (nextSlot hL k.1))
  have hinj : Set.InjOn code (univ.filter (Consistent (N := N) hL rep) : Set (Fin L → Fin N)) := by
    intro w hw w' hw' hc
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
    simp only [code, Prod.mk.injEq] at hc
    apply walk_determined hL rep hrep w w' hw hw' hc.1
    intro k hk hk1
    have := congrFun hc.2 ⟨k, by simp [G, hk]⟩
    simp only at this
    have e : nextSlot hL k = ⟨k.val + 1, hk1⟩ := Fin.ext (nextSlot_val hL k hk1)
    rw [e] at this; exact this
  calc (univ.filter (Consistent (N := N) hL rep)).card
      ≤ (univ : Finset (Fin N × (G → Fin N))).card :=
        Finset.card_le_card_of_injOn code (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
    _ = N ^ (1 + G.card) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
          pow_add, pow_one]

end NearCubicWires.WireExponent3_5.Shared

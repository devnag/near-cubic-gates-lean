import SourceAdapters.Proximity.QueryRows

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact two-record positions in the padded query row. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.QueryRows

open QueryStep

theorem rowFields_split {N : ℕ} (addresses : Fin N → Bool × ℕ) (q j : ℕ) (hj : j < q) :
    ∃ tail : List ℕ, rowFields addresses q = rowFields addresses j ++
      (paddedAddress addresses j).1.toNat :: (paddedAddress addresses j).2 :: tail := by
  let f := fun i => [(paddedAddress addresses i).1.toNat, (paddedAddress addresses i).2]
  refine ⟨((List.range q).drop (j + 1)).flatMap f, ?_⟩
  have hmem : j < (List.range q).length := by simpa using hj
  have hs := List.take_append_drop j (List.range q)
  rw [List.drop_eq_getElem_cons hmem] at hs
  change (List.range q).flatMap f = _
  conv_lhs => rw [← hs]
  rw [List.flatMap_append, List.flatMap_cons]
  simp [f, rowFields, List.take_range, Nat.min_eq_left hj.le]

end NearCubicGates.Adapters.Proximity.QueryRows

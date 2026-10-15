import Proof.Hierarchy.CompetitorSelectedRequestCountLayout

/-! Exact cropped row-major pairing of the completed natural count table
with one residual-offset selection bit per physical cell. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedCells
open CompetitorCountMask CompetitorFinalTable SignedSortKey
open WilliamsProductCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rect {u v : ℕ} (f : Fin u → Fin v → ℕ) (s : Fin u → Fin v → Bool) :=
  (List.ofFn fun i => List.ofFn fun j => (s i j,f i j)).flatten
def cells {u : ℕ} (odd : Bool) (f : Fin u → Fin u → ℕ) (s : Fin u → Fin u → Bool) :=
  if odd then rect (fun i j => f i (lowerColumn j)) (fun i j => s i (lowerColumn j)) else rect f s

theorem rect_counts {u v : ℕ} (f : Fin u → Fin v → ℕ) (s : Fin u → Fin v → Bool) :
    counts (rect f s)=rowMajorNatMatrix f := by
  simp [counts,rect,rowMajorNatMatrix,List.map_flatten,List.map_ofFn,Function.comp_def]

theorem cells_counts {u : ℕ} (odd : Bool) (f : Fin u → Fin u → ℕ) (s : Fin u → Fin u → Bool) :
    counts (cells odd f s)=values odd f := by
  cases odd <;> simp [cells,values,rect_counts]

theorem cells_word {u : ℕ} (Q : ℕ) (odd : Bool) (f : Fin u → Fin u → ℕ) (s : Fin u → Fin u → Bool) :
    CompetitorCountFold.raw Q (counts (cells odd f s))=word Q odd f := by
  rw [cells_counts]
  rfl

theorem cells_length {u : ℕ} (odd : Bool) (f : Fin u → Fin u → ℕ) (s : Fin u → Fin u → Bool) :
    (cells odd f s).length≤u*u := by
  have h := congrArg List.length (cells_counts odd f s)
  rw [counts_length,values_cardinality] at h
  rw [h]
  cases odd
  · exact Nat.le_refl _
  · exact Nat.mul_le_mul_left u (Nat.div_le_self u 2)

theorem rect_fit {u v : ℕ} (Q : ℕ) (f : Fin u → Fin v → ℕ) (s : Fin u → Fin v → Bool)
    (hf : ∀ i j,f i j<2^Q) : ∀ x∈selected (rect f s),x<2^Q := by
  intro x hx
  obtain ⟨pair,hpair,rfl⟩ := List.mem_map.mp hx
  obtain ⟨row,hrow,hpair⟩ := List.mem_flatten.mp hpair
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hpair
  dsimp only
  split
  · exact hf i j
  · positivity

theorem cells_fit {u : ℕ} (Q : ℕ) (odd : Bool) (f : Fin u → Fin u → ℕ) (s : Fin u → Fin u → Bool)
    (hf : ∀ i j,f i j<2^Q) : ∀ x∈selected (cells odd f s),x<2^Q := by
  cases odd
  · exact rect_fit Q f s hf
  · exact rect_fit Q _ _ (fun i j => hf i (lowerColumn j))

end NearCubicWires.RepairOrdinary.CompetitorSelectedCells

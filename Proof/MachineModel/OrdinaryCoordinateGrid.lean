import Proof.MachineModel.OrdinaryKeyDominanceScan

/-! Exact row-major meaning of coordinate sorting. The producer must supply
a permutation of the complete coordinate grid; this theorem then identifies
the sorter's literal output, including every cell payload. -/
namespace NearCubicWires.RepairOrdinary.CoordinateKey
open SignedSortKey RadixSemantics StablePartition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def grid {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool) : List Record :=
  List.ofFn (fun index : Fin (Rows * Used) =>
    let p := finProdFinEquiv.symm index
    key I K p.2.val p.1.val (payload p.1 p.2))

theorem key_antisymm (I K i j x y : ℕ) (c d : Bool)
    (hi : i < 2 ^ I) (hj : j < 2 ^ I) (hx : x < 2 ^ K) (hy : y < 2 ^ K)
    (hle : value (word (key I K i x c)) ≤ value (word (key I K j y d)))
    (hge : value (word (key I K j y d)) ≤ value (word (key I K i x c))) :
    key I K i x c = key I K j y d := by
  have h := (key_order I K i j x y c d hi hj hx hy).mp hle
  have h' := (key_order I K j i y x d c hj hi hy hx).mp hge
  have hxy : x = y := by omega
  have hij : i = j := by omega
  have hcd : c = d := by cases c <;> cases d <;> simp_all
  rw [hxy, hij, hcd]

theorem grid_order {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool)
    (hi : Used ≤ 2 ^ I) (hk : Rows ≤ 2 ^ K) :
    (grid I K payload).Pairwise (fun a b => value (word a) ≤ value (word b)) := by
  rw [grid, List.pairwise_ofFn]
  intro i j hij
  let p : Fin Rows × Fin Used := finProdFinEquiv.symm i
  let q : Fin Rows × Fin Used := finProdFinEquiv.symm j
  have hp : i.val = p.1.val * Used + p.2.val := by
    have h := coordinate_index p.1 p.2
    change (finProdFinEquiv (finProdFinEquiv.symm i)).val = _ at h
    simpa only [Equiv.apply_symm_apply] using h
  have hq : j.val = q.1.val * Used + q.2.val := by
    have h := coordinate_index q.1 q.2
    change (finProdFinEquiv (finProdFinEquiv.symm j)).val = _ at h
    simpa only [Equiv.apply_symm_apply] using h
  apply (key_order I K p.2.val q.2.val p.1.val q.1.val (payload p.1 p.2) (payload q.1 q.2)
    (p.2.isLt.trans_le hi) (q.2.isLt.trans_le hi) (p.1.isLt.trans_le hk) (q.1.isLt.trans_le hk)).mpr
  by_cases hlt : p.1.val < q.1.val
  · exact Or.inl hlt
  have hle : q.1.val ≤ p.1.val := by omega
  by_cases he : p.1.val = q.1.val
  · refine Or.inr ⟨he, Or.inl ?_⟩
    rw [he] at hp
    have h := Fin.lt_def.mp hij
    omega
  · have hm := Nat.mul_le_mul_right Used (show q.1.val + 1 ≤ p.1.val by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    have hbound := q.2.isLt
    have h := Fin.lt_def.mp hij
    omega

theorem grid_antisymm {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool)
    (hi : Used ≤ 2 ^ I) (hk : Rows ≤ 2 ^ K) (a b : Record)
    (ha : a ∈ grid I K payload) (hb : b ∈ grid I K payload)
    (hle : value (word a) ≤ value (word b)) (hge : value (word b) ≤ value (word a)) : a = b := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  apply key_antisymm _ _ _ _ _ _ _ _ _ _ _ _ hle hge
  · exact (finProdFinEquiv.symm i).2.isLt.trans_le hi
  · exact (finProdFinEquiv.symm j).2.isLt.trans_le hi
  · exact (finProdFinEquiv.symm i).1.isLt.trans_le hk
  · exact (finProdFinEquiv.symm j).1.isLt.trans_le hk

theorem sorted_eq_grid {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool)
    (req : SortCarrier.Request) (hp : req.records.Perm (grid I K payload))
    (hi : Used ≤ 2 ^ I) (hk : Rows ≤ 2 ^ K) :
    SortCarrier.sorted req = grid I K payload := by
  have hperm := (SortCarrier.sorted_perm req).trans hp
  exact hperm.eq_of_pairwise
    (fun a b ha hb hab hba => grid_antisymm I K payload hi hk a b (hperm.mem_iff.mp ha) hb hab hba)
    (SortCarrier.sorted_order req) (grid_order I K payload hi hk)

theorem grid_rows {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool) :
    grid I K payload = (List.ofFn (fun row : Fin Rows => List.ofFn (fun inner : Fin Used =>
      key I K inner.val row.val (payload row inner)))).flatten := by
  rw [grid, List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext inner
  have he (h : row.val * Used + inner.val < Rows * Used) :
      (⟨row.val * Used + inner.val, h⟩ : Fin (Rows * Used)) = finProdFinEquiv (row, inner) := by
    apply Fin.ext
    exact (coordinate_index row inner).symm
  simp only [he, Equiv.symm_apply_apply]

end NearCubicWires.RepairOrdinary.CoordinateKey

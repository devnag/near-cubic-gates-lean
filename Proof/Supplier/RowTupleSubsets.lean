import Proof.Supplier.RowTupleDigits

/-! The binary tuple cursor filters positional subsets. The order may differ
from `sublistsLen`, but every positional subset occurs exactly once. Mapping
positions to equal monomials therefore retains their multiplicities. -/
namespace NearCubicWires.RepairOrdinary.RowTupleSubsets
open RowTupleDigits
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def valid (M : ℕ) (ds : List ℕ) : Bool :=
  decide (ds.Pairwise (·<·)) && ds.all (fun d=>decide (d<M))
def selected (w M k : ℕ) : List (List ℕ) :=
  (candidates w k).filter (valid M)

theorem valid_iff (M : ℕ) (ds : List ℕ) :
    valid M ds=true ↔ ds.Pairwise (·<·) ∧ ∀ d∈ds,d<M := by
  simp [valid,List.all_eq_true]

theorem sublist_range_iff (M : ℕ) (ds : List ℕ) :
    ds.Sublist (List.range M) ↔ ds.Pairwise (·<·) ∧ ∀ d∈ds,d<M := by
  constructor
  · intro h
    exact ⟨List.pairwise_lt_range.sublist h,fun d hd=>List.mem_range.mp (h.subset hd)⟩
  · rintro ⟨hp,hb⟩
    apply List.sublist_of_subperm_of_pairwise (r:=(·<·)) _ hp List.pairwise_lt_range
    exact hp.nodup.subperm (fun d hd=>List.mem_range.mpr (hb d hd))

theorem selected_mem (w M k : ℕ) (hM : M≤2^w) (ds : List ℕ) :
    ds∈selected w M k ↔ ds∈(List.range M).sublistsLen k := by
  rw [selected,List.mem_filter,candidates_mem,valid_iff,List.mem_sublistsLen,
    sublist_range_iff]
  constructor
  · rintro ⟨⟨hl,_⟩,hp⟩
    exact ⟨hp,hl⟩
  · rintro ⟨⟨hp,hb⟩,hl⟩
    exact ⟨⟨hl,fun d hd=>(hb d hd).trans_le hM⟩,hp,hb⟩

theorem selected_perm (w M k : ℕ) (hM : M≤2^w) :
    (selected w M k).Perm ((List.range M).sublistsLen k) := by
  apply (List.perm_ext_iff_of_nodup ((candidates_nodup w k).filter _)
    (List.nodup_sublistsLen k List.nodup_range)).mpr
  exact selected_mem w M k hM

def digitWidth (M : ℕ) : ℕ := Nat.log 2 M+1

theorem digit_fit (M : ℕ) : M<2^(digitWidth M) :=
  Nat.lt_pow_succ_log_self (by decide : 1<2) M

theorem digit_capacity (M : ℕ) : 2^(digitWidth M)≤2*max 1 M := by
  by_cases hM : M=0
  · simp [digitWidth,hM]
  · have h := Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hM)
    rw [digitWidth,pow_succ]
    calc
      2^(Nat.log 2 M)*2≤2*M := by omega
      _≤2*max 1 M := Nat.mul_le_mul_left 2 (le_max_right _ _)

theorem candidate_count (M k : ℕ) :
    (candidates (digitWidth M) k).length≤(2*max 1 M)^k := by
  simp only [candidates,List.length_map,List.length_range,pow_mul]
  exact Nat.pow_le_pow_left (digit_capacity M) k

theorem chosen_perm (M k : ℕ) :
    (selected (digitWidth M) M k).Perm ((List.range M).sublistsLen k) :=
  selected_perm _ _ _ (digit_fit M).le

end NearCubicWires.RepairOrdinary.RowTupleSubsets

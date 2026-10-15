import Proof.Supplier.RowTupleCounter

/-! The bounded binary cursor is decoded low block first. Positional digits
are never deduplicated; encoding and decoding are exact within the produced
bit width. These are the values consumed by the upcoming physical selector. -/
namespace NearCubicWires.RepairOrdinary.RowTupleDigits
open LocalBitMultitape RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def digits (w : ℕ) : ℕ→ℕ→List ℕ
  | 0,_=>[]
  | k+1,n=>n%2^w::digits w k (n/2^w)
def encode (w : ℕ) : List ℕ→ℕ
  | []=>0
  | d::ds=>d+2^w*encode w ds

theorem digits_length (w k n : ℕ) : (digits w k n).length=k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [digits,ih]

theorem digits_bound (w k n : ℕ) : ∀ d∈digits w k n,d<2^w := by
  induction k generalizing n with
  | zero => simp [digits]
  | succ k ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Nat.mod_lt _ (by positivity)
    · exact ih _ _ hd

theorem encode_bound (w : ℕ) (ds : List ℕ) (hd : ∀ d∈ds,d<2^w) :
    encode w ds<2^(w*ds.length) := by
  induction ds with
  | nil => simp [encode]
  | cons d ds ih =>
    have hdt := ih (fun a ha=>hd a (List.mem_cons_of_mem _ ha))
    have hdh := hd d (by simp)
    have h := Nat.mul_le_mul_left (2^w) (Nat.succ_le_of_lt hdt)
    simp only [encode,List.length_cons,Nat.mul_add,Nat.mul_one,pow_add]
    nlinarith

theorem digits_encode (w : ℕ) (ds : List ℕ) (hd : ∀ d∈ds,d<2^w) :
    digits w ds.length (encode w ds)=ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hdh := hd d (by simp)
    have hdt := ih (fun a ha=>hd a (List.mem_cons_of_mem _ ha))
    simp only [List.length_cons,encode,digits,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hdh,
      Nat.add_mul_div_left _ _ (by positivity : 0<2^w),Nat.div_eq_of_lt hdh,zero_add,hdt]

theorem encode_digits (w k n : ℕ) (hn : n<2^(w*k)) : encode w (digits w k n)=n := by
  induction k generalizing n with
  | zero => simp only [Nat.mul_zero,pow_zero] at hn; simp [digits,encode,show n=0 by omega]
  | succ k ih =>
    have hn' : n/2^w<2^(w*k) := by
      apply (Nat.div_lt_iff_lt_mul (by positivity : 0<2^w)).mpr
      simpa only [Nat.mul_add,Nat.mul_one,pow_add,Nat.mul_comm] using hn
    rw [digits,encode,ih _ hn']
    exact Nat.mod_add_div n (2^w)

theorem blocks_length (w : ℕ) (ds : List ℕ) : (ds.flatMap (binary w)).length=w*ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [ih,Nat.mul_add,Nat.add_comm]

theorem binary_encode (w : ℕ) (ds : List ℕ) (hd : ∀ d∈ds,d<2^w) :
    binary (w*ds.length) (encode w ds)=ds.flatMap (binary w) := by
  have hv : RadixSemantics.value (ds.flatMap (binary w))=encode w ds := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.flatMap_cons,RadixSemantics.value_append,binary_length,
        binary_value w d (hd d (by simp)),encode]
      rw [ih (fun a ha=>hd a (List.mem_cons_of_mem _ ha))]
  have h := BoundedCounter.binary_of_value (ds.flatMap (binary w))
  rw [blocks_length,hv] at h
  exact h

def candidates (w k : ℕ) := (List.range (2^(w*k))).map (digits w k)

theorem candidates_mem (w k : ℕ) (ds : List ℕ) :
    ds∈candidates w k ↔ ds.length=k ∧ ∀ d∈ds,d<2^w := by
  constructor
  · intro h
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp h
    exact ⟨digits_length w k n,digits_bound w k n⟩
  · rintro ⟨hl,hd⟩
    refine List.mem_map.mpr ⟨encode w ds,?_,?_⟩
    · apply List.mem_range.mpr
      simpa only [hl] using encode_bound w ds hd
    · simpa only [hl] using digits_encode w ds hd

theorem candidates_nodup (w k : ℕ) : (candidates w k).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro a ha b hb he
  have h := congrArg (encode w) he
  rw [encode_digits w k a (List.mem_range.mp ha),encode_digits w k b (List.mem_range.mp hb)] at h
  exact h

end NearCubicWires.RepairOrdinary.RowTupleDigits

import Proof.PCP.VerifierDecodingHeaderSemantics
import Proof.PCP.VerifierDecodingTableRun

/-! Fixed-width reconstruction and the exact chunk predicates tested by
sequential tag scans. These supply the canonical re-encoding theorem. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Sequential
open LocalBitMultitape VerifierEncoding RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem slice_drop (bits : List Bool) (a b w : ℕ) :
    slice (bits.drop a) b w=slice bits (a+b) w := by simp only [slice,List.drop_drop]

theorem slice_slice (bits : List Bool) (a W b w : ℕ) (h : b+w≤W) :
    slice (slice bits a W) b w=slice bits (a+b) w := by
  simp only [slice,List.drop_take,List.drop_drop,List.take_take]
  rw [Nat.min_eq_left (by omega : w≤W-b)]

theorem flat_slices (n w : ℕ) (bits : List Bool) :
    (List.ofFn fun i : Fin n => slice bits (i.val*w) w).flatten=bits.take (n*w) := by
  induction n generalizing bits with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.flatten_cons]
    have he : (fun i : Fin n => slice bits (i.succ.val*w) w)=
        (fun i : Fin n => slice (bits.drop w) (i.val*w) w) := by
      funext i
      rw [slice_drop]
      congr 1
      simp only [Fin.val_succ]
      ring
    rw [he,ih]
    have hn : (n+1)*w=w+n*w := by ring
    rw [hn,List.take_add]
    simp [slice]

theorem flat_slices_exact (n w : ℕ) (bits : List Bool) (h : bits.length=n*w) :
    (List.ofFn fun i : Fin n => slice bits (i.val*w) w).flatten=bits := by
  rw [flat_slices,←h,List.take_length]

theorem slice_length (bits : List Bool) (a w : ℕ) (h : a+w≤bits.length) :
    (slice bits a w).length=w := by
  simp only [slice,List.length_take,List.length_drop]
  omega

theorem received_take (bits : List Bool) (limit : Fin 5) :
    TagMachine.received (TagMachine.extend (bits.take limit.val)) limit.val=
      TagMachine.received (TagMachine.extend bits) limit.val := by
  funext i
  by_cases h : i.val<limit.val <;>
    simp [TagMachine.received,TagMachine.extend,h]

theorem tag_tests_iff (limit : Fin 5) (test : TagMachine.Word → Bool) (n : ℕ) (bits : List Bool) :
    TagScan.tests limit test n bits=true ↔ limit.val*n≤bits.length ∧
      ∀ i : Fin n,test (TagMachine.received (TagMachine.extend (slice bits (i.val*limit.val) limit.val)) limit.val)=true := by
  induction n generalizing bits with
  | zero => simp [TagScan.tests]
  | succ n ih =>
    rw [TagScan.tests]
    by_cases h : limit.val≤bits.length
    · rw [if_pos h,Bool.and_eq_true,ih]
      constructor
      · rintro ⟨ht,hlen,hall⟩
        refine ⟨by simp only [List.length_drop] at hlen; rw [Nat.mul_succ]; omega,?_⟩
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.val_zero,Nat.zero_mul,slice,List.drop_zero,received_take] using ht
        · have hj := hall j
          rw [slice_drop] at hj
          have he : limit.val+j.val*limit.val=j.succ.val*limit.val := by simp only [Fin.val_succ]; ring
          rw [he] at hj
          exact hj
      · rintro ⟨hlen,hall⟩
        refine ⟨?_,?_,?_⟩
        · simpa only [Fin.val_zero,Nat.zero_mul,slice,List.drop_zero,received_take] using hall 0
        · simp only [List.length_drop]
          rw [Nat.mul_succ] at hlen
          omega
        · intro i
          have hi := hall i.succ
          rw [slice_drop]
          have he : limit.val+i.val*limit.val=i.succ.val*limit.val := by simp only [Fin.val_succ]; ring
          rw [he]
          exact hi
    · rw [if_neg h]
      simp only [Bool.false_eq_true,false_iff,not_and]
      intro hn
      have hm : limit.val≤limit.val*(n+1) := Nat.le_mul_of_pos_right _ (by omega)
      omega

end NearCubicWires.RepairSource.VerifierDecoding.Sequential

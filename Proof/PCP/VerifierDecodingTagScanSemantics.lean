import Proof.PCP.VerifierDecodingTagScan

/-! Literal resource and semantic endpoints of the sequential scans. A
successful scan consumes exactly limit*count payload bits, so the final
code delimiter supplies the required expectedLength equality directly. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TagScan
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tests (limit : Fin 5) (test : TagMachine.Word → Bool) : ℕ → List Bool → Bool
  | 0,_ => true
  | n+1,bits => if limit.val ≤ bits.length then
      test (TagMachine.received (TagMachine.extend bits) limit.val) && tests limit test n (bits.drop limit.val)
    else false

theorem iterate_tests (limit : Fin 5) (test : TagMachine.Word → Bool) (count : ℕ) (x : State) :
    (RepeatMachine.iterate (next limit test) count x).1 = tests limit test count x.rest := by
  induction count generalizing x with
  | zero => rfl
  | succ count ih =>
    by_cases h : limit.val ≤ x.rest.length
    · cases ht : test (TagMachine.received (TagMachine.extend x.rest) limit.val) <;>
        simp [RepeatMachine.iterate,next,tests,h,ht,ih]
    · simp [RepeatMachine.iterate,next,tests,h]

theorem successful_shape (limit : Fin 5) (test : TagMachine.Word → Bool) (count : ℕ) (x : State)
    (h : (RepeatMachine.iterate (next limit test) count x).1 = true) :
    let out := (RepeatMachine.iterate (next limit test) count x).2
    out.source = x.source ∧ out.pos = x.pos+2*limit.val*count ∧
      out.rest = x.rest.drop (limit.val*count) ∧ limit.val*count ≤ x.rest.length := by
  induction count generalizing x with
  | zero => simp [RepeatMachine.iterate]
  | succ count ih =>
    have hf : limit.val ≤ x.rest.length := by
      by_contra hn
      simp [RepeatMachine.iterate,next,hn] at h
    have ht : test (TagMachine.received (TagMachine.extend x.rest) limit.val) = true := by
      cases he : test (TagMachine.received (TagMachine.extend x.rest) limit.val) with
      | false => simp [RepeatMachine.iterate,next,hf,he] at h
      | true => rfl
    have hn : (next limit test x).1 = true := by simp [next,hf,ht]
    simp only [RepeatMachine.iterate,hn,↓reduceIte] at h ⊢
    obtain ⟨hs,hp,hr,hb⟩ := ih (next limit test x).2 h
    simp only [next,hf,↓reduceIte] at hs hp hr hb ⊢
    refine ⟨hs,?_,?_,?_⟩
    · rw [hp]
      ring
    · rw [hr,List.drop_drop]
      congr 1
      ring
    · simp only [List.length_drop] at hb
      have he : limit.val*(count+1) = limit.val+limit.val*count := by ring
      rw [he]
      omega

theorem flags_test (count : ℕ) (bits : List Bool) :
    tests 2 (fun _ => true) count bits = decide (2*count ≤ bits.length) := by
  induction count generalizing bits with
  | zero => simp [tests]
  | succ count ih =>
    by_cases h : 2 ≤ bits.length
    · simp only [tests,show (2 : Fin 5).val = 2 from rfl,if_pos h,Bool.true_and,ih,List.length_drop]
      have he : (2*count ≤ bits.length-2) ↔ (2*(count+1) ≤ bits.length) := by omega
      exact decide_eq_decide.mpr he
    · simp only [tests,show (2 : Fin 5).val = 2 from rfl,if_neg h]
      symm
      apply decide_eq_false
      omega

theorem zeros_test (count : ℕ) (bits : List Bool) :
    tests 1 (fun word => !(word 0)) count bits = true ↔
      count ≤ bits.length ∧ bits.take count = List.replicate count false := by
  induction count generalizing bits with
  | zero => simp [tests]
  | succ count ih =>
    cases bits with
    | nil => simp [tests]
    | cons bit bits =>
      cases bit <;> simp [tests,TagMachine.received,TagMachine.extend,ih,List.replicate_succ]

end NearCubicWires.RepairSource.VerifierDecoding.TagScan

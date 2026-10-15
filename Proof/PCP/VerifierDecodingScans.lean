import Proof.PCP.VerifierDecodingTagScanSemantics

/-! Normalized enclosing endpoints of the repeated decoder scans. Successful
runs retain the entire code, move its cursor by the exact number of consumed
payload bits, and restore the physically supplied unary driver to head one. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TagScan
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def initial (pre bits : List Bool) (count : ℕ) :=
  RepeatMachine.cfg 0 (TagMachine.cfg 0 (fun _ => false) (pre++frame bits) pre.length) count 1
noncomputable def finished (pre bits : List Bool) (count : ℕ) (limit : Fin 5) :=
  RepeatMachine.cfg 3
    (TagMachine.cfg 0 (fun _ => false) (pre++frame bits) (pre.length+2*limit.val*count)) count 1

noncomputable def CheckedResult (pre bits : List Bool) (count : ℕ) (limit : Fin 5)
    (test : TagMachine.Word → Bool) (final : Configuration 2 (Fintype.card (RepeatMachine.Control (Fintype.card TagMachine.Control)))) : Prop :=
  if tests limit test count bits then final = finished pre bits count limit
  else final.control = RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 4

theorem checked_run (pre bits : List Bool) (count : ℕ) (limit : Fin 5) (test : TagMachine.Word → Bool) :
    ∃ receipt, runFrom (machine limit test) (count*(2*limit.val+4)+3) (initial pre bits count) = some receipt ∧
      receipt.steps ≤ count*(2*limit.val+4)+3 ∧ CheckedResult pre bits count limit test receipt.final := by
  let x : State := ⟨pre++frame bits,pre.length,bits⟩
  obtain ⟨r,hr,hs,hf⟩ := scan_run pre bits count limit test
  change RepeatMachine.Result input count (RepeatMachine.iterate (next limit test) count x) r.final at hf
  refine ⟨r,hr,hs,?_⟩
  have ht : (RepeatMachine.iterate (next limit test) count x).1 = tests limit test count bits := iterate_tests limit test count x
  cases h : tests limit test count bits with
  | false =>
    simpa only [CheckedResult,h,Bool.false_eq_true,↓reduceIte,RepeatMachine.Result,ht] using hf
  | true =>
    have ho := successful_shape limit test count x (ht.trans h)
    rcases ho with ⟨hsource,hpos,_,_⟩
    have he : RepeatMachine.cfg 3 (input (RepeatMachine.iterate (next limit test) count x).2) count 1 =
        finished pre bits count limit := by
      simp [input,finished,x] at hsource hpos ⊢
      rw [hsource,hpos]
    simp only [RepeatMachine.Result,ht,h,↓reduceIte] at hf
    simpa only [CheckedResult,h,↓reduceIte,he] using hf

/-- Arbitrary state flags: success means exactly that 2s bits were available. -/
theorem flags_run (pre bits : List Bool) (s : ℕ) :
    ∃ receipt, runFrom (machine 2 (fun _ => true)) (8*s+3) (initial pre bits s) = some receipt ∧
      receipt.steps ≤ 8*s+3 ∧
      (if 2*s ≤ bits.length then receipt.final = finished pre bits s 2
       else receipt.final.control = RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 4) := by
  obtain ⟨r,hr,hs,hf⟩ := checked_run pre bits s 2 (fun _ => true)
  refine ⟨r,?_,?_,?_⟩
  · simpa [Nat.mul_comm] using hr
  · simpa [Nat.mul_comm] using hs
  · simpa only [CheckedResult,flags_test,decide_eq_true_eq] using hf

/-- Exact all-zero j-bit field used only by the missing-rule branch. -/
theorem zeros_run (pre bits : List Bool) (j : ℕ) :
    ∃ receipt, runFrom (machine 1 (fun word => !(word 0))) (6*j+3) (initial pre bits j) = some receipt ∧
      receipt.steps ≤ 6*j+3 ∧
      (if j ≤ bits.length ∧ bits.take j = List.replicate j false then receipt.final = finished pre bits j 1
       else receipt.final.control = RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 4) := by
  obtain ⟨r,hr,hs,hf⟩ := checked_run pre bits j 1 (fun word => !(word 0))
  refine ⟨r,?_,?_,?_⟩
  · simpa [Nat.mul_comm] using hr
  · simpa [Nat.mul_comm] using hs
  · simpa only [CheckedResult,zeros_test] using hf

/-- Every present tag is canonical; every absent tag is the literal zero tag. -/
theorem tags_run (pre bits : List Bool) (t : ℕ) (present : Bool) :
    ∃ receipt, runFrom (machine 4 (TagMachine.valid present)) (12*t+3) (initial pre bits t) = some receipt ∧
      receipt.steps ≤ 12*t+3 ∧ CheckedResult pre bits t 4 (TagMachine.valid present) receipt.final := by
  simpa [Nat.mul_comm] using checked_run pre bits t 4 (TagMachine.valid present)

end NearCubicWires.RepairSource.VerifierDecoding.TagScan

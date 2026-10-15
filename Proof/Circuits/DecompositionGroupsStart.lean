import Proof.Circuits.DecompositionBalancedGroups

/-! First physical allocation and repeated shared serialization for arbitrary
actual fixed group count. Both count drivers and the capacity arrive as real
tapes; the original input wrapper remains responsible for producing them. -/
namespace NearCubicWires.RepairOrdinary.DecompositionGroupsStart
open LocalBitMultitape PCPSerializerReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (capacity count : ℕ) (source out : List Bool) (i : Fin 132) : List Bool :=
  if i=0 then source else if i=2 then CompareMachine.word count
  else if i=129 then out else if i=130 then List.replicate capacity true else []
noncomputable def entry (capacity count : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  (⟨eraseMachine.start,bodyHeads pos out.length,input capacity count source out⟩ : Configuration 132 _)

theorem scratch_empty (capacity count : ℕ) (source out : List Bool) (j : Fin 127) :
    input capacity count source out (scratchSlots j)=[] := by
  have hsmall := scratch_small j
  have h0 := (scratch_not_live j).1
  have h2 := (scratch_not_live j).2
  have h129 : scratchSlots j≠129 := by intro h; rw [h] at hsmall; contradiction
  have h130 : scratchSlots j≠130 := by intro h; rw [h] at hsmall; contradiction
  simp only [input,h0,h2,h129,h130,ite_false]

theorem start_run (capacity count : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :
    ∃ r,runFrom eraseMachine (2*capacity+4) (entry capacity count source pos out)=some r ∧
      r.final.heads=(bodyEntry capacity (capacity+1) source pos count out).heads ∧
      r.final.tapes=(bodyEntry capacity (capacity+1) source pos count out).tapes ∧
      r.steps=2*capacity+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := erase_run capacity 0 (bodyHeads pos out.length)
    (input capacity count source out)
    (by intro j; rw [scratch_empty]; exact Nat.zero_le _)
    (by rfl) (by rfl) (by intro j; fin_cases j <;> rfl) (by rfl) (by rfl)
  have result : Result capacity 0 pos count source out r.final := by
    refine ⟨rh,?_,?_,?_,?_,?_,?_⟩
    · rw [rt,erased_live capacity 0 _ 0 (Or.inl rfl)]; rfl
    · rw [rt,erased_live capacity 0 _ 2 (Or.inr (Or.inl rfl))]; rfl
    · rw [rt,erased_live capacity 0 _ 129 (Or.inr (Or.inr rfl))]; rfl
    · rw [rt]; exact erased_driver capacity 0 _
    · rw [rt]; exact erased_log capacity 0 _
    · intro j; rw [rt]; exact erased_slot capacity 0 _ j
  refine ⟨r,hr,?_,?_,rs⟩
  · rw [bodyEntry_heads]; exact rh
  · rw [bodyEntry_tapes]
    simpa only [Nat.zero_max] using result.tapes_eq

end NearCubicWires.RepairOrdinary.DecompositionGroupsStart

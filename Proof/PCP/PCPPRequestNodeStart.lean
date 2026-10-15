import Proof.PCP.PCPPRequestNodeEndpoint

/-! The node bank's first allocation is an actual parallel erase
sweep. The source cursor and outside-bank capacity/output remain live. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeStart
open LocalBitMultitape PCPPRequestNodeReuse
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (capacity : ℕ) (source out : List Bool) (i : Fin 646) : List Bool :=
  if i=0 then source else if i=643 then out
  else if i=644 then List.replicate capacity true else []
noncomputable def entry (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  (⟨eraseMachine.start,bodyHeads pos out.length,input capacity source out⟩ : Configuration 646 _)

theorem scratch_not_live (j : Fin 642) : scratchSlots j≠0 ∧ scratchSlots j≠643 ∧ scratchSlots j≠644 := by
  have h := scratch_small j
  have hpos : 0<(scratchSlots j).val := by change 0<j.val+1; omega
  constructor
  · intro he; rw [he] at hpos; contradiction
  constructor <;> intro he <;> rw [he] at h <;> contradiction

theorem scratch_empty (capacity : ℕ) (source out : List Bool) (j : Fin 642) :
    input capacity source out (scratchSlots j)=[] := by
  obtain ⟨h0,h643,h644⟩ := scratch_not_live j
  simp only [input,h0,h643,h644,ite_false]

theorem start_run (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :
    ∃ r,runFrom eraseMachine (2*capacity+4) (entry capacity source pos out)=some r ∧
      r.final.heads=(bodyEntry capacity source pos out).heads ∧
      r.final.tapes=(bodyEntry capacity source pos out).tapes ∧
      r.steps=2*capacity+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := erase_run capacity 0 (bodyHeads pos out.length)
    (input capacity source out)
    (by intro j; rw [scratch_empty]; exact Nat.zero_le _)
    (by rfl) (by rfl)
    (by intro j; obtain ⟨h0,h643,_⟩ := scratch_not_live j; simp only [bodyHeads,h0,h643,ite_false])
    (by rfl) (by rfl)
  refine ⟨r,hr,?_,?_,rs⟩
  · rw [bodyEntry_heads]; exact rh
  · rw [bodyEntry_tapes,rt]
    funext i
    by_cases h0 : i=0
    · subst i
      rw [erased_live capacity 0 _ 0 (Or.inl rfl)]
      rfl
    by_cases h643 : i=643
    · subst i
      rw [erased_live capacity 0 _ 643 (Or.inr rfl)]
      rfl
    by_cases h644 : i=644
    · subst i; exact erased_driver capacity 0 _
    by_cases h645 : i=645
    · subst i
      change erased capacity 0 (input capacity source out) 645=List.replicate (capacity+1) false
      simpa only [Nat.zero_max] using erased_log capacity 0 (input capacity source out)
    obtain ⟨j,hj⟩ := scratch_covers i h0 h643 h644 h645
    simpa only [bodyTapes,h0,h643,h644,h645,ite_false,hj] using
      erased_slot capacity 0 (input capacity source out) j

end NearCubicWires.RepairOrdinary.PCPPRequestNodeStart

import Proof.PCP.PCPTraversalLayout
import Proof.Amplification.RecoveryCursorCalls

/-! The serializer's actual cold capacity and count calls, inside its fixed
finite traversal controller. No mass, width, capacity or current-count tape
is a supplied parameter of this entry. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_input (source : List Bool) (count : ℕ) (j : Fin 39) :
    input source count (capacitySlots j)=PCPSerializerCapacity.input 10 source count j := by
  refine Fin.addCases (m:=5) (n:=34) (fun i => ?_) (fun i => ?_) j
  · fin_cases i <;> simp [input,capacitySlots,PCPSerializerCapacity.input] <;> rfl
  · have h0 : capacitySlots (i.natAdd 5)≠0 := by
      intro h; have hv := congrArg Fin.val h; dsimp [capacitySlots] at hv; omega
    have h2 : capacitySlots (i.natAdd 5)≠2 := by
      intro h; have hv := congrArg Fin.val h; dsimp [capacitySlots] at hv; omega
    simp only [input,h0,h2,↓reduceIte]
    exact (Fin.addCases_right (m:=5) (n:=34) (motive:=fun _ => List Bool)
      (left:=![source,[],RepairSource.VerifierDecoding.CompareMachine.word count,[],[]])
      (right:=fun _ => []) i).symm

theorem capacity_heads (pos : ℕ) (j : Fin 39) :
    heads pos (capacitySlots j)=PCPSerializerCapacity.heads 10 pos j := by
  refine Fin.addCases (m:=5) (n:=34) (fun i => ?_) (fun i => ?_) j
  · fin_cases i <;> simp [heads,capacitySlots,PCPSerializerCapacity.heads] <;> rfl
  · have h0 : capacitySlots (i.natAdd 5)≠0 := by
      intro h; have hv := congrArg Fin.val h; dsimp [capacitySlots] at hv; omega
    have h2 : capacitySlots (i.natAdd 5)≠2 := by
      intro h; have hv := congrArg Fin.val h; dsimp [capacitySlots] at hv; omega
    simp only [heads,h0,h2,↓reduceIte]
    exact (Fin.addCases_right (m:=5) (n:=34) (motive:=fun _ => ℕ)
      (left:=![pos,0,1,0,0]) (right:=fun _ => 0) i).symm

def entryFuel (B M : ℕ) := PCPSerializerCapacity.coefficient 10 131072*(B+1)^11+2*M+12
noncomputable def current (q : Fin (sizes 0)) (pos : ℕ)
    (tapes : Fin 128 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes 0)
    (⟨q,PCPSerializerCountEntry.finalHeads (heads pos),tapes⟩ : Configuration 128 (sizes 0))

theorem cold_entry (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool) :
    ∃ fuel≤entryFuel (FieldList.stream fields).length fields.length,
    ∃ tapes : Fin 128 → List Bool,
      Timed machine fuel (entry (pre++FieldList.stream fields++suffix) pre.length fields.length)
        (current (programs 0).start pre.length tapes) ∧
      tapes 0=pre++FieldList.stream fields++suffix ∧
      tapes 2=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      tapes 1=List.replicate (FieldList.stream fields).length true ∧
      tapes 28=List.replicate (131072*((FieldList.stream fields).length+1)^10) true ∧
      tapes 79=List.replicate fields.length true ∧ tapes 81=[false] ∧
      tapes 88=List.replicate (fields.length+2) false ∧
      ∀ i : Fin 128,39 ≤ i.val → i≠79 → i≠81 → i≠88 → tapes i=[] := by
  let source := pre++FieldList.stream fields++suffix
  let initial := input source fields.length
  obtain ⟨first,hfirst,hsteps,hheads,hsource,hcount,hB,hC,hother⟩ :=
    PCPSerializerCapacity.focused_run 10 131072 capacitySlots capacity_injective pre fields suffix
      (heads pre.length) initial (capacity_input source fields.length) (capacity_heads pre.length)
  have h79 : first.final.tapes 79=[] := by
    rw [hother 79 (by intro j h; have hv := congrArg Fin.val h; simp only [capacitySlots] at hv; omega)]
    rfl
  have h81 : first.final.tapes 81=[] := by
    rw [hother 81 (by intro j h; have hv := congrArg Fin.val h; simp only [capacitySlots] at hv; omega)]
    rfl
  have h88 : first.final.tapes 88=[] := by
    rw [hother 88 (by intro j h; have hv := congrArg Fin.val h; simp only [capacitySlots] at hv; omega)]
    rfl
  have hcount' : first.final.tapes 2=RepairSource.VerifierDecoding.CompareMachine.word fields.length := hcount
  obtain ⟨last,hlast,hlsteps,hlheads,hltapes⟩ := PCPSerializerCountEntry.ready_run fields.length
    first.final.heads first.final.tapes hcount' h79 h81 h88
    (by rw [hheads]; rfl) (by rw [hheads]; rfl) (by rw [hheads]; rfl) (by rw [hheads]; rfl)
  have hfRun : runFrom (programs 37)
      (PCPSerializerCapacity.coefficient 10 131072*((FieldList.stream fields).length+1)^11)
      ⟨(programs 37).start,heads pre.length,initial⟩=some first := hfirst
  obtain ⟨n,hn,ht⟩ := call_receipt sizes programs 37 next 37 38 _ _ first hfRun (by
    simp [next])
  have hlRun : runFrom (programs 38) (2*fields.length+10)
      (RecoveryCalls.restarted (programs 38) first.final.heads first.final.tapes)=some last := hlast
  obtain ⟨m,hm,hu⟩ := call_receipt sizes programs 37 next 38 0 _ _ last hlRun (by
    simp [next])
  have hp := ht.trans hu
  have hc : controlConfig (RecoveryCalls.code sizes 0)
      (RecoveryCalls.restarted (programs 0) last.final.heads last.final.tapes)=
      current (programs 0).start pre.length last.final.tapes := by
    rw [hlheads,hheads]
    rfl
  rw [hc] at hp
  have hfield := PCPSerializerCountEntry.output_fields fields.length first.final.tapes
  refine ⟨n+m,by dsimp [entryFuel]; omega,last.final.tapes,hp,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hltapes,PCPSerializerCountEntry.output_other _ _ hcount' 0 (by decide) (by decide) (by decide)]
    exact hsource
  · rw [hltapes]; exact hfield.1
  · rw [hltapes,PCPSerializerCountEntry.output_other _ _ hcount' 1 (by decide) (by decide) (by decide)]
    exact hB
  · rw [hltapes,PCPSerializerCountEntry.output_other _ _ hcount' 28 (by decide) (by decide) (by decide)]
    exact hC
  · rw [hltapes]; exact hfield.2.1
  · rw [hltapes]; exact hfield.2.2.1
  · rw [hltapes]; exact hfield.2.2.2
  · intro i hi hi79 hi81 hi88
    rw [hltapes,PCPSerializerCountEntry.output_other _ _ hcount' i hi79 hi81 hi88]
    rw [hother i (by
      intro j h
      have hv := congrArg Fin.val h
      dsimp [capacitySlots] at hv
      omega)]
    have h0 : i≠0 := by intro h; subst i; simp at hi
    have h2 : i≠2 := by intro h; subst i; simp at hi
    simp [initial,input,h0,h2]

end NearCubicWires.RepairOrdinary.PCPTraversal

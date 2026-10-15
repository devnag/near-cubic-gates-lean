import Proof.PCP.PCPPNativeNodeBinary

/-! The input-node prefix executes the native reader and the retained
projection-row lookup. Its result is the actual controller boundary before
the projection-kind classifier, with the decoded kind/index physical. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation RecoveryExecution SourceInterfaces
open RepairSource RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem lookup_read_away (i : Fin 28) (hi : i≠2) : ∀ j,readSlots j≠lookupSlots i := by
  fin_cases i <;> first | exact False.elim (hi rfl) | decide

theorem lookup_initial (source queries : List Bool) (pos base position C : ℕ) (out : List Bool)
    (count : ℕ) (i : Fin 28) (hi : i≠2) :
    initialHeads pos out (lookupSlots i)=PCPPNativeProjectionLookup.heads 0 i ∧
      initialData source queries base position C out (lookupSlots i)=PCPPNativeProjectionLookup.templateData queries count i := by
  fin_cases i <;> first | exact False.elim (hi rfl) |
    simp [initialHeads,initialData,lookupSlots,PCPPNativeProjectionLookup.heads,PCPPNativeProjectionLookup.templateData]

def projectionPrefixBudget {r : ℕ} (skipped : List (List Bool)) (p : ProjectedRandomBit r) :=
  PCPPNativeNodeClassify.budget 1 skipped.length 0+
    PCPPNativeProjectionLookup.budget skipped (projectionCode p).bits+2

theorem projection_prefix_run {r : ℕ} (pre tail : List Bool) (skipped : List (List Bool))
    (p : ProjectedRandomBit r) (suffix : List Bool) (base position C : ℕ) (out : List Bool) :
    ∃ steps heads data,Timed machine steps
      (entry (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
        (FieldList.stream skipped++frame (projectionCode p).bits++suffix) pre.length base position C out)
      (boundary 13 heads data) ∧ steps ≤ projectionPrefixBudget skipped p ∧
      data 0=PCPPNativeNodeRead.source pre tail 1 skipped.length 0 ∧
      heads 0=pre.length+(natWord 1).length+(natWord skipped.length).length+(natWord 0).length ∧
      data 1=FieldList.stream skipped++frame (projectionCode p).bits++suffix ∧
      heads 1=(FieldList.stream skipped).length+2*(projectionCode p).bits.length+1 ∧
      data 14=CompareMachine.word (PCPPNativeProjectionTyped.kind p).val ∧ heads 14=1 ∧
      data 15=CompareMachine.word (PCPPNativeProjectionTyped.index p) ∧ heads 15=1 ∧
      (∀ i,(∀ j,readSlots j≠i) → (∀ j,lookupSlots j≠i) →
        heads i=initialHeads pre.length out i ∧
        data i=initialData (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
          (FieldList.stream skipped++frame (projectionCode p).bits++suffix) base position C out i) := by
  let queries := FieldList.stream skipped++frame (projectionCode p).bits++suffix
  obtain ⟨a,ha,as,ac,a0,ah0,_,_,a7,ah7,_,_,akeep⟩ := reader_run pre tail queries 1 skipped.length 0 base position C out
  have ready (i : Fin 28) : a.final.heads (lookupSlots i)=PCPPNativeProjectionLookup.heads 0 i ∧
      a.final.tapes (lookupSlots i)=PCPPNativeProjectionLookup.templateData queries skipped.length i := by
    by_cases hi : i=2
    · subst i; exact ⟨ah7,a7⟩
    · have k := akeep (lookupSlots i) (lookup_read_away i hi)
      have z := lookup_initial (PCPPNativeNodeRead.source pre tail 1 skipped.length 0) queries pre.length base position C out skipped.length i hi
      exact ⟨k.1.trans z.1,k.2.trans z.2⟩
  obtain ⟨raw,hraw,raws,r0,rh0,_,_,r14,r15,rh14,rh15⟩ := PCPPNativeProjectionTyped.lookup_run [] skipped p suffix
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hraw r0 rh0
  obtain ⟨b,hb,_,bs,bh,bt,bkeep⟩ := RecoveryFocus.dock lookupSlots lookup_injective
    PCPPNativeProjectionLookup.machine _ a.final.heads a.final.tapes
    (PCPPNativeProjectionLookup.templateEntry queries 0 skipped.length)
    (fun i => (ready i).1) (fun i => (ready i).2) raw hraw
  have firstCall := call_run 0 12 _ _ _ a ha (parsed_next 1 a.final.control a.final.scanned ac)
  have secondCall := call_run 12 13 _ _ _ b hb (by rfl)
  have b0 := bkeep 0 (by decide)
  refine ⟨a.steps+1+(b.steps+1),b.final.heads,b.final.tapes,firstCall.trans secondCall,?_,
    b0.2.trans a0,b0.1.trans ah0,(bt 0).trans r0,(bh 0).trans rh0,
    (bt 22).trans r14,(bh 22).trans rh14,(bt 26).trans r15,(bh 26).trans rh15,?_⟩
  · unfold projectionPrefixBudget; omega
  · intro i hir hil
    exact ⟨(bkeep i hil).1.trans (akeep i hir).1,(bkeep i hil).2.trans (akeep i hir).2⟩

theorem word_tag_run (slot : Fin 119) (tag : Fin 5) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (hh : heads slot=1) (ht : data slot=CompareMachine.word tag.val) :
    ∃ r,runFrom (tagProgram slot) (tag.val+1)
      (RecoveryCalls.restarted (tagProgram slot) heads data)=some r ∧
      r.steps=tag.val+1 ∧ r.final.control.val=tag.val+5 ∧
      (∀ i,i≠slot → r.final.heads i=heads i ∧ r.final.tapes i=data i) := by
  obtain ⟨raw,hr,rs,rc,_⟩ := PCPPNativeTemplateRaw.tag_word_run tag
  obtain ⟨r,hrun,rctrl,steps,_,_,keep⟩ := RecoveryFocus.dock (fun _ : Fin 1 => slot)
    (by intro i j _; exact Subsingleton.elim i j) PCPPNativeTag.machine _ heads data
    (PCPPNativeTemplateRaw.tagWordEntry tag) (fun _ => hh) (fun _ => ht) raw hr
  refine ⟨r,hrun,steps.trans rs,?_,?_⟩
  · rw [rctrl]; exact rc
  · intro i hi; exact keep i (fun _ => Ne.symm hi)

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine

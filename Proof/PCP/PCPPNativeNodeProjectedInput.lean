import Proof.PCP.PCPPNativeNodeValue

/-! The full positive/negated projection paths use the actual decoded
index and the retained current-node position. No projection is supplied
as an extra machine parameter or materialized by an unexecuted copy. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation RecoveryExecution SourceInterfaces RepairSource
open ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputProjection {r : ℕ} (negative : Bool) (index : Fin r) : ProjectedRandomBit r :=
  if negative then .negatedBit index else .bit index
def inputKind (negative : Bool) : Fin 5 := if negative then 1 else 0
theorem input_kind {r : ℕ} (negative : Bool) (index : Fin r) :
    PCPPNativeProjectionTyped.kind (inputProjection negative index)=inputKind negative := by
  cases negative <;> rfl
theorem input_index {r : ℕ} (negative : Bool) (index : Fin r) :
    PCPPNativeProjectionTyped.index (inputProjection negative index)=index.val := by
  cases negative <;> rfl
def projectedInputBudget {r : ℕ} (skipped : List (List Bool)) (negative : Bool) (index : Fin r) (position C : ℕ) :=
  projectionPrefixBudget skipped (inputProjection negative index)+(inputKind negative).val+1+
    (4*index.val+16)+PCPPNativeInput.budget negative index.val position C+3

theorem projected_input_run {r : ℕ} (pre tail : List Bool) (skipped : List (List Bool))
    (negative : Bool) (index : Fin r) (suffix : List Bool) (base position C : ℕ) (out : List Bool)
    (hindex : PCPPNativeSumAppend.budget 0 index.val+1 ≤ C)
    (hposition : PCPPNativeSumAppend.budget 0 position+1 ≤ C) :
    ∃ result,runFrom machine (projectedInputBudget skipped negative index position C)
      (entry (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
        (FieldList.stream skipped++frame (projectionCode (inputProjection negative index)).bits++suffix)
        pre.length base position C out)=some result ∧
      result.steps ≤ projectedInputBudget skipped negative index position C ∧
      result.final.tapes 0=PCPPNativeNodeRead.source pre tail 1 skipped.length 0 ∧
      result.final.heads 0=pre.length+(natWord 1).length+(natWord skipped.length).length+(natWord 0).length ∧
      result.final.tapes 1=FieldList.stream skipped++frame (projectionCode (inputProjection negative index)).bits++suffix ∧
      (∀ i,result.final.heads (inputSlots i)=PCPPNativeSumBinary.heads (out++PCPPNativeInput.emitted negative index.val position) i ∧
        result.final.tapes (inputSlots i)=PCPPNativeSumBinary.data 0 index.val position C
          (out++PCPPNativeInput.emitted negative index.val position) i) ∧
      (∀ i,(∀ j,readSlots j≠i) → (∀ j,lookupSlots j≠i) → (∀ j,valueSlots j≠i) →
        (∀ j,inputSlots j≠i) → result.final.heads i=initialHeads pre.length out i ∧
          result.final.tapes i=initialData (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
            (FieldList.stream skipped++frame (projectionCode (inputProjection negative index)).bits++suffix) base position C out i) := by
  obtain ⟨prefixSteps,heads,data,hprefix,ps,p0,ph0,p1,_,p14,ph14,p15,ph15,pkeep⟩ :=
    projection_prefix_run pre tail skipped (inputProjection negative index) suffix base position C out
  rw [input_kind] at p14
  rw [input_index] at p15
  obtain ⟨kind,hkind,ks,kc,kkeep⟩ := word_tag_run 14 (inputKind negative) heads data ph14 p14
  have work (i : Fin 5) (hi : i≠0) :
      kind.final.heads (valueSlots i)=0 ∧ kind.final.tapes (valueSlots i)=[] := by
    have away := value_work_away i hi
    have k := kkeep (valueSlots i) away.2.2
    have p := pkeep (valueSlots i) away.1 away.2.1
    have z := value_work_initial i hi (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
      (FieldList.stream skipped++frame (projectionCode (inputProjection negative index)).bits++suffix)
      pre.length base position C out
    exact ⟨k.1.trans (p.1.trans z.1),k.2.trans (p.2.trans z.2)⟩
  have k15 := kkeep 15 (by decide)
  have ready := value_input index.val kind.final.heads kind.final.tapes
    (k15.1.trans ph15) (k15.2.trans p15) work
  obtain ⟨value,hvalue,vs,vh,vt,vkeep⟩ := value_run index.val kind.final.heads kind.final.tapes ready.1 ready.2
  have fieldReady (i : Fin 24) :
      value.final.heads (fieldSlots true i)=PCPPNativeAddressReusable.heads out i ∧
      value.final.tapes (fieldSlots true i)=PCPPNativeAddressReusable.data 0 index.val C out i := by
    by_cases hi : i=1
    · subst i; exact ⟨vh 1,vt⟩
    · have v := vkeep (fieldSlots true i) (field_value_away i hi)
      have k := kkeep (fieldSlots true i) (field_kind_away i)
      have p := pkeep (fieldSlots true i) (field_read_away true i) (field_lookup_away true i)
      have z := initial_field true i hi (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
        (FieldList.stream skipped++frame (projectionCode (inputProjection negative index)).bits++suffix)
        pre.length base position index.val C out
      exact ⟨v.1.trans (k.1.trans (p.1.trans z.1)),v.2.trans (k.2.trans (p.2.trans z.2))⟩
  have positionReady : value.final.heads 3=0 ∧ value.final.tapes 3=List.replicate position true := by
    have v := vkeep 3 (by decide)
    have k := kkeep 3 (by decide)
    have p := pkeep 3 (by decide) (by decide)
    exact ⟨v.1.trans (k.1.trans p.1),v.2.trans (k.2.trans p.2)⟩
  have inputReady (i : Fin 25) : value.final.heads (inputSlots i)=PCPPNativeSumBinary.heads out i ∧
      value.final.tapes (inputSlots i)=PCPPNativeSumBinary.data 0 index.val position C out i := by
    refine Fin.addCases (m := 24) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa only [inputSlots,PCPPNativeSumBinary.heads,PCPPNativeSumBinary.data,Fin.addCases_left,
        PCPPNativeAddressReusable.heads,PCPPNativeAddressReusable.data,PCPPNativeSumReusable.heads,
        PCPPNativeSumReusable.data] using fieldReady j
    · fin_cases j; exact positionReady
  obtain ⟨raw,hraw,raws,rawh,rawt⟩ := PCPPNativeInput.node_run negative index.val position C out hindex hposition
  obtain ⟨written,hw,_,ws,wh,wt,wkeep⟩ := RecoveryFocus.dock inputSlots input_injective
    (PCPPNativeInput.machine negative) _ value.final.heads value.final.tapes
    (PCPPNativeInput.entry negative index.val position C out)
    (fun i => (inputReady i).1) (fun i => (inputReady i).2) raw hraw
  have full : Timed machine (prefixSteps+(kind.steps+1)+(value.steps+1)+(written.steps+1))
      (entry (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
        (FieldList.stream skipped++frame (projectionCode (inputProjection negative index)).bits++suffix)
        pre.length base position C out)
      (RecoveryCalls.stopped sizes written.final.heads written.final.tapes) := by
    cases negative
    · have kindCall := call_run 13 14 _ _ _ kind hkind (by
        change next 13 kind.final.control kind.final.scanned=some 14
        simp only [next,kc,inputKind,Bool.false_eq_true,ite_false]
        rfl)
      have valueCall := call_run 14 15 _ _ _ value hvalue (by rfl)
      have lastCall := stop_run 15 _ _ _ written hw (by rfl)
      exact ((hprefix.trans kindCall).trans valueCall).trans lastCall
    · have kindCall := call_run 13 16 _ _ _ kind hkind (by
        change next 13 kind.final.control kind.final.scanned=some 16
        simp only [next,kc,inputKind,ite_true]
        rfl)
      have valueCall := call_run 16 17 _ _ _ value hvalue (by rfl)
      have lastCall := stop_run 17 _ _ _ written hw (by rfl)
      exact ((hprefix.trans kindCall).trans valueCall).trans lastCall
  obtain ⟨result,hresult,rf,rs⟩ := full.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have timeBound : prefixSteps+(kind.steps+1)+(value.steps+1)+(written.steps+1) ≤ projectedInputBudget skipped negative index position C := by
    unfold projectedInputBudget; omega
  have more := runFrom_moreFuel machine _
    (projectedInputBudget skipped negative index position C-(prefixSteps+(kind.steps+1)+(value.steps+1)+(written.steps+1))) _ result hresult
  rw [Nat.add_sub_of_le timeBound] at more
  refine ⟨result,more,by omega,?_,?_,?_,?_,?_⟩
  · rw [rf]
    exact (wkeep 0 (by decide)).2.trans ((vkeep 0 (by decide)).2.trans ((kkeep 0 (by decide)).2.trans p0))
  · rw [rf]
    exact (wkeep 0 (by decide)).1.trans ((vkeep 0 (by decide)).1.trans ((kkeep 0 (by decide)).1.trans ph0))
  · rw [rf]
    exact (wkeep 1 (by decide)).2.trans ((vkeep 1 (by decide)).2.trans ((kkeep 1 (by decide)).2.trans p1))
  · intro i
    rw [rf]
    exact ⟨(wh i).trans (congrFun rawh i),(wt i).trans (congrFun rawt i)⟩
  · intro i hir hil hiv hii
    have h14 : i≠14 := by intro h; subst i; exact hil 22 rfl
    rw [rf]
    exact ⟨(wkeep i hii).1.trans ((vkeep i hiv).1.trans ((kkeep i h14).1.trans (pkeep i hir hil).1)),
      (wkeep i hii).2.trans ((vkeep i hiv).2.trans ((kkeep i h14).2.trans (pkeep i hir hil).2))⟩

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine

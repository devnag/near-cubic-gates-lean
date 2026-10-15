import Proof.PCP.PCPPNativeNodeLookup

/-! A projected constant is decoded from its actual paired projection
code, dispatched by two executed classifiers, and emitted twice. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation RecoveryExecution SourceInterfaces RepairSource
open ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def projectedConstBudget (r : ℕ) (skipped : List (List Bool)) (b : Bool) :=
  projectionPrefixBudget skipped (.constant b : ProjectedRandomBit r)+3+(b.toNat+1)+(constBits b b).length+3

theorem projected_const_run (r : ℕ) (pre tail : List Bool) (skipped : List (List Bool))
    (b : Bool) (suffix : List Bool) (base position C : ℕ) (out : List Bool) :
    ∃ result,runFrom machine (projectedConstBudget r skipped b)
      (entry (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
        (FieldList.stream skipped++frame (projectionCode (.constant b : ProjectedRandomBit r)).bits++suffix)
        pre.length base position C out)=some result ∧
      result.steps ≤ projectedConstBudget r skipped b ∧
      result.final.tapes 0=PCPPNativeNodeRead.source pre tail 1 skipped.length 0 ∧
      result.final.heads 0=pre.length+(natWord 1).length+(natWord skipped.length).length+(natWord 0).length ∧
      result.final.tapes 1=FieldList.stream skipped++frame (projectionCode (.constant b : ProjectedRandomBit r)).bits++suffix ∧
      result.final.tapes 5=out++constBits b b ∧ result.final.heads 5=(out++constBits b b).length ∧
      (∀ i,(∀ j,readSlots j≠i) → (∀ j,lookupSlots j≠i) → i≠5 →
        result.final.heads i=initialHeads pre.length out i ∧
        result.final.tapes i=initialData (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
          (FieldList.stream skipped++frame (projectionCode (.constant b : ProjectedRandomBit r)).bits++suffix) base position C out i) := by
  obtain ⟨prefixSteps,heads,data,hprefix,ps,p0,ph0,p1,_,p14,ph14,p15,ph15,pkeep⟩ :=
    projection_prefix_run pre tail skipped (.constant b : ProjectedRandomBit r) suffix base position C out
  obtain ⟨kind,hkind,ks,kc,kkeep⟩ := word_tag_run 14 2 heads data ph14 p14
  let boolTag : Fin 5 := ⟨b.toNat,by cases b <;> decide⟩
  have k15 := kkeep 15 (by decide)
  obtain ⟨value,hvalue,vs,vc,vkeep⟩ := word_tag_run 15 boolTag kind.final.heads kind.final.tapes
    (k15.1.trans ph15) (k15.2.trans p15)
  have outHead : value.final.heads 5=out.length := by
    rw [(vkeep 5 (by decide)).1,(kkeep 5 (by decide)).1,(pkeep 5 (by decide) (by decide)).1]
    rfl
  have outTape : value.final.tapes 5=out := by
    rw [(vkeep 5 (by decide)).2,(kkeep 5 (by decide)).2,(pkeep 5 (by decide) (by decide)).2]
    rfl
  obtain ⟨written,hw,ws,wh,wt,wkeep⟩ := literal_run (constBits b b) out value.final.heads value.final.tapes outHead outTape
  have kindCall := call_run 13 18 _ _ _ kind hkind (by
    change next 13 kind.final.control kind.final.scanned=some 18
    simp only [next,kc]
    rfl)
  have full : Timed machine (prefixSteps+(kind.steps+1)+(value.steps+1)+(written.steps+1))
      (entry (PCPPNativeNodeRead.source pre tail 1 skipped.length 0)
        (FieldList.stream skipped++frame (projectionCode (.constant b : ProjectedRandomBit r)).bits++suffix)
        pre.length base position C out)
      (RecoveryCalls.stopped sizes written.final.heads written.final.tapes) := by
    cases b
    · have valueCall := call_run 18 19 _ _ _ value hvalue (by
        change next 18 value.final.control value.final.scanned=some 19
        simp only [next,vc,boolTag,Bool.toNat_false,Nat.zero_add,ite_true]
        rfl)
      have lastCall := stop_run 19 _ _ _ written hw (by rfl)
      exact ((hprefix.trans kindCall).trans valueCall).trans lastCall
    · have valueCall := call_run 18 20 _ _ _ value hvalue (by
        change next 18 value.final.control value.final.scanned=some 20
        simp only [next,vc,boolTag,Bool.toNat_true,show 1+5=6 by omega,show ¬(6:ℕ)=5 by omega,ite_false,ite_true]
        rfl)
      have lastCall := stop_run 20 _ _ _ written hw (by rfl)
      exact ((hprefix.trans kindCall).trans valueCall).trans lastCall
  obtain ⟨result,hresult,rf,rs⟩ := full.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have timeBound : prefixSteps+(kind.steps+1)+(value.steps+1)+(written.steps+1) ≤ projectedConstBudget r skipped b := by
    unfold projectedConstBudget
    change value.steps=b.toNat+1 at vs
    omega
  have more := runFrom_moreFuel machine _
    (projectedConstBudget r skipped b-(prefixSteps+(kind.steps+1)+(value.steps+1)+(written.steps+1))) _ result hresult
  rw [Nat.add_sub_of_le timeBound] at more
  refine ⟨result,more,by omega,?_,?_,?_,?_,?_,?_⟩
  · rw [rf]
    exact (wkeep 0 (by decide)).2.trans ((vkeep 0 (by decide)).2.trans ((kkeep 0 (by decide)).2.trans p0))
  · rw [rf]
    exact (wkeep 0 (by decide)).1.trans ((vkeep 0 (by decide)).1.trans ((kkeep 0 (by decide)).1.trans ph0))
  · rw [rf]
    exact (wkeep 1 (by decide)).2.trans ((vkeep 1 (by decide)).2.trans ((kkeep 1 (by decide)).2.trans p1))
  · rw [rf]; exact wt
  · rw [rf]; exact wh
  · intro i hir hil h5
    have h14 : i≠14 := by intro h; subst i; exact hil 22 rfl
    have h15 : i≠15 := by intro h; subst i; exact hil 26 rfl
    rw [rf]
    exact ⟨(wkeep i h5).1.trans ((vkeep i h15).1.trans ((kkeep i h14).1.trans (pkeep i hir hil).1)),
      (wkeep i h5).2.trans ((vkeep i h15).2.trans ((kkeep i h14).2.trans (pkeep i hir hil).2))⟩

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine

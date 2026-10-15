import Proof.CaseAnalysis.RecoveryTagPacketPorts

/-! Print either actual scalar and advance the existing counter between
the four consecutive input/NOT/AND/OR tag references. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTagPacket
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem heads_override (out : List Bool) : heads out=fun i=>if i=7 then out.length else 0 := by
  funext i
  fin_cases i <;> rfl
def scalarFixedData (constant C : ℕ) (out : List Bool):=data 0 constant C out
theorem scalar_override (current constant C : ℕ) (out : List Bool) :
    data current constant C out=fun i=>if i=0 then List.replicate current true else scalarFixedData constant C out i := by
  funext i
  fin_cases i <;> rfl

theorem reference_run (useConstant : Bool) (current constant C : ℕ) (out : List Bool)
    (hC : 2*selectedValue useConstant current constant+1 ≤ C) :
    ∃ r,runFrom (reference useConstant) (RecoveryBoundedTagReferenceAppend.budget (selectedValue useConstant current constant) C)
      ⟨(reference useConstant).start,heads out,data current constant C out⟩=some r ∧
      r.steps ≤ RecoveryBoundedTagReferenceAppend.budget (selectedValue useConstant current constant) C ∧
      r.final.heads=heads (out++frame (List.replicate (selectedValue useConstant current constant) true)) ∧
      r.final.tapes=data current constant C (out++frame (List.replicate (selectedValue useConstant current constant) true)) := by
  obtain ⟨p,hp,ps,ph,pt⟩:=RecoveryBoundedTagReferenceAppend.padded_run (selectedValue useConstant current constant)
    (sourceCap useConstant C) C out hC
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock (referenceSlots useConstant) (reference_injective useConstant)
    RecoveryBoundedTagReferenceAppend.machine _ (heads out) (data current constant C out)
    ⟨RecoveryBoundedTagReferenceAppend.machine.start,RecoveryBoundedTagReferenceAppend.heads out,
      RecoveryBoundedTagReferenceAppend.paddedData (selectedValue useConstant current constant) (sourceCap useConstant C) C out⟩
    (reference_heads useConstant out) (reference_tapes useConstant current constant C out) p hp
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,referenceSlots useConstant j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      exact (reference_heads useConstant _ j).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h7 : i≠7:=fun h=>hi ⟨4,h.symm⟩
      simp only [heads_override,if_neg h7]
  · have he:=HierarchyWidth.install_eq (referenceSlots useConstant) (reference_injective useConstant)
      (data current constant C out) r.final.tapes _ (by intro j;rw [rt j,pt]) (by intro i hi;exact (rkeep i hi).2)
    rw [←he]
    exact reference_install useConstant current constant C out _

theorem increment_run (current constant C : ℕ) (out : List Bool) (hC : current+1 ≤ C) :
    ∃ r,runFrom increment (2*current+4) ⟨increment.start,heads out,data current constant C out⟩=some r ∧
      r.steps=2*current+4 ∧ r.final.heads=heads out ∧ r.final.tapes=data (current+1) constant C out := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready current C hC).focus_at
    incrementSlots (by decide) (heads out) (data current constant C out)
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl)
  have he : install incrementSlots (data current constant C out)
      ![List.replicate (current+1) true,List.replicate C false]=data (current+1) constant C out := by
    apply HierarchyWidth.install_eq incrementSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      have h0 : i≠0:=fun h=>hi 0 h.symm
      simp only [scalar_override,if_neg h0]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

noncomputable def next:=Composition.machine (reference false) increment
def nextBudget (current C : ℕ):=12*current+2*C+23

theorem next_run (current constant C : ℕ) (out : List Bool) (hC : 2*current+1 ≤ C) :
    ∃ r,runFrom next (nextBudget current C) ⟨next.start,heads out,data current constant C out⟩=some r ∧
      r.steps ≤ nextBudget current C ∧ r.final.heads=heads (out++frame (List.replicate current true)) ∧
      r.final.tapes=data (current+1) constant C (out++frame (List.replicate current true)) := by
  obtain ⟨a,ar,asteps,ah,atapes⟩:=reference_run false current constant C out hC
  obtain ⟨b,br,bsteps,bh,bt⟩:=increment_run current constant C (out++frame (List.replicate current true)) (by omega)
  have br' : runFrom increment (2*current+4) (restart a.final increment.start)=some b := by
    change runFrom increment _ ⟨increment.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have full:=Composition.run_join (reference false) increment _ _ _ a b ar br'
  have he : RecoveryBoundedTagReferenceAppend.budget (selectedValue false current constant) C+1+(2*current+4)=nextBudget current C := by
    change (10*current+2*C+18)+1+(2*current+4)=12*current+2*C+23
    omega
  rw [he] at full
  refine ⟨joinedReceipt a b,full,?_,bh,bt⟩
  change a.steps+1+b.steps ≤ nextBudget current C
  change a.steps ≤ 10*current+2*C+18 at asteps
  unfold nextBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedTagPacket

import Proof.CaseAnalysis.RecoveryClauseLookup

/-! A single original NOT, AND or OR uses the existing native node printer.
The literal and clause consumers choose its already retained raw operands. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseNative
open LocalBitMultitape SourceInterfaces RepairRepresentation PCPPNativeClauseBank
open RecoveryBoundedUniversalGates (values caps data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tag (kind : Fin 3):=kind.val+2
noncomputable def machine (kind : Fin 3):=nodeMachine (tag kind) 0 1 0 3
def emitted (kind : Fin 3) (left right : ℕ):=nodeBits (tag kind) 0 1 0 3 (values left right)
def budget (kind : Fin 3) (left right C : ℕ):=nodeBudget (tag kind) 0 1 0 3 (values left right) C

theorem padded_run (kind : Fin 3) (left right W C : ℕ) (out : List Bool)
    (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom (machine kind) (budget kind left right C)
      ⟨(machine kind).start,PCPPNativeClauseBank.heads out,data left right C out⟩=some r ∧
      r.steps ≤ budget kind left right C ∧ r.final.heads=PCPPNativeClauseBank.heads (out++emitted kind left right) ∧
      r.final.tapes=data left right C (out++emitted kind left right) := by
  have hleft:=PCPPNativeClauseCapacity.sum_capacity 0 left W C (by omega) hC
  have hright:=PCPPNativeClauseCapacity.sum_capacity 0 right W C (by omega) hC
  obtain ⟨p,hp,ps,ph,pt⟩:=node_run (tag kind) 0 1 0 3 (by decide) (by decide)
    (values left right) C out hleft hright
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config (machine kind) (caps C) _ _ p hp
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · rw [rf]
    change p.final.heads=_
    exact ph
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps C i) (p.final.tapes i))=_
    rw [pt]
    rfl

theorem budget_bound (kind : Fin 3) (left right W C : ℕ)
    (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    budget kind left right C ≤ 8*C+19 := by
  have hleft:=PCPPNativeClauseCapacity.sum_capacity 0 left W C (by omega) hC
  have hright:=PCPPNativeClauseCapacity.sum_capacity 0 right W C (by omega) hC
  have htag : (natWord (tag kind)).length ≤ 7 := by fin_cases kind <;> decide
  unfold budget nodeBudget PCPPNativeSumReusable.budget
  change (natWord (tag kind)).length+1+(2*PCPPNativeSumAppend.budget 0 left+2*C+7)+1+
    (2*PCPPNativeSumAppend.budget 0 right+2*C+7) ≤ _
  omega

theorem not_native (n left : ℕ) :
    emitted 0 left 0=PCPPRequestNodeSchema.native (.not left : BooleanNode n) := by
  simp [emitted,tag,nodeBits,RecoveryBoundedUniversalGates.values,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields]
theorem and_native (n left right : ℕ) :
    emitted 1 left right=PCPPRequestNodeSchema.native (.and left right : BooleanNode n) := by
  simp [emitted,tag,nodeBits,RecoveryBoundedUniversalGates.values,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields]
theorem or_native (n left right : ℕ) :
    emitted 2 left right=PCPPRequestNodeSchema.native (.or left right : BooleanNode n) := by
  simp [emitted,tag,nodeBits,RecoveryBoundedUniversalGates.values,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields]

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseNative

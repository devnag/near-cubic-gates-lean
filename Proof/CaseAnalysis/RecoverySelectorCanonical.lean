import Proof.CaseAnalysis.RecoverySelectorNextState

/-! A complete original selector head runs between exact reusable banks with
one fixed cubic recovery bound. The program is independent of that bound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (W : ℕ):=16384*(W+1)^2
def stepBudget (W : ℕ):=67108864*(W+1)^3
noncomputable def stateConfig (index base C D value limit pos : ℕ)
    (out source stack : List Bool) :=
  (⟨machine.start,stateHeads out stack pos,
    stateData index base C D value limit out source stack⟩ : Configuration 42 _)

theorem canonical_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W D : ℕ) (out skipped tail stack : List Bool)
    (wire : LiveWire b) (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hv : value≤W)
    (hD : 8388608*(W+1)^3≤D) :
    ∃ r,runFrom machine (stepBudget W)
      (stateConfig (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) b.nodes.length
        (capacity W) D value limit skipped.length out
        (skipped++frame (List.replicate wire.output.val true)++tail) stack)=some r ∧
      r.steps ≤ stepBudget W ∧
      r.final.heads=stateHeads (nextOut b row start limit value wire.output.val out hblock)
        (RecoveryBoundedSelectorReference.pushed (RecoveryBoundedSelectorJoin.counter b row start limit value hblock) stack)
        (skipped.length+2*wire.output.val+1) ∧
      r.final.tapes=stateData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        (RecoveryBoundedSelectorJoin.counter b row start limit value hblock+2)
        (capacity W) D (value+1) limit (nextOut b row start limit value wire.output.val out hblock)
        (skipped++frame (List.replicate wire.output.val true)++tail)
        (RecoveryBoundedSelectorReference.pushed (RecoveryBoundedSelectorJoin.counter b row start limit value hblock) stack) := by
  have hr : wire.output.val≤W := by have h:=wire.output.isLt; omega
  have hl : limit≤W := by omega
  have ha : RecoveryBoundedSelectorJoin.counter b row start limit value hblock≤W := by
    have h:=prefixCount_bound (unaryItems row start limit value hblock)
    have hlen : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
    rw [hlen] at h
    unfold RecoveryBoundedSelectorJoin.counter
    omega
  have hc : 1≤capacity W := by
    unfold capacity
    have h : 0 < (W+1)^2 := by positivity
    omega
  have hd : RecoveryBoundedReferenceAppend.budget wire.output.val limit (capacity W)≤D :=
    (RecoveryBoundedReferenceAppend.budget_cubic wire.output.val limit W hr hl).trans hD
  obtain ⟨r,hRun,rs,rh,rt⟩:=body_run b row start limit value W (capacity W) D out skipped tail stack wire
    hblock hi hp hv (by rfl) hd
  have budgetBound:=budget_cubic wire.output.val limit
    (RecoveryBoundedSelectorJoin.counter b row start limit value hblock)
    (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) value W hr hl ha (by omega) hv
  change budget wire.output.val limit (RecoveryBoundedSelectorJoin.counter b row start limit value hblock)
    (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) value (capacity W) ≤ stepBudget W at budgetBound
  have more:=runFrom_moreFuel machine _
    (stepBudget W-budget wire.output.val limit (RecoveryBoundedSelectorJoin.counter b row start limit value hblock)
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) value (capacity W)) _ r hRun
  rw [Nat.add_sub_of_le budgetBound] at more
  have entryEq : entry (n:=n) row start b.nodes.length (capacity W) D value limit wire.output.val out skipped tail stack=
      stateConfig (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) b.nodes.length
        (capacity W) D value limit skipped.length out
        (skipped++frame (List.replicate wire.output.val true)++tail) stack := by
    apply configuration_ext
    · rfl
    · exact entry_heads row start b.nodes.length (capacity W) D value limit wire.output.val out skipped tail stack
    · exact entry_tapes row start b.nodes.length (capacity W) D value limit wire.output.val out skipped tail stack hc
  rw [entryEq] at more
  refine ⟨r,more,rs.trans budgetBound,?_,?_⟩
  · exact rh.trans (done_heads b row start limit value (capacity W) D wire.output.val out skipped tail stack hblock W hp (by rfl))
  · exact rt.trans (done_tapes b row start limit value (capacity W) D wire.output.val out skipped tail stack hblock W hp (by rfl))

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop

import Proof.Assembly.ActualClause

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace LiveClauseSites
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal P1TopDown
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size
open SelectedBranchPhases (cache clause)
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k r scratch : Nat)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
 (H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
 (A : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
 (siteFuel : Nat)

/-- Inputs exposed by applying the actual clause machine. The physical site
must consume the queried literals and return a clean cache on the next bank.
No whole-clause Step is assumed. -/
structure SiteLoop where
 after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool
 head : ∀ j, j≤2^(a.output rq).clauseBits → ∀ i,H j (cache sources p k r scratch mode i)=0
 terminal_head : ∀ j,j<2^(a.output rq).clauseBits → H j (Selected.terminal sources p k r scratch)=0
 count : ∀ j,j<2^(a.output rq).clauseBits → A j (Selected.terminal sources p k r scratch)=
   List.replicate (2^(a.output rq).clauseBits) true
 cached : ∀ j,j<2^(a.output rq).clauseBits → ∀ i,A j (cache sources p k r scratch mode i)=
   PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity j
   (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [] i
 site_run : ∀ (j : Nat) (hj : j<2^(a.output rq).clauseBits),
   Step (site mode ph).2 siteFuel (H j)
     (install (cache sources p k r scratch mode) (A j)
       (PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity j
         (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity))
         (natListWord [literalIndex ((a.output rq).clauses ⟨j,hj⟩).left,
           literalIndex ((a.output rq).clauses ⟨j,hj⟩).right]))) (H (j+1)) (after j)
 restored : ∀ j,j<2^(a.output rq).clauseBits → ∀ i,after j (cache sources p k r scratch mode i)=
   PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity j
   (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [] i
 next : ∀ j,j<2^(a.output rq).clauseBits → A (j+1)=
   install (cache sources p k r scratch mode) (after j)
    (PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity (j+1)
     (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [])

theorem SiteLoop.rounds (R : SiteLoop sources p k r scratch site mode ph a rq H A siteFuel)
 (j : Nat) (hj : j<2^(a.output rq).clauseBits) :
 Step (clause sources p k r scratch site mode ph).2
  (4*(2^(a.output rq).clauseBits)+PCPPQueryCachedBounds.callBudget a (rq.circuit.size+rq.arity)+siteFuel+21)
  (H j) (A j) (H (j+1)) (A (j+1)) := by
 rw [R.next j hj]
 exact (Selected.run sources p k r scratch mode site ph a rq ⟨j,hj⟩ siteFuel
   (H j) (H (j+1)) (A j) (R.after j)
   (R.head j (Nat.le_of_lt hj)) (R.head (j+1) hj)
   (R.terminal_head j hj) (R.count j hj) (R.cached j hj)
   (R.site_run j hj) (R.restored j hj)).enlarge (by dsimp only;omega)

end
end LiveClauseSites

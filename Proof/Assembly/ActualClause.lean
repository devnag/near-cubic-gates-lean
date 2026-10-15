import Proof.Assembly.Clause
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace LiveClauseSites
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal P1TopDown SelectedRecoveryIntegration
open private NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.cache_injective
 from Proof.CaseAnalysis.FinalAdmittedEntry
noncomputable section
namespace Selected
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k r scratch : Nat) (mode : Bool)
theorem original_cache_injective : Function.Injective (WorkspaceSelectedEntryReady.cache sources p k mode) :=
    NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.cache_injective
     (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k p.clauseDegree p.degree
     (WorkspaceSelectedAdmission.capacity sources p).E mode

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

theorem remap_injective {t B : Nat} (P : Nat) (hP : 2≤P)
 (c : Fin 19→Fin t) (hc : Function.Injective c) (f : Fin 19→Fin B)
 (hf : ∀ i,(f i).val=if (c i).val<2 then (c i).val else P+(c i).val-2) :
 Function.Injective f := by
 intro i j he
 apply hc
 apply Fin.ext
 have hv := congrArg Fin.val he
 rw [hf,hf] at hv
 split_ifs at hv <;> omega

theorem cache_injective : Function.Injective (SelectedBranchPhases.cache sources p k r scratch mode) := by
 have hp : 2≤WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
   unfold WorkspaceSelectedEntry.size
   omega
 exact remap_injective _ hp (WorkspaceSelectedEntryReady.cache sources p k mode)
   (original_cache_injective sources p k mode)
   (SelectedBranchPhases.cache sources p k r scratch mode) (fun _=>rfl)

def terminal : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) :=
 ⟨SelectedBranchPhases.offset sources p k r+53,by have := SelectedBranchPhases.fresh_lt sources p k r scratch;omega⟩

theorem cache_ne_terminal (i : Fin 19) : SelectedBranchPhases.cache sources p k r scratch mode i ≠
 terminal sources p k r scratch := by
 have ht := WorkspaceSelectedEntryReady.old_size sources p k
 have hp : 302≤WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
   unfold WorkspaceSelectedEntry.size
   omega
 have hc := (WorkspaceSelectedEntryReady.cache sources p k mode i).isLt
 intro he
 have hv := congrArg Fin.val he
 change (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
    (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
    WorkspaceSelectedEntry.size sources k r p.clauseDegree+
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) =
    SelectedBranchPhases.offset sources p k r+53 at hv
 dsimp [SelectedBranchPhases.offset] at hv
 split_ifs at hv <;> omega

theorem run
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (ph : CloseoutRowsOriginalSchedule.Phase)
 (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
 (ci : Fin (2^(a.output rq).clauseBits)) (siteFuel : Nat)
 (H H' : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A A' : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
 (hH : ∀ j,H ((SelectedBranchPhases.cache sources p k r scratch mode) j)=0) (hH' : ∀ j,H' ((SelectedBranchPhases.cache sources p k r scratch mode) j)=0) (hterminal : H (terminal sources p k r scratch)=0)
 (hcount : A (terminal sources p k r scratch)=List.replicate (2^(a.output rq).clauseBits) true)
 (hcache : ∀ j,A ((SelectedBranchPhases.cache sources p k r scratch mode) j)=PCPPQueryIndexPadding.clauseData
   (pcppOutput rq (a.output rq)) rq.arity ci.val
   (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [] j)
 (hsite : Step (site mode ph).2 siteFuel H
   (install (SelectedBranchPhases.cache sources p k r scratch mode) A (PCPPQueryIndexPadding.clauseData
     (pcppOutput rq (a.output rq)) rq.arity ci.val
     (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity))
     (natListWord [literalIndex ((a.output rq).clauses ci).left,
       literalIndex ((a.output rq).clauses ci).right]))) H' A')
 (hrestored : ∀ j,A' ((SelectedBranchPhases.cache sources p k r scratch mode) j)=PCPPQueryIndexPadding.clauseData
   (pcppOutput rq (a.output rq)) rq.arity ci.val
   (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [] j) :
 Step (SelectedBranchPhases.clause sources p k r scratch site mode ph).2
   (4*ci.val+PCPPQueryCachedBounds.callBudget a (rq.circuit.size+rq.arity)+siteFuel+21)
   H A H' (install (SelectedBranchPhases.cache sources p k r scratch mode) A' (PCPPQueryIndexPadding.clauseData
     (pcppOutput rq (a.output rq)) rq.arity (ci.val+1)
     (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [])) := by
 exact LiveClauseSites.run
   (SelectedBranchPhases.cache sources p k r scratch mode)
   (cache_injective sources p k r scratch mode) (terminal sources p k r scratch)
   (cache_ne_terminal sources p k r scratch mode) a rq ci (site mode ph).2 siteFuel
   H H' A A' hH hH' hterminal hcount hcache hsite hrestored

end Selected
end
end LiveClauseSites

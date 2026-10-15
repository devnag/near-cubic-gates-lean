import Proof.PCP.PCPPNativeSourceLayout

/-! A checked cold native emitter is followed by paid framing, the exact
one PCPP source call, and physical shared-cache setup. Domain and size come
from that emitter's actual retained tapes; no prepared source input is added. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeSource
open LocalBitMultitape RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) (nativeFuel : ℕ) :=
  6*nativeFuel+8+PCPPSourceCache.totalBudget a request

theorem source_run (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (target size domain : Fin t) (distinct : size≠domain) (forward : CursorRestore.NoLeft p target)
    (request : PCPPRequest a.minimumArity) (nativeFuel : ℕ) (nativeInput : Fin t → List Bool)
    (native : ExecutionReceipt t s) (hnative : run p nativeFuel nativeInput=some native)
    (hout : native.final.tapes target=PCPPNative.descriptor request.circuit)
    (hhead : native.final.heads target=(PCPPNative.descriptor request.circuit).length)
    (hsize : native.final.tapes size=List.replicate request.circuit.size true)
    (hdomain : native.final.tapes domain=List.replicate request.arity true) :
    ∃ result,run (machine a p target size domain) (budget a request nativeFuel) (input a nativeInput)=some result ∧
      result.steps ≤ budget a request nativeFuel ∧
      (∀ j : Fin 19,result.final.tapes (sourceSlots a size domain (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j : Fin 19,result.final.heads (sourceSlots a size domain (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (sourceSlots a size domain (PCPPSourceCache.sizeSlot a))=
        List.replicate request.circuit.size true ∧
      result.final.heads (sourceSlots a size domain (PCPPSourceCache.sizeSlot a))=0 := by
  obtain ⟨framed,hf,ft,fh,fkeep,fs⟩ := PCPPNativeFrame.frame_run p target forward nativeFuel nativeInput native hnative
    (PCPPNative.descriptor request.circuit) hout hhead
  let prepared := TapeEmbedding.receipt (fun _ : Fin (PCPPSourceCache.tapes a) => 0)
    (fun _ : Fin (PCPPSourceCache.tapes a) => []) framed
  have hp := TapeEmbedding.run_embed (AppendOutputFrame.machine p target)
    (fun _ : Fin (PCPPSourceCache.tapes a) => 0) (fun _ : Fin (PCPPSourceCache.tapes a) => []) _ _ framed hf
  have allH : ∀ i,prepared.final.heads i=0 := by
    intro i
    refine Fin.addCases (m := (t+2)+2) (n := PCPPSourceCache.tapes a) (fun j => ?_) (fun j => ?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ _ _).trans (fh j)
    · exact TapeEmbedding.receipt_heads_new _ _ _ _
  have hinput : ∀ j,prepared.final.tapes (sourceSlots a size domain j)=PCPPSourceCache.input a request j := by
    apply source_input a size domain request prepared.final.tapes
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ft
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ((fkeep size).trans hsize)
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ((fkeep domain).trans hdomain)
    · intro j
      exact TapeEmbedding.receipt_tapes_new _ _ _ _
  obtain ⟨cache,hc,ct,ch,cs,csh,csteps⟩ := PCPPSourceCache.polynomial_run a request
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,_⟩ := RecoveryFocus.dock (sourceSlots a size domain)
    (source_injective a size domain distinct) (PCPPSourceCache.machine a) _
    prepared.final.heads prepared.final.tapes _ (by intro j; exact allH _) hinput cache hc
  have joined := Composition.run_join (first a p target) (last a size domain)
    _ _ _ prepared lastReceipt hp hl
  have hin : Composition.leftConfig _ (TapeEmbedding.config
      (fun _ : Fin (PCPPSourceCache.tapes a) => 0) (fun _ : Fin (PCPPSourceCache.tapes a) => [])
      (initialConfiguration (AppendOutputFrame.machine p target) (AppendOutputFrame.input nativeInput)))=
      initialConfiguration (machine a p target size domain) (input a nativeInput) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      all_goals simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at joined
  have nativeSteps := runFrom_steps_le p nativeFuel _ native hnative
  have hlen := SelectiveReset.prefix_head (prefix_of_run p nativeFuel _ native hnative).1 target
  rw [hhead] at hlen
  change (PCPPNative.descriptor request.circuit).length ≤ 0+native.steps at hlen
  have hbudget : (2*native.steps+4*(PCPPNative.descriptor request.circuit).length+7)+1+
      PCPPSourceCache.totalBudget a request ≤ budget a request nativeFuel := by
    unfold budget
    omega
  let result := Composition.joinedReceipt prepared lastReceipt
  have more := run_moreFuel (machine a p target size domain) _
    (budget a request nativeFuel-((2*native.steps+4*(PCPPNative.descriptor request.circuit).length+7)+1+
      PCPPSourceCache.totalBudget a request)) _ result joined
  rw [Nat.add_sub_of_le hbudget] at more
  refine ⟨result,more,?_,?_,?_,?_,?_⟩
  · change framed.steps+1+lastReceipt.steps ≤ _
    rw [ls]
    omega
  · intro j
    exact (lt _).trans (ct j)
  · intro j
    exact (lh _).trans (ch j)
  · exact (lt _).trans cs
  · exact (lh _).trans csh

end NearCubicWires.RepairOrdinary.PCPPNativeSource

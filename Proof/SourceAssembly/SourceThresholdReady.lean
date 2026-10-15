import Proof.SourceAssembly.SourceThresholdBounds

/- Paid rewind of the three completed logical streams, using the retained
quadratic C driver. Metadata and counted-loop driver remain outside the reset. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def streams (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) : Fin 3→List Bool:=
  ![SourceAssemblyThresholdLoop.outputs r.arity (SourceAssemblyThresholdCache.bits a r ci hk)
      (SourceAssemblySymmetricHeaderQuery.count a r ci) 0,
    SourceAssemblyThresholdLoop.outputs r.arity (SourceAssemblyThresholdCache.bits a r ci hk)
      (SourceAssemblySymmetricHeaderQuery.count a r ci) 1,
    frame (SourceAssemblyThresholdTop.payload (SourceAssemblySymmetricHeaderQuery.count a r ci))]
def slots : Fin 5→Fin 210:=![199,200,204,101,206]
def first:=TapeEmbedding.machine 4 SourceAssemblyThresholdTopQuery.machine
def last:=RecoveryFocus.machine slots (SourceAssemblyClear.rewind 3)
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 210→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (SourceAssemblyThresholdTopQuery.input a r ci C) (fun _ : Fin 4=>[])
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) : Fin 210→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (SourceAssemblyThresholdTopQuery.finalHeads a r ci hk) (fun _ : Fin 4=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  dockH slots (beforeHeads a r ci hk) (fun _=>0)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  SourceAssemblyThresholdTopQuery.budget a r ci C+1+2*Capacity.value r.arity+2

theorem before_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) (i : Fin 5) :
    beforeHeads a r ci hk (slots i)=SourceAssemblyClear.join
      (fun j=>(streams a r ci hk j).length) 0 0 i := by
  fin_cases i
  · change SourceAssemblyThresholdTopQuery.finalHeads a r ci hk 199=_
    rw [SourceAssemblyThresholdTopQuery.finalHeads,dockH_other _ _ _ 199 (by decide)]
    change SourceAssemblyThresholdQuery.finalHeads a r ci hk (SourceAssemblyThresholdQuery.slots 29)=_
    rw [SourceAssemblyThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 29]
    rfl
  · change SourceAssemblyThresholdTopQuery.finalHeads a r ci hk 200=_
    rw [SourceAssemblyThresholdTopQuery.finalHeads,dockH_other _ _ _ 200 (by decide)]
    change SourceAssemblyThresholdQuery.finalHeads a r ci hk (SourceAssemblyThresholdQuery.slots 30)=_
    rw [SourceAssemblyThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 30]
    rfl
  · change SourceAssemblyThresholdTopQuery.finalHeads a r ci hk (SourceAssemblyThresholdTopQuery.slots 2)=_
    rw [SourceAssemblyThresholdTopQuery.finalHeads,dockH_slot SourceAssemblyThresholdTopQuery.slots (by decide) _ _ 2]
    change (SourceAssemblyThresholdTop.finalOut _ 0).length=_
    rw [SourceAssemblyThresholdTop.final_exact]
    rfl
  · change SourceAssemblyThresholdTopQuery.finalHeads a r ci hk 101=0
    rw [SourceAssemblyThresholdTopQuery.finalHeads,dockH_other _ _ _ 101 (by decide)]
    change SourceAssemblyThresholdQuery.finalHeads a r ci hk (SourceAssemblyThresholdQuery.slots 22)=0
    rw [SourceAssemblyThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 22]
    rfl
  · rfl

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci hk) A ∧
      A 199=streams a r ci hk 0 ∧A 200=streams a r ci hk 1 ∧A 204=streams a r ci hk 2 ∧
      A 140=CompareMachine.word (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
      A 161=natWord (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
      A 207=[] ∧A 208=[] ∧A 209=[] := by
  obtain ⟨A,ha,h199,h200,h140,h161,h204,h101⟩:=SourceAssemblyThresholdTopQuery.run a r ci C hc hk
  let bank : Fin 210→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have firstStep : Step first (SourceAssemblyThresholdTopQuery.budget a r ci C)
      (fun _=>0) (input a r ci C) (beforeHeads a r ci hk) bank :=
    (ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have hlen : ∀ i,(streams a r ci hk i).length≤Capacity.value r.arity := by
    intro i;fin_cases i
    · exact SourceAssemblyThresholdBounds.outputs_bound _ _ _
        (SourceAssemblyThresholdQuery.count_le a r ci) (SourceAssemblyThresholdCache.bits_length a r ci hk) 0
    · exact SourceAssemblyThresholdBounds.outputs_bound _ _ _
        (SourceAssemblyThresholdQuery.count_le a r ci) (SourceAssemblyThresholdCache.bits_length a r ci hk) 1
    · exact SourceAssemblyThresholdBounds.top_bound _ _ (SourceAssemblyThresholdQuery.count_le a r ci)
  have selected : ∀ i,bank (slots i)=SourceAssemblyClear.join (streams a r ci hk)
      (List.replicate (Capacity.value r.arity) true) [] i := by
    intro i;fin_cases i
    · exact h199
    · exact h200
    · exact h204
    · exact h101
    · rfl
  have raw:=SourceAssemblyClear.raw_rewind (streams a r ci hk) (fun i=>(streams a r ci hk i).length)
    (Capacity.value r.arity) hlen
  have lastStep:=raw.dock slots (by decide) (beforeHeads a r ci hk) bank (before_heads a r ci hk) selected
  refine ⟨_,(firstStep.seq lastStep).enlarge (by unfold budget;omega),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots (by decide) bank _ 0
  · exact install_slot slots (by decide) bank _ 1
  · exact install_slot slots (by decide) bank _ 2
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact install_other slots bank _ 207 (by decide)
  · exact install_other slots bank _ 208 (by decide)
  · exact install_other slots bank _ 209 (by decide)

end
end SourceAssemblyThresholdReady

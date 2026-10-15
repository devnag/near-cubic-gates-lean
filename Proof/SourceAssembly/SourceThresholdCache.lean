import Proof.SourceAssembly.SourceThresholdBitmap
import Proof.SourceAssembly.SourceThreshold

/- Actual clause query → native count/header plus retained bitmap cache used by
THR Cold. No bitmap, count, weight cache or capacity driver is assumed resident. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdCache
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 7→Fin 170:=![3,135,101,166,167,168,169]
def first:=TapeEmbedding.machine 4 SourceAssemblySymmetricHeaderQuery.machine
def last:=RecoveryFocus.machine slots SourceAssemblyThresholdBitmap.machine
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 170→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (SourceAssemblySymmetricHeaderQuery.input a r ci C) (fun _ : Fin 4=>[])
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) : Fin 170→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (SourceAssemblySymmetricHeaderQuery.finalHeads a r ci) (fun _ : Fin 4=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=dockH slots (beforeHeads a r ci) SourceAssemblyThresholdBitmap.readyHeads
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  SourceAssemblySymmetricHeaderQuery.budget a r ci C+1+SourceAssemblyThresholdBitmap.budget r.arity

def bits (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :=
  PCPPQuerySupport.mask r (a.output r) ⟨index ((a.output r).clauses ci).left,hk⟩
theorem bits_length (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) : (bits a r ci hk).length=r.arity:=by
  simp [bits,PCPPQuerySupport.mask]

theorem before_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 7) :
    beforeHeads a r ci (slots i)=SourceAssemblyThresholdBitmap.heads r.arity i := by
  fin_cases i
  · change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 3=r.arity
    rw [SourceAssemblySymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 3 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.beforeHeads a r ci ((3 : Fin 141).castAdd 25)=_
    rw [SourceAssemblySymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ SourceAssemblySymmetricQuery.slots_inj _ _ 6
  · change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 135=1
    rw [SourceAssemblySymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 135 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.beforeHeads a r ci ((135 : Fin 141).castAdd 25)=_
    rw [SourceAssemblySymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ SourceAssemblySymmetricQuery.slots_inj _ _ 8
  · change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 101=0
    rw [SourceAssemblySymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 101 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.beforeHeads a r ci ((101 : Fin 141).castAdd 25)=0
    rw [SourceAssemblySymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_other _ _ _ 101 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci) A ∧
      A 131=frame (natWord r.arity) ∧A 101=List.replicate (Capacity.value r.arity) true ∧
      A 140=CompareMachine.word (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
      A 161=natWord (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
      A 164=frame (natWord (SourceAssemblySymmetricHeaderQuery.count a r ci)) ∧
      A 166=frame (weights (bits a r ci hk)) ∧A 167=frame (bits a r ci hk) := by
  obtain ⟨A,ha,h3,h131,h135,h140,h101,h161,h164⟩:=SourceAssemblyThresholdHeader.run a r ci C hc
  let bank : Fin 170→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have firstStep : Step first (SourceAssemblySymmetricHeaderQuery.budget a r ci C)
      (fun _=>0) (input a r ci C) (beforeHeads a r ci) bank :=
    (ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  let Q:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
  have selected : ∀ i,bank (slots i)=SourceAssemblyThresholdBitmap.input Q r.arity (bits a r ci hk) i := by
    intro i;fin_cases i
    · exact h3.trans (by simp only [SourceAssemblySymmetricQuery.bitmap,
        SourceAssemblyLiteralSupport.value,dif_pos hk];rfl)
    · exact h135
    · exact h101
    · rfl
    · rfl
    · rfl
    · rfl
  obtain ⟨k,_hk,raw⟩:=SourceAssemblyThresholdBitmap.run Q r.arity (bits a r ci hk) (bits_length a r ci hk)
  have lastStep:=raw.dock slots (by decide) (beforeHeads a r ci) bank (before_heads a r ci) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank _ 131 (by decide)).trans h131
  · exact install_slot slots (by decide) bank _ 2
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_other slots bank _ 164 (by decide)).trans h164
  · exact install_slot slots (by decide) bank _ 3
  · exact install_slot slots (by decide) bank _ 4

end
end SourceAssemblyThresholdCache

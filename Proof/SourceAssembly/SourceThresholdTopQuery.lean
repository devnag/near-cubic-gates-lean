import Proof.SourceAssembly.SourceThresholdQuery

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdTopQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 6→Fin 206:=![164,203,204,205,140,201]
def first:=TapeEmbedding.machine 3 SourceAssemblyThresholdQuery.machine
def last:=RecoveryFocus.machine slots SourceAssemblyThresholdTop.machine
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 206→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (SourceAssemblyThresholdQuery.input a r ci C) (fun _ : Fin 3=>[])
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) : Fin 206→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (SourceAssemblyThresholdQuery.finalHeads a r ci hk) (fun _ : Fin 3=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  dockH slots (beforeHeads a r ci hk) (SourceAssemblyThresholdTop.H
    (SourceAssemblyThresholdTop.finalOut (SourceAssemblySymmetricHeaderQuery.count a r ci)))
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  SourceAssemblyThresholdQuery.budget a r ci C+1+
    SourceAssemblyThresholdTop.budget (SourceAssemblySymmetricHeaderQuery.count a r ci)

theorem selected_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) (i : Fin 6) :
    beforeHeads a r ci hk (slots i)=SourceAssemblyThresholdTop.inputHeads i := by
  fin_cases i
  · change SourceAssemblyThresholdQuery.finalHeads a r ci hk 164=0
    rw [SourceAssemblyThresholdQuery.finalHeads,dockH_other _ _ _ 164 (by decide)]
    change SourceAssemblyThresholdCache.finalHeads a r ci 164=0
    rw [SourceAssemblyThresholdCache.finalHeads,dockH_other _ _ _ 164 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 164=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 24
  · rfl
  · rfl
  · rfl
  · change SourceAssemblyThresholdQuery.finalHeads a r ci hk (SourceAssemblyThresholdQuery.slots 32)=1
    rw [SourceAssemblyThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 32]
    rfl
  · change SourceAssemblyThresholdQuery.finalHeads a r ci hk (SourceAssemblyThresholdQuery.slots 31)=0
    rw [SourceAssemblyThresholdQuery.finalHeads,dockH_slot _ SourceAssemblyThresholdQuery.slots_inj _ _ 31]
    rfl

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci hk) A ∧
      A 199=SourceAssemblyThresholdLoop.outputs r.arity
        (SourceAssemblyThresholdCache.bits a r ci hk) (SourceAssemblySymmetricHeaderQuery.count a r ci) 0 ∧
      A 200=SourceAssemblyThresholdLoop.outputs r.arity
        (SourceAssemblyThresholdCache.bits a r ci hk) (SourceAssemblySymmetricHeaderQuery.count a r ci) 1 ∧
      A 140=CompareMachine.word (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
      A 161=natWord (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
      A 204=frame (SourceAssemblyThresholdTop.payload (SourceAssemblySymmetricHeaderQuery.count a r ci)) ∧
      A 101=List.replicate (Capacity.value r.arity) true := by
  obtain ⟨A,ha,h199,h200,h140,h161,h164,h201,h101⟩:=SourceAssemblyThresholdQuery.run a r ci C hc hk
  let bank : Fin 206→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 3=>[])
  have firstStep : Step first (SourceAssemblyThresholdQuery.budget a r ci C)
      (fun _=>0) (input a r ci C) (beforeHeads a r ci hk) bank :=
    (ha.embed (fun _ : Fin 3=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  let n:=SourceAssemblySymmetricHeaderQuery.count a r ci
  have hn:n≤r.arity:=SourceAssemblyThresholdQuery.count_le a r ci
  have hlen:2*(natWord n).length+1≤Capacity.value r.arity := by
    have hh:natBitLength n≤n+1:=Nat.add_le_add_right (Nat.log_le_self 2 n) 1
    rw [DecompositionSource.natWord_length];unfold Capacity.value;nlinarith
  have selected : ∀ i,bank (slots i)=SourceAssemblyThresholdTop.input n (Capacity.value r.arity) i := by
    intro i;fin_cases i
    · exact h164
    · rfl
    · rfl
    · rfl
    · exact h140
    · exact h201
  have lastStep:=(SourceAssemblyThresholdTop.run n (Capacity.value r.arity) hlen).dock slots (by decide)
    (beforeHeads a r ci hk) bank (selected_heads a r ci hk) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank _ 199 (by decide)).trans h199
  · exact (install_other slots bank _ 200 (by decide)).trans h200
  · exact install_slot slots (by decide) bank _ 4
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_slot slots (by decide) bank _ 2).trans (SourceAssemblyThresholdTop.final_exact n)
  · exact (install_other slots bank _ 101 (by decide)).trans h101

end
end SourceAssemblyThresholdTopQuery

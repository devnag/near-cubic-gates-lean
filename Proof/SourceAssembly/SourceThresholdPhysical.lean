import Proof.SourceAssembly.SourceThresholdReady

/- Full fixed physical THR parity-circuit producer from the actual queried
bank. Every source field and rewind driver comes from the paid prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdPhysical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def gates (q n : Nat) (bits : List Bool) : List CloseoutRowsTupleSeek.GatePair:=
  (List.range n).map (fun j=>(natWord q++weights bits++false::natWord j,bits))
theorem gates_length (q n : Nat) (bits : List Bool) : (gates q n bits).length=n:=by simp [gates]
theorem gates_native (q n : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.nativeWord (gates q n bits)=
    SourceAssemblyThresholdLoop.outputs q bits n 0 := by
  simp only [CloseoutRowsTupleSeek.nativeWord,gates,List.flatMap_map];rfl
theorem gates_support (q n : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.supportWord (gates q n bits)=
    SourceAssemblyThresholdLoop.outputs q bits n 1 := by
  simp only [CloseoutRowsTupleSeek.supportWord,gates,List.flatMap_map];rfl

def native (q n : Nat) (bits : List Bool):=SourceAssemblySymmetricAssemble.circuitWord
  (SourceAssemblyThresholdTop.payload n) (gates q n bits)
def slots : Fin 8→Fin 210:=![161,204,199,200,140,207,208,209]
theorem slots_inj : Function.Injective slots:=by decide
def writer:=RecoveryFocus.machine slots SourceAssemblySymmetricAssemble.machine
def machine:=Composition.machine SourceAssemblyThresholdReady.machine writer
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  dockH slots (SourceAssemblyThresholdReady.finalHeads a r ci hk)
    (SourceAssemblySymmetricAssemble.H
      (SourceAssemblyThresholdTop.payload (SourceAssemblySymmetricHeaderQuery.count a r ci))
      (gates r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)
        (SourceAssemblyThresholdCache.bits a r ci hk)) 3)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  SourceAssemblyThresholdReady.budget a r ci C+1+
    SourceAssemblySymmetricAssemble.budget
      (SourceAssemblyThresholdTop.payload (SourceAssemblySymmetricHeaderQuery.count a r ci))
      (gates r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)
        (SourceAssemblyThresholdCache.bits a r ci hk))

theorem selected_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) (i : Fin 8) :
    SourceAssemblyThresholdReady.finalHeads a r ci hk (slots i)=
      SourceAssemblySymmetricAssemble.H
        (SourceAssemblyThresholdTop.payload (SourceAssemblySymmetricHeaderQuery.count a r ci))
        (gates r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)
          (SourceAssemblyThresholdCache.bits a r ci hk)) 0 i := by
  fin_cases i
  · change SourceAssemblyThresholdReady.finalHeads a r ci hk 161=0
    rw [SourceAssemblyThresholdReady.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change SourceAssemblyThresholdTopQuery.finalHeads a r ci hk 161=0
    rw [SourceAssemblyThresholdTopQuery.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change SourceAssemblyThresholdQuery.finalHeads a r ci hk 161=0
    rw [SourceAssemblyThresholdQuery.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change SourceAssemblyThresholdCache.finalHeads a r ci 161=0
    rw [SourceAssemblyThresholdCache.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 161=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 21
  · exact dockH_slot _ (by decide) _ _ 2
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_slot _ (by decide) _ _ 1
  · change SourceAssemblyThresholdReady.finalHeads a r ci hk 140=1
    rw [SourceAssemblyThresholdReady.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change SourceAssemblyThresholdTopQuery.finalHeads a r ci hk 140=1
    exact dockH_slot _ (by decide) _ _ 4
  · exact dockH_other _ _ _ 207 (by decide)
  · exact dockH_other _ _ _ 208 (by decide)
  · exact dockH_other _ _ _ 209 (by decide)

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    ∃ A,Step machine (budget a r ci C hk) (fun _=>0)
      (SourceAssemblyThresholdReady.input a r ci C) (finalHeads a r ci hk) A ∧
      A 207=native r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)
        (SourceAssemblyThresholdCache.bits a r ci hk) ∧
      A 208=CloseoutRowsTupleSeek.supportWord (gates r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)
        (SourceAssemblyThresholdCache.bits a r ci hk)) := by
  obtain ⟨A,ha,h199,h200,h204,h140,h161,h207,h208,h209⟩:=SourceAssemblyThresholdReady.run a r ci C hc hk
  let n:=SourceAssemblySymmetricHeaderQuery.count a r ci
  let bits:=SourceAssemblyThresholdCache.bits a r ci hk
  have selected : ∀ i,A (slots i)=SourceAssemblySymmetricAssemble.A
      (SourceAssemblyThresholdTop.payload n) (gates r.arity n bits) 0 i := by
    intro i;fin_cases i
    · change A 161=natWord (gates r.arity n bits).length
      rw [gates_length];exact h161
    · exact h204
    · exact h199.trans (gates_native _ _ _).symm
    · exact h200.trans (gates_support _ _ _).symm
    · change A 140=CompareMachine.word (gates r.arity n bits).length
      rw [gates_length];exact h140
    · exact h207
    · exact h208
    · exact h209
  have lastStep:=(SourceAssemblySymmetricAssemble.run
      (SourceAssemblyThresholdTop.payload n) (gates r.arity n bits)).dock slots slots_inj
        (SourceAssemblyThresholdReady.finalHeads a r ci hk) A (selected_heads a r ci hk) selected
  exact ⟨_,ha.seq lastStep,install_slot slots slots_inj A _ 5,install_slot slots slots_inj A _ 6⟩

end
end SourceAssemblyThresholdPhysical

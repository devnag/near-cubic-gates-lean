import Proof.SourceAssembly.SourceSymmetricReset
import Proof.SourceAssembly.SourceSymmetricAssemble

/- One fixed physical program consumes the real clause-query bank and produces
one complete native parity circuit with its original support stream. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricPhysical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def gates (q : Nat) (bits : List Bool) : List CloseoutRowsTupleSeek.GatePair:=
  (SourceAssemblySymmetricScan.selected bits q).map
    (fun j=>(bottomWord (Identity.onehot q j) 0,Identity.onehot q j))
theorem gates_length (q : Nat) (bits : List Bool) : (gates q bits).length=
    (SourceAssemblySymmetricScan.selected bits q).length:=List.length_map _
theorem gates_native (q : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.nativeWord (gates q bits)=
    SourceAssemblySymmetricScan.outputs q bits q 0 := by
  simp only [CloseoutRowsTupleSeek.nativeWord,gates,List.flatMap_map]
  rfl
theorem gates_support (q : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.supportWord (gates q bits)=
    SourceAssemblySymmetricScan.outputs q bits q 1 := by
  simp only [CloseoutRowsTupleSeek.supportWord,gates,List.flatMap_map]
  rfl

def selectedGates (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=gates r.arity (SourceAssemblySymmetricQuery.bitmap a r ci)
def top (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=
  SourceAssemblySymmetricTop.table (SourceAssemblySymmetricHeaderQuery.count a r ci)
def native (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=
  SourceAssemblySymmetricAssemble.circuitWord (top a r ci) (selectedGates a r ci)
def slots : Fin 8→Fin 170:=![161,142,138,139,140,167,168,169]
theorem slots_inj : Function.Injective slots:=by decide
def direction (i : Fin 170):=if i=140 then HeadMove.right else .stay
def bump:=DecompositionCountPosition.move direction
def writer:=RecoveryFocus.machine slots SourceAssemblySymmetricAssemble.machine
def machine:=Composition.machine SourceAssemblySymmetricReset.machine (Composition.machine bump writer)
def bumpedHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=fun i=>HeadMove.apply (direction i)
      (SourceAssemblySymmetricReset.finalHeads a r ci i)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=dockH slots (bumpedHeads a r ci)
      (SourceAssemblySymmetricAssemble.H (top a r ci) (selectedGates a r ci) 3)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  SourceAssemblySymmetricReset.budget a r ci C+3+
    SourceAssemblySymmetricAssemble.budget (top a r ci) (selectedGates a r ci)

theorem reset_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 8) :
    SourceAssemblySymmetricReset.finalHeads a r ci (slots i)=0 := by
  fin_cases i
  · change SourceAssemblySymmetricReset.finalHeads a r ci 161=0
    rw [SourceAssemblySymmetricReset.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 161=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 21
  · change SourceAssemblySymmetricReset.finalHeads a r ci 142=0
    rw [SourceAssemblySymmetricReset.finalHeads,dockH_other _ _ _ 142 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 142=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 1
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_slot _ (by decide) _ _ 1
  · change SourceAssemblySymmetricReset.finalHeads a r ci 140=0
    rw [SourceAssemblySymmetricReset.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 140=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 3
  · exact dockH_other _ _ _ 167 (by decide)
  · exact dockH_other _ _ _ 168 (by decide)
  · exact dockH_other _ _ _ 169 (by decide)

theorem selected_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 8) :
    bumpedHeads a r ci (slots i)=SourceAssemblySymmetricAssemble.H (top a r ci) (selectedGates a r ci) 0 i := by
  unfold bumpedHeads
  rw [reset_heads]
  fin_cases i <;>simp [direction,slots,HeadMove.apply,SourceAssemblySymmetricAssemble.H]

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0)
      (SourceAssemblySymmetricReset.input a r ci C) (finalHeads a r ci) A ∧
      A 167=native a r ci ∧A 168=CloseoutRowsTupleSeek.supportWord (selectedGates a r ci) := by
  obtain ⟨A,ha,h138,h139,h140,h142,h161,h167,h168,h169⟩:=SourceAssemblySymmetricReset.run a r ci C hc
  obtain ⟨br,hr,hf,_⟩:=DecompositionCountPosition.move_run direction
    (SourceAssemblySymmetricReset.finalHeads a r ci) A
  have stepB : Step bump 1 (SourceAssemblySymmetricReset.finalHeads a r ci) A (bumpedHeads a r ci) A :=
    Step.of_run hr (by rw [hf];rfl) (by rw [hf])
  have hlen : (selectedGates a r ci).length=SourceAssemblySymmetricHeaderQuery.count a r ci:=gates_length _ _
  have selected : ∀ i,A (slots i)=SourceAssemblySymmetricAssemble.A (top a r ci) (selectedGates a r ci) 0 i := by
    intro i;fin_cases i
    · change A 161=natWord (selectedGates a r ci).length
      rw [hlen];exact h161
    · exact h142
    · exact h138.trans (gates_native _ _).symm
    · exact h139.trans (gates_support _ _).symm
    · change A 140=CompareMachine.word (selectedGates a r ci).length
      rw [hlen];exact h140
    · exact h167
    · exact h168
    · exact h169
  have writeStep:=(SourceAssemblySymmetricAssemble.run (top a r ci) (selectedGates a r ci)).dock
    slots slots_inj (bumpedHeads a r ci) A (selected_heads a r ci) selected
  refine ⟨_,(ha.seq (stepB.seq writeStep)).enlarge (by unfold budget;omega),?_,?_⟩
  · exact install_slot slots slots_inj A _ 5
  · exact install_slot slots slots_inj A _ 6

theorem native_head (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) : finalHeads a r ci 167=(native a r ci).length:=
  dockH_slot slots slots_inj _ _ 5

end
end SourceAssemblySymmetricPhysical

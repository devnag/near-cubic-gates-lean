import Proof.SourceAssembly.SourceSymmetric

/- First actual synthetic source consumer: the queried clause itself supplies
the bitmap, arity, headers, scratch and loop driver consumed by the SYM scan. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 9→Fin 141:=![13,137,131,138,139,133,3,140,135]
theorem slots_inj : Function.Injective slots:=by decide
def first:=TapeEmbedding.machine 4 SourceAssemblyParityQuery.machine
def last:=RecoveryFocus.machine slots SourceAssemblySymmetricCold.machine
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 141→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (SourceAssemblyParityQuery.input a r ci C) (fun _ : Fin 4=>[])
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  SourceAssemblyParityQuery.budget a r ci C+1+SourceAssemblySymmetricCold.budget r.arity

def bitmap (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=
  ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
    (SourceAssemblyLiteralSupport.value a r (index ((a.output r).clauses ci).left))
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=
  dockH slots (fun _=>0) (SourceAssemblySymmetricCold.heads r.arity (bitmap a r ci) r.arity)

theorem capacity_fit (q : Nat) : 2*(natWord q).length+1 ≤ Capacity.value q := by
  have hw : natBitLength q ≤ q+1:=Nat.add_le_add_right (Nat.log_le_self 2 q) 1
  simp only [DecompositionSource.natWord_length,Capacity.value]
  nlinarith

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci) A ∧
      A 138=SourceAssemblySymmetricScan.outputs r.arity (bitmap a r ci) r.arity 0 ∧
      A 139=SourceAssemblySymmetricScan.outputs r.arity (bitmap a r ci) r.arity 1 ∧
      A 140=CompareMachine.word (SourceAssemblySymmetricScan.selected (bitmap a r ci) r.arity).length ∧
      A 13=UnaryTemplate.tape r.arity ∧A 3=bitmap a r ci ∧
      A 4=ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (SourceAssemblyLiteralSupport.value a r (index ((a.output r).clauses ci).right)) ∧
      A 101=List.replicate (Capacity.value r.arity) true := by
  obtain ⟨A,ha,h3,h4,h131,h133,h135,h101,h13⟩:=SourceAssemblyParityQuery.run a r ci C hc
  let bank : Fin 141→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  have stepA : Step first (SourceAssemblyParityQuery.budget a r ci C)
      (fun _=>0) (input a r ci C) (fun _=>0) bank :=
    ((ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl).congr
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=SourceAssemblySymmetricCold.input
      r.arity (Capacity.value r.arity) (bitmap a r ci) i := by
    intro i;fin_cases i
    · exact h13
    · rfl
    · exact h131
    · rfl
    · rfl
    · exact h133
    · exact h3
    · rfl
    · exact h135
  have hb:=SourceAssemblySymmetricCold.run r.arity (Capacity.value r.arity)
    (bitmap a r ci) (capacity_fit r.arity)
  let out:=SourceAssemblySymmetricCold.words r.arity (Capacity.value r.arity) (bitmap a r ci) r.arity
  have lastStep:=hb.dock slots slots_inj (fun _=>0) bank (by intro i;rfl) selected
  refine ⟨install slots bank out,stepA.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank out 3
  · exact install_slot slots slots_inj bank out 4
  · exact install_slot slots slots_inj bank out 7
  · exact install_slot slots slots_inj bank out 0
  · exact install_slot slots slots_inj bank out 6
  · exact (install_other slots bank out 4 (by decide)).trans h4
  · exact (install_other slots bank out 101 (by decide)).trans h101

end
end SourceAssemblySymmetricQuery

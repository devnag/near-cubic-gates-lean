import Proof.SourceAssembly.SourceThresholdCache

/- Actual queried support/cache/count → reusable THR staircase loop. The33
callee inputs are docked from five retained tapes and freshly allocated work. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots (i : Fin 33) : Fin 203:=if i=22 then 101 else if i=26 then 131 else if i=27 then 166 else
  if i=28 then 167 else if i=32 then 140 else i.natAdd 170
theorem slots_inj : Function.Injective slots:=by decide
def oldSlots : Fin 5→Fin 170:=![101,131,166,167,140]
def first:=TapeEmbedding.machine 33 SourceAssemblyThresholdCache.machine
def last:=RecoveryFocus.machine slots SourceAssemblyThresholdCold.machine
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 203→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (SourceAssemblyThresholdCache.input a r ci C) (fun _ : Fin 33=>[])
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) : Fin 203→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (SourceAssemblyThresholdCache.finalHeads a r ci) (fun _ : Fin 33=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  dockH slots (beforeHeads a r ci) (SourceAssemblyThresholdCold.heads r.arity
    (SourceAssemblyThresholdCache.bits a r ci hk) (SourceAssemblySymmetricHeaderQuery.count a r ci))
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  SourceAssemblyThresholdCache.budget a r ci C+1+
    SourceAssemblyThresholdCold.budget r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)

theorem count_le (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) : SourceAssemblySymmetricHeaderQuery.count a r ci≤r.arity := by
  exact (List.length_filter_le _ _).trans List.length_range.le

theorem old_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 5) :
    SourceAssemblyThresholdCache.finalHeads a r ci (oldSlots i)=0 := by
  fin_cases i
  · exact dockH_slot _ (by decide) _ _ 2
  · change SourceAssemblyThresholdCache.finalHeads a r ci 131=0
    rw [SourceAssemblyThresholdCache.finalHeads,dockH_other _ _ _ 131 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 131=0
    rw [SourceAssemblySymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 131 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.beforeHeads a r ci ((131 : Fin 141).castAdd 25)=0
    rw [SourceAssemblySymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ SourceAssemblySymmetricQuery.slots_inj _ _ 2
  · exact dockH_slot _ (by decide) _ _ 3
  · exact dockH_slot _ (by decide) _ _ 4
  · change SourceAssemblyThresholdCache.finalHeads a r ci 140=0
    rw [SourceAssemblyThresholdCache.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change SourceAssemblySymmetricHeaderQuery.finalHeads a r ci 140=0
    exact dockH_slot _ SourceAssemblySymmetricHeaderQuery.slots_inj _ _ 3

theorem selected_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 33) : beforeHeads a r ci (slots i)=0 := by
  by_cases h22:i=22
  · subst i;exact old_heads a r ci 0
  by_cases h26:i=26
  · subst i;exact old_heads a r ci 1
  by_cases h27:i=27
  · subst i;exact old_heads a r ci 2
  by_cases h28:i=28
  · subst i;exact old_heads a r ci 3
  by_cases h32:i=32
  · subst i;exact old_heads a r ci 4
  simp only [slots,h22,h26,h27,h28,h32,if_false,beforeHeads,Fin.addCases_right]

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
      A 164=frame (natWord (SourceAssemblySymmetricHeaderQuery.count a r ci)) ∧
      A 201=List.replicate (Capacity.value r.arity) false ∧A 101=List.replicate (Capacity.value r.arity) true := by
  obtain ⟨A,ha,h131,h101,h140,h161,h164,h166,h167⟩:=SourceAssemblyThresholdCache.run a r ci C hc hk
  let bank : Fin 203→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 33=>[])
  have firstStep : Step first (SourceAssemblyThresholdCache.budget a r ci C)
      (fun _=>0) (input a r ci C) (beforeHeads a r ci) bank :=
    (ha.embed (fun _ : Fin 33=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=SourceAssemblyThresholdCold.input r.arity
      (SourceAssemblySymmetricHeaderQuery.count a r ci) (SourceAssemblyThresholdCache.bits a r ci hk) i := by
    intro i
    by_cases h22:i=22
    · subst i;exact h101
    by_cases h26:i=26
    · subst i;exact h131
    by_cases h27:i=27
    · subst i;exact h166
    by_cases h28:i=28
    · subst i;exact h167
    by_cases h32:i=32
    · subst i;exact h140
    simp only [slots,h22,h26,h27,h28,h32,if_false,bank,Fin.addCases_right,SourceAssemblyThresholdCold.input]
  have raw:=SourceAssemblyThresholdCold.run r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)
    (SourceAssemblyThresholdCache.bits a r ci hk) (count_le a r ci)
    (SourceAssemblyThresholdCache.bits_length a r ci hk)
  have lastStep:=raw.dock slots slots_inj (beforeHeads a r ci) bank (selected_heads a r ci) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank _ 29
  · exact install_slot slots slots_inj bank _ 30
  · exact install_slot slots slots_inj bank _ 32
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_other slots bank _ 164 (by decide)).trans h164
  · exact install_slot slots slots_inj bank _ 31
  · exact install_slot slots slots_inj bank _ 22

end
end SourceAssemblyThresholdQuery

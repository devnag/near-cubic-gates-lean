import Proof.SourceAssembly.SourceSymmetricHeaderQuery
import Proof.SourceAssembly.SourceThresholdTop

/- Stronger receipt for the SAME checked query/header code, retaining exactly
the caches used by the subsequent actual THR source consumer. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdHeader
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

open SourceAssemblySymmetricQuery in
theorem selected_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci) A ∧
      A 3=bitmap a r ci ∧A 131=frame (natWord r.arity) ∧A 135=CompareMachine.word r.arity ∧
      A 140=CompareMachine.word (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
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
  refine ⟨install slots bank out,stepA.seq lastStep,?_,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank out 6
  · exact install_slot slots slots_inj bank out 2
  · exact install_slot slots slots_inj bank out 8
  · exact install_slot slots slots_inj bank out 7
  · exact (install_other slots bank out 101 (by decide)).trans h101

open SourceAssemblySymmetricHeaderQuery in
theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci) A ∧
      A 3=SourceAssemblySymmetricQuery.bitmap a r ci ∧A 131=frame (natWord r.arity) ∧
      A 135=CompareMachine.word r.arity ∧A 140=CompareMachine.word (count a r ci) ∧
      A 101=List.replicate (Capacity.value r.arity) true ∧A 161=natWord (count a r ci) ∧
      A 164=frame (natWord (count a r ci)) := by
  obtain ⟨A,ha,h3,h131,h135,h140,h101⟩:=selected_run a r ci C hc
  let bank : Fin 166→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 25=>[])
  have firstStep : Step first (SourceAssemblySymmetricQuery.budget a r ci C)
      (fun _=>0) (input a r ci C) (beforeHeads a r ci) bank :=
    (ha.embed (fun _ : Fin 25=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  obtain ⟨B,hb,_top,header,framed,driver⟩:=SourceAssemblySymmetricHeader.run (count a r ci)
  have selected : ∀ i,bank (slots i)=SourceAssemblySymmetricHeader.input (count a r ci) i := by
    intro i
    by_cases hi:i=3
    · subst i;exact h140
    · rw [slots_fresh i hi]
      simp only [bank,Fin.addCases_right,SourceAssemblySymmetricHeader.input,hi,if_false]
  have lastStep:=hb.dock slots slots_inj (beforeHeads a r ci) bank (selected_heads a r ci) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank B 3 (by decide)).trans h3
  · exact (install_other slots bank B 131 (by decide)).trans h131
  · exact (install_other slots bank B 135 (by decide)).trans h135
  · exact (install_slot slots slots_inj bank B 3).trans driver
  · exact (install_other slots bank B 101 (by decide)).trans h101
  · exact (install_slot slots slots_inj bank B 21).trans header
  · exact (install_slot slots slots_inj bank B 24).trans framed

end
end SourceAssemblyThresholdHeader

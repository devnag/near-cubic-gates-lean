import Proof.SourceAssembly.SourceThresholdCanonical

/- Stronger receipts for the SAME checked programs retain the actual q header.
Existing interfaces remain unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section
namespace SourceAssemblyThresholdQuery
theorem run_retained (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
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
      A 201=List.replicate (Capacity.value r.arity) false ∧A 101=List.replicate (Capacity.value r.arity) true ∧ A 131=frame (natWord r.arity) := by
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
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots slots_inj bank _ 29
  · exact install_slot slots slots_inj bank _ 30
  · exact install_slot slots slots_inj bank _ 32
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_other slots bank _ 164 (by decide)).trans h164
  · exact install_slot slots slots_inj bank _ 31
  · exact install_slot slots slots_inj bank _ 22

  · exact install_slot slots slots_inj bank _ 26

end SourceAssemblyThresholdQuery

namespace SourceAssemblyThresholdTopQuery
theorem run_retained (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
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
      A 101=List.replicate (Capacity.value r.arity) true ∧ A 131=frame (natWord r.arity) := by
  obtain ⟨A,ha,h199,h200,h140,h161,h164,h201,h101,h131⟩:=SourceAssemblyThresholdQuery.run_retained a r ci C hc hk
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
  refine ⟨_,firstStep.seq lastStep,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank _ 199 (by decide)).trans h199
  · exact (install_other slots bank _ 200 (by decide)).trans h200
  · exact install_slot slots (by decide) bank _ 4
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact (install_slot slots (by decide) bank _ 2).trans (SourceAssemblyThresholdTop.final_exact n)
  · exact (install_other slots bank _ 101 (by decide)).trans h101

  · exact (install_other slots bank _ 131 (by decide)).trans h131

end SourceAssemblyThresholdTopQuery

namespace SourceAssemblyThresholdReady
theorem run_retained (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci hk) A ∧
      A 199=streams a r ci hk 0 ∧A 200=streams a r ci hk 1 ∧A 204=streams a r ci hk 2 ∧
      A 140=CompareMachine.word (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
      A 161=natWord (SourceAssemblySymmetricHeaderQuery.count a r ci) ∧
      A 207=[] ∧A 208=[] ∧A 209=[] ∧ A 131=frame (natWord r.arity) := by
  obtain ⟨A,ha,h199,h200,h140,h161,h204,h101,h131⟩:=SourceAssemblyThresholdTopQuery.run_retained a r ci C hc hk
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
  refine ⟨_,(firstStep.seq lastStep).enlarge (by unfold budget;omega),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots (by decide) bank _ 0
  · exact install_slot slots (by decide) bank _ 1
  · exact install_slot slots (by decide) bank _ 2
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact install_other slots bank _ 207 (by decide)
  · exact install_other slots bank _ 208 (by decide)
  · exact install_other slots bank _ 209 (by decide)

  · exact (install_other slots bank _ 131 (by decide)).trans h131

end SourceAssemblyThresholdReady

namespace SourceAssemblyThresholdPhysical
theorem run_retained (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
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
        (SourceAssemblyThresholdCache.bits a r ci hk)) ∧ A 131=frame (natWord r.arity) := by
  obtain ⟨A,ha,h199,h200,h204,h140,h161,h207,h208,h209,h131⟩:=SourceAssemblyThresholdReady.run_retained a r ci C hc hk
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
  exact ⟨_,ha.seq lastStep,install_slot slots slots_inj A _ 5,install_slot slots slots_inj A _ 6,
    (install_other slots A _ 131 (by decide)).trans h131⟩

end SourceAssemblyThresholdPhysical

end

import Proof.MachineModel.OrdinaryMatrixVariablePacket

/-! One original request and its physical bit-offset driver execute through
native Williams counts and the complete serialized packet append. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariablePacket
open LocalBitMultitape MatrixScoreBatch RepairRepresentation MatrixWilliamsProduct
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_other (a : WilliamsAlgorithm) (j : Fin 10) (hj : j≠6) :
    ∀ k,slots a k≠(((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17) := by
  have h424 : (MatrixVariableDimensions.selected j).val≠424 := by
    fin_cases j <;> first | contradiction | decide
  have h422 := MatrixVariableProduct.selected_ne j
  have hk : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  have hjb := (MatrixVariableDimensions.selected j).isLt
  intro k he
  have hv := congrArg Fin.val he
  fin_cases k
  · change 424=(MatrixVariableDimensions.selected j).val at hv
    exact h424 hv.symm
  · change MatrixVariableProduct.tapes a+14=(MatrixVariableDimensions.selected j).val at hv
    omega
  · change (MatrixVariableProduct.outputTape a).val=(MatrixVariableDimensions.selected j).val at hv
    unfold MatrixVariableProduct.outputTape MatrixVariableProduct.slots at hv
    split at hv
    · exact h422 hv.symm
    · simp only [Fin.val_natAdd] at hv
      omega
  · change MatrixVariableProduct.tapes a+16=(MatrixVariableDimensions.selected j).val at hv
    omega

theorem packet_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) (out : List Bool)
    (ht : bit<r.p) : ∃ actual,
    runFrom (machine a negative) (budget a r bit negative) (input a r bit out)=some actual ∧
    actual.final.tapes (outputTape a)=out++packet r negative bit ∧
    actual.final.heads (outputTape a)=(out++packet r negative bit).length ∧
    actual.final.tapes (offset a)=UnaryTemplate.tape (2*bit) ∧ actual.final.heads (offset a)=1 ∧
    actual.final.tapes (count a)=UnaryTemplate.tape (planeCounts r negative bit).length ∧
    actual.final.heads (count a)=1 ∧ actual.final.tapes (sourceTape a)=planeCounts r negative bit ∧
    actual.final.heads (sourceTape a)=(planeCounts r negative bit).length ∧
    (∀ j,actual.final.tapes (((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17)=
      MatrixVariableDimensions.values r negative bit j) ∧
    actual.steps≤budget a r bit negative := by
  obtain ⟨base,hb,bt,bh,nt,nh,fields,heads,ot,oh,bs⟩ := MatrixVariableCount.count_run a r negative bit out ht
  obtain ⟨lastRun,hl,lt,lh,offsetT,offsetH,countT,countH,sourceT,sourceH,other,ls⟩ :=
    call_run a negative bit (planeCounts r negative bit) out base.final
      (by
        intro j; fin_cases j
        · exact fields 6
        · exact nt
        · exact bt
        · exact ot)
      (by
        intro j; fin_cases j
        · exact heads 6
        · exact nh
        · exact bh
        · exact oh)
  have joined := Composition.run_join (MatrixVariableCount.machine a negative) (last a negative)
    _ _ _ base lastRun hb hl
  have hp : out++MatrixPacketPrefix.prefixWord negative bit++planeCounts r negative bit=out++packet r negative bit := by
    simp only [MatrixPacketPrefix.prefixWord,packet,List.append_assoc]
  rw [hp] at lt lh
  refine ⟨Composition.joinedReceipt base lastRun,joined,lt,lh,offsetT,offsetH,countT,countH,sourceT,sourceH,?_,?_⟩
  · intro j
    by_cases hj : j=6
    · subst j
      exact offsetT
    · exact (other _ (field_other a j hj)).1.trans (fields j)
  · change base.steps+1+lastRun.steps≤budget a r bit negative
    rw [ls]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixVariablePacket

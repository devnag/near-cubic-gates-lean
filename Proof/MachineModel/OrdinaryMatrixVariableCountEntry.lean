import Proof.MachineModel.OrdinaryMatrixVariableCount

/-! Whole original request through indexed native counts and their literal
physical block-length driver, with the global append stream preserved. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableCount
open LocalBitMultitape MatrixScoreBatch RepairRepresentation MatrixWilliamsProduct
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_length (r : Request) (negative : Bool) (bit : ℕ) :
    (planeCounts r negative bit).length=r.U^2*(r.d+1) := by
  rw [planeCounts_length]
  have hb : natBitLength r.U=r.d+1 := by simp [Request.U,natBitLength,Nat.log_pow]
  rw [hb]

theorem count_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) (out : List Bool)
    (ht : bit<r.p) : ∃ actual,
    runFrom (machine a negative) (budget a r) (input a r bit out)=some actual ∧
    actual.final.tapes ((MatrixVariableProduct.outputTape a).castAdd 17)=planeCounts r negative bit ∧
    actual.final.heads ((MatrixVariableProduct.outputTape a).castAdd 17)=0 ∧
    actual.final.tapes (slots a 16)=UnaryTemplate.tape (planeCounts r negative bit).length ∧
    actual.final.heads (slots a 16)=0 ∧
    (∀ j,actual.final.tapes (((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17)=MatrixVariableDimensions.values r negative bit j) ∧
    (∀ j,actual.final.heads (((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17)=MatrixVariableDimensions.heads j) ∧
    actual.final.tapes ((16 : Fin 17).natAdd (MatrixVariableProduct.tapes a))=out ∧
    actual.final.heads ((16 : Fin 17).natAdd (MatrixVariableProduct.tapes a))=out.length ∧
    actual.steps≤budget a r := by
  obtain ⟨base,hb,bt,bh,fields,heads,bs⟩ := MatrixVariableProduct.product_run a r negative bit ht
  have hemb := TapeEmbedding.run_embed (MatrixVariableProduct.machine a negative) (extraHeads out) (extraTapes out) _ _ base hb
  let prepared := TapeEmbedding.receipt (extraHeads out) (extraTapes out) base
  have oldT (i : Fin (MatrixVariableProduct.tapes a)) : prepared.final.tapes (i.castAdd 17)=base.final.tapes i := by
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17)
      (motive := fun _ => List Bool) base.final.tapes (extraTapes out)) (i.castAdd 17)=_
    rw [Fin.addCases_left]
  have oldH (i : Fin (MatrixVariableProduct.tapes a)) : prepared.final.heads (i.castAdd 17)=base.final.heads i := by
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17)
      (motive := fun _ => ℕ) base.final.heads (extraHeads out)) (i.castAdd 17)=_
    rw [Fin.addCases_left]
  have extraT (i : Fin 17) : prepared.final.tapes (i.natAdd (MatrixVariableProduct.tapes a))=extraTapes out i := by
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17)
      (motive := fun _ => List Bool) base.final.tapes (extraTapes out)) (i.natAdd (MatrixVariableProduct.tapes a))=_
    rw [Fin.addCases_right]
  have extraH (i : Fin 17) : prepared.final.heads (i.natAdd (MatrixVariableProduct.tapes a))=extraHeads out i := by
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17)
      (motive := fun _ => ℕ) base.final.heads (extraHeads out)) (i.natAdd (MatrixVariableProduct.tapes a))=_
    rw [Fin.addCases_right]
  obtain ⟨focused,hf,ft,fh,old,ot,oh,fs⟩ := call_run a r.U r.d prepared.final
    (by
      intro j; fin_cases j
      · exact (oldT _).trans (fields 2)
      · exact (oldT _).trans (fields 0)
      all_goals
        change prepared.final.tapes ((_ : Fin 17).natAdd (MatrixVariableProduct.tapes a))=[]
        rw [extraT]
        rfl)
    (by
      intro j; fin_cases j
      · exact (oldH _).trans (heads 2)
      · exact (oldH _).trans (heads 0)
      all_goals
        change prepared.final.heads ((_ : Fin 17).natAdd (MatrixVariableProduct.tapes a))=0
        rw [extraH]
        rfl)
  have hj := Composition.run_join (first a negative) (last a) _ _ _ prepared focused hemb hf
  rw [←native_length r negative bit] at ft
  refine ⟨Composition.joinedReceipt prepared focused,hj,(old _).1.trans ((oldT _).trans bt),
    (old _).2.trans ((oldH _).trans bh),ft,fh,?_,?_,?_,?_,?_⟩
  · intro j; exact (old _).1.trans ((oldT _).trans (fields j))
  · intro j; exact (old _).2.trans ((oldH _).trans (heads j))
  · exact ot.trans (extraT 16)
  · exact oh.trans (extraH 16)
  · change base.steps+1+focused.steps≤budget a r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixVariableCount

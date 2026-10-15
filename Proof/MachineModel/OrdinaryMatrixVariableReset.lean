import Proof.MachineModel.OrdinaryMatrixVariableProduct
import Proof.MachineModel.OrdinaryMaskedReset

/-! The indexed Williams call pays a return of every local work head while
retaining the external bit-offset cursor. The log is an actual extra tape. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableReset
open LocalBitMultitape MatrixScoreBatch MatrixWilliamsProduct RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def selected (a : WilliamsAlgorithm) (i : Fin (MatrixVariableProduct.tapes a)) : Bool :=
  decide (i.val≠424)
noncomputable def machine (a : WilliamsAlgorithm) (negative : Bool) :=
  MaskedReset.machine (MatrixVariableProduct.machine a negative) (selected a)
noncomputable def input (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) :=
  Rewind.recording (MatrixVariableProduct.input a r bit) 0
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) := 2*MatrixVariableProduct.budget a r+2

theorem input_head (a : WilliamsAlgorithm) (r : Request) (bit : ℕ)
    (i : Fin (MatrixVariableProduct.tapes a)) (hi : selected a i=true) :
    (MatrixVariableProduct.input a r bit).heads i=0 := by
  revert hi
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hi
    change (Fin.addCases (m := 425) (n := (source a).program.tapeCount)
      (motive := fun _ => ℕ) (MatrixVariableInput.input r bit).heads (fun _ => 0)) (j.castAdd (source a).program.tapeCount)=0
    rw [Fin.addCases_left]
    change (MatrixVariablePlane.input r bit).heads j=0
    rw [MatrixVariablePlane.input_heads]
    have hn : j≠424 := by
      intro he
      subst j
      simp [selected] at hi
    simp [hn]
  · intro _
    change (Fin.addCases (m := 425) (n := (source a).program.tapeCount)
      (motive := fun _ => ℕ) (MatrixVariableInput.input r bit).heads (fun _ => 0)) (j.natAdd 425)=0
    rw [Fin.addCases_right]

theorem reset_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) (ht : bit<r.p) : ∃ actual,
    runFrom (machine a negative) (budget a r) (input a r bit)=some actual ∧
    actual.final.tapes ((MatrixVariableProduct.outputTape a).castAdd 1)=planeCounts r negative bit ∧
    (∀ j,actual.final.tapes (((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 1)=MatrixVariableDimensions.values r negative bit j) ∧
    (∀ i : Fin (MatrixVariableProduct.tapes a),actual.final.heads (i.castAdd 1)=if i.val=424 then 1 else 0) ∧
    actual.final.heads ((0 : Fin 1).natAdd (MatrixVariableProduct.tapes a))=0 ∧
    (∃ log,actual.final.tapes ((0 : Fin 1).natAdd (MatrixVariableProduct.tapes a))=List.replicate log false ∧ log≤MatrixVariableProduct.budget a r) ∧
    actual.steps≤budget a r := by
  obtain ⟨base,hb,bt,_,fields,heads,bs⟩ := MatrixVariableProduct.product_run a r negative bit ht
  have hh : ∀ i,selected a i=true → base.final.heads i≤base.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ base hb).1 i
    simpa only [input_head a r bit i hi,Nat.zero_add] using h
  obtain ⟨actual,ha,hf,hs,_⟩ := MaskedReset.reset_run (MatrixVariableProduct.machine a negative)
    (selected a) _ _ base hb hh
  have hle : 2*base.steps+2≤budget a r := by unfold budget; omega
  have more := runFrom_moreFuel (machine a negative) (2*base.steps+2)
    (budget a r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hle] at more
  have oldT (i : Fin (MatrixVariableProduct.tapes a)) : actual.final.tapes (i.castAdd 1)=base.final.tapes i := by
    rw [hf]
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 1)
      (motive := fun _ => List Bool) base.final.tapes (fun _ => List.replicate base.steps false)) (i.castAdd 1)=_
    rw [Fin.addCases_left]
  refine ⟨actual,more,(oldT _).trans bt,?_,?_,?_,?_,by omega⟩
  · intro j; exact (oldT _).trans (fields j)
  · intro i
    rw [hf]
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 1)
      (motive := fun _ => ℕ) (fun i => if selected a i then 0 else base.final.heads i) (fun _ => 0)) (i.castAdd 1)=_
    rw [Fin.addCases_left]
    simp only [selected,Bool.decide_iff]
    by_cases he : i.val=424
    · have hei : i=(424 : Fin 425).castAdd (source a).program.tapeCount := Fin.ext he
      subst i
      have h6 : base.final.heads ((424 : Fin 425).castAdd (source a).program.tapeCount)=1 := heads 6
      simpa using h6
    · simp [he]
  · rw [hf]
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 1)
      (motive := fun _ => ℕ) (fun i => if selected a i then 0 else base.final.heads i) (fun _ => 0)) ((0 : Fin 1).natAdd (MatrixVariableProduct.tapes a))=0
    rw [Fin.addCases_right]
  · refine ⟨base.steps,?_,bs⟩
    rw [hf]
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 1)
      (motive := fun _ => List Bool) base.final.tapes (fun _ => List.replicate base.steps false)) ((0 : Fin 1).natAdd (MatrixVariableProduct.tapes a))=_
    rw [Fin.addCases_right]

end NearCubicWires.RepairOrdinary.MatrixVariableReset

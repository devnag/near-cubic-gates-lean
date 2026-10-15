import Proof.MachineModel.OrdinaryMatrixVariablePacketEntry

/-! Whole native packet append with one paid local reset. The bit-offset
and global append cursors remain live; every other head returns to zero. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariablePacketReset
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixWilliamsProduct (source)
open MatrixVariablePacket (offset outputTape)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def selected (a : WilliamsAlgorithm) (i : Fin (MatrixVariableCount.tapes a)) : Bool :=
  decide (i.val≠424 ∧ i.val≠MatrixVariableProduct.tapes a+16)
noncomputable def machine (a : WilliamsAlgorithm) (negative : Bool) :=
  MaskedReset.machine (MatrixVariablePacket.machine a negative) (selected a)
noncomputable def input (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (out : List Bool) :=
  Rewind.recording (MatrixVariablePacket.input a r bit out) 0
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (negative : Bool) :=
  2*MatrixVariablePacket.budget a r bit negative+2

theorem input_head (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (out : List Bool)
    (i : Fin (MatrixVariableCount.tapes a)) (hi : selected a i=true) :
    (MatrixVariablePacket.input a r bit out).heads i=0 := by
  revert hi
  refine Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17) (fun j => ?_) (fun j => ?_) i
  · intro hi
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17)
      (motive := fun _ => ℕ) (MatrixVariableProduct.input a r bit).heads (MatrixVariableCount.extraHeads out)) (j.castAdd 17)=0
    rw [Fin.addCases_left]
    apply MatrixVariableReset.input_head
    have hi' : j.val≠424 ∧ j.val≠MatrixVariableProduct.tapes a+16 := by
      simpa only [selected,Fin.val_castAdd,Bool.decide_iff] using hi
    simpa only [MatrixVariableReset.selected,Bool.decide_iff] using hi'.1
  · intro hi
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17)
      (motive := fun _ => ℕ) (MatrixVariableProduct.input a r bit).heads (MatrixVariableCount.extraHeads out)) (j.natAdd (MatrixVariableProduct.tapes a))=0
    rw [Fin.addCases_right]
    have hj : j≠16 := by
      intro he
      subst j
      simp [selected] at hi
    simp [MatrixVariableCount.extraHeads,hj]

theorem reset_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) (out : List Bool)
    (ht : bit<r.p) : ∃ actual,
    runFrom (machine a negative) (budget a r bit negative) (input a r bit out)=some actual ∧
    actual.final.tapes ((outputTape a).castAdd 1)=out++packet r negative bit ∧
    actual.final.tapes ((offset a).castAdd 1)=UnaryTemplate.tape (2*bit) ∧
    (∀ j,actual.final.tapes ((((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1)=
      MatrixVariableDimensions.values r negative bit j) ∧
    (∀ i : Fin (MatrixVariableCount.tapes a),actual.final.heads (i.castAdd 1)=
      if i=offset a then 1 else if i=outputTape a then (out++packet r negative bit).length else 0) ∧
    actual.final.heads ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))=0 ∧
    (∃ log,actual.final.tapes ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))=List.replicate log false ∧
      log≤MatrixVariablePacket.budget a r bit negative) ∧
    actual.steps≤budget a r bit negative := by
  obtain ⟨base,hb,bt,bh,offsetT,offsetH,_,_,_,_,fields,bs⟩ := MatrixVariablePacket.packet_run a r negative bit out ht
  have hh : ∀ i,selected a i=true → base.final.heads i≤base.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ base hb).1 i
    simpa only [input_head a r bit out i hi,Nat.zero_add] using h
  obtain ⟨actual,ha,hf,hs,_⟩ := MaskedReset.reset_run (MatrixVariablePacket.machine a negative)
    (selected a) _ _ base hb hh
  have hle : 2*base.steps+2≤budget a r bit negative := by unfold budget; omega
  have more := runFrom_moreFuel (machine a negative) (2*base.steps+2)
    (budget a r bit negative-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hle] at more
  have oldT (i : Fin (MatrixVariableCount.tapes a)) : actual.final.tapes (i.castAdd 1)=base.final.tapes i := by
    rw [hf]
    change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1)
      (motive := fun _ => List Bool) base.final.tapes (fun _ => List.replicate base.steps false)) (i.castAdd 1)=_
    rw [Fin.addCases_left]
  have oldH (i : Fin (MatrixVariableCount.tapes a)) : actual.final.heads (i.castAdd 1)=
      if selected a i then 0 else base.final.heads i := by
    rw [hf]
    change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1)
      (motive := fun _ => ℕ) (fun i => if selected a i then 0 else base.final.heads i) (fun _ => 0)) (i.castAdd 1)=_
    rw [Fin.addCases_left]
  refine ⟨actual,more,(oldT _).trans bt,(oldT _).trans offsetT,(fun j => (oldT _).trans (fields j)),?_,?_,?_,by omega⟩
  · intro i
    rw [oldH]
    by_cases ho : i=offset a
    · subst i
      rw [show selected a (offset a)=false by simp [selected,offset]]
      simpa only [Bool.false_eq_true,↓reduceIte] using offsetH
    by_cases hout : i=outputTape a
    · subst i
      rw [show selected a (outputTape a)=false by simp [selected,outputTape]]
      simpa only [Bool.false_eq_true,↓reduceIte,ho] using bh
    have hv0 : i.val≠424 := by intro he; exact ho (Fin.ext he)
    have hv1 : i.val≠MatrixVariableProduct.tapes a+16 := by intro he; exact hout (Fin.ext he)
    simp [selected,hv0,hv1,ho,hout]
  · rw [hf]
    change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1)
      (motive := fun _ => ℕ) (fun i => if selected a i then 0 else base.final.heads i) (fun _ => 0)) ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))=0
    rw [Fin.addCases_right]
  · refine ⟨base.steps,?_,bs⟩
    rw [hf]
    change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1)
      (motive := fun _ => List Bool) base.final.tapes (fun _ => List.replicate base.steps false)) ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))=_
    rw [Fin.addCases_right]

end NearCubicWires.RepairOrdinary.MatrixVariablePacketReset

import Proof.Supplier.EquationCutAmbientLayout

namespace NearCubicWires.RepairOrdinary.EquationCut.Ambient
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem restore_stage (pre suffix out : List Bool) (C p : Nat) (odd : Bool) (c : Cut)
    (hf : EquationRow.Fits p c) (hC : 128*((weights c).length+1)*(p+1) ≤ C) :
    ∃ r,runFrom restoreProgram (2*baseBudget (weights c).length p+2)
      ⟨restoreProgram.start,heads pre.length out,tapes C (pre++cutWord p c++suffix) out (weights c).length p odd⟩=some r ∧
      r.final.heads=heads pre.length (out++cutWord (p+1) (EquationRow.padded odd c)) ∧
      r.final.tapes=tapes C (pre++cutWord p c++suffix) (out++cutWord (p+1) (EquationRow.padded odd c)) (weights c).length p odd ∧
      r.steps ≤ 2*baseBudget (weights c).length p+2 := by
  obtain ⟨base,hb,bh,bt,bs⟩ := EquationCut.restore_run pre suffix out C p odd c hf hC
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config restoreSlots (by decide) restored
    (heads pre.length out) (tapes C (pre++cutWord p c++suffix) out (weights c).length p odd) _ _ base hb
  have hi : RecoveryFocus.config restoreSlots (heads pre.length out)
      (tapes C (pre++cutWord p c++suffix) out (weights c).length p odd)
      (⟨restored.start,restoreHeads pre.length out,restoreTapes C (pre++cutWord p c++suffix) out (weights c).length p odd⟩ : Configuration 6 _)=
      (⟨restoreProgram.start,heads pre.length out,tapes C (pre++cutWord p c++suffix) out (weights c).length p odd⟩ : Configuration 21 _) := by
    apply WilliamsSourceCrop.focus_same restoreSlots
      (⟨restoreProgram.start,heads pre.length out,tapes C (pre++cutWord p c++suffix) out (weights c).length p odd⟩ : Configuration 21 _)
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans_le bs⟩
  · rw [rf]
    simp only [RecoveryFocus.config,bh]
    funext i; fin_cases i <;>
      simp [pick_restore,restoreHeads,EquationCut.heads,heads,extraHeads,EquationScalarStream.heads,Fin.addCases]
  · rw [rf]
    simp only [RecoveryFocus.config,bt]
    funext i; fin_cases i <;>
      simp [pick_restore,restoreTapes,EquationCut.tapes,tapes,extras,EquationScalarStream.tapes,Fin.addCases]

theorem weight_stage (pre : List Bool) (values : List Int) (suffix out : List Bool) (C p : Nat) (odd : Bool)
    (hf : ∀ z∈values,z.natAbs<2^p) :
    ∃ r,runFrom weightProgram (weightBudget values.length p)
      ⟨weightProgram.start,heads pre.length out,tapes C (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(EquationWidenLoop.stream p values).length) (out++paddedWeights p odd values) ∧
      r.final.tapes=tapes C (pre++EquationWidenLoop.stream p values++suffix)
        (out++paddedWeights p odd values) values.length p odd ∧ r.steps ≤ weightBudget values.length p := by
  obtain ⟨base,hb,bh,bt,bs⟩ := weights_run pre values suffix out p odd hf
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots (by decide) weightMachine
    (heads pre.length out) (tapes C (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd) _ _ base hb
  have hi : RecoveryFocus.config slots (heads pre.length out)
      (tapes C (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd)
      (⟨weightMachine.start,EquationCut.heads pre.length out,
        EquationCut.tapes (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd⟩ : Configuration 5 _)=
      (⟨weightProgram.start,heads pre.length out,tapes C (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd⟩ : Configuration 21 _) := by
    apply WilliamsSourceCrop.focus_same slots
      (⟨weightProgram.start,heads pre.length out,tapes C (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd⟩ : Configuration 21 _)
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans_le bs⟩
  · rw [rf]
    simp only [RecoveryFocus.config,bh]
    funext i; fin_cases i <;>
      simp [pick,EquationCut.heads,heads,extraHeads,EquationScalarStream.heads,Fin.addCases]
  · rw [rf]
    simp only [RecoveryFocus.config,bt]
    funext i; fin_cases i <;>
      simp [pick,EquationCut.tapes,tapes,extras,EquationScalarStream.tapes,Fin.addCases]

theorem scalar_stage (negate : Bool) (pre suffix out : List Bool) (C L p : Nat) (odd : Bool) (z : Int)
    (hz : z.natAbs<2^p) (hC : 65*(p+1) ≤ C) :
    ∃ r,runFrom (scalarProgram negate) (EquationScalarStream.budget C p)
      ⟨(scalarProgram negate).start,heads pre.length out,tapes C (pre++frame (signMagnitude p z)++suffix) out L p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(frame (signMagnitude p z)).length)
        (out++frame (signMagnitude (p+1) (EquationScalar.target negate z))) ∧
      r.final.tapes=tapes C (pre++frame (signMagnitude p z)++suffix)
        (out++frame (signMagnitude (p+1) (EquationScalar.target negate z))) L p odd ∧
      r.steps ≤ EquationScalarStream.budget C p := by
  obtain ⟨base,hb,bh,bt,bs⟩ := EquationScalarStream.scalar_run negate pre suffix out C p z hz hC
  have h := TapeEmbedding.run_embed (EquationScalarStream.machine negate) extraHeads (extras C L p odd) _ _ base hb
  have hi : TapeEmbedding.config extraHeads (extras C L p odd)
      (EquationScalarStream.entry negate C pre.length (pre++frame (signMagnitude p z)++suffix) out)=
      (⟨(scalarProgram negate).start,heads pre.length out,tapes C (pre++frame (signMagnitude p z)++suffix) out L p odd⟩ : Configuration 21 _) := rfl
  rw [hi] at h
  refine ⟨TapeEmbedding.receipt extraHeads (extras C L p odd) base,h,?_,?_,bs⟩
  · change (Fin.addCases (m:=17) (n:=4) (motive:=fun _=>Nat) base.final.heads extraHeads)=_
    rw [bh]
    simp only [heads,frame_length,signMagnitude_length,Nat.mul_add,Nat.mul_one,Nat.add_assoc,
      show 2+1=3 from rfl]
  · change (Fin.addCases (m:=17) (n:=4) (motive:=fun _=>List Bool) base.final.tapes (extras C L p odd))=_
    rw [bt]
    rfl

end
end NearCubicWires.RepairOrdinary.EquationCut.Ambient

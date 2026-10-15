import Proof.Supplier.EquationCutSecond

/-! The literal complete paper-B.2 byte emitter. One original equation
field stream is read twice with one paid source restoration, producing
exactly its two signed weak cuts in the actual matrix request codec. -/
namespace NearCubicWires.RepairOrdinary.EquationCut.Ambient
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def output (p : Nat) (odd : Bool) (c : Cut) :=
  cutWord (p+1) (EquationRow.padded odd c)++
    cutWord (p+1) (EquationRow.successor (EquationRow.padded odd c))

theorem cut_budget (C L p : Nat) (hC : 128*(L+1)*(p+1) ≤ C) :
    (2*baseBudget L p+2)+1+secondBudget C L p ≤ budget C := by
  unfold baseBudget secondBudget weightBudget EquationScalarStream.budget budget
  nlinarith

theorem cut_run (pre suffix out : List Bool) (C p : Nat) (odd : Bool) (c : Cut)
    (hf : EquationRow.Fits p c) (hC : 128*((weights c).length+1)*(p+1) ≤ C) :
    ∃ r,runFrom machine (budget C)
      (entry C pre.length (pre++cutWord p c++suffix) out (weights c).length p odd)=some r ∧
      r.final.heads=heads (pre.length+(cutWord p c).length) (out++output p odd c) ∧
      r.final.tapes=tapes C (pre++cutWord p c++suffix) (out++output p odd c) (weights c).length p odd ∧
      r.steps ≤ budget C := by
  obtain ⟨first,hf1,fh,ft,_fs⟩ := restore_stage pre suffix out C p odd c hf hC
  have hscalar : 65*(p+1) ≤ C := by nlinarith
  obtain ⟨last,hl,lh,lt,_ls⟩ := second_run pre suffix
    (out++cutWord (p+1) (EquationRow.padded odd c)) C p odd c hf hscalar
  have he : Composition.restart first.final second.start=
      (⟨second.start,heads pre.length (out++cutWord (p+1) (EquationRow.padded odd c)),
        tapes C (pre++cutWord p c++suffix) (out++cutWord (p+1) (EquationRow.padded odd c)) (weights c).length p odd⟩ : Configuration 21 _) := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact ft
  rw [←he] at hl
  have joined := Composition.run_join restoreProgram second _ _ _ first last hf1 hl
  have ht := cut_budget C (weights c).length p hC
  have hmore := runFrom_moreFuel machine _
    (budget C-((2*baseBudget (weights c).length p+2)+1+secondBudget C (weights c).length p))
    _ (Composition.joinedReceipt first last) joined
  rw [Nat.add_sub_of_le ht] at hmore
  refine ⟨Composition.joinedReceipt first last,hmore,?_,?_,?_⟩
  · change last.final.heads=_
    simpa only [output,List.append_assoc] using lh
  · change last.final.tapes=_
    simpa only [output,List.append_assoc] using lt
  · exact runFrom_steps_le machine (budget C) _ _ hmore

theorem row_capacity (d p : Nat) (odd : Bool) (c : Cut)
    (hl : c.leftWeights.length=d) (hr : c.rightWeights.length+odd.toNat=d) :
    128*((weights c).length+1)*(p+1) ≤ 128*(2*d+1)*(p+1) := by
  have hw : (weights c).length ≤ 2*d := by simp only [weights,List.length_append]; omega
  gcongr

end
end NearCubicWires.RepairOrdinary.EquationCut.Ambient

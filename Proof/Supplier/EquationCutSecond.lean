import Proof.Supplier.EquationCutAmbientStages

/-! Second cut: stream the same original weights, then actually increment
the threshold and negate the coefficient in the reusable scalar bank. -/
namespace NearCubicWires.RepairOrdinary.EquationCut.Ambient
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def secondBudget (C L p : Nat) := weightBudget L p+1+(2*EquationScalarStream.budget C p+1)

theorem successor_word (p : Nat) (odd : Bool) (c : Cut) :
    cutWord (p+1) (EquationRow.successor (EquationRow.padded odd c))=
    paddedWeights p odd (weights c)++frame (signMagnitude (p+1) (c.threshold+1))++frame (signMagnitude (p+1) (-c.coefficient)) := by
  cases odd <;> simp [cutWord,fields,weights,EquationWidenLoop.stream,paddedWeights,
    EquationRow.successor,EquationRow.padded,EquationRow.paddedRight,List.flatMap_append,List.append_assoc]

theorem scalar_pair (pre suffix out : List Bool) (C L p : Nat) (z v : Int) (odd : Bool)
    (hz : z.natAbs<2^p) (hv : v.natAbs<2^p) (hC : 65*(p+1) ≤ C) :
    ∃ r,runFrom secondTail (2*EquationScalarStream.budget C p+1)
      ⟨secondTail.start,heads pre.length out,tapes C (pre++frame (signMagnitude p z)++frame (signMagnitude p v)++suffix) out L p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(frame (signMagnitude p z)).length+(frame (signMagnitude p v)).length)
        (out++frame (signMagnitude (p+1) (z+1))++frame (signMagnitude (p+1) (-v))) ∧
      r.final.tapes=tapes C (pre++frame (signMagnitude p z)++frame (signMagnitude p v)++suffix)
        (out++frame (signMagnitude (p+1) (z+1))++frame (signMagnitude (p+1) (-v))) L p odd ∧
      r.steps ≤ 2*EquationScalarStream.budget C p+1 := by
  obtain ⟨first,hf,fh,ft,fs⟩ := scalar_stage false pre (frame (signMagnitude p v)++suffix) out C L p odd z hz hC
  obtain ⟨last,hl,lh,lt,ls⟩ := scalar_stage true (pre++frame (signMagnitude p z)) suffix
    (out++frame (signMagnitude (p+1) (z+1))) C L p odd v hv hC
  have he : Composition.restart first.final (scalarProgram true).start=
      (⟨(scalarProgram true).start,heads (pre++frame (signMagnitude p z)).length (out++frame (signMagnitude (p+1) (z+1))),
        tapes C ((pre++frame (signMagnitude p z))++frame (signMagnitude p v)++suffix)
          (out++frame (signMagnitude (p+1) (z+1))) L p odd⟩ : Configuration 21 _) := by
    apply configuration_ext
    · rfl
    · simpa only [Composition.restart,EquationScalar.target,List.length_append,Bool.false_eq_true,ite_false] using fh
    · simpa only [Composition.restart,EquationScalar.target,List.append_assoc,Bool.false_eq_true,ite_false] using ft
  rw [←he] at hl
  have joined := Composition.run_join (scalarProgram false) (scalarProgram true) _ _ _ first last hf hl
  have heq : EquationScalarStream.budget C p+1+EquationScalarStream.budget C p=2*EquationScalarStream.budget C p+1 := by omega
  rw [heq] at joined
  refine ⟨Composition.joinedReceipt first last,?_,?_,lt,?_⟩
  · simpa only [secondTail,Composition.machine,Composition.leftConfig,List.append_assoc] using joined
  · change last.final.heads=_
    simpa only [List.length_append,EquationScalar.target,ite_true] using lh
  · change first.steps+1+last.steps ≤ _
    omega

theorem second_run (pre suffix out : List Bool) (C p : Nat) (odd : Bool) (c : Cut)
    (hf : EquationRow.Fits p c) (hC : 65*(p+1) ≤ C) :
    ∃ r,runFrom second (secondBudget C (weights c).length p)
      ⟨second.start,heads pre.length out,tapes C (pre++cutWord p c++suffix) out (weights c).length p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(cutWord p c).length)
        (out++cutWord (p+1) (EquationRow.successor (EquationRow.padded odd c))) ∧
      r.final.tapes=tapes C (pre++cutWord p c++suffix)
        (out++cutWord (p+1) (EquationRow.successor (EquationRow.padded odd c))) (weights c).length p odd ∧
      r.steps ≤ secondBudget C (weights c).length p := by
  obtain ⟨first,hfirst,fh,ft,fs⟩ := weight_stage pre (weights c)
    (frame (signMagnitude p c.threshold)++frame (signMagnitude p c.coefficient)++suffix) out C p odd hf.1
  obtain ⟨last,hl,lh,lt,ls⟩ := scalar_pair (pre++EquationWidenLoop.stream p (weights c)) suffix
    (out++paddedWeights p odd (weights c)) C (weights c).length p c.threshold c.coefficient odd hf.2.1 hf.2.2 hC
  have he : Composition.restart first.final secondTail.start=
      (⟨secondTail.start,heads (pre++EquationWidenLoop.stream p (weights c)).length (out++paddedWeights p odd (weights c)),
        tapes C ((pre++EquationWidenLoop.stream p (weights c))++frame (signMagnitude p c.threshold)++frame (signMagnitude p c.coefficient)++suffix)
          (out++paddedWeights p odd (weights c)) (weights c).length p odd⟩ : Configuration 21 _) := by
    apply configuration_ext
    · rfl
    · simpa only [Composition.restart,List.length_append] using fh
    · simpa only [Composition.restart,List.append_assoc] using ft
  rw [←he] at hl
  have joined := Composition.run_join weightProgram secondTail _ _ _ first last hfirst hl
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_,?_⟩
  · simpa only [secondBudget,second,Composition.machine,Composition.leftConfig,cut_word,List.append_assoc] using joined
  · change last.final.heads=_
    rw [successor_word,cut_word]
    simpa only [List.length_append,Nat.add_assoc,List.append_assoc] using lh
  · change last.final.tapes=_
    rw [successor_word,cut_word]
    simpa only [List.append_assoc] using lt
  · change first.steps+1+last.steps ≤ _
    unfold secondBudget
    omega

end
end NearCubicWires.RepairOrdinary.EquationCut.Ambient

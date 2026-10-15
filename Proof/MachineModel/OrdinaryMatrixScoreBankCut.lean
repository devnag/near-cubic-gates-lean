import Proof.MachineModel.OrdinaryMatrixScoreBankFields
import Proof.MachineModel.OrdinaryMatrixScoreLeftLoop

/-! The actual local bank loader copies the two weight lists (`width` weights each, counted by the
`width` template), then both scalar fields, from the retained raw-header cursor. No bit-count
driver or positioned-field premise is supplied. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBankCut
open LocalBitMultitape SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def weightsMachine := Composition.machine MatrixScoreBankFields.machine MatrixScoreBankFields.machine
def fieldMachine := TapeEmbedding.machine 1 MatrixScoreBankField.machine
noncomputable def scalarsMachine := Composition.machine fieldMachine fieldMachine
noncomputable def machine := Composition.machine weightsMachine scalarsMachine
def budget (d p : ℕ) := (d*(2*p+6)+3)+1+(d*(2*p+6)+3)+1+((2*p+3)+1+(2*p+3))

theorem field_run (p d : ℕ) (z : ℤ) (pre suffix out : List Bool) :
    ∃ actual,runFrom fieldMachine (2*p+3)
      (RecoveryCalls.restarted fieldMachine ![pre.length,out.length,1]
        ![pre++frame (signMagnitude p z)++suffix,out,UnaryTemplate.tape d])=some actual ∧
      actual.final.heads=![pre.length+(frame (signMagnitude p z)).length,
        (out++frame (signMagnitude p z)).length,1] ∧
      actual.final.tapes=![pre++frame (signMagnitude p z)++suffix,out++frame (signMagnitude p z),UnaryTemplate.tape d] ∧
      actual.steps=2*p+3 := by
  obtain ⟨base,hb,hf,hs⟩ := MatrixScoreBankField.field_run (signMagnitude p z) pre suffix out
  have he := TapeEmbedding.run_embed MatrixScoreBankField.machine (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => UnaryTemplate.tape d) _ _ base hb
  have hlen : (signMagnitude p z).length=p+1 := by simp [signMagnitude]
  have htime : 2*(signMagnitude p z).length+1=2*p+3 := by rw [hlen]; omega
  rw [htime] at he hs
  let expanded := TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ : Fin 1 => UnaryTemplate.tape d) base
  have hi : TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ : Fin 1 => UnaryTemplate.tape d)
      (MatrixScoreBankField.cfg 0 (pre++frame (signMagnitude p z)++suffix) pre.length out)=
      RecoveryCalls.restarted fieldMachine ![pre.length,out.length,1]
        ![pre++frame (signMagnitude p z)++suffix,out,UnaryTemplate.tape d] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at he
  refine ⟨expanded,he,?_,?_,hs⟩
  · change (TapeEmbedding.config _ _ base.final).heads=_
    rw [hf]
    funext i; fin_cases i <;> rfl
  · change (TapeEmbedding.config _ _ base.final).tapes=_
    rw [hf]
    funext i; fin_cases i <;> rfl

theorem scalars_run (p d : ℕ) (theta coefficient : ℤ) (pre suffix out : List Bool) :
    ∃ actual,runFrom scalarsMachine ((2*p+3)+1+(2*p+3))
      (RecoveryCalls.restarted scalarsMachine ![pre.length,out.length,1]
        ![pre++frame (signMagnitude p theta)++frame (signMagnitude p coefficient)++suffix,out,UnaryTemplate.tape d])=some actual ∧
      actual.final.heads=![pre.length+(frame (signMagnitude p theta)++frame (signMagnitude p coefficient)).length,
        (out++frame (signMagnitude p theta)++frame (signMagnitude p coefficient)).length,1] ∧
      actual.final.tapes=![pre++frame (signMagnitude p theta)++frame (signMagnitude p coefficient)++suffix,
        out++frame (signMagnitude p theta)++frame (signMagnitude p coefficient),UnaryTemplate.tape d] ∧
      actual.steps≤(2*p+3)+1+(2*p+3) := by
  obtain ⟨first,hf,fh,ft,fs⟩ := field_run p d theta pre (frame (signMagnitude p coefficient)++suffix) out
  obtain ⟨last,hl,lh,lt,ls⟩ := field_run p d coefficient (pre++frame (signMagnitude p theta)) suffix
    (out++frame (signMagnitude p theta))
  have hi : Composition.restart first.final fieldMachine.start=
      RecoveryCalls.restarted fieldMachine ![(pre++frame (signMagnitude p theta)).length,(out++frame (signMagnitude p theta)).length,1]
        ![(pre++frame (signMagnitude p theta))++frame (signMagnitude p coefficient)++suffix,
          out++frame (signMagnitude p theta),UnaryTemplate.tape d] := by
    apply configuration_ext
    · rfl
    · change first.final.heads=_
      simpa only [List.length_append,RecoveryCalls.restarted] using fh
    · change first.final.tapes=_
      simpa only [List.append_assoc,RecoveryCalls.restarted] using ft
  rw [← hi] at hl
  have joined := Composition.run_join fieldMachine fieldMachine _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,?_,?_,lt,?_⟩
  · simpa only [List.append_assoc,RecoveryCalls.restarted,Composition.leftConfig,scalarsMachine,Composition.machine] using joined
  · change last.final.heads=_
    simpa only [List.length_append,Nat.add_assoc] using lh
  · change first.steps+1+last.steps≤_
    omega

theorem weights_run (p : ℕ) (weights right : List ℤ) (pre suffix out : List Bool) (hlen : right.length=weights.length) :
    ∃ actual,runFrom weightsMachine ((weights.length*(2*p+6)+3)+1+(weights.length*(2*p+6)+3))
      (RecoveryCalls.restarted weightsMachine ![pre.length,out.length,1]
        ![pre++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix,out,UnaryTemplate.tape weights.length])=some actual ∧
      actual.final.heads=![pre.length+(MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right).length,
        (out++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right).length,1] ∧
      actual.final.tapes=![pre++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix,
        out++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right,UnaryTemplate.tape weights.length] ∧
      actual.steps≤(weights.length*(2*p+6)+3)+1+(weights.length*(2*p+6)+3) := by
  obtain ⟨first,hf,fh,ft,fs⟩ := MatrixScoreBankFields.physical_run p weights pre (MatrixScoreCanonical.fields p right++suffix) out
  obtain ⟨last,hl,lh,lt,ls⟩ := MatrixScoreBankFields.physical_run p right (pre++MatrixScoreCanonical.fields p weights) suffix
    (out++MatrixScoreCanonical.fields p weights)
  rw [hlen] at hl lt ls
  have hi : Composition.restart first.final MatrixScoreBankFields.machine.start=
      RecoveryCalls.restarted MatrixScoreBankFields.machine ![(pre++MatrixScoreCanonical.fields p weights).length,
        (out++MatrixScoreCanonical.fields p weights).length,1]
        ![(pre++MatrixScoreCanonical.fields p weights)++MatrixScoreCanonical.fields p right++suffix,
          out++MatrixScoreCanonical.fields p weights,UnaryTemplate.tape weights.length] := by
    apply configuration_ext
    · rfl
    · change first.final.heads=_
      simpa only [List.length_append,RecoveryCalls.restarted] using fh
    · change first.final.tapes=_
      simpa only [List.append_assoc,RecoveryCalls.restarted] using ft
  rw [← hi] at hl
  have joined := Composition.run_join MatrixScoreBankFields.machine MatrixScoreBankFields.machine _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,?_,?_,lt,?_⟩
  · simpa only [List.append_assoc,RecoveryCalls.restarted,Composition.leftConfig,weightsMachine,Composition.machine] using joined
  · change last.final.heads=_
    simpa only [List.length_append,Nat.add_assoc] using lh
  · change first.steps+1+last.steps≤_
    omega

theorem bank_run (r : Request) (gate : Fin r.Gates) (pre suffix out : List Bool) :
    ∃ actual,runFrom machine (budget r.width r.p)
      (RecoveryCalls.restarted machine ![pre.length,out.length,1]
        ![pre++cutWord r.p (r.cuts.get gate)++suffix,out,UnaryTemplate.tape r.width])=some actual ∧
      actual.final.heads=![pre.length+(cutWord r.p (r.cuts.get gate)).length,
        (out++cutWord r.p (r.cuts.get gate)).length,1] ∧
      actual.final.tapes=![pre++cutWord r.p (r.cuts.get gate)++suffix,out++cutWord r.p (r.cuts.get gate),UnaryTemplate.tape r.width] ∧
      actual.steps≤budget r.width r.p := by
  have mem := List.get_mem r.cuts gate
  obtain ⟨hlength,hrlength⟩ := r.lengths _ mem
  let A := MatrixScoreCanonical.fields r.p (r.cuts.get gate).leftWeights
  let B := MatrixScoreCanonical.fields r.p (r.cuts.get gate).rightWeights
  let T := frame (signMagnitude r.p (r.cuts.get gate).threshold)
  let K := frame (signMagnitude r.p (r.cuts.get gate).coefficient)
  have hcut : A++B++T++K=cutWord r.p (r.cuts.get gate) := MatrixScoreLeftLoop.source_eq r gate
  obtain ⟨first,hf,fh,ft,fs⟩ := weights_run r.p (r.cuts.get gate).leftWeights (r.cuts.get gate).rightWeights
    pre (T++K++suffix) out (by omega)
  rw [hlength] at hf ft fs
  obtain ⟨last,hl,lh,lt,ls⟩ := scalars_run r.p r.width (r.cuts.get gate).threshold (r.cuts.get gate).coefficient
    (pre++A++B) suffix (out++A++B)
  have hi : Composition.restart first.final scalarsMachine.start=
      RecoveryCalls.restarted scalarsMachine ![(pre++A++B).length,(out++A++B).length,1]
        ![(pre++A++B)++T++K++suffix,out++A++B,UnaryTemplate.tape r.width] := by
    apply configuration_ext
    · rfl
    · change first.final.heads=_
      simpa only [List.length_append,Nat.add_assoc,RecoveryCalls.restarted] using fh
    · change first.final.tapes=_
      simpa only [List.append_assoc,RecoveryCalls.restarted] using ft
  rw [← hi] at hl
  have joined := Composition.run_join weightsMachine scalarsMachine _ _ _ first last hf hl
  have sourceEq : pre++A++B++(T++K++suffix)=pre++cutWord r.p (r.cuts.get gate)++suffix := by rw [← hcut]; simp only [List.append_assoc]
  have outputEq : out++A++B++T++K=out++cutWord r.p (r.cuts.get gate) := by rw [← hcut]; simp only [List.append_assoc]
  change runFrom _ _ (Composition.leftConfig _ (RecoveryCalls.restarted _ ![pre.length,out.length,1]
    ![pre++A++B++(T++K++suffix),out,UnaryTemplate.tape r.width]))=_ at joined
  rw [sourceEq] at joined
  change last.final.heads=![(pre++A++B).length+(T++K).length,(out++A++B++T++K).length,1] at lh
  rw [outputEq] at lh
  have cursorEq : (pre++A++B).length+(T++K).length=pre.length+(cutWord r.p (r.cuts.get gate)).length := by
    rw [← hcut]
    simp only [List.length_append]
    omega
  rw [cursorEq] at lh
  change last.final.tapes=![pre++A++B++T++K++suffix,out++A++B++T++K,UnaryTemplate.tape r.width] at lt
  rw [outputEq] at lt
  have finalSourceEq : pre++A++B++T++K++suffix=pre++cutWord r.p (r.cuts.get gate)++suffix := by rw [← hcut]; simp only [List.append_assoc]
  rw [finalSourceEq] at lt
  refine ⟨Composition.joinedReceipt first last,joined,lh,lt,?_⟩
  change first.steps+1+last.steps≤_
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreBankCut

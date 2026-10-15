import Proof.Supplier.EquationCutWeights

/-! The complete first cut is streamed directly to its final output. -/
namespace NearCubicWires.RepairOrdinary.EquationCut
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def weights (c : Cut) := c.leftWeights++c.rightWeights
def baseBudget (L p : Nat) := L*(2*p+8)+7*p+25

theorem cut_word (p : Nat) (c : Cut) : cutWord p c=
    EquationWidenLoop.stream p (weights c)++frame (signMagnitude p c.threshold)++frame (signMagnitude p c.coefficient) := by
  simp [cutWord,fields,weights,EquationWidenLoop.stream,List.flatMap_append,List.append_assoc]
theorem padded_word (p : Nat) (odd : Bool) (c : Cut) : cutWord (p+1) (EquationRow.padded odd c)=
    paddedWeights p odd (weights c)++frame (signMagnitude (p+1) c.threshold)++frame (signMagnitude (p+1) c.coefficient) := by
  cases odd <;> simp [cutWord,fields,weights,EquationWidenLoop.stream,paddedWeights,
    EquationRow.padded,EquationRow.paddedRight,List.flatMap_append,List.append_assoc]

theorem scalar_stage (pre suffix out : List Bool) (L p : Nat) (z : Int) (odd : Bool)
    (hz : z.natAbs<2^p) :
    ∃ r,runFrom scalarProgram (2*p+5)
      ⟨scalarProgram.start,heads pre.length out,tapes (pre++frame (signMagnitude p z)++suffix) out L p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(frame (signMagnitude p z)).length) (out++frame (signMagnitude (p+1) z)) ∧
      r.final.tapes=tapes (pre++frame (signMagnitude p z)++suffix) (out++frame (signMagnitude (p+1) z)) L p odd ∧
      r.steps=2*p+5 := by
  obtain ⟨base,hb,bf,bs⟩ := EquationWiden.scalar_run pre suffix out p z hz
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config scalarSlots (by decide) EquationWiden.machine
    (heads pre.length out) (tapes (pre++frame (signMagnitude p z)++suffix) out L p odd) _ _ base hb
  have hi : RecoveryFocus.config scalarSlots (heads pre.length out)
      (tapes (pre++frame (signMagnitude p z)++suffix) out L p odd)
      (EquationWiden.cfg 0 (pre++frame (signMagnitude p z)++suffix) pre.length out)=
      (⟨scalarProgram.start,heads pre.length out,tapes (pre++frame (signMagnitude p z)++suffix) out L p odd⟩ : Configuration 5 5) := by
    apply WilliamsSourceCrop.focus_same scalarSlots
      (⟨scalarProgram.start,heads pre.length out,tapes (pre++frame (signMagnitude p z)++suffix) out L p odd⟩ : Configuration 5 5)
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick_scalar,heads,EquationWiden.cfg,frame_length,signMagnitude_length]
    omega
  · rw [rf,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick_scalar,tapes,EquationWiden.cfg]

theorem scalar_pair (pre suffix out : List Bool) (L p : Nat) (z v : Int) (odd : Bool)
    (hz : z.natAbs<2^p) (hv : v.natAbs<2^p) :
    ∃ r,runFrom baseTail (4*p+11)
      ⟨baseTail.start,heads pre.length out,tapes (pre++frame (signMagnitude p z)++frame (signMagnitude p v)++suffix) out L p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(frame (signMagnitude p z)).length+(frame (signMagnitude p v)).length)
        (out++frame (signMagnitude (p+1) z)++frame (signMagnitude (p+1) v)) ∧
      r.final.tapes=tapes (pre++frame (signMagnitude p z)++frame (signMagnitude p v)++suffix)
        (out++frame (signMagnitude (p+1) z)++frame (signMagnitude (p+1) v)) L p odd ∧ r.steps=4*p+11 := by
  obtain ⟨first,hf,fh,ft,fs⟩ := scalar_stage pre (frame (signMagnitude p v)++suffix) out L p z odd hz
  obtain ⟨last,hl,lh,lt,ls⟩ := scalar_stage (pre++frame (signMagnitude p z)) suffix
    (out++frame (signMagnitude (p+1) z)) L p v odd hv
  have he : Composition.restart first.final scalarProgram.start=
      (⟨scalarProgram.start,heads (pre++frame (signMagnitude p z)).length (out++frame (signMagnitude (p+1) z)),
        tapes ((pre++frame (signMagnitude p z))++frame (signMagnitude p v)++suffix)
          (out++frame (signMagnitude (p+1) z)) L p odd⟩ : Configuration 5 5) := by
    apply configuration_ext
    · rfl
    · simpa only [Composition.restart,List.length_append] using fh
    · simpa only [Composition.restart,List.append_assoc] using ft
  rw [←he] at hl
  have joined := Composition.run_join scalarProgram scalarProgram _ _ _ first last hf hl
  have heq : (2*p+5)+1+(2*p+5)=4*p+11 := by omega
  rw [heq] at joined
  refine ⟨Composition.joinedReceipt first last,?_,?_,lt,?_⟩
  · simpa only [baseTail,Composition.machine,Composition.leftConfig,List.append_assoc] using joined
  · change last.final.heads=_
    simpa only [List.length_append] using lh
  · change first.steps+1+last.steps=_
    omega

theorem base_run (pre suffix out : List Bool) (p : Nat) (odd : Bool) (c : Cut) (hf : EquationRow.Fits p c) :
    ∃ r,runFrom base (baseBudget (weights c).length p)
      ⟨base.start,heads pre.length out,tapes (pre++cutWord p c++suffix) out (weights c).length p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(cutWord p c).length) (out++cutWord (p+1) (EquationRow.padded odd c)) ∧
      r.final.tapes=tapes (pre++cutWord p c++suffix) (out++cutWord (p+1) (EquationRow.padded odd c)) (weights c).length p odd ∧
      r.steps ≤ baseBudget (weights c).length p := by
  obtain ⟨first,hfirst,fh,ft,fs⟩ := weights_run pre (weights c)
    (frame (signMagnitude p c.threshold)++frame (signMagnitude p c.coefficient)++suffix) out p odd hf.1
  obtain ⟨last,hl,lh,lt,ls⟩ := scalar_pair (pre++EquationWidenLoop.stream p (weights c)) suffix
    (out++paddedWeights p odd (weights c)) (weights c).length p c.threshold c.coefficient odd hf.2.1 hf.2.2
  have he : Composition.restart first.final baseTail.start=
      (⟨baseTail.start,heads (pre++EquationWidenLoop.stream p (weights c)).length (out++paddedWeights p odd (weights c)),
        tapes ((pre++EquationWidenLoop.stream p (weights c))++frame (signMagnitude p c.threshold)++frame (signMagnitude p c.coefficient)++suffix)
          (out++paddedWeights p odd (weights c)) (weights c).length p odd⟩ : Configuration 5 _) := by
    apply configuration_ext
    · rfl
    · simpa only [Composition.restart,List.length_append] using fh
    · simpa only [Composition.restart,List.append_assoc] using ft
  rw [←he] at hl
  have joined := Composition.run_join weightMachine baseTail _ _ _ first last hfirst hl
  have htime : weightBudget (weights c).length p+1+(4*p+11)=baseBudget (weights c).length p := by
    unfold weightBudget baseBudget; omega
  rw [htime] at joined
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_,?_⟩
  · simpa only [base,Composition.machine,Composition.leftConfig,cut_word,List.append_assoc] using joined
  · change last.final.heads=_
    rw [padded_word,cut_word]
    simpa only [List.length_append,Nat.add_assoc,List.append_assoc] using lh
  · change last.final.tapes=_
    rw [padded_word,cut_word]
    simpa only [List.append_assoc] using lt
  · change first.steps+1+last.steps ≤ _
    unfold weightBudget baseBudget at *
    omega

end
end NearCubicWires.RepairOrdinary.EquationCut

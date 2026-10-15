import Proof.Supplier.EquationCutLayout

namespace NearCubicWires.RepairOrdinary.EquationCut
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem weight_stage (pre : List Bool) (values : List Int) (suffix out : List Bool) (p : Nat) (odd : Bool)
    (hf : ∀ z∈values,z.natAbs<2^p) :
    ∃ r,runFrom weightProgram (values.length*(2*p+8)+3)
      ⟨weightProgram.start,heads pre.length out,tapes (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(EquationWidenLoop.stream p values).length) (out++EquationWidenLoop.stream (p+1) values) ∧
      r.final.tapes=tapes (pre++EquationWidenLoop.stream p values++suffix)
        (out++EquationWidenLoop.stream (p+1) values) values.length p odd ∧
      r.steps ≤ values.length*(2*p+8)+3 := by
  obtain ⟨base,hb,bf,bs⟩ := EquationWidenLoop.loop_run pre values suffix out p hf
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config weightSlots (by decide) EquationWidenLoop.machine
    (heads pre.length out) (tapes (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd) _ _ base hb
  have hi : RecoveryFocus.config weightSlots (heads pre.length out)
      (tapes (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd)
      (EquationWidenLoop.cfg 0 (pre++EquationWidenLoop.stream p values++suffix) pre.length out values.length 1)=
      (⟨weightProgram.start,heads pre.length out,tapes (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd⟩ : Configuration 5 _) := by
    apply WilliamsSourceCrop.focus_same weightSlots
      (⟨weightProgram.start,heads pre.length out,tapes (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd⟩ : Configuration 5 _)
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans_le bs⟩
  · rw [rf,bf]
    funext i; fin_cases i <;>
      simp [RecoveryFocus.config,pick_weight,heads,EquationWidenLoop.cfg,RepeatMachine.cfg,
        controlConfig,TapeEmbedding.config,EquationWiden.cfg,Fin.addCases]
  · rw [rf,bf]
    funext i; fin_cases i <;>
      simp [RecoveryFocus.config,pick_weight,tapes,EquationWidenLoop.cfg,RepeatMachine.cfg,
        controlConfig,TapeEmbedding.config,EquationWiden.cfg,Fin.addCases]

theorem zero_stage (source out : List Bool) (pos L p : Nat) (odd : Bool) :
    ∃ r,runFrom zeroProgram (3*p+8)
      ⟨zeroProgram.start,heads pos out,tapes source out L p odd⟩=some r ∧
      r.final.heads=heads pos (out++frame (signMagnitude (p+1) 0)) ∧
      r.final.tapes=tapes source (out++frame (signMagnitude (p+1) 0)) L p odd ∧ r.steps=3*p+8 := by
  obtain ⟨base,hb,bf,bs⟩ := EquationZeroField.scalar_run p out
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config zeroSlots (by decide) EquationZeroField.machine
    (heads pos out) (tapes source out L p odd) _ _ base hb
  have hi : RecoveryFocus.config zeroSlots (heads pos out) (tapes source out L p odd)
      (EquationZeroField.cfg 0 (p+2) 1 out)=
      (⟨zeroProgram.start,heads pos out,tapes source out L p odd⟩ : Configuration 5 4) := by
    apply WilliamsSourceCrop.focus_same zeroSlots (⟨zeroProgram.start,heads pos out,tapes source out L p odd⟩ : Configuration 5 4)
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick_zero,heads,EquationZeroField.cfg]
  · rw [rf,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick_zero,tapes,EquationZeroField.cfg]

theorem weights_run (pre : List Bool) (values : List Int) (suffix out : List Bool) (p : Nat) (odd : Bool)
    (hf : ∀ z∈values,z.natAbs<2^p) :
    ∃ r,runFrom weightMachine (weightBudget values.length p)
      ⟨weightMachine.start,heads pre.length out,tapes (pre++EquationWidenLoop.stream p values++suffix) out values.length p odd⟩=some r ∧
      r.final.heads=heads (pre.length+(EquationWidenLoop.stream p values).length) (out++paddedWeights p odd values) ∧
      r.final.tapes=tapes (pre++EquationWidenLoop.stream p values++suffix)
        (out++paddedWeights p odd values) values.length p odd ∧ r.steps ≤ weightBudget values.length p := by
  obtain ⟨first,hfirst,fh,ft,_fs⟩ := weight_stage pre values suffix out p odd hf
  let source := pre++EquationWidenLoop.stream p values++suffix
  let pos := pre.length+(EquationWidenLoop.stream p values).length
  let middle := out++EquationWidenLoop.stream (p+1) values
  have hpath : ∃ n,n ≤ weightBudget values.length p ∧ Timed weightMachine n
      ⟨weightMachine.start,heads pre.length out,tapes source out values.length p odd⟩
      (RecoveryCalls.stopped weightSizes (heads pos (out++paddedWeights p odd values))
        (tapes source (out++paddedWeights p odd values) values.length p odd)) := by
    cases odd
    · obtain ⟨n,hn,h⟩ := stop_receipt weightSizes weightPrograms 0 weightNext 0 _ _ first hfirst
        (by simp [weightNext,Configuration.scanned,fh,ft,tapes,heads,readTapeBit])
      refine ⟨n,by unfold weightBudget; omega,?_⟩
      simpa only [fh,ft,paddedWeights,Bool.false_eq_true,ite_false,List.append_nil,source,pos,
        weightMachine,RecoveryCalls.machine,controlConfig,weightPrograms,Fin.cases_zero] using h
    · obtain ⟨n,hn,h⟩ := call_receipt weightSizes weightPrograms 0 weightNext 0 1 _ _ first hfirst
        (by simp [weightNext,Configuration.scanned,fh,ft,tapes,heads,readTapeBit])
      obtain ⟨last,hl,lh,lt,_ls⟩ := zero_stage source middle pos values.length p true
      obtain ⟨m,hm,g⟩ := stop_receipt weightSizes weightPrograms 0 weightNext 1 _ _ last hl (by rfl)
      have he : controlConfig (RecoveryCalls.code weightSizes 1)
          (RecoveryCalls.restarted (weightPrograms 1) first.final.heads first.final.tapes)=
          controlConfig (RecoveryCalls.code weightSizes 1)
          (⟨zeroProgram.start,heads pos middle,tapes source middle values.length p true⟩ : Configuration 5 4) := by
        rw [fh,ft]
        rfl
      rw [he] at h
      have joined := h.trans g
      refine ⟨n+m,by unfold weightBudget; omega,?_⟩
      simpa only [lh,lt,paddedWeights,ite_true,List.append_assoc,source,pos,middle,
        weightMachine,RecoveryCalls.machine,controlConfig,weightPrograms,Fin.cases_zero] using joined
  obtain ⟨n,hn,h⟩ := hpath
  obtain ⟨r,hr,rf,rs⟩ := h.run (by simp [weightMachine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hmore := runFrom_moreFuel weightMachine n (weightBudget values.length p-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hmore
  exact ⟨r,hmore,by simp [rf,RecoveryCalls.stopped,pos],by simp [rf,RecoveryCalls.stopped,source],rs.trans_le hn⟩

end
end NearCubicWires.RepairOrdinary.EquationCut

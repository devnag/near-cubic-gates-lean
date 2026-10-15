import Proof.MachineModel.OrdinaryMatrixBatchRightPlaneBounds

/-! Paid field operations for the actual coefficient extractor. The raw
cut cursor streams while the d-template and growing coefficient bank are
retained; both weight blocks will be skipped before copying the coefficient. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientFields
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos d : ℕ) (out : List Bool) : Configuration 3 s :=
  ⟨q,![pos,1,out.length],![source,UnaryTemplate.tape d,out]⟩
noncomputable def skip := TapeEmbedding.machine 1 MatrixScoreSkipFields.machine
def threshold := TapeEmbedding.machine 2 MatrixScoreSkipField.machine
def copySlots : Fin 2 → Fin 3 := ![0,2]
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def copy := RecoveryFocus.machine copySlots MatrixScoreBankField.machine

theorem skip_run (p : ℕ) (weights : List ℤ) (pre suffix out : List Bool) : ∃ actual,
    runFrom skip (weights.length*(2*p+6)+3)
      (cfg skip.start (pre++MatrixScoreCanonical.fields p weights++suffix) pre.length weights.length out)=some actual ∧
    actual.final=cfg actual.final.control (pre++MatrixScoreCanonical.fields p weights++suffix)
      (pre.length+(MatrixScoreCanonical.fields p weights).length) weights.length out ∧
    actual.steps≤weights.length*(2*p+6)+3 := by
  obtain ⟨base,hb,bs,bf⟩ := MatrixScoreSkipFields.fields_run p weights pre suffix
  have he := TapeEmbedding.run_embed MatrixScoreSkipFields.machine (fun _ : Fin 1 => out.length)
    (fun _ : Fin 1 => out) _ _ base hb
  have hi : TapeEmbedding.config (fun _ : Fin 1 => out.length) (fun _ : Fin 1 => out)
      (MatrixScoreSkipFields.cfg 0 (pre++MatrixScoreCanonical.fields p weights++suffix) pre.length weights.length)=
      cfg skip.start (pre++MatrixScoreCanonical.fields p weights++suffix) pre.length weights.length out := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · simp only [TapeEmbedding.config,MatrixScoreSkipFields.cfg_tapes]
      funext i; fin_cases i <;> rfl
  rw [hi] at he
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1 => out.length) (fun _ : Fin 1 => out) base,he,?_,bs⟩
  change TapeEmbedding.config (fun _ : Fin 1 => out.length) (fun _ : Fin 1 => out) base.final=cfg base.final.control _ _ _ _
  rw [bf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · simp only [TapeEmbedding.config,MatrixScoreSkipFields.cfg_tapes]
    funext i; fin_cases i <;> rfl

theorem threshold_run (bits pre suffix out : List Bool) (d : ℕ) : ∃ actual,
    runFrom threshold (2*bits.length+1)
      (cfg threshold.start (pre++frame bits++suffix) pre.length d out)=some actual ∧
    actual.final=cfg actual.final.control (pre++frame bits++suffix) (pre.length+(frame bits).length) d out ∧
    actual.steps=2*bits.length+1 := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixScoreSkipField.field_run bits pre suffix
  have he := TapeEmbedding.run_embed MatrixScoreSkipField.machine (![1,out.length] : Fin 2 → ℕ)
    ![UnaryTemplate.tape d,out] _ _ base hb
  have hi : TapeEmbedding.config (![1,out.length] : Fin 2 → ℕ) ![UnaryTemplate.tape d,out]
      (MatrixScoreSkipField.cfg 0 (pre++frame bits++suffix) pre.length)=
      cfg threshold.start (pre++frame bits++suffix) pre.length d out := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at he
  refine ⟨TapeEmbedding.receipt (![1,out.length] : Fin 2 → ℕ) ![UnaryTemplate.tape d,out] base,he,?_,bs⟩
  change TapeEmbedding.config (![1,out.length] : Fin 2 → ℕ) ![UnaryTemplate.tape d,out] base.final=cfg base.final.control _ _ _ _
  rw [bf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem copy_run (bits pre suffix out : List Bool) (d : ℕ) : ∃ actual,
    runFrom copy (2*bits.length+1)
      (cfg copy.start (pre++frame bits++suffix) pre.length d out)=some actual ∧
    actual.final=cfg actual.final.control (pre++frame bits++suffix) (pre.length+(frame bits).length) d (out++frame bits) ∧
    actual.steps=2*bits.length+1 := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixScoreBankField.field_run bits pre suffix out
  let entry := cfg copy.start (pre++frame bits++suffix) pre.length d out
  have hi : RecoveryFocus.config copySlots entry.heads entry.tapes
      (MatrixScoreBankField.cfg 0 (pre++frame bits++suffix) pre.length out)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  obtain ⟨actual,ha,af,as⟩ := RecoveryFocus.run_config copySlots copy_injective MatrixScoreBankField.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,as.trans bs⟩
  rw [af,bf]
  have hp (i : Fin 3) : RecoveryFocus.pick copySlots i=(![some 0,none,some 1] : Fin 3 → Option (Fin 2)) i := by
    fin_cases i
    · exact RecoveryFocus.pick_slot copySlots copy_injective 0
    · decide
    · exact RecoveryFocus.pick_slot copySlots copy_injective 1
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hp,entry,cfg,MatrixScoreBankField.cfg]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hp,entry,cfg,MatrixScoreBankField.cfg]

end NearCubicWires.RepairOrdinary.MatrixCoefficientFields

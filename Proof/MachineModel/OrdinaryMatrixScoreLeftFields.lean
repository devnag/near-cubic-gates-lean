import Proof.MachineModel.OrdinaryMatrixScoreThresholdDriver
import Proof.MachineModel.OrdinaryMatrixScoreSkipFields

/-! The actual original-stream right-weight skip and threshold update dock
in the reusable score carrier, preserving the real assignment and constants. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreLeftFields
open LocalBitMultitape SignedSortKey MatrixScoreWeight
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos apos : ℕ) : Fin 22 → ℕ :=
  Fin.addCases (m := 20) (n := 2) (motive := fun _ => ℕ) (MatrixScoreFoldEntry.heads pos apos) (fun _ => 0)
def tapes (source assignment : List Bool) (d c cap w x y : ℕ) (work : Fin 12 → List Bool)
    (driver counter : List Bool) : Fin 22 → List Bool :=
  Fin.addCases (m := 20) (n := 2) (motive := fun _ => List Bool)
    (MatrixScoreFoldEntry.tapes source assignment d c cap w x y work) ![driver,counter]
def skipSlots : Fin 2 → Fin 22 := ![0,17]
def skipPick : Fin 22 → Option (Fin 2) :=
  ![some 0,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 1,none,none,none,none]
theorem pick_skip (i : Fin 22) : RecoveryFocus.pick skipSlots i=skipPick i := by
  fin_cases i
  all_goals first | decide | exact RecoveryFocus.pick_slot skipSlots (by decide) 0 | exact RecoveryFocus.pick_slot skipSlots (by decide) 1
noncomputable def skip := RecoveryFocus.machine skipSlots MatrixScoreSkipFields.machine

theorem skip_run (weights : List ℤ) (pre suffix assignment driver counter : List Bool)
    (p apos c cap w x y : ℕ) (work : Fin 12 → List Bool) :
    ∃ actual,runFrom skip (weights.length*(2*p+6)+3)
      (RecoveryCalls.restarted skip (heads pre.length apos)
        (tapes (pre++MatrixScoreCanonical.fields p weights++suffix) assignment weights.length c cap w x y work driver counter))=some actual ∧
      actual.final.heads=heads (pre.length+(MatrixScoreCanonical.fields p weights).length) apos ∧
      actual.final.tapes=tapes (pre++MatrixScoreCanonical.fields p weights++suffix) assignment weights.length c cap w x y work driver counter ∧
      actual.steps≤weights.length*(2*p+6)+3 := by
  let source := pre++MatrixScoreCanonical.fields p weights++suffix
  let ambient := tapes source assignment weights.length c cap w x y work driver counter
  obtain ⟨base,hb,hs,hf⟩ := MatrixScoreSkipFields.fields_run p weights pre suffix
  have hi : RecoveryFocus.config skipSlots (heads pre.length apos) ambient
      (MatrixScoreSkipFields.cfg 0 source pre.length weights.length)=
      RecoveryCalls.restarted skip (heads pre.length apos) ambient := by
    apply WilliamsSourceCrop.focus_same skipSlots (RecoveryCalls.restarted skip (heads pre.length apos) ambient)
    · intro i; fin_cases i <;> rfl
    · intro i
      rw [MatrixScoreSkipFields.cfg_tapes]
      fin_cases i <;> rfl
  obtain ⟨actual,hr,haf,has⟩ := RecoveryFocus.run_config skipSlots (by decide) MatrixScoreSkipFields.machine
    (heads pre.length apos) ambient _ _ base hb
  rw [hi] at hr
  refine ⟨actual,hr,?_,?_,has.trans_le hs⟩
  · rw [haf,hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_skip,skipPick,MatrixScoreSkipFields.cfg,ZeroPadding.config,
      RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,MatrixScoreSkipField.cfg,
      heads,MatrixScoreFoldEntry.heads]
  · rw [haf,hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_skip,skipPick,MatrixScoreSkipFields.cfg_tapes,ambient,tapes,
      Fin.addCases,MatrixScoreFoldEntry.tapes,source]

def thresholdLayout : Fin 22 ≃ Fin 22 where
  toFun := ![0,20,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,21,1,17,18,19]
  invFun := ![0,18,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,19,20,21,1,17]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
noncomputable def threshold := TapeRenaming.machine thresholdLayout
  (TapeEmbedding.machine 4 MatrixScoreThresholdDriver.machine)

theorem threshold_run (pre suffix assignment : List Bool) (apos d p c w x y P N : ℕ) (theta : ℤ)
    (scratch : Fin 10 → List Bool) (hs : ∀ i,(scratch i).length≤c)
    (habs : theta.natAbs<2^p) (hw : p≤w) (hc : 4*w+3≤c)
    (hfit : theta.natAbs+(if theta<0 then N else P)<2^w) :
    ∃ finalScratch : Fin 10 → List Bool,(∀ i,(finalScratch i).length≤c) ∧
      ∃ actual,runFrom threshold (MatrixScoreThresholdDriver.budget c p w)
        (RecoveryCalls.restarted threshold (heads pre.length apos)
          (tapes (pre++frame (MatrixScoreBatch.signMagnitude p theta)++suffix) assignment d c (c+1) w x y
            (MatrixScoreFoldEntry.accumulators c w P N scratch) [] []))=some actual ∧
        actual.final.heads=heads (pre.length+2*p+3) apos ∧
        actual.final.tapes=tapes (pre++frame (MatrixScoreBatch.signMagnitude p theta)++suffix) assignment d c (c+1) w x y
          (MatrixScoreFoldEntry.accumulators c w
            (nextPositive P theta.natAbs (decide (theta<0)) true)
            (nextNegative N theta.natAbs (decide (theta<0)) true) finalScratch) [true,true] (zeros 2) ∧
        actual.steps≤MatrixScoreThresholdDriver.budget c p w := by
  obtain ⟨finalScratch,hss,base,hb,bh,bt,bs⟩ := MatrixScoreThresholdDriver.threshold_run pre suffix p c w P N theta scratch hs habs hw hc hfit
  have he := TapeEmbedding.run_embed MatrixScoreThresholdDriver.machine ![apos,1,0,0]
    ![assignment,UnaryTemplate.tape d,frame (binary w x),frame (binary w y)] _ _ base hb
  let expanded := TapeEmbedding.receipt ![apos,1,0,0]
    ![assignment,UnaryTemplate.tape d,frame (binary w x),frame (binary w y)] base
  have hr := TapeRenaming.run_rename thresholdLayout (TapeEmbedding.machine 4 MatrixScoreThresholdDriver.machine) _ _ _ he
  have hi : TapeRenaming.config thresholdLayout (TapeEmbedding.config ![apos,1,0,0]
      ![assignment,UnaryTemplate.tape d,frame (binary w x),frame (binary w y)]
      (RecoveryCalls.restarted MatrixScoreThresholdDriver.machine (MatrixScoreThresholdDriver.heads pre.length 0)
        (MatrixScoreThresholdDriver.tapes (pre++frame (MatrixScoreBatch.signMagnitude p theta)++suffix) [] [] c w P N scratch)))=
      RecoveryCalls.restarted threshold (heads pre.length apos)
        (tapes (pre++frame (MatrixScoreBatch.signMagnitude p theta)++suffix) assignment d c (c+1) w x y
          (MatrixScoreFoldEntry.accumulators c w P N scratch) [] []) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨finalScratch,hss,TapeRenaming.receipt thresholdLayout expanded,hr,?_,?_,bs⟩
  · funext i
    fin_cases i <;> simp [TapeRenaming.receipt,TapeRenaming.config,thresholdLayout,expanded,TapeEmbedding.receipt,
      TapeEmbedding.config,Fin.addCases,bh,heads,MatrixScoreFoldEntry.heads,MatrixScoreThresholdDriver.heads,MatrixScoreWeightClear.heads]
  · funext i
    fin_cases i <;> simp [TapeRenaming.receipt,TapeRenaming.config,thresholdLayout,expanded,TapeEmbedding.receipt,
      TapeEmbedding.config,Fin.addCases,bt,tapes,MatrixScoreFoldEntry.tapes,MatrixScoreFoldEntry.accumulators,
      MatrixScoreThresholdDriver.tapes,MatrixScoreWeightClear.tapes]

end NearCubicWires.RepairOrdinary.MatrixScoreLeftFields

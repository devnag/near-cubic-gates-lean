import Proof.CaseAnalysis.RowsEstimatorLinearBudget

/-! Stop the mandatory cold prefix at its existing exact scanner boundary.
Raw d, p, G and literal byte count are available before the reset capacity
is evaluated. No second source scan or guessed count is introduced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scanned
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (C : ℕ) : Fin 6→List Bool:=![[],[],[],[],List.replicate C true,List.replicate C false]
def rewound (row : EquationRow.Input) (C : ℕ) : Fin 70→List Bool :=
  Fin.addCases (m:=64) (n:=6) (motive:=fun _=>List Bool) (Prepare.input row) (extra C)
noncomputable def output (row : EquationRow.Input) (C : ℕ) : Fin 70→List Bool :=
  Fin.addCases (m:=64) (n:=6) (motive:=fun _=>List Bool) (Prepare.output row) (extra C)
noncomputable def last:=TapeEmbedding.machine 6 Prepare.machine
noncomputable def machine:=Composition.machine Cold.first last
noncomputable def entry (row : EquationRow.Input) (C : ℕ) :=
  (⟨machine.start,Cold.heads row,Cold.input row C⟩ : Configuration 70 _)
def budget (row : EquationRow.Input) (C : ℕ):=2*C+2+1+Prepare.budget row

theorem run (row : EquationRow.Input) (C : ℕ) (hC : (Header.stream row).length≤C) : ∃ actual,
    runFrom machine (budget row C) (entry row C)=some actual ∧
      actual.final.tapes=output row C ∧ (∀ i,actual.final.heads i=0) ∧
      actual.steps≤budget row C := by
  obtain ⟨rwrun,hr,rf,_rs⟩:=CompetitorRecordRewind.rewind_run
    (Header.stream row) C (Header.stream row).length hC
  obtain ⟨before,hb,_,bs,bh,bt,keep⟩:=RecoveryFocus.dock Cold.slots (by decide)
    CompetitorRecordRewind.machine (2*C+2) (Cold.heads row) (Cold.input row C) _
    (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl) rwrun hr
  have allH : ∀ i,before.final.heads i=0 := by
    intro i
    by_cases hs : ∃ j,Cold.slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [bh j,rf]
      fin_cases j <;>rfl
    · have hi : i≠52:=fun he=>hs ⟨0,he.symm⟩
      rw [(keep i (by simpa only [not_exists] using hs)).1]
      simp only [Cold.heads,hi,ite_false]
  have allT : before.final.tapes=rewound row C := by
    funext i
    by_cases hs : ∃ j,Cold.slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [bt j,rf]
      fin_cases j <;>rfl
    · rw [(keep i (by simpa only [not_exists] using hs)).2]
      have hi : i≠69:=fun he=>hs ⟨2,he.symm⟩
      revert hi
      refine Fin.addCases (m:=64) (n:=6) (fun j _=>?_) (fun j hi=>?_) i
      · simp only [rewound,Fin.addCases_left]
        change Cold.input row C ((j.castAdd 4).castAdd 2)=Prepare.input row j
        simp only [Cold.input,Framed.input,Framed.extend,Fin.addCases_left]
      · fin_cases j
        all_goals first | rfl | exact False.elim (hi rfl)
  obtain ⟨child,ch,ct,chh,cs⟩:=Prepare.ready row
  let after:=TapeEmbedding.receipt (fun _ : Fin 6=>0) (extra C) child
  have hl:=TapeEmbedding.run_embed Prepare.machine (fun _ : Fin 6=>0) (extra C) _ _ child ch
  have hi : TapeEmbedding.config (fun _ : Fin 6=>0) (extra C)
      (initialConfiguration Prepare.machine (Prepare.input row))=
      Composition.restart before.final last.start := by
    apply configuration_ext
    · rfl
    · funext i
      rw [show (Composition.restart before.final last.start).heads i=0 from allH i]
      refine Fin.addCases (m:=64) (n:=6) (fun j=>?_) (fun j=>?_) i <;>
        simp [TapeEmbedding.config,initialConfiguration]
    · change _=before.final.tapes
      rw [allT]
      rfl
  rw [hi] at hl
  have hj:=Composition.run_join Cold.first last _ _ _ before after hb hl
  refine ⟨Composition.joinedReceipt before after,hj,?_,?_,?_⟩
  · change after.final.tapes=output row C
    funext i
    refine Fin.addCases (m:=64) (n:=6) (fun j=>?_) (fun j=>?_) i
    · simp only [Scanned.output,Fin.addCases_left]
      exact (TapeEmbedding.receipt_tapes_old _ _ child j).trans (congrFun ct j)
    · simp only [Scanned.output,Fin.addCases_right]
      exact TapeEmbedding.receipt_tapes_new _ _ child j
  · intro i
    change after.final.heads i=0
    refine Fin.addCases (m:=64) (n:=6) (fun j=>?_) (fun j=>?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ child j).trans (chh j)
    · exact TapeEmbedding.receipt_heads_new _ _ child j
  · change before.steps+1+child.steps≤_
    have hrs:=runFrom_steps_le CompetitorRecordRewind.machine _ _ _ hr
    unfold budget
    omega

theorem scalar_words (row : EquationRow.Input) (C : ℕ) :
    output row C 0=List.replicate row.d true ∧ output row C 17=List.replicate row.p true ∧
    output row C 34=List.replicate row.cuts.length true ∧
    output row C 53=List.replicate (Header.stream row).length true := by
  refine ⟨?_,?_,?_,?_⟩
  · change Prepare.output row 0=_
    exact ((install_other Prepare.scanSlots _ _ _ (by decide)).trans
      (install_slot Prepare.fieldSlots (by decide) _ _ 0)).trans (by rfl)
  · change Prepare.output row 17=_
    exact ((install_other Prepare.scanSlots _ _ 17 (by decide)).trans
      (install_other Prepare.fieldSlots _ _ 17 (by decide))).trans (by rfl)
  · change Prepare.output row 34=_
    exact (install_slot Prepare.scanSlots (by decide) _ _ 2).trans (by rfl)
  · change Prepare.output row 53=_
    exact (install_slot Prepare.scanSlots (by decide) _ _ 3).trans (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scanned

import Proof.Hierarchy.CompetitorSelectedCountPrefix

/-! Whole physical residual-offset selection followed by exact natural SUM.
The selected count is framed at scalar width w and head zero. The source
mask and original complete count table survive for enclosing scans. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev states {t s : ℕ} (_ : Machine t s) := s
noncomputable def sumProgram := RecoveryFocus.machine sumSlots CompetitorCountProducer.machine
noncomputable def machine := Composition.machine prefixMachine sumProgram
noncomputable def wholeInput (b w : ℕ) (xs : List (Bool × ℕ)) := Composition.leftConfig (states sumProgram) (input b w xs)
def budget (b w n : ℕ) := prefixBudget b n+1+CompetitorCountProducer.budget w n
def finalHeads (b n : ℕ) := Function.update (scanHeads n) 9 (b*n)

theorem native_run (b w : ℕ) (xs : List (Bool × ℕ)) (hw : b≤w)
    (hx : ∀ x∈CompetitorCountMask.selected xs,x<2^b)
    (hfit : (CompetitorCountMask.selected xs).sum<2^w) : ∃ actual,
    runFrom machine (budget b w xs.length) (wholeInput b w xs)=some actual ∧
      actual.steps≤budget b w xs.length ∧ actual.final.heads=finalHeads b xs.length ∧
      actual.final.tapes 15=frame (binary w (CompetitorCountMask.selected xs).sum) ∧
      actual.final.tapes 12=List.replicate w true ∧
      actual.final.tapes 1=CompetitorCountMask.mask xs ∧
      actual.final.tapes 8=CompetitorCountFold.raw b (CompetitorCountMask.counts xs) := by
  obtain ⟨first,hf,fs,fh,ft,f1,f8⟩ := prefix_run b w xs
  obtain ⟨child,ch,c5,_,cs,chh,_,c2⟩ := CompetitorCountProducer.template_run b w
    (CompetitorCountMask.selected xs) hw hx hfit
  simp only [CompetitorCountMask.selected_length] at ch cs chh
  let entry := initialConfiguration CompetitorCountProducer.machine
    (CompetitorCountProducer.templateInput b w (CompetitorCountMask.selected xs))
  have hi : RecoveryFocus.config sumSlots first.final.heads first.final.tapes entry=
      Composition.restart first.final sumProgram.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [fh]
      fin_cases i <;> simp [sumSlots,heads,scanHeads,CompetitorCountMask.heads,Fin.addCases,entry,initialConfiguration]
    · intro i
      exact ft i
  obtain ⟨last,hl,lf,ls⟩ := RecoveryFocus.run_config sumSlots (by decide) CompetitorCountProducer.machine
    first.final.heads first.final.tapes _ entry child ch
  rw [hi] at hl
  have hj := Composition.run_join prefixMachine sumProgram _ _ _ first last hf hl
  have pick (i : Fin 20) : RecoveryFocus.pick sumSlots i=
      (![none,none,none,some 8,none,none,none,none,none,some 0,none,some 1,some 2,some 3,
        some 4,some 5,some 6,some 7,some 9,some 10] : Fin 20 → Option (Fin 11)) i := by
    fin_cases i <;> first
      | decide
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 0
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 1
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 2
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 3
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 4
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 5
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 6
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 7
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 8
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 9
      | exact RecoveryFocus.pick_slot sumSlots (by decide) 10
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget b w xs.length
    rw [ls]
    unfold budget
    omega
  · change last.final.heads=_
    rw [lf]
    funext i
    simp only [RecoveryFocus.config,pick,fh,chh]
    fin_cases i <;> simp [heads,finalHeads,scanHeads,CompetitorCountMask.heads,CompetitorCountProducer.finalHeads,Fin.addCases]
  · change last.final.tapes 15=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using c5
  · change last.final.tapes 12=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using c2
  · change last.final.tapes 1=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using f1
  · change last.final.tapes 8=_
    rw [lf]
    simpa [RecoveryFocus.config,pick] using f8

end NearCubicWires.RepairOrdinary.CompetitorSelectedCount

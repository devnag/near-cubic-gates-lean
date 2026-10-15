import Proof.Circuits.DecompositionSourceBounds

/-! Decode an actual native count and pay the return of its source head.
The unary result stays at its reusable sentinel head one. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource.Count
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 11) := decide (i=0)
noncomputable def machine := MaskedReset.machine PCPPQueryNatural.machine selected
def budget (n : ℕ) := 2*PCPPQueryNatural.budget n+2
noncomputable def entry (source : List Bool) := Rewind.recording (PCPPQueryNatural.entry source 0) 0

theorem count_run (n : ℕ) (tail : List Bool) :
    ∃ r,runFrom machine (budget n) (entry (RepairRepresentation.natWord n++tail))=some r ∧
      r.steps ≤ budget n ∧
      r.final.tapes 0=RepairRepresentation.natWord n++tail ∧ r.final.heads 0=0 ∧
      r.final.tapes 10=UnaryTemplate.tape n ∧ r.final.heads 10=1 := by
  obtain ⟨base,hb,hbs,ht,_,hu,huh⟩ := PCPPQueryNatural.natural_run [] tail n
  simp only [List.nil_append,List.length_nil] at hb ht
  have hh : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=0 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run PCPPQueryNatural.machine _ _ base hb).1 0
    simpa [PCPPQueryNatural.entry] using h
  obtain ⟨r,hr,hf,hs,_⟩ := MaskedReset.reset_run PCPPQueryNatural.machine selected _ _ base hb hh
  have hbound : 2*base.steps+2 ≤ budget n := by unfold budget; omega
  have hm := runFrom_moreFuel machine _ (budget n-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨r,hm,by omega,?_,?_,?_,?_⟩
  · rw [hf]; simpa [SelectiveReset.finished,Rewind.config,Fin.addCases] using ht
  · rw [hf]; simp [SelectiveReset.finished,Rewind.config,selected,Fin.addCases]
  · rw [hf]; simpa [SelectiveReset.finished,Rewind.config,Fin.addCases] using hu
  · rw [hf]; simpa [SelectiveReset.finished,Rewind.config,selected,Fin.addCases] using huh

theorem focus_run {u z : ℕ} (slots : Fin 12→Fin u) (hinj : Function.Injective slots)
    (ambient : Configuration u z) (n : ℕ) (tail : List Bool)
    (ht : ∀ j,ambient.tapes (slots j)=if j=0 then RepairRepresentation.natWord n++tail else [])
    (hh : ∀ j,ambient.heads (slots j)=0) :
    ∃ r,runFrom (RecoveryFocus.machine slots machine) (budget n)
      (Composition.restart ambient (RecoveryFocus.machine slots machine).start)=some r ∧
      r.steps ≤ budget n ∧
      r.final.tapes (slots 0)=RepairRepresentation.natWord n++tail ∧ r.final.heads (slots 0)=0 ∧
      r.final.tapes (slots 10)=UnaryTemplate.tape n ∧ r.final.heads (slots 10)=1 ∧
      (∀ i,RecoveryFocus.pick slots i=none → r.final.tapes i=ambient.tapes i ∧ r.final.heads i=ambient.heads i) := by
  obtain ⟨base,hb,hs,ht0,hh0,ht10,hh10⟩ := count_run n tail
  obtain ⟨r,hr,hf,hsteps⟩ := RecoveryFocus.run_config slots hinj machine ambient.heads ambient.tapes _ _ base hb
  have he : RecoveryFocus.config slots ambient.heads ambient.tapes
      (entry (RepairRepresentation.natWord n++tail))=
      Composition.restart ambient (RecoveryFocus.machine slots machine).start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simpa [entry,Rewind.recording,Rewind.config,PCPPQueryNatural.entry,Fin.addCases] using hh i
    · intro i
      have hi := ht i
      fin_cases i <;> simpa [entry,Rewind.recording,Rewind.config,PCPPQueryNatural.entry,Fin.addCases] using hi
  rw [he] at hr
  have tape (j : Fin 12) : r.final.tapes (slots j)=base.final.tapes j := by
    simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slots hinj]
  have head (j : Fin 12) : r.final.heads (slots j)=base.final.heads j := by
    simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slots hinj]
  refine ⟨r,hr,by omega,(tape 0).trans ht0,(head 0).trans hh0,
    (tape 10).trans ht10,(head 10).trans hh10,?_⟩
  intro i hi
  simp [hf,RecoveryFocus.config,hi]

theorem budget_bound (n : ℕ) : budget n ≤ 128*(n+1)^2 := by
  have h : natBitLength n ≤ n+1 := by unfold natBitLength; have := Nat.log_le_self 2 n; omega
  dsimp [budget,PCPPQueryNatural.budget,MatrixDimensionPrepare.budget]
  nlinarith [Nat.mul_le_mul_left n h]

end NearCubicWires.RepairOrdinary.DecompositionSource.Count

import Proof.PCP.PCPPQueryInput

/-! The actual natural-field reader computes the arity and query-index
drivers from their source bytes. This focus theorem retains every inactive
cursor and tape and is used at those two concrete query-entry consumers. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryNatural
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev states := 8+(8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes))
noncomputable def machine : Machine 11 states := MatrixDimensionPrepare.machine
def budget (n : ℕ) := MatrixDimensionPrepare.budget (natBitLength n) n
noncomputable def entry (source : List Bool) (pos : ℕ) : Configuration 11 states :=
  ⟨machine.start,(fun i => if i=0 then pos else 0),(fun i => if i=0 then source else [])⟩

theorem natural_run (pre tail : List Bool) (n : ℕ) :
    ∃ r,runFrom machine (budget n)
      (entry (pre++RepairRepresentation.natWord n++tail) pre.length)=some r ∧
      r.steps≤budget n ∧ r.final.tapes 0=pre++RepairRepresentation.natWord n++tail ∧
      r.final.heads 0=pre.length+2*natBitLength n+1 ∧
      r.final.tapes 10=UnaryTemplate.tape n ∧ r.final.heads 10=1 := by
  obtain ⟨r,hr,hsource,hpos,_,_,_,_,_,_,hu,huh,hs⟩ :=
    MatrixDimensionPrepare.prepare_run pre tail (natBitLength n) n
      (Nat.lt_pow_succ_log_self (by decide) n)
  have hword : pre++List.replicate (natBitLength n) true++false::(SignedSortKey.binary (natBitLength n) n++tail)=
      pre++RepairRepresentation.natWord n++tail := by simp [WilliamsInputHeader.natWord_eq,List.append_assoc]
  rw [hword] at hr hsource
  have he : Composition.leftConfig (8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes))
      (MatrixDimensionPrepare.input (pre++RepairRepresentation.natWord n++tail) pre.length)=
      entry (pre++RepairRepresentation.natWord n++tail) pre.length := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at hr
  exact ⟨r,hr,hs,hsource,hpos,hu,huh⟩

theorem focus_run {u z : ℕ} (slots : Fin 11→Fin u) (hinj : Function.Injective slots)
    (ambient : Configuration u z) (pre tail : List Bool) (n : ℕ)
    (ht : ∀ j,ambient.tapes (slots j)=if j=0 then pre++RepairRepresentation.natWord n++tail else [])
    (hh : ∀ j,ambient.heads (slots j)=if j=0 then pre.length else 0) :
    ∃ r,runFrom (RecoveryFocus.machine slots machine) (budget n)
      (Composition.restart ambient (RecoveryFocus.machine slots machine).start)=some r ∧
      r.steps≤budget n ∧ r.final.tapes (slots 0)=pre++RepairRepresentation.natWord n++tail ∧
      r.final.heads (slots 0)=pre.length+2*natBitLength n+1 ∧
      r.final.tapes (slots 10)=UnaryTemplate.tape n ∧ r.final.heads (slots 10)=1 ∧
      (∀ i,RecoveryFocus.pick slots i=none → r.final.tapes i=ambient.tapes i ∧ r.final.heads i=ambient.heads i) := by
  obtain ⟨base,hb,hs,hsour,hpos,hu,huh⟩ := natural_run pre tail n
  obtain ⟨r,hr,hf,hsteps⟩ := RecoveryFocus.run_config slots hinj machine ambient.heads ambient.tapes _ _ base hb
  have he : RecoveryFocus.config slots ambient.heads ambient.tapes
      (entry (pre++RepairRepresentation.natWord n++tail) pre.length)=
      Composition.restart ambient (RecoveryFocus.machine slots machine).start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact hh i
    · intro i; exact ht i
  rw [he] at hr
  have htape (j : Fin 11) : r.final.tapes (slots j)=base.final.tapes j := by
    simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slots hinj]
  have hhead (j : Fin 11) : r.final.heads (slots j)=base.final.heads j := by
    simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slots hinj]
  refine ⟨r,hr,by omega,(htape 0).trans hsour,(hhead 0).trans hpos,(htape 10).trans hu,(hhead 10).trans huh,?_⟩
  intro i hi
  simp [hf,RecoveryFocus.config,hi]

end NearCubicWires.RepairOrdinary.PCPPQueryNatural

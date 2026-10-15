import Proof.Hierarchy.CompetitorThresholdTail

/-! The whole cold scalar fold inside the threshold machine's actual tape
layout. Fresh threshold work remains blank, and the global term cursor is
retained at the end of the literal scalar record stream. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorSumFold CompetitorThresholdAmbient
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def foldSlots (i : Fin 95) : Fin 110 := i.castAdd 15
def input (b : ℕ) (xs : List CompetitorValidity.Estimate) : Fin 110 → List Bool :=
  Fin.addCases (m := 95) (n := 15) (motive := fun _ => List Bool) (CompetitorSumEntry.input b xs) (fun _ => [])
noncomputable def foldProgram := RecoveryFocus.machine foldSlots CompetitorSumEntry.machine

theorem fold_injective : Function.Injective foldSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 110 => a.val) h)
theorem fold_other (j : Fin 95) (i : Fin 110) (hi : 95 ≤ i.val) : foldSlots j≠i := by
  intro h
  have hv := congrArg (fun a : Fin 110 => a.val) h
  change j.val=i.val at hv
  omega
theorem folded_valid (b : ℕ) (a : CompetitorValidity.Estimate) (xs : List CompetitorValidity.Estimate)
    (hv : CompetitorSumWidth.Trace b a xs) : (folded a xs).Valid b := by
  induction xs generalizing a with
  | nil => exact hv
  | cons c cs ih => exact ih _ hv.2.2

theorem fold_run (b : ℕ) (xs : List CompetitorValidity.Estimate) (hb : 1≤b)
    (hv : CompetitorSumWidth.Trace b CompetitorSumWidth.zero xs) :
    ∃ r,run foldProgram (CompetitorSumEntry.budget b xs.length) (input b xs)=some r ∧
      r.steps≤CompetitorSumEntry.budget b xs.length ∧
      Store b (folded CompetitorSumWidth.zero xs) (words b xs) (project r.final.tapes) ∧
      (∀ i,r.final.heads (native i)=heads (words b xs).length i) ∧
      (∀ i : Fin 110,95 ≤ i.val → r.final.heads i=0) ∧
      (∀ i : Fin 110,95 ≤ i.val → r.final.tapes i=[]) ∧
      (folded CompetitorSumWidth.zero xs).value=(xs.map CompetitorValidity.Estimate.value).sum := by
  obtain ⟨base,out,hr,hs,ht,hh,hstore,hvalue⟩ := CompetitorSumEntry.cold_sum_run b xs hb hv
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config foldSlots fold_injective CompetitorSumEntry.machine
    (fun _ => 0) (input b xs) _ _ base hr
  have hi : RecoveryFocus.config foldSlots (fun _ => 0) (input b xs)
      (initialConfiguration CompetitorSumEntry.machine (CompetitorSumEntry.input b xs))=
      initialConfiguration foldProgram (input b xs) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick foldSlots i <;>
        simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing foldSlots (input b xs) (CompetitorSumEntry.input b xs)
        (by intro i; simp [input,foldSlots])
  rw [hi] at hrun
  have hproject : project r.final.tapes=out := by
    funext i
    rw [hf]
    change install foldSlots (input b xs) base.final.tapes (foldSlots (i.castAdd 1))=out i
    exact (install_slot foldSlots fold_injective _ _ (i.castAdd 1)).trans (ht i)
  refine ⟨r,hrun,hsteps.trans_le hs,?_,?_,?_,?_,hvalue⟩
  · rw [hproject]
    exact hstore
  · intro i
    rw [hf]
    change (RecoveryFocus.config foldSlots (fun _ => 0) (input b xs) base.final).heads (foldSlots (i.castAdd 1))=_
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots fold_injective] using hh i
  · intro i hi'
    have hp : RecoveryFocus.pick foldSlots i=none := by
      cases h : RecoveryFocus.pick foldSlots i with
      | none => rfl
      | some j => exact False.elim (fold_other j i hi' (RecoveryFocus.slot_of_pick foldSlots h))
    simp only [hf,RecoveryFocus.config,hp]
  · intro i hi'
    have ht' : input b xs i=[] := by
      refine Fin.addCases (m := 95) (n := 15) ?_ ?_ i hi'
      · intro j hj
        simp only [Fin.val_castAdd] at hj
        omega
      · intro j _
        simp [input]
    rw [hf]
    change install foldSlots (input b xs) base.final.tapes i=[]
    exact (install_other foldSlots _ _ i (fun j => fold_other j i hi')).trans ht'

end NearCubicWires.RepairOrdinary.CompetitorThresholdCold

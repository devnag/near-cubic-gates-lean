import Proof.PCP.PCPPNativeAddressReusable
import Proof.PCP.ProjectionNormalizationConstants

/-! Fixed native tag/zero fields are printed by the existing literal
machine at the live native descriptor cursor. No local workspace changes. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeLiteralAppend
open LocalBitMultitape PCPPNativeAddressReusable
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1 → Fin 24 := fun _ => 20
noncomputable def machine (bits : List Bool) := RecoveryFocus.machine slots (HierarchyFixedWord.raw bits)
noncomputable def entry (bits : List Bool) (base index C : ℕ) (out : List Bool) :=
  (⟨(machine bits).start,heads out,data base index C out⟩ : Configuration 24 _)

theorem append_run (bits : List Bool) (base index C : ℕ) (out : List Bool) :
    ∃ r,runFrom (machine bits) bits.length (entry bits base index C out)=some r ∧
      r.steps=bits.length ∧ r.final.heads=heads (out++bits) ∧
      r.final.tapes=data base index C (out++bits) := by
  obtain ⟨raw,hr,rf,rs⟩ := Constants.write_run bits out
  obtain ⟨r,hrun,_,rsteps,rheads,rtapes,rkeep⟩ := RecoveryFocus.dock slots (by
    intro i j _; exact Subsingleton.elim i j) (HierarchyFixedWord.raw bits) _
    (heads out) (data base index C out) (Constants.cfg bits out 0 (by omega))
    (by intro i; fin_cases i; simp [slots,heads,Constants.cfg])
    (by intro i; fin_cases i; simp [slots,data,Constants.cfg]) raw hr
  refine ⟨r,hrun,rsteps.trans rs,?_,?_⟩
  · funext i
    by_cases hi : i=20
    · subst i
      have h := rheads 0
      rw [rf] at h
      simpa only [slots,Constants.cfg,heads,ite_true,List.length_append] using h
    · rw [(rkeep i (by intro j; simpa only [slots] using Ne.symm hi)).1]
      simp only [heads,hi,ite_false]
  · funext i
    by_cases hi : i=20
    · subst i
      have h := rtapes 0
      rw [rf] at h
      simpa [slots,Constants.cfg,data] using h
    · rw [(rkeep i (by intro j; simpa only [slots] using Ne.symm hi)).2]
      simp only [data,hi,ite_false]

end NearCubicWires.RepairOrdinary.PCPPNativeLiteralAppend

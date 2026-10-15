import Proof.CaseAnalysis.RecoveryConstantPrep

/-! The constant-value call retains both actual selected children. Its
first shared field index is a physically present retained scalar. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedConstant
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 48→ℕ:=
  Fin.addCases (m:=46) (n:=2) (motive:=fun _=>ℕ) (RecoveryBoundedSelectorPair.heads out) (fun _=>0)
def data (index base C D value limit total L : ℕ) (out source : List Bool)
    (secondIndex firstIndex : ℕ) (savedFirst savedSecond : List Bool) : Fin 48→List Bool:=
  Fin.addCases (m:=46) (n:=2) (motive:=fun _=>List Bool)
    (RecoveryBoundedSelectorPair.data index base C D value limit total L out source secondIndex savedFirst)
    ![List.replicate firstIndex true,savedSecond]
def prepareSlots : Fin 9→Fin 48:=![25,47,46,1,41,34,32,22,23]
noncomputable def prepare:=RecoveryFocus.machine prepareSlots RecoveryBoundedConstantPrep.machine

theorem prepare_heads (out : List Bool) : ∀ j,heads out (prepareSlots j)=0 := by
  intro j
  fin_cases j <;> rfl

theorem prepare_tapes (index base C D value limit total L : ℕ) (out source : List Bool)
    (secondIndex firstIndex : ℕ) (saved : List Bool) :
    ∀ j,data index base C D value limit total L out source secondIndex firstIndex saved (List.replicate C false) (prepareSlots j)=
      RecoveryBoundedSelectorHandoff.data base index firstIndex value C 0 j := by
  intro j
  fin_cases j <;> rfl

theorem prepare_install (index base C D value limit total L : ℕ) (out source : List Bool)
    (secondIndex firstIndex : ℕ) (saved : List Bool) :
    install prepareSlots (data index base C D value limit total L out source secondIndex firstIndex saved (List.replicate C false))
      (RecoveryBoundedConstantPrep.output base firstIndex C)=
      data firstIndex (base+1) C D 1 limit total L out source secondIndex firstIndex saved
        (ZeroPadding.pad C (List.replicate base true)) := by
  apply HierarchyWidth.install_eq prepareSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i
    refine Fin.addCases (m:=46) (n:=2) (fun j=>?_) (fun j=>?_) i
    · intro hi
      have h1 : j≠1 := by intro he; subst j; exact hi 3 rfl
      have h41 : j≠41 := by intro he; subst j; exact hi 4 rfl
      have h25 : j≠25 := by intro he; subst j; exact hi 0 rfl
      have h34 : j≠34 := by intro he; subst j; exact hi 5 rfl
      simp only [data,Fin.addCases_left,RecoveryBoundedSelectorPair.data,h1,h41,or_false,if_false,
        if_neg h25,if_neg h34]
    · intro hi
      fin_cases j
      · rfl
      · exact False.elim (hi 1 rfl)

theorem prepare_run (index base C D value limit total L : ℕ) (out source : List Bool)
    (secondIndex firstIndex : ℕ) (saved : List Bool)
    (ha : base+1 ≤ C) (hi : index ≤ C) (hn : firstIndex+1 ≤ C) (hv : value ≤ C) :
    ∃ r,runFrom prepare (2*C+4*base+4*firstIndex+29)
      ⟨prepare.start,heads out,data index base C D value limit total L out source secondIndex firstIndex saved (List.replicate C false)⟩=some r ∧
      r.steps=2*C+4*base+4*firstIndex+29 ∧ r.final.heads=heads out ∧
      r.final.tapes=data firstIndex (base+1) C D 1 limit total L out source secondIndex firstIndex saved
        (ZeroPadding.pad C (List.replicate base true)) := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedConstantPrep.prepare_ready base index firstIndex value C ha hi hn hv).focus_at
    prepareSlots (by decide) (heads out)
    (data index base C D value limit total L out source secondIndex firstIndex saved (List.replicate C false))
    (prepare_tapes index base C D value limit total L out source secondIndex firstIndex saved) (prepare_heads out)
  exact ⟨r,hr,rs,rh,rt.trans (prepare_install index base C D value limit total L out source secondIndex firstIndex saved)⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedConstant

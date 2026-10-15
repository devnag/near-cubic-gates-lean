import Proof.CaseAnalysis.RecoverySelectorStreamReset
import Proof.CaseAnalysis.RecoverySelectorHandoff

/-! The actual first-to-second selector handoff on the retained 46-tape
bank. The prior-wire stream is reused and the first selected output is saved. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorPair
open LocalBitMultitape RepairRepresentation RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 46→ℕ :=
  Fin.addCases (m:=44) (n:=2) (motive:=fun _=>ℕ)
    (RecoveryBoundedSelectorReuse.finalHeads out) (fun _=>0)
def fixedData (C D limit total L : ℕ) (out source : List Bool) (next : ℕ) : Fin 46→List Bool :=
  ![[],[],
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,List.replicate C false,out,List.replicate C false,
    List.replicate C true,List.replicate (C+1) false,[],[],[],[],[],
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
    [],CompareMachine.word limit,List.replicate C false,
    source,List.replicate C false,List.replicate D false,List.replicate C false,
    [],CompareMachine.word total,List.replicate L false,List.replicate next true,[]]
def data (index base C D value limit total L : ℕ) (out source : List Bool)
    (next : ℕ) (saved : List Bool) (i : Fin 46) : List Bool :=
  if i=1 ∨ i=41 then ZeroPadding.pad C (List.replicate index true)
  else if i=25 then List.replicate base true
  else if i=34 then ZeroPadding.pad C (List.replicate value true)
  else if i=45 then saved else fixedData C D limit total L out source next i

theorem data_embedding (index base C D value limit total L : ℕ) (out source : List Bool)
    (next : ℕ) (saved : List Bool) :
    Fin.addCases (m:=44) (n:=2) (motive:=fun _=>List Bool)
      (RecoveryBoundedSelectorReuse.finalData index base C D value limit total L out source)
      ![List.replicate next true,saved]=data index base C D value limit total L out source next saved := by
  funext i
  fin_cases i
  all_goals first | rfl | (change ZeroPadding.pad 0 _=_; exact ZeroPadding.pad_zero _)
def handoffSlots : Fin 9→Fin 46:=![25,45,44,1,41,34,32,22,23]
noncomputable def handoff:=RecoveryFocus.machine handoffSlots RecoveryBoundedSelectorHandoff.machine

theorem handoff_heads (out : List Bool) : ∀ j,heads out (handoffSlots j)=0 := by
  intro j
  fin_cases j <;> rfl

theorem handoff_tapes (index base C D value limit total L : ℕ) (out source : List Bool) (next : ℕ) :
    ∀ j,data index base C D value limit total L out source next (List.replicate C false) (handoffSlots j)=
      RecoveryBoundedSelectorHandoff.data base index next value C 0 j := by
  intro j
  fin_cases j <;> rfl

theorem handoff_install (index base C D value limit total L : ℕ) (out source : List Bool) (next : ℕ) :
    install handoffSlots (data index base C D value limit total L out source next (List.replicate C false))
      (RecoveryBoundedSelectorHandoff.data base index next value C 5)=
      data next (base+1) C D 0 limit total L out source next (ZeroPadding.pad C (List.replicate base true)) := by
  apply HierarchyWidth.install_eq handoffSlots (by decide)
  · intro j
    fin_cases j <;> rfl
  · intro i hi
    have h1 : i≠1 := fun h=>hi 3 h.symm
    have h41 : i≠41 := fun h=>hi 4 h.symm
    have h25 : i≠25 := fun h=>hi 0 h.symm
    have h34 : i≠34 := fun h=>hi 5 h.symm
    have h45 : i≠45 := fun h=>hi 1 h.symm
    simp only [data,or_false,if_neg h25,if_neg h34,if_neg h45,h1,h41,if_false]

theorem handoff_run (index base C D value limit total L : ℕ) (out source : List Bool) (next : ℕ)
    (ha : base+1 ≤ C) (hi : index ≤ C) (hn : next+1 ≤ C) (hv : value ≤ C) :
    ∃ r,runFrom handoff (2*C+4*base+4*next+24)
      ⟨handoff.start,heads out,data index base C D value limit total L out source next (List.replicate C false)⟩=some r ∧
      r.steps=2*C+4*base+4*next+24 ∧ r.final.heads=heads out ∧
      r.final.tapes=data next (base+1) C D 0 limit total L out source next (ZeroPadding.pad C (List.replicate base true)) := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedSelectorHandoff.handoff_ready base index next value C ha hi hn hv).focus_at
    handoffSlots (by decide) (heads out)
    (data index base C D value limit total L out source next (List.replicate C false))
    (handoff_tapes index base C D value limit total L out source next) (handoff_heads out)
  exact ⟨r,hr,rs,rh,rt.trans (handoff_install index base C D value limit total L out source next)⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorPair

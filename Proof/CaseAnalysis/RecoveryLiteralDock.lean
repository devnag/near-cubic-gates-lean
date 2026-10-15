import Proof.CaseAnalysis.RecoveryLiteralReset
import Proof.CaseAnalysis.RecoveryLiteralOriginal

/-! Execute the checked original literal in the retained71-bank. The ten
source/decoder extension tapes survive the complete graph operation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralDock
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 61) : Fin 71:=i.castAdd 10
theorem slots_injective : Function.Injective slots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 71=>k.val) h)
noncomputable def machine (second : Bool):=RecoveryFocus.machine slots (RecoveryBoundedLiteral.machine second)
def heads (second neg : Bool) (H : Fin 71→ℕ) (ref : ℕ) (out : List Bool):=
  if neg then Function.update H 20 (out++RecoveryBoundedLiteral.emitted second ref).length else H
noncomputable def output (second neg : Bool) (A : Fin 71→List Bool)
    (before : List ℕ) (ref node C : ℕ) (out : List Bool):=
  install slots A (RecoveryBoundedLiteral.output second neg (fun i=>A (slots i)) before ref node C out)

theorem local_heads (second neg : Bool) (H : Fin 71→ℕ) (ref : ℕ) (out : List Bool) (j : Fin 61) :
    heads second neg H ref out (slots j)=
      RecoveryBoundedLiteral.heads second neg (fun i=>H (slots i)) ref out j := by
  cases neg
  · rfl
  · by_cases hj : j=20
    · subst j;rfl
    · have hj' : slots j≠20:=fun he=>hj (Fin.ext (congrArg (fun k : Fin 71=>k.val) he))
      simp only [heads,RecoveryBoundedLiteral.heads,RecoveryBoundedClauseGate.heads,
        ↓reduceIte,Function.update_of_ne hj,Function.update_of_ne hj']

theorem literal_run (second neg : Bool) (H : Fin 71→ℕ) (A : Fin 71→List Bool)
    (before : List ℕ) (ref node W C L : ℕ) (out tail : List Bool)
    (hLookup : ∀ j,H (slots (RecoveryBoundedClauseSelect.lookupSlots j))=0)
    (aLookup : ∀ j,A (slots (RecoveryBoundedClauseSelect.lookupSlots j))=
      RecoveryBoundedClauseLookup.input before ref C L tail j)
    (hGate : ∀ j,H (slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j))=PCPPNativeClauseBank.heads out j)
    (aGate : ∀ j,A (slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j))=RecoveryBoundedUniversalGates.data 0 0 C out j)
    (hReplace : ∀ j,H (slots (RecoveryBoundedClauseReplace.slots second j))=0)
    (aReplace : ∀ j,A (slots (RecoveryBoundedClauseReplace.slots second j))=RecoveryBoundedClauseReplace.data node 0 C 0 j)
    (hSign : readTapeBit (A 48) (H 48)=neg)
    (hL : RecoveryBoundedClauseLookup.rawBudget before ref ≤ L)
    (href : ref ≤ W) (hC : 16384*(W+1)^2 ≤ C) (hn : node+1 ≤ C) :
    ∃ r,runFrom (machine second) (RecoveryBoundedLiteral.budget second before ref node C)
      ⟨(machine second).start,H,A⟩=some r ∧
      r.steps ≤ RecoveryBoundedLiteral.budget second before ref node C ∧
      r.final.heads=heads second neg H ref out ∧ r.final.tapes=output second neg A before ref node C out := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedLiteral.literal_run second neg (fun i=>H (slots i))
    (fun i=>A (slots i)) before ref node W C L out tail hLookup aLookup hGate aGate hReplace aReplace hSign hL href hC hn
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective (RecoveryBoundedLiteral.machine second)
    _ H A _ (by intro j;rfl) (by intro j;rfl) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      exact (local_heads second neg H ref out j).symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      have h20 : i≠20:=fun he=>hi ⟨20,he.symm⟩
      cases neg <;> simp [heads,h20]
  · have he : install slots A (RecoveryBoundedLiteral.output second neg (fun i=>A (slots i)) before ref node C out)=r.final.tapes := by
      apply HierarchyWidth.install_eq slots slots_injective
      · intro j;rw [rt j,pt]
      · intro i hi;exact (rkeep i hi).2
    exact he.symm

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralDock

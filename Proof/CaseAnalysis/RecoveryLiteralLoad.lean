import Proof.CaseAnalysis.RecoveryLiteralDriver
import Proof.PCP.PCPFieldMoves
import Proof.Amplification.RecoveryFocusDock

/-! Read one original framed literal code directly into its existing decoder.
The decoder's sign/index ports are the retained literal bank's 48/49, so no
sign or index copy is introduced. Only nine scratch tapes and the source
cursor extend the original61-bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralLoad
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readSlots : Fin 3→Fin 71:=![70,61,23]
def driverSlots : Fin 11→Fin 71:=![61,62,63,64,65,66,48,67,68,49,69]
theorem read_injective : Function.Injective readSlots:=by decide
theorem driver_injective : Function.Injective driverSlots:=by decide
noncomputable def read:=RecoveryFocus.machine readSlots PCPFieldMoves.advanceMachine
noncomputable def driver:=RecoveryFocus.machine driverSlots RepairSource.RecoverySourceLiteral.driverMachine
noncomputable def machine:=Composition.machine read driver
def heads (H : Fin 71→ℕ) (position : ℕ):=Function.update H 70 position
def loaded (A : Fin 71→List Bool) (bits : List Bool) (C : ℕ):=
  Function.update A 61 (ZeroPadding.pad C (frame bits))
def budget (index : ℕ) (negative : Bool):=
  4*(RecoveryBoundedLiteralDriver.code index negative).length+4+1+
    RepairSource.RecoverySourceLiteral.driverBudget index negative

theorem read_run (H : Fin 71→ℕ) (A : Fin 71→List Bool) (C : ℕ) (pre bits tail : List Bool)
    (hH : ∀ j,H (readSlots j)=(![pre.length,0,0] : Fin 3→ℕ) j)
    (hA : ∀ j,A (readSlots j)=(![pre++frame bits++tail,List.replicate C false,
      List.replicate (C+1) false] : Fin 3→List Bool) j)
    (hC : (frame bits).length ≤ C) :
    ∃ r,runFrom read (4*bits.length+4) ⟨read.start,H,A⟩=some r ∧
      r.steps=4*bits.length+4 ∧ r.final.heads=heads H (pre.length+2*bits.length+1) ∧
      r.final.tapes=loaded A bits C := by
  obtain ⟨p,pr,pt,ph,ps⟩:=PCPFieldMoves.advance_run pre bits tail C (C+1)
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock readSlots read_injective PCPFieldMoves.advanceMachine _ H A
    (PCPFieldMoves.entry pre bits tail C (C+1))
    (by intro j;fin_cases j <;> exact hH _)
    (by intro j;fin_cases j
        · change A 70=ZeroPadding.pad 0 (pre++frame bits++tail)
          rw [ZeroPadding.pad_zero]
          exact hA 0
        · change A 61=ZeroPadding.pad C []
          simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
          exact hA 1
        · change A 23=ZeroPadding.pad (C+1) []
          simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
          exact hA 2) p pr
  have hmax : max (C+1) (2*bits.length+1)=C+1 := by rw [frame_length] at hC;omega
  refine ⟨r,hr,rs.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,readSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j
      · rfl
      · exact (hH 1).symm
      · exact (hH 2).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h70 : i≠70:=fun h=>hi ⟨0,h.symm⟩
      simp only [heads,Function.update_of_ne h70]
  · funext i
    by_cases hi : ∃ j,readSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      fin_cases j
      · exact (hA 0).symm
      · rfl
      · change List.replicate (max (C+1) (2*bits.length+1)) false=A 23
        rw [hmax]
        exact (hA 2).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).2]
      have h61 : i≠61:=fun h=>hi ⟨1,h.symm⟩
      simp only [loaded,Function.update_of_ne h61]

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralLoad

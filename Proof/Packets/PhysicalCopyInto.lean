import Proof.Packets.PhysicalBankCopy
import Proof.Rows.PhysicalFocusBoundary

/-! Copy a whole resident R-bit word between two distinct ambient ports.
The physical R-template is retained; every cursor and every other tape stays
at its original boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace FixedLivePackets.Materializer.PhysicalCopyInto
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
noncomputable section

def slots {t : Nat} (width source target : Fin t) : Fin 3→Fin t := ![width,source,target]
def machine {t : Nat} (width source target : Fin t) :=
  RecoveryFocus.machine (slots width source target) PhysicalBankCopy.machine

theorem run {t : Nat} (R : Nat) (width source target : Fin t)
    (hwsrc : width≠source) (hwtgt : width≠target) (hst : source≠target)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (hw : H width=1) (hs : H source=0) (ht : H target=0)
    (hword : A width=UnaryTemplate.tape R) (hsl : (A source).length=R) (htl : (A target).length=R) :
    Step (machine width source target) (2*R+2) H A H (Function.update A target (A source)) := by
  have hi : Function.Injective (slots width source target) := by
    intro i j he
    fin_cases i <;>fin_cases j <;>simp_all [slots]
  have h:=PhysicalBankCopy.copy_step_boundary (A source) (A target) (htl.trans hsl.symm) [] [] [] []
  have small : Step PhysicalBankCopy.machine (2*R+2)
      ![1,0,0] ![UnaryTemplate.tape R,A source,A target]
      ![1,0,0] ![UnaryTemplate.tape R,A source,A source] := by
    simpa only [PhysicalBankCopy.cfg,hsl,List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] using h
  apply PhysicalFocusBoundary.focus small (slots width source target) hi H H A
    (Function.update A target (A source))
  · intro i;fin_cases i <;>simp [slots,hw,hs,ht]
  · intro i;fin_cases i <;>simp [slots,hword]
  · intro i;fin_cases i <;>simp [slots,hw,hs,ht]
  · intro i;fin_cases i <;>simp [slots,Function.update,hword,hwtgt,hst]
  · intro i away
    have hn : i≠target := by intro he;subst i;exact away 2 rfl
    exact ⟨rfl,by simp [Function.update,hn]⟩

end
end FixedLivePackets.Materializer.PhysicalCopyInto

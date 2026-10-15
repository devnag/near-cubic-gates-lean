import Proof.MachineModel.CountIndexClean
import Proof.PCP.PCPSerializerCapacityFocus

/-! Dock the actual count converter into the existing native bank. Shared
ports are count115, width109, fields52/107 and driver104/log105. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 18→Fin 128:=
  ![115,116,117,118,119,120,121,122,123,124,109,52,125,126,127,107,104,105]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def machine:=RecoveryFocus.machine slots CountIndexClean.machine
def changed (A : Fin 128→List Bool) (C w M : ℕ):=
  Function.update (Function.update (Function.update A 115 (List.replicate C false))
    52 (ZeroPadding.pad C (frame (binary w (M-1)))))
    107 (ZeroPadding.pad C (frame (binary w (M-1))))

theorem count_run (C w M : ℕ) (hM : 0<M) (hw : M<2^w)
    (hC : CountIndex.budget w M+1≤C) (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (slots j)=0)
    (ha : ∀ j,A (slots j)=CountIndexCopy.input C w M j) :
    ∃ r,runFrom machine (CountIndexClean.budget C w M) ⟨machine.start,H,A⟩=some r ∧
      r.final.heads=H ∧
      r.final.tapes=install slots A (CountIndexClean.output C w M) ∧
      r.steps≤CountIndexClean.budget C w M :=
  (CountIndexClean.ready C w M hM hw hC).focus_at slots slots_injective H A ha hh

end NearCubicWires.ExtIncidence.BankCount

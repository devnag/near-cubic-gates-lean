import Proof.CaseAnalysis.RowsGateNativeMeaning
import Proof.CaseAnalysis.RowsGateFieldsMeaning

/-! The cold native request aliases the five actual decoded gate fields.
Only new work tapes are blank; the original 998-tape decoder bank remains
opaque and no field stream is serialized a second time. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateCold
open LocalBitMultitape RecoveryRootRound CloseoutRowsGateSupport
open SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oldSlots (i : Fin 998) : Fin 1035 := i.castAdd 37
def sources : Fin 5 → Fin 998 := ![361,368,994,625,802]
def slots : Fin 42 → Fin 1035 :=
  Fin.addCases (motive := fun _ : Fin (5+37) => Fin 1035)
    (fun i => oldSlots (sources i)) (fun j => j.natAdd 998)
theorem old_injective : Function.Injective oldSlots := by
  intro i j h;exact Fin.ext (congrArg (fun k => k.val) h)
theorem sources_injective : Function.Injective sources := by decide
theorem slots_injective : Function.Injective slots := by
  intro i j
  refine Fin.addCases (m := 5) (n := 37) (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (m := 5) (n := 37) (fun j => ?_) (fun j => ?_) j
    · intro h
      simp only [slots,Fin.addCases_left] at h
      exact congrArg (Fin.castAdd 37) (sources_injective (old_injective h))
    · intro h
      have hv := congrArg Fin.val h
      simp only [slots,Fin.addCases_left,Fin.addCases_right,oldSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hi := (sources i).isLt
      omega
  · refine Fin.addCases (m := 5) (n := 37) (fun j => ?_) (fun j => ?_) j
    · intro h
      have hv := congrArg Fin.val h
      simp only [slots,Fin.addCases_left,Fin.addCases_right,oldSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hj := (sources j).isLt
      omega
    · intro h
      have hv := congrArg Fin.val h
      apply Fin.ext
      simp only [slots,Fin.addCases_right,Fin.val_natAdd] at hv ⊢
      omega
def input (bits : List Bool) : Fin 1035 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (998+37) => List Bool)
    (CloseoutRowsGateFields.input bits) (fun _ => [])
noncomputable def prefixMachine := RecoveryFocus.machine oldSlots CloseoutRowsGateFields.machine
noncomputable def requestMachine (compressed : Bool) :=
  RecoveryFocus.machine slots (CloseoutRowsGateNative.framedMachine compressed)
noncomputable def calls (compressed : Bool) : Fin 2 → Σ s,Machine 1035 s
  | ⟨0,_⟩ => ⟨_,prefixMachine⟩
  | ⟨1,_⟩ => ⟨_,requestMachine compressed⟩
  | ⟨j+2,hj⟩ => False.elim (by omega)
noncomputable def sizes (compressed : Bool) (j : Fin 2) := (calls compressed j).1
noncomputable def programs (compressed : Bool) (j : Fin 2) : Machine 1035 (sizes compressed j) :=
  (calls compressed j).2
def guard (bits : Fin 1035 → Bool) := bits 147 && bits 367 && bits 819 && bits 996
noncomputable def next (compressed : Bool) (j : Fin 2) (_ : Fin (sizes compressed j))
    (bits : Fin 1035 → Bool) : Option (Fin 2) :=
  if j.val=0 && guard bits then some 1 else none
noncomputable def machine (compressed : Bool) := RecoveryCalls.machine (sizes compressed) (programs compressed) 0 (next compressed)
def signSource (bits : List Bool) :=
  frame (RecoveryFixedUnpair.leftWord (CloseoutRowsGateHeader.codeWord bits 1))
def budget {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool) :=
  CloseoutRowsGateFields.budget bits+1+
    CloseoutRowsGateNative.framedBudget compressed (gateFields g.gate) (gateMembers g.support)
      (signSource bits) g.gate.threshold.natAbs g.gate.encodingBits+1

theorem native_input (fields : List (Bool×List Bool)) (membership source : List Bool) (n : ℕ) :
    CloseoutRowsGateNative.framedInput fields membership source n=
      Fin.addCases (motive := fun _ : Fin (5+37) => List Bool)
        (CloseoutRowsGateNative.fieldsInput fields membership source n) (fun _ => []) := by
  funext i
  fin_cases i <;> rfl

theorem fresh {bits : List Bool} (bank : Fin 998 → List Bool) (j : Fin 37) :
    install oldSlots (input bits) bank (j.natAdd 998)=[] := by
  rw [install_other _ _ _ _ (by
    intro i hi
    have hv := congrArg Fin.val hi
    simp only [oldSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega)]
  simp only [input,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.CloseoutRowsGateCold

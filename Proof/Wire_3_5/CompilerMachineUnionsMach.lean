import Proof.Wire_3_5.CompilerMachineUnionsWord
import Proof.Wire_3_5.CompilerMachineKit3

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The slot maps -/

def uLoad : Fin 3 → Fin 11 := ![0, 3, 10]
def uNudge : Fin 1 → Fin 11 := ![0]
def uAnd : Fin 4 → Fin 11 := ![3, 6, 4, 10]
def uEq : Fin 4 → Fin 11 := ![4, 8, 9, 10]
def uIncr : Fin 4 → Fin 11 := ![3, 7, 4, 10]
def uOr : Fin 4 → Fin 11 := ![4, 2, 5, 10]
def uEmit : Fin 3 → Fin 11 := ![5, 1, 10]
def uIncrG : Fin 4 → Fin 11 := ![2, 7, 4, 10]
def uEmitZ : Fin 3 → Fin 11 := ![4, 1, 10]
def uPut : Fin 1 → Fin 11 := ![1]

theorem uLoad_inj : Function.Injective uLoad := by decide

theorem install_uLoad (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install uLoad A v = ![v 0, A 1, A 2, v 1, A 4, A 5, A 6, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_slot uLoad uLoad_inj A v 0
  · exact install_other uLoad A v 1 (by decide)
  · exact install_other uLoad A v 2 (by decide)
  · exact install_slot uLoad uLoad_inj A v 1
  · exact install_other uLoad A v 4 (by decide)
  · exact install_other uLoad A v 5 (by decide)
  · exact install_other uLoad A v 6 (by decide)
  · exact install_other uLoad A v 7 (by decide)
  · exact install_other uLoad A v 8 (by decide)
  · exact install_other uLoad A v 9 (by decide)
  · exact install_slot uLoad uLoad_inj A v 2

theorem dockH_uLoad (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH uLoad H v = ![v 0, H 1, H 2, v 1, H 4, H 5, H 6, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_slot uLoad uLoad_inj H v 0
  · exact dockH_other uLoad H v 1 (by decide)
  · exact dockH_other uLoad H v 2 (by decide)
  · exact dockH_slot uLoad uLoad_inj H v 1
  · exact dockH_other uLoad H v 4 (by decide)
  · exact dockH_other uLoad H v 5 (by decide)
  · exact dockH_other uLoad H v 6 (by decide)
  · exact dockH_other uLoad H v 7 (by decide)
  · exact dockH_other uLoad H v 8 (by decide)
  · exact dockH_other uLoad H v 9 (by decide)
  · exact dockH_slot uLoad uLoad_inj H v 2

theorem uNudge_inj : Function.Injective uNudge := by decide

theorem install_uNudge (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install uNudge A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_slot uNudge uNudge_inj A v 0
  · exact install_other uNudge A v 1 (by decide)
  · exact install_other uNudge A v 2 (by decide)
  · exact install_other uNudge A v 3 (by decide)
  · exact install_other uNudge A v 4 (by decide)
  · exact install_other uNudge A v 5 (by decide)
  · exact install_other uNudge A v 6 (by decide)
  · exact install_other uNudge A v 7 (by decide)
  · exact install_other uNudge A v 8 (by decide)
  · exact install_other uNudge A v 9 (by decide)
  · exact install_other uNudge A v 10 (by decide)

theorem dockH_uNudge (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH uNudge H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_slot uNudge uNudge_inj H v 0
  · exact dockH_other uNudge H v 1 (by decide)
  · exact dockH_other uNudge H v 2 (by decide)
  · exact dockH_other uNudge H v 3 (by decide)
  · exact dockH_other uNudge H v 4 (by decide)
  · exact dockH_other uNudge H v 5 (by decide)
  · exact dockH_other uNudge H v 6 (by decide)
  · exact dockH_other uNudge H v 7 (by decide)
  · exact dockH_other uNudge H v 8 (by decide)
  · exact dockH_other uNudge H v 9 (by decide)
  · exact dockH_other uNudge H v 10 (by decide)

theorem uAnd_inj : Function.Injective uAnd := by decide

theorem install_uAnd (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install uAnd A v = ![A 0, A 1, A 2, v 0, v 2, A 5, v 1, A 7, A 8, A 9, v 3] := by
  funext i
  fin_cases i
  · exact install_other uAnd A v 0 (by decide)
  · exact install_other uAnd A v 1 (by decide)
  · exact install_other uAnd A v 2 (by decide)
  · exact install_slot uAnd uAnd_inj A v 0
  · exact install_slot uAnd uAnd_inj A v 2
  · exact install_other uAnd A v 5 (by decide)
  · exact install_slot uAnd uAnd_inj A v 1
  · exact install_other uAnd A v 7 (by decide)
  · exact install_other uAnd A v 8 (by decide)
  · exact install_other uAnd A v 9 (by decide)
  · exact install_slot uAnd uAnd_inj A v 3

theorem dockH_uAnd (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH uAnd H v = ![H 0, H 1, H 2, v 0, v 2, H 5, v 1, H 7, H 8, H 9, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other uAnd H v 0 (by decide)
  · exact dockH_other uAnd H v 1 (by decide)
  · exact dockH_other uAnd H v 2 (by decide)
  · exact dockH_slot uAnd uAnd_inj H v 0
  · exact dockH_slot uAnd uAnd_inj H v 2
  · exact dockH_other uAnd H v 5 (by decide)
  · exact dockH_slot uAnd uAnd_inj H v 1
  · exact dockH_other uAnd H v 7 (by decide)
  · exact dockH_other uAnd H v 8 (by decide)
  · exact dockH_other uAnd H v 9 (by decide)
  · exact dockH_slot uAnd uAnd_inj H v 3

theorem uEq_inj : Function.Injective uEq := by decide

theorem install_uEq (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install uEq A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, v 1, v 2, v 3] := by
  funext i
  fin_cases i
  · exact install_other uEq A v 0 (by decide)
  · exact install_other uEq A v 1 (by decide)
  · exact install_other uEq A v 2 (by decide)
  · exact install_other uEq A v 3 (by decide)
  · exact install_slot uEq uEq_inj A v 0
  · exact install_other uEq A v 5 (by decide)
  · exact install_other uEq A v 6 (by decide)
  · exact install_other uEq A v 7 (by decide)
  · exact install_slot uEq uEq_inj A v 1
  · exact install_slot uEq uEq_inj A v 2
  · exact install_slot uEq uEq_inj A v 3

theorem dockH_uEq (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH uEq H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, v 1, v 2, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other uEq H v 0 (by decide)
  · exact dockH_other uEq H v 1 (by decide)
  · exact dockH_other uEq H v 2 (by decide)
  · exact dockH_other uEq H v 3 (by decide)
  · exact dockH_slot uEq uEq_inj H v 0
  · exact dockH_other uEq H v 5 (by decide)
  · exact dockH_other uEq H v 6 (by decide)
  · exact dockH_other uEq H v 7 (by decide)
  · exact dockH_slot uEq uEq_inj H v 1
  · exact dockH_slot uEq uEq_inj H v 2
  · exact dockH_slot uEq uEq_inj H v 3

theorem uIncr_inj : Function.Injective uIncr := by decide

theorem install_uIncr (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install uIncr A v = ![A 0, A 1, A 2, v 0, v 2, A 5, A 6, v 1, A 8, A 9, v 3] := by
  funext i
  fin_cases i
  · exact install_other uIncr A v 0 (by decide)
  · exact install_other uIncr A v 1 (by decide)
  · exact install_other uIncr A v 2 (by decide)
  · exact install_slot uIncr uIncr_inj A v 0
  · exact install_slot uIncr uIncr_inj A v 2
  · exact install_other uIncr A v 5 (by decide)
  · exact install_other uIncr A v 6 (by decide)
  · exact install_slot uIncr uIncr_inj A v 1
  · exact install_other uIncr A v 8 (by decide)
  · exact install_other uIncr A v 9 (by decide)
  · exact install_slot uIncr uIncr_inj A v 3

theorem dockH_uIncr (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH uIncr H v = ![H 0, H 1, H 2, v 0, v 2, H 5, H 6, v 1, H 8, H 9, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other uIncr H v 0 (by decide)
  · exact dockH_other uIncr H v 1 (by decide)
  · exact dockH_other uIncr H v 2 (by decide)
  · exact dockH_slot uIncr uIncr_inj H v 0
  · exact dockH_slot uIncr uIncr_inj H v 2
  · exact dockH_other uIncr H v 5 (by decide)
  · exact dockH_other uIncr H v 6 (by decide)
  · exact dockH_slot uIncr uIncr_inj H v 1
  · exact dockH_other uIncr H v 8 (by decide)
  · exact dockH_other uIncr H v 9 (by decide)
  · exact dockH_slot uIncr uIncr_inj H v 3

theorem uOr_inj : Function.Injective uOr := by decide

theorem install_uOr (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install uOr A v = ![A 0, A 1, v 1, A 3, v 0, v 2, A 6, A 7, A 8, A 9, v 3] := by
  funext i
  fin_cases i
  · exact install_other uOr A v 0 (by decide)
  · exact install_other uOr A v 1 (by decide)
  · exact install_slot uOr uOr_inj A v 1
  · exact install_other uOr A v 3 (by decide)
  · exact install_slot uOr uOr_inj A v 0
  · exact install_slot uOr uOr_inj A v 2
  · exact install_other uOr A v 6 (by decide)
  · exact install_other uOr A v 7 (by decide)
  · exact install_other uOr A v 8 (by decide)
  · exact install_other uOr A v 9 (by decide)
  · exact install_slot uOr uOr_inj A v 3

theorem dockH_uOr (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH uOr H v = ![H 0, H 1, v 1, H 3, v 0, v 2, H 6, H 7, H 8, H 9, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other uOr H v 0 (by decide)
  · exact dockH_other uOr H v 1 (by decide)
  · exact dockH_slot uOr uOr_inj H v 1
  · exact dockH_other uOr H v 3 (by decide)
  · exact dockH_slot uOr uOr_inj H v 0
  · exact dockH_slot uOr uOr_inj H v 2
  · exact dockH_other uOr H v 6 (by decide)
  · exact dockH_other uOr H v 7 (by decide)
  · exact dockH_other uOr H v 8 (by decide)
  · exact dockH_other uOr H v 9 (by decide)
  · exact dockH_slot uOr uOr_inj H v 3

theorem uEmit_inj : Function.Injective uEmit := by decide

theorem install_uEmit (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install uEmit A v = ![A 0, v 1, A 2, A 3, A 4, v 0, A 6, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_other uEmit A v 0 (by decide)
  · exact install_slot uEmit uEmit_inj A v 1
  · exact install_other uEmit A v 2 (by decide)
  · exact install_other uEmit A v 3 (by decide)
  · exact install_other uEmit A v 4 (by decide)
  · exact install_slot uEmit uEmit_inj A v 0
  · exact install_other uEmit A v 6 (by decide)
  · exact install_other uEmit A v 7 (by decide)
  · exact install_other uEmit A v 8 (by decide)
  · exact install_other uEmit A v 9 (by decide)
  · exact install_slot uEmit uEmit_inj A v 2

theorem dockH_uEmit (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH uEmit H v = ![H 0, v 1, H 2, H 3, H 4, v 0, H 6, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other uEmit H v 0 (by decide)
  · exact dockH_slot uEmit uEmit_inj H v 1
  · exact dockH_other uEmit H v 2 (by decide)
  · exact dockH_other uEmit H v 3 (by decide)
  · exact dockH_other uEmit H v 4 (by decide)
  · exact dockH_slot uEmit uEmit_inj H v 0
  · exact dockH_other uEmit H v 6 (by decide)
  · exact dockH_other uEmit H v 7 (by decide)
  · exact dockH_other uEmit H v 8 (by decide)
  · exact dockH_other uEmit H v 9 (by decide)
  · exact dockH_slot uEmit uEmit_inj H v 2

theorem uIncrG_inj : Function.Injective uIncrG := by decide

theorem install_uIncrG (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install uIncrG A v = ![A 0, A 1, v 0, A 3, v 2, A 5, A 6, v 1, A 8, A 9, v 3] := by
  funext i
  fin_cases i
  · exact install_other uIncrG A v 0 (by decide)
  · exact install_other uIncrG A v 1 (by decide)
  · exact install_slot uIncrG uIncrG_inj A v 0
  · exact install_other uIncrG A v 3 (by decide)
  · exact install_slot uIncrG uIncrG_inj A v 2
  · exact install_other uIncrG A v 5 (by decide)
  · exact install_other uIncrG A v 6 (by decide)
  · exact install_slot uIncrG uIncrG_inj A v 1
  · exact install_other uIncrG A v 8 (by decide)
  · exact install_other uIncrG A v 9 (by decide)
  · exact install_slot uIncrG uIncrG_inj A v 3

theorem dockH_uIncrG (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH uIncrG H v = ![H 0, H 1, v 0, H 3, v 2, H 5, H 6, v 1, H 8, H 9, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other uIncrG H v 0 (by decide)
  · exact dockH_other uIncrG H v 1 (by decide)
  · exact dockH_slot uIncrG uIncrG_inj H v 0
  · exact dockH_other uIncrG H v 3 (by decide)
  · exact dockH_slot uIncrG uIncrG_inj H v 2
  · exact dockH_other uIncrG H v 5 (by decide)
  · exact dockH_other uIncrG H v 6 (by decide)
  · exact dockH_slot uIncrG uIncrG_inj H v 1
  · exact dockH_other uIncrG H v 8 (by decide)
  · exact dockH_other uIncrG H v 9 (by decide)
  · exact dockH_slot uIncrG uIncrG_inj H v 3

theorem uEmitZ_inj : Function.Injective uEmitZ := by decide

theorem install_uEmitZ (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install uEmitZ A v = ![A 0, v 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_other uEmitZ A v 0 (by decide)
  · exact install_slot uEmitZ uEmitZ_inj A v 1
  · exact install_other uEmitZ A v 2 (by decide)
  · exact install_other uEmitZ A v 3 (by decide)
  · exact install_slot uEmitZ uEmitZ_inj A v 0
  · exact install_other uEmitZ A v 5 (by decide)
  · exact install_other uEmitZ A v 6 (by decide)
  · exact install_other uEmitZ A v 7 (by decide)
  · exact install_other uEmitZ A v 8 (by decide)
  · exact install_other uEmitZ A v 9 (by decide)
  · exact install_slot uEmitZ uEmitZ_inj A v 2

theorem dockH_uEmitZ (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH uEmitZ H v = ![H 0, v 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other uEmitZ H v 0 (by decide)
  · exact dockH_slot uEmitZ uEmitZ_inj H v 1
  · exact dockH_other uEmitZ H v 2 (by decide)
  · exact dockH_other uEmitZ H v 3 (by decide)
  · exact dockH_slot uEmitZ uEmitZ_inj H v 0
  · exact dockH_other uEmitZ H v 5 (by decide)
  · exact dockH_other uEmitZ H v 6 (by decide)
  · exact dockH_other uEmitZ H v 7 (by decide)
  · exact dockH_other uEmitZ H v 8 (by decide)
  · exact dockH_other uEmitZ H v 9 (by decide)
  · exact dockH_slot uEmitZ uEmitZ_inj H v 2

theorem uPut_inj : Function.Injective uPut := by decide

theorem install_uPut (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install uPut A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_other uPut A v 0 (by decide)
  · exact install_slot uPut uPut_inj A v 0
  · exact install_other uPut A v 2 (by decide)
  · exact install_other uPut A v 3 (by decide)
  · exact install_other uPut A v 4 (by decide)
  · exact install_other uPut A v 5 (by decide)
  · exact install_other uPut A v 6 (by decide)
  · exact install_other uPut A v 7 (by decide)
  · exact install_other uPut A v 8 (by decide)
  · exact install_other uPut A v 9 (by decide)
  · exact install_other uPut A v 10 (by decide)

theorem dockH_uPut (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH uPut H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_other uPut H v 0 (by decide)
  · exact dockH_slot uPut uPut_inj H v 0
  · exact dockH_other uPut H v 2 (by decide)
  · exact dockH_other uPut H v 3 (by decide)
  · exact dockH_other uPut H v 4 (by decide)
  · exact dockH_other uPut H v 5 (by decide)
  · exact dockH_other uPut H v 6 (by decide)
  · exact dockH_other uPut H v 7 (by decide)
  · exact dockH_other uPut H v 8 (by decide)
  · exact dockH_other uPut H v 9 (by decide)
  · exact dockH_other uPut H v 10 (by decide)

/-! ## The machines -/

noncomputable def uLoadD := RecoveryFocus.machine uLoad loadM
noncomputable def uNudgeD := RecoveryFocus.machine uNudge nudgeM
noncomputable def uAndD := RecoveryFocus.machine uAnd (zipM andOut keep false)
noncomputable def uEqD := RecoveryFocus.machine uEq eqM
noncomputable def uIncrD := RecoveryFocus.machine uIncr (zipM incrOut incrNxt true)
noncomputable def uOrD := RecoveryFocus.machine uOr (zipM orOut keep false)
noncomputable def uEmitD := RecoveryFocus.machine uEmit emitM
noncomputable def uIncrGD := RecoveryFocus.machine uIncrG (zipM incrOut incrNxt true)
noncomputable def uEmitZD := RecoveryFocus.machine uEmitZ emitM
noncomputable def uPutD := RecoveryFocus.machine uPut (putM false)

/-- Extend a tested entry: increment its size, join the monomial, write it out. -/
noncomputable def uExtendM := Composition.machine (Composition.machine uIncrD uOrD) uEmitD

/-- The record body of pass 1: load, step past, test, and extend when below size `Q'`. -/
noncomputable def uBodyM :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine uLoadD uNudgeD) uAndD) uEqD)
    (branchM 9 uExtendM (idle 11))

/-- Pass 1: the stream loop, then the monomial's own entry and the terminator. -/
noncomputable def uPass1LoopM :=
  Composition.machine (Composition.machine (Composition.machine (StreamController.machine uBodyM 0) uIncrGD) uEmitZD)
    uPutD

def uSelSO : Fin 11 → Bool := ![true, true, false, false, false, false, false, false, false, false, false]

noncomputable def uPass1M := MaskedReset.machine uPass1LoopM uSelSO

def uApp : Fin 3 → Fin 12 := ![0, 1, 11]

noncomputable def uAppD := RecoveryFocus.machine uApp appendResetM

/-- **One lift step**: pass 1, then the new entries appended after the old ones. -/
noncomputable def uLiftM := Composition.machine uPass1M uAppD

/-! ## The docked steps -/

theorem zeroHeads4 : (![0, 0, 0, 0] : Fin 4 → ℕ) = fun _ => 0 := by
  funext i; fin_cases i <;> rfl

section Docked
variable (cap : ℕ) (T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 : List Bool) (p o : ℕ)

theorem uload_step (pre r post y : List Bool) (hl : y.length = r.length) (hcap : 2 * r.length + 1 ≤ cap) :
    Step uLoadD (2 * (2 * r.length + 1) + 2) ![pre.length, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![pre ++ frame r ++ post, T1, T2, frame y, T4, T5, T6, T7, T8, T9, List.replicate cap false]
      ![pre.length + 2 * r.length, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![pre ++ frame r ++ post, T1, T2, frame r, T4, T5, T6, T7, T8, T9, List.replicate cap false] := by
  have e0 := loadStep pre r post (frame y) cap hcap
  rw [overlay_exact _ _ (by simp [frame_length, hl])] at e0
  have e1 := dockRun e0 uLoad uLoad_inj ![pre.length, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![pre ++ frame r ++ post, T1, T2, frame y, T4, T5, T6, T7, T8, T9, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_uLoad, dockH_uLoad] at e1
  exact e1

theorem unudge_step :
    Step uNudgeD 1 ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, List.replicate cap false]
      ![p + 1, o, 0, 0, 0, 0, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, List.replicate cap false] := by
  have e1 := dockRun (nudge_run T0 p) uNudge uNudge_inj ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, List.replicate cap false] (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [install_uNudge, dockH_uNudge] at e1
  exact e1

/-- A masked register transducer docked on (input, input, output, log): heads stay, the output register is replaced. -/
theorem zipDock {k : ℕ} (slots : Fin 4 → Fin 11) (hi : Function.Injective slots) (out nxt : Bool → Bool → Bool → Bool)
    (init : Bool) (u v z : List Bool) (hl : u.length = v.length) (hz : z.length = u.length)
    (hcap : 2 * u.length + 1 ≤ cap) (H : Fin 11 → ℕ) (A : Fin 11 → List Bool) (hH : ∀ j, H (slots j) = 0)
    (hA : ∀ j, A (slots j) = ![frame u, frame v, frame z, List.replicate cap false] j) (_hk : k = 0) :
    Step (RecoveryFocus.machine slots (zipM out nxt init)) (2 * (2 * u.length + 1) + 2) H A H
      (install slots A ![frame u, frame v, frame (ZipMap.map out nxt u v init), List.replicate cap false]) := by
  have e0 := zipStep out nxt init u v (frame z) hl cap hcap
  rw [overlay_exact _ _ (by simp [frame_length, ZipMap.map_length out nxt u v init hl, hz]), zeroHeads4] at e0
  exact dockKeep e0 slots hi H A hH hA

theorem uand_step (r t z : List Bool) (hl : r.length = t.length) (hz : z.length = r.length) (hcap : 2 * r.length + 1 ≤ cap) :
    Step uAndD (2 * (2 * r.length + 1) + 2) ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, frame r, frame z, T5, frame t, T7, T8, T9, List.replicate cap false]
      ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, frame r, frame (ZipMap.map andOut keep r t false), T5, frame t, T7, T8, T9, List.replicate cap false] := by
  have e1 := zipDock (k := 0) cap uAnd uAnd_inj andOut keep false r t z hl hz hcap ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, frame r, frame z, T5, frame t, T7, T8, T9, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl) rfl
  rw [install_uAnd] at e1
  exact e1

theorem ueq_step (z zt : List Bool) (c : Bool) (hl : z.length = zt.length) (hcap : 2 * z.length + 1 ≤ cap) :
    Step uEqD (2 * (2 * z.length + 1) + 2) ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame z, T5, T6, T7, frame zt, [c], List.replicate cap false]
      ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, T3, frame z, T5, T6, T7, frame zt, [decide (z = zt)], List.replicate cap false] := by
  have e0 := eqStep z zt c hl cap hcap
  rw [zeroHeads4] at e0
  have e1 := dockKeep e0 uEq uEq_inj ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, frame z, T5, T6, T7, frame zt, [c], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_uEq] at e1
  exact e1

theorem uincr_step (r t z : List Bool) (hl : r.length = t.length) (hz : z.length = r.length)
    (hcap : 2 * r.length + 1 ≤ cap) :
    Step uIncrD (2 * (2 * r.length + 1) + 2) ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, frame r, frame z, T5, T6, frame t, T8, T9, List.replicate cap false]
      ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, T2, frame r, frame (ZipMap.map incrOut incrNxt r t true), T5, T6, frame t, T8, T9,
        List.replicate cap false] := by
  have e1 := zipDock (k := 0) cap uIncr uIncr_inj incrOut incrNxt true r t z hl hz hcap
    ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0] ![T0, T1, T2, frame r, frame z, T5, T6, frame t, T8, T9, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl) rfl
  rw [install_uIncr] at e1
  exact e1

theorem uor_step (z g z2 : List Bool) (hl : z.length = g.length) (hz : z2.length = z.length)
    (hcap : 2 * z.length + 1 ≤ cap) :
    Step uOrD (2 * (2 * z.length + 1) + 2) ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, frame g, T3, frame z, frame z2, T6, T7, T8, T9, List.replicate cap false]
      ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, frame g, T3, frame z, frame (ZipMap.map orOut keep z g false), T6, T7, T8, T9,
        List.replicate cap false] := by
  have e1 := zipDock (k := 0) cap uOr uOr_inj orOut keep false z g z2 hl hz hcap
    ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0] ![T0, T1, frame g, T3, frame z, frame z2, T6, T7, T8, T9, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl) rfl
  rw [install_uOr] at e1
  exact e1

theorem uincrG_step (g t z : List Bool) (hl : g.length = t.length) (hz : z.length = g.length)
    (hcap : 2 * g.length + 1 ≤ cap) :
    Step uIncrGD (2 * (2 * g.length + 1) + 2) ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, frame g, T3, frame z, T5, T6, frame t, T8, T9, List.replicate cap false]
      ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, T1, frame g, T3, frame (ZipMap.map incrOut incrNxt g t true), T5, T6, frame t, T8, T9,
        List.replicate cap false] := by
  have e1 := zipDock (k := 0) cap uIncrG uIncrG_inj incrOut incrNxt true g t z hl hz hcap
    ![p, o, 0, 0, 0, 0, 0, 0, 0, 0, 0] ![T0, T1, frame g, T3, frame z, T5, T6, frame t, T8, T9, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl) rfl
  rw [install_uIncrG] at e1
  exact e1

theorem uemit_step (w out BW : List Bool) (hcap : 2 * w.length + 1 ≤ cap) :
    Step uEmitD (2 * (2 * w.length + 1) + 2) ![p, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, overlay out BW, T2, T3, T4, frame w, T6, T7, T8, T9, List.replicate cap false]
      ![p, out.length + (2 * w.length + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, overlay (out ++ frame w) BW, T2, T3, T4, frame w, T6, T7, T8, T9, List.replicate cap false] := by
  have e1 := dockRun (emitStep w out BW cap hcap) uEmit uEmit_inj ![p, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, overlay out BW, T2, T3, T4, frame w, T6, T7, T8, T9, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_uEmit, dockH_uEmit] at e1
  exact e1

theorem uemitZ_step (w out BW : List Bool) (hcap : 2 * w.length + 1 ≤ cap) :
    Step uEmitZD (2 * (2 * w.length + 1) + 2) ![p, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, overlay out BW, T2, T3, frame w, T5, T6, T7, T8, T9, List.replicate cap false]
      ![p, out.length + (2 * w.length + 1), 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, overlay (out ++ frame w) BW, T2, T3, frame w, T5, T6, T7, T8, T9, List.replicate cap false] := by
  have e1 := dockRun (emitStep w out BW cap hcap) uEmitZ uEmitZ_inj ![p, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, overlay out BW, T2, T3, frame w, T5, T6, T7, T8, T9, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_uEmitZ, dockH_uEmitZ] at e1
  exact e1

theorem uput_step (out BW : List Bool) :
    Step uPutD 1 ![p, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, overlay out BW, T2, T3, T4, T5, T6, T7, T8, T9, List.replicate cap false]
      ![p, out.length + 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![T0, overlay (out ++ [false]) BW, T2, T3, T4, T5, T6, T7, T8, T9, List.replicate cap false] := by
  have e0 := putStep false (overlay out BW) out.length
  rw [overlay_write] at e0
  have e1 := dockRun e0 uPut uPut_inj ![p, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![T0, overlay out BW, T2, T3, T4, T5, T6, T7, T8, T9, List.replicate cap false] (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [install_uPut, dockH_uPut] at e1
  exact e1

end Docked

end NearCubicWires.WireExponent3_5.CompilerMachine.Unions

import Proof.MachineModel.NativeMaster
import Proof.MachineModel.NativeFanout

/-! The native bank shares the measured C driver and retains the original
source/output cursors outside the parallel metadata pass. -/
namespace NearCubicWires.ExtIncidence.NativeFanoutLayout
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank (i : Fin 128) : Fin 277:=if i=104 then 133 else i.natAdd 149
def sources (j : Fin 15) : Fin 277:=(NativeMaster.fields j).castAdd 128
def targets : Fin 124→Fin 128:=![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,106,107,108,109,110,111,112,114,115,116,117,118,119,120,121,122,123,124,125,126,127]
def selection : ℕ→Option (Fin 15)
  | 0 => some 0
  | 9 => some 1
  | 13 => some 2
  | 18 => some 3
  | 21 => some 4
  | 29 => some 5
  | 33 => some 6
  | 35 => some 7
  | 38 => some 8
  | 39 => some 9
  | 40 => some 9
  | 45 => some 10
  | 46 => some 11
  | 51 => some 10
  | 61 => some 11
  | 66 => some 12
  | 90 => some 13
  | 106 => some 10
  | 108 => some 11
  | 109 => some 12
  | 111 => some 13
  | 112 => some 14
  | _ => none
def choice (i : Fin 124):=selection (targets i).val
def ports : Fin (15+(124+1)+1)→Fin 277:=
  Fin.addCases (Fin.addCases sources (Fin.addCases (fun i=>bank (targets i))
    (fun _ : Fin 1=>bank 104))) (fun _ : Fin 1=>bank 105)
theorem bank_injective : Function.Injective bank:=by
  intro i j h
  have hv:=congrArg (fun x : Fin 277=>x.val) h
  simp only [bank] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv
  · subst i;subst j;rfl
  · omega
  · omega
  · exact Fin.ext (by omega)
theorem targets_injective : Function.Injective targets:=by decide
theorem ports_injective : Function.Injective ports:=by decide
noncomputable def machine:=RecoveryFocus.machine ports (NativeFanout.machine choice)

end NearCubicWires.ExtIncidence.NativeFanoutLayout

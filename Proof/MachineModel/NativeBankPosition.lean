import Proof.MachineModel.NativeBankInputs
import Proof.Circuits.DecompositionCountPosition

/-! One actual transition places the retained native loop headers while
leaving the source and growing output cursors in place. -/
namespace NearCubicWires.ExtIncidence.NativeBankPosition
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout NativeInitialize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raised (i : Fin 128) : Bool:=
  decide (i=15 ∨ i=18 ∨ i=24 ∨ i=35 ∨ i=37 ∨ i=38 ∨ i=45 ∨ i=46 ∨ i=112)
def heads (pos : ℕ) (out : List Bool) (i : Fin 128):=
  if i=31 then out.length else if i=113 then pos else if raised i then 1 else 0
def directions (i : Fin 277) : HeadMove:=if i=bank 15 ∨ i=bank 18 ∨ i=bank 24 ∨
    i=bank 35 ∨ i=bank 37 ∨ i=bank 38 ∨ i=bank 45 ∨ i=bank 46 ∨ i=bank 112 then .right else .stay
def machine:=DecompositionCountPosition.move directions

theorem heads_bank (H : Fin 277→ℕ) (pos : ℕ) (out : List Bool)
    (hh : ∀ i,H (bank i)=extraH pos out i) (i : Fin 128) :
    (directions (bank i)).apply (H (bank i))=heads pos out i:=by
  rw [hh]
  fin_cases i <;> simp [directions,bank,heads,raised,extraH,HeadMove.apply]

theorem native_heads (pos : ℕ) (out : List Bool) (i : Fin 113) :
    heads pos out (BankCount.old i)=CloseoutRowsBankFields.heads out i:=by
  fin_cases i <;> rfl

theorem count_heads (pos : ℕ) (out : List Bool) (i : Fin 18) :
    heads pos out (BankCount.slots i)=0:=by fin_cases i <;> rfl

theorem raw_heads (pos : ℕ) (out : List Bool) (i : Fin 5) :
    heads pos out (BankCount.rawOld (BankExecution.slots i))=Padded.heads pos 0 0 i:=by
  fin_cases i <;> rfl

theorem position_run (H : Fin 277→ℕ) (A : Fin 277→List Bool) (pos : ℕ) (out : List Bool)
    (hh : ∀ i,H (bank i)=extraH pos out i) : ∃ H',
    Step machine 1 H A H' A ∧ ∀ i,H' (bank i)=heads pos out i:=by
  obtain ⟨r,hr,hf,_hs⟩:=DecompositionCountPosition.move_run directions H A
  refine ⟨fun i=>(directions i).apply (H i),Step.of_run hr (congrArg Configuration.heads hf)
    (congrArg Configuration.tapes hf),heads_bank H pos out hh⟩

end NearCubicWires.ExtIncidence.NativeBankPosition

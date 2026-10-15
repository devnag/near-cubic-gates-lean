import Proof.Amplification.RecoveryRowStructureChildrenDecode
import Proof.Amplification.RecoveryRowLookupWidth

/-! The paired-row caller retains one ordinary lookup workspace beside the
existing streamed row. Its full table source and row-count driver are
physical inputs; a later table controller supplies them once and advances
the count of checked prior rows. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Children where
  base : Data
  bank : RecoveryRowLookupStream.Data
  copyCapacity : Nat
  total : Nat
  lookupCapacity : Nat

noncomputable def Children.tapes (x : Children) : Fin 68→List Bool :=
  Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool) (cfg x.base x.copyCapacity (0 : Fin 1)).tapes
    (RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity)
def Children.heads (x : Children) : Fin 68→Nat :=
  Fin.addCases (m:=52) (n:=16) (motive:=fun _=>Nat) (cfg x.base x.copyCapacity (0 : Fin 1)).heads (fun _=>0)
noncomputable def Children.cfg {s : Nat} (x : Children) (q : Fin s) : Configuration 68 s :=
  ⟨q,x.heads,x.tapes⟩

def Children.Valid (x : Children) (word bits : List Bool) : Prop :=
  x.base.Valid word ∧ RecoveryRowLookupTable.Inv x.base.state.bits.length ⟨x.bank,bits⟩ ∧
    x.bank.row.pos=0 ∧ x.bank.saved.length=x.bank.row.width ∧
    2*x.base.state.bits.length+1≤x.copyCapacity ∧
    x.total*(RecoveryRowLookupStream.budget x.bank.row.width+3)+5≤x.lookupCapacity

noncomputable def onBase {s : Nat} (p : Machine 52 s) := TapeEmbedding.machine 16 p

theorem base_run {s : Nat} (p : Machine 52 s) (x : Children) (out : Data) (fuel : Nat)
    (base : ExecutionReceipt 52 s)
    (hr : runFrom p fuel (cfg x.base x.copyCapacity p.start)=some base)
    (hf : base.final=cfg out x.copyCapacity base.final.control) :
    ∃ r,runFrom (onBase p) fuel (x.cfg p.start)=some r ∧
      r.final=({x with base:=out} : Children).cfg r.final.control ∧ r.steps=base.steps := by
  let tapes := RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity
  let result := TapeEmbedding.receipt (fun _ : Fin 16=>0) tapes base
  have h := TapeEmbedding.run_embed p (fun _ : Fin 16=>0) tapes fuel _ base hr
  refine ⟨result,h,?_,rfl⟩
  change TapeEmbedding.config (fun _ : Fin 16=>0) tapes base.final=({x with base:=out} : Children).cfg _
  rw [hf]
  rfl

def bankSlots : Fin 16→Fin 68 := fun i=>i.natAdd 52
theorem bankSlots_injective : Function.Injective bankSlots := by
  intro i j h
  exact Fin.ext (by have hv := congrArg Fin.val h; simp [bankSlots] at hv; omega)
noncomputable def bankMachine := RecoveryFocus.machine bankSlots RecoveryRowLookupTable.rewindMachine

theorem install_bank (x : Children) (bank : RecoveryRowLookupStream.Data) :
    install bankSlots x.tapes (RecoveryRowLookupTable.readyTapes bank x.total x.lookupCapacity)=
      ({x with bank:=bank} : Children).tapes := by
  funext i
  refine Fin.addCases (m:=52) (n:=16) (motive:=fun i=>
    install bankSlots x.tapes (RecoveryRowLookupTable.readyTapes bank x.total x.lookupCapacity) i=
      ({x with bank:=bank} : Children).tapes i) ?_ ?_ i
  · intro j
    have hother : ∀ k,bankSlots k≠j.castAdd 16 := by
      intro k he
      have hv := congrArg Fin.val he
      simp [bankSlots] at hv
      omega
    simpa only [Children.tapes,Fin.addCases_left] using
      install_other bankSlots x.tapes (RecoveryRowLookupTable.readyTapes bank x.total x.lookupCapacity) (j.castAdd 16) hother
  · intro j
    simpa only [Children.tapes,bankSlots,Fin.addCases_right] using
      install_slot bankSlots bankSlots_injective x.tapes (RecoveryRowLookupTable.readyTapes bank x.total x.lookupCapacity) j

end NearCubicWires.RepairOrdinary.RecoveryRowStructure

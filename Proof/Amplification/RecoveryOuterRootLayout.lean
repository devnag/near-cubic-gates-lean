import Proof.Amplification.RecoveryOuterTableWhole
import Proof.Foundations.OrdinaryTapeRenaming

namespace NearCubicWires.RepairOrdinary.RecoveryOuterRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  data : RecoveryOuterLeaf.State
  total : Nat
  key : List Bool

def State.root (x : State) : RecoveryRowRoot.State := ⟨x.data.outer,x.total,x.key⟩
def State.extra (x : State) : Fin 2→List Bool := ![CompareMachine.word x.total,frame x.key]
def State.extraHeads : Fin 2→Nat := ![1,0]
noncomputable def State.tapes (x : State) : Fin 86→List Bool :=
  Fin.addCases (m:=84) (n:=2) (motive:=fun _=>List Bool) x.data.tapes x.extra
def State.heads (x : State) : Fin 86→Nat :=
  Fin.addCases (m:=84) (n:=2) (motive:=fun _=>Nat) x.data.heads State.extraHeads
noncomputable def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 86 s := ⟨q,x.heads,x.tapes⟩
def State.Valid (x : State) (word outerBits innerBits : List Bool) :=
  x.data.Valid word outerBits innerBits ∧ x.key.length=x.data.outer.base.state.bits.length

def layout : Fin 86≃Fin 86 where
  toFun := fun i=>if h:i.val<68 then ⟨i.val,by omega⟩ else if h:i.val<70 then ⟨i.val+16,by omega⟩ else ⟨i.val-2,by omega⟩
  invFun := fun i=>if h:i.val<68 then ⟨i.val,by omega⟩ else if h:i.val<84 then ⟨i.val+2,by omega⟩ else ⟨i.val-16,by omega⟩
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

noncomputable def rootMachine := TapeRenaming.machine layout (TapeEmbedding.machine 16 RecoveryRowRoot.checkMachine)
def output (x : State) (bits : List Bool) : State :=
  {x with data:=RecoveryOuterLeaf.withOuter x.data (RecoveryRowRoot.checked x.root bits).data}

theorem layout_config {s : Nat} (x : State) (q : Fin s) :
    TapeRenaming.config layout (TapeEmbedding.config (fun _ : Fin 16=>0) x.data.extra (x.root.cfg q))=x.cfg q := by
  apply configuration_ext
  · rfl
  · funext i
    obtain ⟨j,rfl⟩ := layout.surjective i
    change (TapeEmbedding.config (fun _ : Fin 16=>0) x.data.extra (x.root.cfg q)).heads (layout.symm (layout j))=x.heads (layout j)
    rw [layout.symm_apply_apply]
    fin_cases j <;> rfl
  · funext i
    obtain ⟨j,rfl⟩ := layout.surjective i
    change (TapeEmbedding.config (fun _ : Fin 16=>0) x.data.extra (x.root.cfg q)).tapes (layout.symm (layout j))=x.tapes (layout j)
    rw [layout.symm_apply_apply]
    fin_cases j <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryOuterRoot

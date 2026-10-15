import Proof.Amplification.RecoveryRowLeafReturned

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leafGate : Machine 68 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,
    fun i=>if i=50 then some (scanned 27) else none,fun _=>.stay⟩ else none

theorem leaf_gate_step (heads : Fin 68→Nat) (tapes : Fin 68→List Bool) (old bit : Bool)
    (h50 : heads 50=0) (h27 : heads 27=0) (t50 : tapes 50=[old]) (t27 : tapes 27=[bit]) :
    step leafGate (⟨0,heads,tapes⟩ : Configuration 68 2)=
      some (⟨1,heads,Function.update tapes 50 [bit]⟩ : Configuration 68 2) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i=50
    · subst i
      simp [applyAction,Configuration.scanned,h50,h27,t50,t27,readTapeBit,writeTapeBit]
    · simp [applyAction,hi]

theorem leaf_gate_run (heads : Fin 68→Nat) (tapes : Fin 68→List Bool) (old bit : Bool)
    (h50 : heads 50=0) (h27 : heads 27=0) (t50 : tapes 50=[old]) (t27 : tapes 27=[bit]) :
    ∃ r,runFrom leafGate 1 (⟨0,heads,tapes⟩ : Configuration 68 2)=some r ∧
      r.final=⟨1,heads,Function.update tapes 50 [bit]⟩ ∧ r.steps=1 := by
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) (leaf_gate_step heads tapes old bit h50 h27 t50 t27)).run (by rfl)
  exact ⟨r,hr,hf,hs⟩

def leafFinished (x : Children) (word : List Bool)
    (out : RecoveryRowLeaf.LeafResult x.base.state x.base.extra x.base.kind word) : Children :=
  {leafReturned x word out with base:=setValid (leafReturned x word out).base true}

theorem leafFinished_tapes (x : Children) (word : List Bool)
    (out : RecoveryRowLeaf.LeafResult x.base.state x.base.extra x.base.kind word) :
    (leafFinished x word out).tapes=Function.update (leafReturned x word out).tapes 50 [true] := by
  change Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
    (cfg (setValid (leafReturned x word out).base true) x.copyCapacity (0 : Fin 1)).tapes
      (RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity)=_
  rw [cfg_valid,bank_update_left]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRowStructure

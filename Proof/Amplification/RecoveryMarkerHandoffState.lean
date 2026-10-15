import Proof.Amplification.RecoveryMarkerCorrected

namespace NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev CheckState := RecoveryNestedTable.State
abbrev MarkerState := RecoveryMarkerClause.State
noncomputable def tapes (marker : MarkerState) (x : CheckState) : Fin 212→List Bool :=
  Fin.addCases (m:=57) (n:=155) (motive:=fun _=>List Bool) marker.tapes (x.cfg (0 : Fin 1)).tapes
def heads (x : CheckState) : Fin 212→Nat :=
  Fin.addCases (m:=57) (n:=155) (motive:=fun _=>Nat) (fun _=>0)
    (Fin.addCases (m:=69) (n:=86) (motive:=fun _=>Nat)
      (Fin.addCases (m:=68) (n:=1) (motive:=fun _=>Nat) x.inner.heads (fun _=>1)) x.outer.heads)
noncomputable def cfg {s : Nat} (marker : MarkerState) (x : CheckState) (q : Fin s) : Configuration 212 s :=
  ⟨q,heads x,tapes marker x⟩
def source : Fin 3→Fin 212 := ![54,55,25]
def localTarget : Fin 3→Fin 155 := ![154,38,37]
def target (which : Fin 3) : Fin 212 := (localTarget which).natAdd 57
def slots (which : Fin 3) : Fin 4→Fin 212 := ![source which,target which,108,79]
theorem slots_injective (which : Fin 3) : Function.Injective (slots which) := by fin_cases which <;> decide
noncomputable def copyMachine (which : Fin 3) := RecoveryFocus.machine (slots which) RecoveryRootRound.copyMachine

def setExtra (x : CheckState) (e : RecoveryClauseEvaluation.Extra) : CheckState :=
  {x with inner:={x.inner with base:={x.inner.base with extra:=e}}}
def stored (x : CheckState) (which : Fin 3) (word : List Bool) : CheckState :=
  if which.val=0 then {x with outer:={x.outer with key:=word}}
  else if which.val=1 then setExtra x {x.inner.base.extra with committed:=word}
  else setExtra x {x.inner.base.extra with binaryCount:=word}

theorem extra_tapes (x : CheckState) (e : RecoveryClauseEvaluation.Extra) (j : Fin 14)
    (word : List Bool)
    (he : e.tapes x.inner.base.state=Function.update (x.inner.base.extra.tapes x.inner.base.state) j word) :
    ((setExtra x e).cfg (0 : Fin 1)).tapes=
      Function.update (x.cfg (0 : Fin 1)).tapes ((j.natAdd 28).castAdd 113) word := by
  unfold RecoveryNestedTable.State.cfg RecoveryBankPair.cfg RecoveryNestedTable.State.innerCfg
    RecoveryRowTable.tableCfg
    RecoveryRowStructure.Children.tapes RecoveryRowStructure.cfg RecoveryRowStream.Data.cfg
    RecoveryRowStream.Data.left RecoveryRowLeaf.tapes RecoveryClauseEvaluation.tapes
  dsimp only [setExtra]
  rw [he]
  simp only [bank_update_right,bank_update_left]
  rfl

theorem stored_tapes (x : CheckState) (which : Fin 3) (word : List Bool) :
    ((stored x which word).cfg (0 : Fin 1)).tapes=
      Function.update (x.cfg (0 : Fin 1)).tapes (localTarget which) (frame word) := by
  fin_cases which
  · change Fin.addCases (m:=69) (n:=86) (motive:=fun _=>List Bool)
      (x.innerCfg (0 : Fin 1)).tapes
      (Fin.addCases (m:=84) (n:=2) (motive:=fun _=>List Bool)
        x.outer.data.tapes ![RepairSource.VerifierDecoding.CompareMachine.word x.outer.total,frame word])=_
    have he : (![RepairSource.VerifierDecoding.CompareMachine.word x.outer.total,frame word] : Fin 2→List Bool)=
        Function.update x.outer.extra 1 (frame word) := by funext j; fin_cases j <;> rfl
    rw [he,bank_update_right,bank_update_right]
    rfl
  · apply extra_tapes x _ 10 (frame word)
    funext j
    fin_cases j <;> rfl
  · apply extra_tapes x _ 9 (frame word)
    funext j
    fin_cases j <;> rfl

theorem stored_heads (x : CheckState) (which : Fin 3) (word : List Bool) :
    heads (stored x which word)=heads x := by
  fin_cases which <;> rfl

theorem stored_ambient (marker : MarkerState) (x : CheckState) (which : Fin 3) (word : List Bool) :
    tapes marker (stored x which word)=Function.update (tapes marker x) (target which) (frame word) := by
  unfold tapes
  rw [stored_tapes,bank_update_right]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff

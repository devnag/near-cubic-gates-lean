import Proof.Amplification.RecoveryBoundedNativeUnaryPhase

/-! The two unary-guard passes share one physical limit sentinel and bank.
Only the value cursor is outside the reverse fold's selected tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads (pos driver : ℕ) : Fin 2→ℕ:=![pos,driver]
def extraData (value total : ℕ) : Fin 2→List Bool:=![List.replicate value true,CompareMachine.word total]
def foldSlots : Fin 35→Fin 36:=Fin.addCases (m:=34) (n:=1) (motive:=fun _=>Fin 36)
  (fun j=>j.castAdd 2) (fun _=>35)
noncomputable def first:=RecoveryBoundedNativeUnaryLoop.machine
noncomputable def second:=TapeEmbedding.machine 2 RecoveryBoundedNativeUnaryPhase.machine
noncomputable def third:=RecoveryFocus.machine foldSlots (RecoveryBoundedNativeFoldLoop.machine true)
noncomputable def machine:=Composition.machine (Composition.machine first second) third

def foldHeads (out : List Bool) (live pos driver : ℕ) : Fin 36→ℕ:=
  Fin.addCases (m:=34) (n:=2) (motive:=fun _=>ℕ) (RecoveryBoundedNativeFold.heads out live) (extraHeads pos driver)
def foldData (acc C value total : ℕ) (flag : Bool) (out stack : List Bool) : Fin 36→List Bool:=
  Fin.addCases (m:=34) (n:=2) (motive:=fun _=>List Bool)
    (RecoveryBoundedNativeFold.data 0 acc C flag out stack []) (extraData value total)

theorem prefix_heads (C value total : ℕ) (a : RecoveryBoundedNativeUnaryLoop.State) :
    (RecoveryBoundedNativeUnaryLoop.configuration 3 C value a total 1).heads=
      Fin.addCases (m:=34) (n:=2) (motive:=fun _=>ℕ)
        (RecoveryBoundedNativeUnaryPhase.heads a.out a.stack) (extraHeads a.offset 1) := by
  funext i
  fin_cases i <;> rfl

theorem prefix_tapes (C value total : ℕ) (a : RecoveryBoundedNativeUnaryLoop.State) :
    (RecoveryBoundedNativeUnaryLoop.configuration 3 C value a total 1).tapes=
      Fin.addCases (m:=34) (n:=2) (motive:=fun _=>List Bool)
        (RecoveryBoundedNativeUnaryPhase.data a.index a.position C a.flag a.out a.stack) (extraData value total) := by
  funext i
  fin_cases i <;> rfl

theorem fold_heads_input (C total pos base : ℕ) (flag : Bool) (out pre : List Bool) (refs : List ℕ)
    (j : Fin 35) :
    foldHeads out (RecoveryBoundedNativeFoldLoop.stack pre refs).length pos 1 (foldSlots j)=
      (RecoveryBoundedNativeFoldLoop.configuration 0 true C flag pre refs ⟨base,0,0,out⟩ total 1).heads j := by
  fin_cases j <;> rfl

theorem fold_tapes_input (C value total base : ℕ) (flag : Bool) (out pre : List Bool) (refs : List ℕ)
    (j : Fin 35) :
    foldData base C value total flag out (RecoveryBoundedNativeFoldLoop.stack pre refs) (foldSlots j)=
      (RecoveryBoundedNativeFoldLoop.configuration 0 true C flag pre refs ⟨base,0,0,out⟩ total 1).tapes j := by
  fin_cases j
  all_goals first | rfl |
    (change RecoveryBoundedNativeFoldLoop.stack pre refs=RecoveryBoundedNativeFoldLoop.stack pre refs++[]; simp)

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin

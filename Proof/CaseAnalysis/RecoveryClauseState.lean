import Proof.CaseAnalysis.RecoveryLiteralStream
import Proof.CaseAnalysis.RecoveryClauseMeaning

/-! The original clause's retained bank invariant. It packages actual gate,
reference and source ports, with arbitrary bounded decoder/lookup scratch;
the executed literal reset, not an entry assumption, cleans that scratch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseState
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratch : Fin 13→Fin 71:=![61,62,63,64,65,66,48,67,68,49,69,37,30]
def gate (j : Fin 29):=RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots 3 j)
def restore (j : Fin 5):=RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots false j)

structure State (H : Fin 71→ℕ) (A : Fin 71→List Bool) (node left right C L : ℕ)
    (out pre source refs : List Bool) : Prop where
  gateH : ∀ j,H (gate j)=PCPPNativeClauseBank.heads out j
  gateA : ∀ j,A (gate j)=RecoveryBoundedUniversalGates.data left right C out j
  restoreH : ∀ j,H (restore j)=0
  restoreA : ∀ j,A (restore j)=RecoveryBoundedClauseReplace.data node left C 0 j
  zeroH : H 34=0
  zeroA : A 34=List.replicate C false
  scratchH : ∀ j,H (scratch j)=0
  scratchBound : ∀ j,(A (scratch j)).length ≤ C
  refsH : H 59=0
  refsA : A 59=refs
  logH : H 43=0
  logA : A 43=List.replicate L false
  sourceH : H 70=pre.length
  sourceA : A 70=source

variable {H : Fin 71→ℕ} {A : Fin 71→List Bool} {node left right C L : ℕ}
  {out pre source refs : List Bool}

theorem reset_heads (h : State H A node left right C L out pre source refs) (second : Bool) :
    ∀ j,H (RecoveryBoundedLiteralReset.slots second j)=0 := by
  intro j
  fin_cases j
  all_goals first
    | exact h.scratchH 0 | exact h.scratchH 1 | exact h.scratchH 2
    | exact h.scratchH 3 | exact h.scratchH 4 | exact h.scratchH 5
    | exact h.scratchH 6 | exact h.scratchH 7 | exact h.scratchH 8
    | exact h.scratchH 9 | exact h.scratchH 10 | exact h.scratchH 11 | exact h.scratchH 12
    | exact h.restoreH 3 | exact h.restoreH 4
    | cases second
      · exact h.restoreH 1
      · exact h.gateH 25

theorem reset_bounds (h : State H A node left right C L out pre source refs) (second : Bool)
    (hl : left ≤ C) (hr : right ≤ C) :
    ∀ j,(A (RecoveryBoundedLiteralReset.workSlots second j)).length ≤ C := by
  intro j
  fin_cases j
  all_goals first
    | exact h.scratchBound 0 | exact h.scratchBound 1 | exact h.scratchBound 2
    | exact h.scratchBound 3 | exact h.scratchBound 4 | exact h.scratchBound 5
    | exact h.scratchBound 6 | exact h.scratchBound 7 | exact h.scratchBound 8
    | exact h.scratchBound 9 | exact h.scratchBound 10 | exact h.scratchBound 11 | exact h.scratchBound 12
    | cases second
      · have ha:=h.gateA 1
        change A 45=ZeroPadding.pad C (List.replicate left true) at ha
        change (A 45).length ≤ C
        rw [ha,ZeroPadding.pad_length,List.length_replicate,max_eq_left hl]
      · have ha:=h.gateA 25
        change A 47=ZeroPadding.pad C (List.replicate right true) at ha
        change (A 47).length ≤ C
        rw [ha,ZeroPadding.pad_length,List.length_replicate,max_eq_left hr]

theorem lookup_heads (h : State H A node left right C L out pre source refs) :
    ∀ j,H (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseSelect.lookupSlots j))=0 := by
  intro j
  fin_cases j
  · exact h.refsH
  · exact h.scratchH 11
  · exact h.scratchH 9
  · exact h.scratchH 12
  · exact h.logH

theorem literal_heads (h : State H A node left right C L out pre source refs) (second : Bool) :
    ∀ j,H (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j))=
      PCPPNativeClauseBank.heads out j := by
  intro j
  have hj:=h.gateH j
  fin_cases j <;> cases second <;> first | exact hj | exact h.gateH 25 | exact h.zeroH

theorem replace_heads (h : State H A node left right C L out pre source refs) (second : Bool) :
    ∀ j,H (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots second j))=0 := by
  intro j
  have hj:=h.restoreH j
  fin_cases j <;> cases second <;> first | exact hj | exact h.gateH 25

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseState

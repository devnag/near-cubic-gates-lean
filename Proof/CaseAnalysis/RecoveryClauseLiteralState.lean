import Proof.CaseAnalysis.RecoveryClauseLiteralHeads

/-! The whole streamed literal returns the same reusable original clause
bank. Decoder and lookup scratch remain arbitrary but fit the same C sweep. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseState
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RecoveryBoundedClauseLiteralOutput (data graph heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def literalValue (neg : Bool) (node ref : ℕ):=if neg then node else ref
def nextLeft (second neg : Bool) (left node ref : ℕ):=if second then left else literalValue neg node ref
def nextRight (second neg : Bool) (right node ref : ℕ):=if second then literalValue neg node ref else right

theorem literal_state (H : Fin 71→ℕ) (A : Fin 71→List Bool) (node left right C L : ℕ)
    (out pre source refs : List Bool) (h : State H A node left right C L out pre source refs)
    (second neg : Bool) (before : List ℕ) (ref : ℕ) (bits : List Bool) (work : Fin 11→List Bool)
    (hwork : ∀ j,(work j).length ≤ C)
    (hprefix : (RecoveryBoundedSelectorLoop.sourceWord before).length ≤ C) (hframe : 2*ref+1 ≤ C) :
    State (heads H second neg ref out pre bits) (data A second neg before ref node C out bits work)
      (node+neg.toNat) (nextLeft second neg left node ref) (nextRight second neg right node ref) C L
      (graph second neg ref out) (pre++frame bits) source refs := by
  have h20 : A 20=out := by
    have ha:=h.gateA 20
    change A 20=ZeroPadding.pad 0 out at ha
    simpa only [ZeroPadding.pad_zero] using ha
  have aGate : ∀ j,data A second neg before ref node C out bits work (gate j)=
      RecoveryBoundedUniversalGates.data (nextLeft second neg left node ref) (nextRight second neg right node ref)
        C (graph second neg ref out) j := by
    intro j
    by_cases hj1 : j=1
    · subst j
      cases second
      · exact RecoveryBoundedClauseLiteralOutput.data_reference A false neg before ref node C out bits work
      · have hh:=RecoveryBoundedClauseLiteralOutput.data_other A true neg before ref node C out bits work 45
          (by decide) (by decide) (by decide)
        exact hh.trans (h.gateA 1)
    by_cases hj25 : j=25
    · subst j
      cases second
      · have hh:=RecoveryBoundedClauseLiteralOutput.data_other A false neg before ref node C out bits work 47
          (by decide) (by decide) (by decide)
        exact hh.trans (h.gateA 25)
      · exact RecoveryBoundedClauseLiteralOutput.data_reference A true neg before ref node C out bits work
    by_cases hj20 : j=20
    · subst j
      exact (RecoveryBoundedClauseLiteralOutput.data_graph A second neg before ref node C out bits work h20).trans
        (ZeroPadding.pad_zero _).symm
    have hn : ∀ k,RecoveryBoundedLiteralReset.workSlots second k≠gate j := by
      cases second <;> fin_cases j <;> first | contradiction | decide
    have hi20 : gate j≠20 := by fin_cases j <;> first | contradiction | decide
    have hi25 : gate j≠25 := by fin_cases j <;> decide
    have hd : RecoveryBoundedUniversalGates.data left right C out j=
        RecoveryBoundedUniversalGates.data (nextLeft second neg left node ref) (nextRight second neg right node ref)
          C (graph second neg ref out) j := by
      fin_cases j <;> first | rfl | contradiction
    exact (RecoveryBoundedClauseLiteralOutput.data_other A second neg before ref node C out bits work (gate j) hn hi20 hi25).trans
      ((h.gateA j).trans hd)
  refine ⟨?_,aGate,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    by_cases hj : j=20
    · subst j
      exact RecoveryBoundedClauseLiteralOutput.head_graph H second neg ref out pre bits (h.gateH 20)
    have hh:=RecoveryBoundedClauseLiteralOutput.head_other H second neg ref out pre bits (gate j)
      (by fin_cases j <;> first | contradiction | decide) (by fin_cases j <;> decide)
    rw [hh]
    have he : PCPPNativeClauseBank.heads out j=PCPPNativeClauseBank.heads (graph second neg ref out) j := by
      simp only [PCPPNativeClauseBank.heads,if_neg hj]
    exact (h.gateH j).trans he
  · intro j
    rw [RecoveryBoundedClauseLiteralOutput.head_other _ _ _ _ _ _ _ _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)]
    exact h.restoreH j
  · intro j
    fin_cases j
    · exact RecoveryBoundedClauseLiteralOutput.data_count A second neg before ref node C out bits work (h.restoreA 0)
    · exact aGate 1
    · rw [RecoveryBoundedClauseLiteralOutput.data_other _ _ _ _ _ _ _ _ _ _ _ (by cases second <;> decide) (by decide) (by decide)]
      exact h.restoreA 2
    · rw [RecoveryBoundedClauseLiteralOutput.data_other _ _ _ _ _ _ _ _ _ _ _ (by cases second <;> decide) (by decide) (by decide)]
      exact h.restoreA 3
    · rw [RecoveryBoundedClauseLiteralOutput.data_other _ _ _ _ _ _ _ _ _ _ _ (by cases second <;> decide) (by decide) (by decide)]
      exact h.restoreA 4
  · rw [RecoveryBoundedClauseLiteralOutput.head_other _ _ _ _ _ _ _ _ (by decide) (by decide)]
    exact h.zeroH
  · rw [RecoveryBoundedClauseLiteralOutput.data_other _ _ _ _ _ _ _ _ _ _ _ (by cases second <;> decide) (by decide) (by decide)]
    exact h.zeroA
  · intro j
    rw [RecoveryBoundedClauseLiteralOutput.head_other _ _ _ _ _ _ _ _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)]
    exact h.scratchH j
  · have hb (j : Fin 11) : (data A second neg before ref node C out bits work (RecoveryBoundedLiteralLoad.driverSlots j)).length ≤ C := by
      rw [RecoveryBoundedClauseLiteralOutput.data_driver]
      exact hwork j
    intro j
    fin_cases j
    all_goals first
      | exact hb 0 | exact hb 1 | exact hb 2 | exact hb 3 | exact hb 4 | exact hb 5
      | exact hb 6 | exact hb 7 | exact hb 8 | exact hb 9 | exact hb 10
      | change (data A second neg before ref node C out bits work 37).length ≤ C
        rw [data,RecoveryBoundedLiteralDock.output_prefix,ZeroPadding.pad_length,max_eq_left hprefix]
      | change (data A second neg before ref node C out bits work 30).length ≤ C
        rw [data,RecoveryBoundedLiteralDock.output_selected_frame,ZeroPadding.pad_length,frame_length,List.length_replicate,max_eq_left hframe]
  · rw [RecoveryBoundedClauseLiteralOutput.head_other _ _ _ _ _ _ _ _ (by decide) (by decide)]
    exact h.refsH
  · rw [RecoveryBoundedClauseLiteralOutput.data_other _ _ _ _ _ _ _ _ _ _ _ (by cases second <;> decide) (by decide) (by decide)]
    exact h.refsA
  · rw [RecoveryBoundedClauseLiteralOutput.head_other _ _ _ _ _ _ _ _ (by decide) (by decide)]
    exact h.logH
  · rw [RecoveryBoundedClauseLiteralOutput.data_other _ _ _ _ _ _ _ _ _ _ _ (by cases second <;> decide) (by decide) (by decide)]
    exact h.logA
  · exact RecoveryBoundedClauseLiteralOutput.head_source H second neg ref out pre bits
  · rw [RecoveryBoundedClauseLiteralOutput.data_other _ _ _ _ _ _ _ _ _ _ _ (by cases second <;> decide) (by decide) (by decide)]
    exact h.sourceA

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseState

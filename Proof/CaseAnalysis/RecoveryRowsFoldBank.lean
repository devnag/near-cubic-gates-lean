import Proof.CaseAnalysis.RecoveryRowsScan
import Proof.CaseAnalysis.RecoveryGrammarFold

/-! The original reverse fold docks onto the already retained row bank.
Its local reference scratch uses blank73; the same full row-count driver
is on115. No extra initialized fold bank or reference scan is introduced. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowsFold
open LocalBitMultitape SourceInterfaces RepairSource.VerifierDecoding
open RecoveryBoundedRows RecoveryBoundedClauseList
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 35) : Fin 116:=if j=1 then 73 else if j=31 then 74 else if j=34 then 115 else j.castAdd 81
theorem slots_injective : Function.Injective slots:=by decide
def caps (B : ℕ) (j : Fin 35):=if j=20 ∨ j=25 ∨ j=31 ∨ j=34 then 0 else B
def ambient (node C D F L B n count Q clauses : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (P : Fin 37→List Bool):=
  scanData (RecoveryBoundedRows.data (rowData node C D F L B out n count Q clauses [] source
    (pre++stackWord refs) packet) P) refs.length
def ambientHeads (out pre : List Bool) (refs : List ℕ):=
  scanHeads (RecoveryBoundedRows.heads (RecoveryBoundedRowAfter.heads out (pre++stackWord refs)))

theorem input_heads (out pre : List Bool) (refs : List ℕ) :
    ∀ j,ambientHeads out pre refs (slots j)=RecoveryBoundedGrammarFold.heads out pre refs j := by
  intro j;fin_cases j <;> rfl

theorem fold_blank (base C B : ℕ) (out pre : List Bool) (refs : List ℕ) (hC : C+1≤B)
    (j : Fin 35) (h20 : j≠20) (h22 : j≠22) (h25 : j≠25) (h31 : j≠31) (h34 : j≠34) :
    ZeroPadding.pad (caps B j) (RecoveryBoundedGrammarFold.data base C out pre refs j)=List.replicate B false := by
  fin_cases j
  all_goals first
    | exact False.elim (h20 rfl)
    | exact False.elim (h22 rfl)
    | exact False.elim (h25 rfl)
    | exact False.elim (h31 rfl)
    | exact False.elim (h34 rfl)
    | exact RecoveryBoundedSelectorLoop.pad_erased B C (by omega)
    | exact RecoveryBoundedSelectorLoop.pad_erased B (C+1) hC
    | exact RecoveryBoundedSelectorLoop.pad_erased B 0 (Nat.zero_le B)
    | exact RecoveryBoundedSelectorLoop.pad_erased B 1 (by omega)
theorem ambient_blank (node C D F L B n count Q clauses : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (P : Fin 37→List Bool) (hC : C+1≤B) (hD : D≤B) (hL : L≤B)
    (j : Fin 35) (h20 : j≠20) (h22 : j≠22) (h25 : j≠25) (h31 : j≠31) (h34 : j≠34) :
    ambient node C D F L B n count Q clauses out source pre packet refs P (slots j)=List.replicate B false := by
  fin_cases j
  all_goals first
    | exact False.elim (h20 rfl)
    | exact False.elim (h22 rfl)
    | exact False.elim (h25 rfl)
    | exact False.elim (h31 rfl)
    | exact False.elim (h34 rfl)
    | rfl
    | exact RecoveryBoundedRowPrototype.blank_original node C D F L n count Q clauses B out source hC hD hL
        _ (by decide) (by decide) (by decide) (by decide)

theorem input_data (node C D F L B n count Q clauses : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (P : Fin 37→List Bool) (hC : C+1≤B) (hD : D≤B) (hL : L≤B) :
    ∀ j,ambient node C D F L B n count Q clauses out source pre packet refs P (slots j)=
      ZeroPadding.pad (caps B j) (RecoveryBoundedGrammarFold.data node C out pre refs j) := by
  have state:=RecoveryBoundedRow.clause_state node C D F L out [] n count [] [] Q source [] clauses
  obtain ⟨_,a20,a25,_,_⟩:=RecoveryBoundedRowReusable.state_fields _ _ node 0 0 C L out [] source [] state
  intro j
  by_cases h20 : j=20
  · subst j
    change ZeroPadding.pad 0 (RecoveryBoundedRow.data node C D F L out n count [] [] Q source [] clauses 20)=ZeroPadding.pad 0 out
    rw [a20]
  by_cases h25 : j=25
  · subst j
    change ZeroPadding.pad 0 (RecoveryBoundedRow.data node C D F L out n count [] [] Q source [] clauses 25)=
      ZeroPadding.pad 0 (List.replicate node true)
    rw [a25]
  by_cases h22 : j=22
  · subst j
    change ZeroPadding.pad B (RecoveryBoundedRow.data node C D F L out n count [] [] Q source [] clauses 22)=
      ZeroPadding.pad B (List.replicate C true)
    have ha:=state.gateA 22
    change RecoveryBoundedRow.data node C D F L out n count [] [] Q source [] clauses 22=
      ZeroPadding.pad 0 (List.replicate C true) at ha
    rw [ZeroPadding.pad_zero] at ha
    rw [ha]
  by_cases h31 : j=31
  · subst j
    change pre++stackWord refs=ZeroPadding.pad 0 (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)
    rw [ZeroPadding.pad_zero]
    rfl
  by_cases h34 : j=34
  · subst j
    change CompareMachine.word refs.length=ZeroPadding.pad 0 (CompareMachine.word refs.length)
    exact (ZeroPadding.pad_zero _).symm
  rw [ambient_blank node C D F L B n count Q clauses out source pre packet refs P hC hD hL j h20 h22 h25 h31 h34,
    fold_blank node C B out pre refs hC j h20 h22 h25 h31 h34]

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowsFold

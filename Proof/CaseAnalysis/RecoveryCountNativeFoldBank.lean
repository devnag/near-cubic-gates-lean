import Proof.CaseAnalysis.RecoveryCountScan

/-! The original final OR uses the saved count references and the same
full-bound driver on153. Its stack keeps the already paid P backing; the
separate randomness driver remains at its reusable head2 outside the focus. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountNativeFold
open LocalBitMultitape SourceInterfaces RepairSource.VerifierDecoding
open RecoveryBoundedClauseList (stackWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 35) : Fin 153:=if j=34 then 152 else (RecoveryBoundedRowsFold.slots j).castAdd 37
theorem slots_injective : Function.Injective slots:=by decide
def caps (B P : ℕ) (j : Fin 35):=if j=31 then P else RecoveryBoundedRowsFold.caps B j

def heads (out pre : List Bool) (refs : List ℕ):=
  RecoveryBoundedCountUniform.scanHeads (RecoveryBoundedCountBank.heads out (pre++stackWord refs) 1 1) 1
def bank (node C D F L B P n count Q clauses total : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool) (bd cd : List Bool):=
  RecoveryBoundedCountUniform.scanData
    (RecoveryBoundedCountBank.data B P
      (RecoveryBoundedGrammarBank.ready (RecoveryBoundedRowPrototype.fields C D F L n count Q clauses)
        node B out (pre++stackWord refs) packet source) proj total cold bd cd) refs.length

theorem bank_left (node C D F L B P n count Q clauses total : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool) (bd cd : List Bool) (i : Fin 116) :
    bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd (i.castAdd 37)=
    RecoveryBoundedFixedRestart.data P
      (RecoveryBoundedGrammarBank.ready (RecoveryBoundedRowPrototype.fields C D F L n count Q clauses)
        node B out (pre++stackWord refs) packet source) proj total i := by
  rw [show i.castAdd 37=(i.castAdd 36).castAdd 1 by apply Fin.ext;rfl]
  simp only [bank,RecoveryBoundedCountUniform.scanData,RecoveryBoundedCountBank.data,Fin.addCases_left]

theorem row_projection (node C D F L B P n count Q clauses total : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (proj : Fin 37→List Bool) (j : Fin 35) (h31 : j≠31) (h34 : j≠34) :
    RecoveryBoundedFixedRestart.data P
      (RecoveryBoundedRows.rowData node C D F L B out n count Q clauses [] source (pre++stackWord refs) packet)
      proj total (RecoveryBoundedRowsFold.slots j)=
    RecoveryBoundedRowsFold.ambient node C D F L B n count Q clauses out source pre packet refs proj
      (RecoveryBoundedRowsFold.slots j) := by
  fin_cases j
  all_goals first
    | exact False.elim (h31 rfl)
    | exact False.elim (h34 rfl)
    | exact ZeroPadding.pad_zero _

theorem input_heads (out pre : List Bool) (refs : List ℕ) :
    ∀ j,heads out pre refs (slots j)=RecoveryBoundedGrammarFold.heads out pre refs j := by
  intro j
  fin_cases j <;> rfl

theorem input_data (node C D F L B P n count Q clauses total : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool) (bd cd : List Bool)
    (hC : C+1≤B) (hD : D≤B) (hL : L≤B) :
    ∀ j,bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd (slots j)=
      ZeroPadding.pad (caps B P j) (RecoveryBoundedGrammarFold.data node C out pre refs j) := by
  intro j
  by_cases h34 : j=34
  · subst j
    change CompareMachine.word refs.length=ZeroPadding.pad 0 (CompareMachine.word refs.length)
    exact (ZeroPadding.pad_zero _).symm
  rw [slots,if_neg h34,bank_left]
  by_cases h31 : j=31
  · subst j
    change ZeroPadding.pad P (RecoveryBoundedGrammarBank.ready
      (RecoveryBoundedRowPrototype.fields C D F L n count Q clauses) node B out
      (pre++stackWord refs) packet source 74)=
      ZeroPadding.pad P (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)
    rw [RecoveryBoundedGrammarBank.ready74]
    rfl
  rw [RecoveryBoundedFixedFinish.ready_original node C D F L n count Q clauses B out source
    (pre++stackWord refs) packet hC hD hL,row_projection _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j h31 h34,
    caps,if_neg h31]
  exact RecoveryBoundedRowsFold.input_data node C D F L B n count Q clauses out source pre packet refs proj hC hD hL j

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountNativeFold

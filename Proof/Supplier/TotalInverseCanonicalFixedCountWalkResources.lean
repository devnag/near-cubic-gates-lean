import Proof.Circuits.TotalInverseCanonicalCompilerForwardResources

/-! # Exact resource split of the canonical fixed-count walk

Each fixed-count call is a controller around exactly two recursive callees:
the fixed-count grammar compiler and the guarded verifier-row scheduler.  This
module separates those two call trajectories from the controller's own width
and fuel, without changing either executable runner interface.
-/

namespace NearCubicWires.TotalInverseCanonicalFixedCountWalkResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.TotalInverseCanonicalCompilerForwardResources
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalSelectiveFixedCountProgram
open NearCubicWires.TotalSelectiveVerifierRowsProgram
open NearCubicWires.ValidatorPolynomialDomination

open private canonicalOutputs canonicalWidth canonicalCount canonicalBound from
  Proof.Circuits.TotalInverseCanonicalCompilerResources

open private selectiveFixedCountGrammarWire selectiveFixedCountRowsWire from
  Proof.MachineModel.TotalSelectiveFixedCountProgram

/-! ## 1. One fixed-count level without its two recursive callees -/

/-- The seven non-callee width heads of one fixed-count controller call. -/
def selectiveFixedCountLocalLevelBits (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) : ℕ :=
  max
    (natBitLength
      (selectiveFixedCountInput (selectiveStateCode state)
        (encodeTaggedList outputs) (structuralInputArity width bound)
        (structuralRowWidth width bound) (width + bound + 1) width count bound
        candidate.val)) <|
    max
      (natBitLength
        (selectiveFixedCountGrammarInput (selectiveStateCode state)
          (structuralInputArity width bound) (structuralRowWidth width bound)
          (width + bound + 1) width bound candidate.val)) <|
      max
        (natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveFixedCountGrammarWire width bound state candidate)))) <|
        max
          (natBitLength
            (selectiveVerifierRowsInput
              (selectiveStateCode
                (selectiveFixedCountGrammarWire width bound state
                  candidate).state)
              (encodeTaggedList outputs) (structuralInputArity width bound)
              (structuralRowWidth width bound) (width + bound + 1) width count
              (candidate.val + 1))) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveFixedCountRowsWire outputs width count bound state
                    candidate)))) <|
            max
              (natBitLength
                (selectiveEmitInput
                  ((selectiveFixedCountRowsWire outputs width count bound state
                      candidate).state.target -
                    (selectiveFixedCountRowsWire outputs width count bound state
                      candidate).state.next)
                  (selectiveFixedCountRowsWire outputs width count bound state
                    candidate).state.next
                  (selectiveSelectedCode
                    (selectiveFixedCountRowsWire outputs width count bound state
                      candidate).state.selected)
                  (rawCircuitNodeCode (n := descriptionWidth width bound)
                    (.and
                      (selectiveFixedCountGrammarWire width bound state
                        candidate).output
                      (selectiveFixedCountRowsWire outputs width count bound
                        state candidate).output)))) <|
              natBitLength
                (Nat.pair 0
                  (selectiveWireCode
                    (selectiveCompileTableFixedCount outputs width count bound
                      state candidate)))

/-- The exact non-callee fuel of one fixed-count controller call. -/
def selectiveFixedCountLocalLevelFuel (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) : ℕ :=
  69 +
    selectiveEmitFuel
      ((selectiveFixedCountRowsWire outputs width count bound state
          candidate).state.target -
        (selectiveFixedCountRowsWire outputs width count bound state
          candidate).state.next)
      (selectiveSelectedCode
        (selectiveFixedCountRowsWire outputs width count bound state
          candidate).state.selected)

/-! ## 2. The three exact trajectories -/

/-- Maximum grammar-callee width along the fixed-count candidate trajectory. -/
def selectiveFixedCountGrammarWalkBits (outputs : List ℕ)
    (width count bound : ℕ)
    (grammarRunner : SelectiveFixedCountGrammarRunner width bound) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → ℕ
  | _, [] => 0
  | state, candidate :: rest =>
      max (grammarRunner.bits state candidate)
        (selectiveFixedCountGrammarWalkBits outputs width count bound
          grammarRunner
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest)

/-- Maximum verifier-row-callee width on that trajectory. -/
def selectiveFixedCountRowsWalkBits (outputs : List ℕ)
    (width count bound : ℕ)
    (rowsRunner :
      SelectiveVerifierRowsProgramRunner totalSelectiveVerifierRowsProgram
        outputs width count bound) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → ℕ
  | _, [] => 0
  | state, candidate :: rest =>
      max
        (rowsRunner.bits
          (selectiveFixedCountGrammarWire width bound state candidate).state
          (candidate.val + 1))
        (selectiveFixedCountRowsWalkBits outputs width count bound rowsRunner
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest)

/-- Maximum local controller width on that trajectory. -/
def selectiveFixedCountLocalWalkBits (outputs : List ℕ)
    (width count bound : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → ℕ
  | _, [] => 0
  | state, candidate :: rest =>
      max (selectiveFixedCountLocalLevelBits outputs width count bound state
          candidate)
        (selectiveFixedCountLocalWalkBits outputs width count bound
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest)

/-- Sum of grammar-callee fuels along the candidate trajectory. -/
def selectiveFixedCountGrammarWalkFuel (outputs : List ℕ)
    (width count bound : ℕ)
    (grammarRunner : SelectiveFixedCountGrammarRunner width bound) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → ℕ
  | _, [] => 0
  | state, candidate :: rest =>
      grammarRunner.fuel state candidate +
        selectiveFixedCountGrammarWalkFuel outputs width count bound
          grammarRunner
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest

/-- Sum of verifier-row-callee fuels along the candidate trajectory. -/
def selectiveFixedCountRowsWalkFuel (outputs : List ℕ)
    (width count bound : ℕ)
    (rowsRunner :
      SelectiveVerifierRowsProgramRunner totalSelectiveVerifierRowsProgram
        outputs width count bound) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → ℕ
  | _, [] => 0
  | state, candidate :: rest =>
      rowsRunner.fuel
          (selectiveFixedCountGrammarWire width bound state candidate).state
          (candidate.val + 1) +
        selectiveFixedCountRowsWalkFuel outputs width count bound rowsRunner
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest

/-- Sum of local fixed-count controller fuels along the trajectory. -/
def selectiveFixedCountLocalWalkFuel (outputs : List ℕ)
    (width count bound : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → ℕ
  | _, [] => 0
  | state, candidate :: rest =>
      selectiveFixedCountLocalLevelFuel outputs width count bound state
          candidate +
        selectiveFixedCountLocalWalkFuel outputs width count bound
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest

set_option maxHeartbeats 800000 in
-- Normalizing the eight-head width maximum exposes both runner projections.
private theorem selectiveFixedCountWalkBits_eq_callee_split
    (outputs : List ℕ) (width count bound : ℕ)
    (grammarRunner : SelectiveFixedCountGrammarRunner width bound)
    (rowsRunner :
      SelectiveVerifierRowsProgramRunner totalSelectiveVerifierRowsProgram
        outputs width count bound)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) :
    selectiveFixedCountWalkBits outputs width count bound
        (TotalSelectiveFixedCountProgram.selectiveFixedCountRunnerOfLevels
          outputs width count bound
          grammarRunner rowsRunner)
        state candidates =
      max
        (selectiveFixedCountLocalWalkBits outputs width count bound state
          candidates)
        (max
          (selectiveFixedCountGrammarWalkBits outputs width count bound
            grammarRunner state candidates)
          (selectiveFixedCountRowsWalkBits outputs width count bound rowsRunner
            state candidates)) := by
  induction candidates generalizing state with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [selectiveFixedCountWalkBits,
        selectiveFixedCountLocalWalkBits, selectiveFixedCountGrammarWalkBits,
        selectiveFixedCountRowsWalkBits]
      rw [ih]
      simp only [
        TotalSelectiveFixedCountProgram.selectiveFixedCountRunnerOfLevels,
        TotalSelectiveFixedCountProgram.selectiveFixedCountLevelBits,
        selectiveFixedCountLocalLevelBits]
      ac_rfl

set_option maxHeartbeats 800000 in
-- Normalizing the nested controller fuel exposes both runner projections.
private theorem selectiveFixedCountWalkFuel_eq_callee_split
    (outputs : List ℕ) (width count bound : ℕ)
    (grammarRunner : SelectiveFixedCountGrammarRunner width bound)
    (rowsRunner :
      SelectiveVerifierRowsProgramRunner totalSelectiveVerifierRowsProgram
        outputs width count bound)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) :
    selectiveFixedCountWalkFuel outputs width count bound
        (TotalSelectiveFixedCountProgram.selectiveFixedCountRunnerOfLevels
          outputs width count bound
          grammarRunner rowsRunner)
        state candidates =
      selectiveFixedCountGrammarWalkFuel outputs width count bound grammarRunner
          state candidates +
        selectiveFixedCountRowsWalkFuel outputs width count bound rowsRunner
          state candidates +
        selectiveFixedCountLocalWalkFuel outputs width count bound state
          candidates := by
  induction candidates generalizing state with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [selectiveFixedCountWalkFuel,
        selectiveFixedCountGrammarWalkFuel, selectiveFixedCountRowsWalkFuel,
        selectiveFixedCountLocalWalkFuel]
      rw [ih]
      simp only [
        TotalSelectiveFixedCountProgram.selectiveFixedCountRunnerOfLevels,
        TotalSelectiveFixedCountProgram.selectiveFixedCountLevelFuel,
        selectiveFixedCountLocalLevelFuel]
      omega

/-! ## 3. Canonical inverse instantiation -/

private noncomputable def canonicalInitialState
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    SelectiveState
      (descriptionWidth
        (canonicalWidth contracts clockDepth advantageExponent pcp target)
        (canonicalBound contracts clockDepth advantageExponent target)) :=
  SelectiveState.empty
    (descriptionWidth
      (canonicalWidth contracts clockDepth advantageExponent pcp target)
      (canonicalBound contracts clockDepth advantageExponent target))
    (index - structuralInputArity
      (canonicalWidth contracts clockDepth advantageExponent pcp target)
      (canonicalBound contracts clockDepth advantageExponent target))

noncomputable def totalInverseCanonicalFixedCountGrammarWalkBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  selectiveFixedCountGrammarWalkBits
    (canonicalOutputs contracts clockDepth machine advantageExponent pcp target)
    (canonicalWidth contracts clockDepth advantageExponent pcp target)
    (canonicalCount contracts clockDepth advantageExponent pcp target)
    (canonicalBound contracts clockDepth advantageExponent target)
    (selectiveFixedCountGrammarRunner _ _)
    (canonicalInitialState contracts clockDepth advantageExponent pcp target
      index)
    (List.ofFn id)

noncomputable def totalInverseCanonicalFixedCountRowsWalkBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  selectiveFixedCountRowsWalkBits
    (canonicalOutputs contracts clockDepth machine advantageExponent pcp target)
    (canonicalWidth contracts clockDepth advantageExponent pcp target)
    (canonicalCount contracts clockDepth advantageExponent pcp target)
    (canonicalBound contracts clockDepth advantageExponent target)
    (totalInverseCanonicalRowsRunner contracts clockDepth machine
      advantageExponent pcp target)
    (canonicalInitialState contracts clockDepth advantageExponent pcp target
      index)
    (List.ofFn id)

noncomputable def totalInverseCanonicalFixedCountLocalWalkBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  selectiveFixedCountLocalWalkBits
    (canonicalOutputs contracts clockDepth machine advantageExponent pcp target)
    (canonicalWidth contracts clockDepth advantageExponent pcp target)
    (canonicalCount contracts clockDepth advantageExponent pcp target)
    (canonicalBound contracts clockDepth advantageExponent target)
    (canonicalInitialState contracts clockDepth advantageExponent pcp target
      index)
    (List.ofFn id)

noncomputable def totalInverseCanonicalFixedCountGrammarWalkFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  selectiveFixedCountGrammarWalkFuel
    (canonicalOutputs contracts clockDepth machine advantageExponent pcp target)
    (canonicalWidth contracts clockDepth advantageExponent pcp target)
    (canonicalCount contracts clockDepth advantageExponent pcp target)
    (canonicalBound contracts clockDepth advantageExponent target)
    (selectiveFixedCountGrammarRunner _ _)
    (canonicalInitialState contracts clockDepth advantageExponent pcp target
      index)
    (List.ofFn id)

noncomputable def totalInverseCanonicalFixedCountRowsWalkFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  selectiveFixedCountRowsWalkFuel
    (canonicalOutputs contracts clockDepth machine advantageExponent pcp target)
    (canonicalWidth contracts clockDepth advantageExponent pcp target)
    (canonicalCount contracts clockDepth advantageExponent pcp target)
    (canonicalBound contracts clockDepth advantageExponent target)
    (totalInverseCanonicalRowsRunner contracts clockDepth machine
      advantageExponent pcp target)
    (canonicalInitialState contracts clockDepth advantageExponent pcp target
      index)
    (List.ofFn id)

noncomputable def totalInverseCanonicalFixedCountLocalWalkFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  selectiveFixedCountLocalWalkFuel
    (canonicalOutputs contracts clockDepth machine advantageExponent pcp target)
    (canonicalWidth contracts clockDepth advantageExponent pcp target)
    (canonicalCount contracts clockDepth advantageExponent pcp target)
    (canonicalBound contracts clockDepth advantageExponent target)
    (canonicalInitialState contracts clockDepth advantageExponent pcp target
      index)
    (List.ofFn id)

theorem totalInverseCanonicalFixedCountWalkBits_eq_calleeFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalCompilerFixedCountWalkBits contracts clockDepth machine
        advantageExponent pcp target index =
      max
        (totalInverseCanonicalFixedCountLocalWalkBits contracts clockDepth
          machine advantageExponent pcp target index)
        (max
          (totalInverseCanonicalFixedCountGrammarWalkBits contracts clockDepth
            machine advantageExponent pcp target index)
          (totalInverseCanonicalFixedCountRowsWalkBits contracts clockDepth
            machine advantageExponent pcp target index)) := by
  exact selectiveFixedCountWalkBits_eq_callee_split _ _ _ _ _ _ _ _

theorem totalInverseCanonicalFixedCountWalkFuel_eq_calleeFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalCompilerFixedCountWalkFuel contracts clockDepth machine
        advantageExponent pcp target index =
      totalInverseCanonicalFixedCountGrammarWalkFuel contracts clockDepth
          machine advantageExponent pcp target index +
        totalInverseCanonicalFixedCountRowsWalkFuel contracts clockDepth machine
          advantageExponent pcp target index +
        totalInverseCanonicalFixedCountLocalWalkFuel contracts clockDepth machine
          advantageExponent pcp target index := by
  exact selectiveFixedCountWalkFuel_eq_callee_split _ _ _ _ _ _ _ _

/-! ## 4. Close the local fixed-count fuel -/

private theorem selectiveFixedCountLocalLevelFuel_le
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) :
    selectiveFixedCountLocalLevelFuel outputs width count bound state candidate ≤
      86 := by
  unfold selectiveFixedCountLocalLevelFuel selectiveEmitFuel
  by_cases hselected :
      selectiveSelectedCode
          (selectiveFixedCountRowsWire outputs width count bound state
            candidate).state.selected = 0
  · simp only [hselected, ↓reduceIte]
    split <;> omega
  · simp only [hselected, ↓reduceIte]
    omega

private theorem selectiveFixedCountLocalWalkFuel_le
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) :
    selectiveFixedCountLocalWalkFuel outputs width count bound state candidates ≤
      86 * candidates.length := by
  induction candidates generalizing state with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [selectiveFixedCountLocalWalkFuel, List.length_cons]
      have hlevel := selectiveFixedCountLocalLevelFuel_le outputs width count
        bound state candidate
      have hrest := ih
        (selectiveCompileTableFixedCount outputs width count bound state
          candidate).state
      omega

theorem totalInverseCanonicalFixedCountLocalWalkFuel_le
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalFixedCountLocalWalkFuel contracts clockDepth machine
        advantageExponent pcp target index ≤
      86 * canonicalBound contracts clockDepth advantageExponent target := by
  unfold totalInverseCanonicalFixedCountLocalWalkFuel
  simpa using selectiveFixedCountLocalWalkFuel_le
    (canonicalOutputs contracts clockDepth machine advantageExponent pcp target)
    (canonicalWidth contracts clockDepth advantageExponent pcp target)
    (canonicalCount contracts clockDepth advantageExponent pcp target)
    (canonicalBound contracts clockDepth advantageExponent target)
    (canonicalInitialState contracts clockDepth advantageExponent pcp target
      index)
    (List.ofFn id)

/-! ## 5. Polynomial splices -/

theorem totalInverseCanonicalFixedCountWalkBits_dominated_of_calleeFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ)
    (hlocal : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalFixedCountLocalWalkBits contracts clockDepth
          machine advantageExponent pcp) coefficient degree)
    (hgrammar : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalFixedCountGrammarWalkBits contracts clockDepth
          machine advantageExponent pcp) coefficient degree)
    (hrows : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalFixedCountRowsWalkBits contracts clockDepth
          machine advantageExponent pcp) coefficient degree) :
    ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerFixedCountWalkBits contracts clockDepth
          machine advantageExponent pcp) coefficient degree := by
  obtain ⟨localCoefficient, hlocal⟩ := hlocal
  obtain ⟨grammarCoefficient, hgrammar⟩ := hgrammar
  obtain ⟨rowsCoefficient, hrows⟩ := hrows
  exact ⟨max localCoefficient (max grammarCoefficient rowsCoefficient),
    fun target index hindex => by
      rw [totalInverseCanonicalFixedCountWalkBits_eq_calleeFrontier]
      exact (hlocal target index hindex).max
        ((hgrammar target index hindex).max (hrows target index hindex))⟩

theorem totalInverseCanonicalFixedCountWalkFuel_dominated_of_calleeFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ)
    (hgrammar : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalFixedCountGrammarWalkFuel contracts clockDepth
          machine advantageExponent pcp) coefficient degree)
    (hrows : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalFixedCountRowsWalkFuel contracts clockDepth
          machine advantageExponent pcp) coefficient degree)
    (hbound : ∃ coefficient, ∀ target,
      PolyBounded
        (canonicalBound contracts clockDepth advantageExponent target)
        (max 1 target) coefficient degree) :
    ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerFixedCountWalkFuel contracts clockDepth
          machine advantageExponent pcp) coefficient degree := by
  obtain ⟨grammarCoefficient, hgrammar⟩ := hgrammar
  obtain ⟨rowsCoefficient, hrows⟩ := hrows
  obtain ⟨boundCoefficient, hbound⟩ := hbound
  exact ⟨grammarCoefficient + rowsCoefficient + 86 * boundCoefficient,
    fun target index hindex => by
      rw [totalInverseCanonicalFixedCountWalkFuel_eq_calleeFrontier]
      have hcallees :=
        (hgrammar target index hindex).add (hrows target index hindex)
      have hlocal := (hbound target).const_mul 86
      exact (hcallees.add hlocal).mono
        (Nat.add_le_add_left
          (totalInverseCanonicalFixedCountLocalWalkFuel_le contracts
            clockDepth machine advantageExponent pcp target index) _)⟩

end NearCubicWires.TotalInverseCanonicalFixedCountWalkResources

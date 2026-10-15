import Proof.Supplier.SelectiveUnaryRun
import Batteries.Tactic.OpenPrivate

/-!
# The clause tower's three middle levels

Three neighbouring levels of the nested structural compiler are executed here.

* `selectiveClauseProgram` (`241` instructions, level 11) compiles one decoded
  three-literal clause.  Its controller occupies `76` positions and relocates
  three callees: the `137`-instruction literal decoder, the `10`-instruction
  private tagged lookup and the `18`-instruction append transition.
* `selectiveClausesProgram` (`335` instructions, level 10) compiles a whole
  decoded clause list and its right-associated `and` suffix.  Its controller
  occupies `68` positions and relocates the clause compiler above, the
  `8`-instruction spine-length fold and the same append transition.
* `structuralAddressProgram` (`276` instructions, level 12) evaluates one
  projected query address.  It carries no selective compiler state at all: its
  `28`-instruction controller walks a row-major table cursor and interprets each
  imported projection code with the published projected-bit program.

Nothing in this module edits a compiled interface.  The three level programs and
the private tagged lookup are reached with `open private`, so every module below
stays byte-identical.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.CanonicalProjectedRandomBitProgram
open NearCubicWires.CanonicalThreeCNFLiteralProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open private selectiveCompileClause_ordered selectiveCompileClauses_ordered
  from Proof.Supplier.SelectiveCountCasesRun

open private run_encodedListLengthLoop
  from Proof.Foundations.CanonicalEncodedListLengthProgram

open private selectiveClauseProgram selectiveClauseControllerProgram
  selectiveClauseControllerProgram_length selectiveClauseInput
  selectiveClausesProgram selectiveClausesControllerProgram
  selectiveClausesControllerProgram_length selectiveClausesInput
  structuralAddressProgram structuralAddressControllerProgram
  structuralAddressControllerProgram_length structuralAddressInput
  structuralTaggedLookupProgram structuralTaggedLookupInput
  structuralTaggedLookupFuel structuralTaggedLookupBits
  run_structuralTaggedLookupProgram run_structuralTaggedLookupLoop
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. Lengths of the four relocated callees

Every decoding lemma below splits one of the three level programs at a fixed
boundary, so each callee's length is needed as a rewrite.  None of them is
exported by its own module. -/

set_option maxRecDepth 8000 in
@[simp] theorem threeCNFLiteralProgram_length :
    threeCNFLiteralProgram.length = 137 := by
  rfl

@[simp] theorem structuralTaggedLookupProgram_length :
    structuralTaggedLookupProgram.length = 10 := by
  rfl

@[simp] theorem encodedListLengthProgram_length :
    encodedListLengthProgram.length = 8 := by
  rfl

set_option maxRecDepth 8000 in
@[simp] theorem selectiveEmitProgram_length :
    selectiveEmitProgram.length = 18 := by
  rfl

set_option maxRecDepth 40000 in
@[simp] theorem projectedRandomBitProgram_length :
    projectedRandomBitProgram.length = 238 := by
  rfl

set_option maxRecDepth 40000 in
@[simp] theorem selectiveClauseProgram_length' :
    selectiveClauseProgram.length = 241 := by
  rfl

set_option maxRecDepth 40000 in
@[simp] theorem selectiveClausesProgram_length' :
    selectiveClausesProgram.length = 335 := by
  rfl

set_option maxRecDepth 40000 in
@[simp] theorem structuralAddressProgram_length' :
    structuralAddressProgram.length = 276 := by
  rfl

/-! ## 2. Decoding the three fixed instruction streams

Each level program is one controller followed by two or three relocated
callees.  Every later step decodes through exactly one of the lemmas below, so
no proof in this module ever forces a whole instruction list. -/

theorem selectiveClauseProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveClauseControllerProgram 76 213 223)[pc]? = some instruction) :
    selectiveClauseProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveClauseControllerProgram 76 213 223).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveClauseControllerProgram_length] at hpc
  simp only [selectiveClauseProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveClauseControllerProgram_length]
    omega)]
  exact hlookup

theorem selectiveClauseProgram_literalCallable :
    ProgramCallableAt selectiveClauseProgram threeCNFLiteralProgram
      76 1000 50 23 := by
  intro pc instruction hlookup
  have hpc : pc < threeCNFLiteralProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [threeCNFLiteralProgram_length] at hpc
  simp only [selectiveClauseProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveClauseControllerProgram_length]
    omega)]
  simp only [selectiveClauseControllerProgram_length]
  rw [show 76 + pc - 76 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveClauseProgram_lookupCallable :
    ProgramCallableAt selectiveClauseProgram structuralTaggedLookupProgram
      213 3000 50 29 := by
  intro pc instruction hlookup
  have hpc : pc < structuralTaggedLookupProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [structuralTaggedLookupProgram_length] at hpc
  simp only [selectiveClauseProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length]
  rw [show 213 + pc - (76 + 137) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveClauseProgram_emitCallable :
    ProgramCallableAt selectiveClauseProgram selectiveEmitProgram
      223 4000 50 62 := by
  intro pc instruction hlookup
  simp only [selectiveClauseProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveClauseControllerProgram_length, threeCNFLiteralProgram_length,
    structuralTaggedLookupProgram_length]
  rw [show 223 + pc - (76 + 137 + 10) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveClausesProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveClausesControllerProgram 68 309 317)[pc]? = some instruction) :
    selectiveClausesProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveClausesControllerProgram 68 309 317).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveClausesControllerProgram_length] at hpc
  simp only [selectiveClausesProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClausesControllerProgram_length, selectiveClauseProgram_length',
      encodedListLengthProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClausesControllerProgram_length, selectiveClauseProgram_length']
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveClausesControllerProgram_length]
    omega)]
  exact hlookup

theorem selectiveClausesProgram_clauseCallable :
    ProgramCallableAt selectiveClausesProgram selectiveClauseProgram
      68 1000 50 28 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveClauseProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveClauseProgram_length'] at hpc
  simp only [selectiveClausesProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClausesControllerProgram_length, selectiveClauseProgram_length',
      encodedListLengthProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClausesControllerProgram_length, selectiveClauseProgram_length']
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveClausesControllerProgram_length]
    omega)]
  simp only [selectiveClausesControllerProgram_length]
  rw [show 68 + pc - 68 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveClausesProgram_lengthCallable :
    ProgramCallableAt selectiveClausesProgram encodedListLengthProgram
      309 6000 50 15 := by
  intro pc instruction hlookup
  have hpc : pc < encodedListLengthProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [encodedListLengthProgram_length] at hpc
  simp only [selectiveClausesProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveClausesControllerProgram_length, selectiveClauseProgram_length',
      encodedListLengthProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveClausesControllerProgram_length, selectiveClauseProgram_length']
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveClausesControllerProgram_length, selectiveClauseProgram_length']
  rw [show 309 + pc - (68 + 241) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveClausesProgram_emitCallable :
    ProgramCallableAt selectiveClausesProgram selectiveEmitProgram
      317 7000 50 50 := by
  intro pc instruction hlookup
  simp only [selectiveClausesProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveClausesControllerProgram_length, selectiveClauseProgram_length',
      encodedListLengthProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveClausesControllerProgram_length, selectiveClauseProgram_length',
    encodedListLengthProgram_length]
  rw [show 317 + pc - (68 + 241 + 8) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem structuralAddressProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (structuralAddressControllerProgram 28 38)[pc]? = some instruction) :
    structuralAddressProgram[pc]? = some instruction := by
  have hpc : pc < (structuralAddressControllerProgram 28 38).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [structuralAddressControllerProgram_length] at hpc
  simp only [structuralAddressProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      structuralAddressControllerProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [structuralAddressControllerProgram_length]
    omega)]
  exact hlookup

theorem structuralAddressProgram_lookupCallable :
    ProgramCallableAt structuralAddressProgram structuralTaggedLookupProgram
      28 1000 50 13 := by
  intro pc instruction hlookup
  have hpc : pc < structuralTaggedLookupProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [structuralTaggedLookupProgram_length] at hpc
  simp only [structuralAddressProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      structuralAddressControllerProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [structuralAddressControllerProgram_length]
    omega)]
  simp only [structuralAddressControllerProgram_length]
  rw [show 28 + pc - 28 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem structuralAddressProgram_projectedBitCallable :
    ProgramCallableAt structuralAddressProgram projectedRandomBitProgram
      38 2000 50 19 := by
  intro pc instruction hlookup
  simp only [structuralAddressProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      structuralAddressControllerProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    structuralAddressControllerProgram_length,
    structuralTaggedLookupProgram_length]
  rw [show 38 + pc - (28 + 10) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 3. Level 11 at the typed level

`selectiveCompileClause` is a fixed five-append schedule with no loop: three
literals, of which only the negative ones append a `not`, and the two canonical
`or` nodes.  The controller walks it with a phase register rather than a spine,
so the typed layer needs only the named intermediate wires. -/

/-- The clause compiler's first literal wire. -/
def selectiveClauseFirstWire {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) (clause : Fin 3 → Literal q) : SelectiveWire n :=
  selectiveCompileLiteral state values (clause 0)

/-- The clause compiler's second literal wire. -/
def selectiveClauseSecondWire {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) (clause : Fin 3 → Literal q) : SelectiveWire n :=
  selectiveCompileLiteral (selectiveClauseFirstWire state values clause).state
    values (clause 1)

/-- The clause compiler's first disjunction. -/
def selectiveClauseFirstOrSecondWire {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) (clause : Fin 3 → Literal q) : SelectiveWire n :=
  selectiveOr (selectiveClauseSecondWire state values clause).state
    (selectiveClauseFirstWire state values clause).output
    (selectiveClauseSecondWire state values clause).output

/-- The clause compiler's third literal wire. -/
def selectiveClauseThirdWire {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) (clause : Fin 3 → Literal q) : SelectiveWire n :=
  selectiveCompileLiteral
    (selectiveClauseFirstOrSecondWire state values clause).state values
    (clause 2)

theorem selectiveCompileClause_eq {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) (clause : Fin 3 → Literal q) :
    selectiveCompileClause state values clause =
      selectiveOr (selectiveClauseThirdWire state values clause).state
        (selectiveClauseFirstOrSecondWire state values clause).output
        (selectiveClauseThirdWire state values clause).output := rfl

/-- One literal wire is the raw live value, and additionally one `not` append
exactly on a negative literal. -/
theorem selectiveCompileLiteral_eq {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) (literal : Literal q) :
    selectiveCompileLiteral state values literal =
      (match literal with
        | .positive query => { state := state, output := values.getD query.val 0 }
        | .negative query => selectiveNot state (values.getD query.val 0)) := by
  cases literal <;> rfl

/-! ## 4. Level 10 at the typed level

The source compiler folds the clause list to the right, so the outermost `and`
node is appended last and its left child is the first clause.  The controller
instead compiles every clause first, retains their outputs on the standard
private reverse spine, and only then emits the conjunctions from the innermost
outwards.  Both orders append exactly the same nodes in exactly the same order.

The reverse pass is literally the unary compiler's conjunction fold, so
`selectiveUnaryFold` and `selectiveUnaryFold_concat` are consumed unchanged. -/

/-- The forward pass: one compiled clause per list entry, in the ascending order
the controller visits them. -/
def selectiveClausesHeads {q n : ℕ} :
    SelectiveState n → List ℕ → List (Fin 3 → Literal q) →
      SelectiveWireList n
  | state, _values, [] => { state := state, values := [] }
  | state, values, clause :: rest =>
      let head := selectiveCompileClause state values clause
      let tail := selectiveClausesHeads head.state values rest
      { state := tail.state
        values := head.output :: tail.values }

theorem selectiveClausesHeads_ordered {q n : ℕ}
    (clauses : List (Fin 3 → Literal q)) (state : SelectiveState n)
    (values : List ℕ) (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveClausesHeads state values clauses).state := by
  induction clauses generalizing state with
  | nil => exact hordered
  | cons clause rest ih =>
      exact ih _ (selectiveCompileClause_ordered state values clause hordered)

/-- **The clause-list controller's scheduling identity.**  The source compiler's
right-associated conjunction is exactly the forward clause pass followed by the
reverse fold over the retained spine. -/
theorem selectiveCompileClauses_eq_fold {q n : ℕ}
    (clauses : List (Fin 3 → Literal q)) (state : SelectiveState n)
    (values : List ℕ) :
    selectiveCompileClauses state values clauses =
      selectiveUnaryFold
        (selectiveConst (selectiveClausesHeads state values clauses).state
          true).state
        (selectiveConst (selectiveClausesHeads state values clauses).state
          true).output
        (selectiveClausesHeads state values clauses).values.reverse := by
  induction clauses generalizing state with
  | nil => rfl
  | cons clause rest ih =>
      have hcompile :
          selectiveCompileClauses state values (clause :: rest) =
            selectiveAnd
              (selectiveCompileClauses
                (selectiveCompileClause state values clause).state values
                rest).state
              (selectiveCompileClause state values clause).output
              (selectiveCompileClauses
                (selectiveCompileClause state values clause).state values
                rest).output := rfl
      have hheads :
          selectiveClausesHeads state values (clause :: rest) =
            { state :=
                (selectiveClausesHeads
                  (selectiveCompileClause state values clause).state values
                  rest).state
              values :=
                (selectiveCompileClause state values clause).output ::
                  (selectiveClausesHeads
                    (selectiveCompileClause state values clause).state values
                    rest).values } := rfl
      rw [hcompile, hheads]
      simp only [List.reverse_cons]
      rw [selectiveUnaryFold_concat, ih]

/-! ## 5. Level 12 at the typed level

The address controller carries no compiler state.  It walks a row-major table
cursor once per address bit, interprets each imported projection code with the
published projected-bit program, and accumulates the results little-endian
against a doubling place value.  §5 identifies that accumulation with the source
compiler's `projectionTableAddress`. -/

/-- One projected address bit as the table itself reports it. -/
def structuralAddressBool (outputs : List ℕ) (width randomnessCode cursor : ℕ) :
    Bool :=
  (decodeProjectedRandomBit width
      (projectionRawOutput (outputs.getD cursor 0))).eval
    (tableRandomness width randomnessCode)

/-- The same bit as the machine holds it, in register `14`. -/
def structuralAddressBit (outputs : List ℕ) (width randomnessCode cursor : ℕ) :
    ℕ :=
  projectedRandomBitOutput width
    (projectionRawOutput (outputs.getD cursor 0)) randomnessCode

theorem structuralAddressBit_eq_toNat (outputs : List ℕ)
    (width randomnessCode cursor : ℕ) :
    structuralAddressBit outputs width randomnessCode cursor =
      (structuralAddressBool outputs width randomnessCode cursor).toNat := rfl

/-- The remaining suffix of the little-endian address, innermost bit first. -/
def structuralAddressSum (outputs : List ℕ) (width randomnessCode : ℕ) :
    ℕ → ℕ → ℕ
  | _cursor, 0 => 0
  | cursor, count + 1 =>
      structuralAddressBit outputs width randomnessCode cursor +
        2 * structuralAddressSum outputs width randomnessCode (cursor + 1) count

/-- Interpreter accumulator of the address loop: the controller carries a
doubling place value and adds it exactly on a set bit. -/
def structuralAddressFold (outputs : List ℕ) (width randomnessCode : ℕ) :
    ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _place, accumulated, _cursor => accumulated
  | count + 1, place, accumulated, cursor =>
      structuralAddressFold outputs width randomnessCode count (place + place)
        (accumulated +
          (if structuralAddressBit outputs width randomnessCode cursor = 0 then 0
            else place))
        (cursor + 1)

private theorem encodeBitInput_succ {n : ℕ} (input : BitInput (n + 1)) :
    encodeBitInput input =
      (input 0).toNat +
        2 * encodeBitInput (fun index : Fin n => input index.succ) := by
  unfold encodeBitInput
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · cases input 0 <;> simp
  · apply Finset.sum_congr rfl
    intro index _
    split
    · change 2 ^ (index.val + 1) = 2 * 2 ^ index.val
      rw [pow_succ]
      omega
    · simp

theorem structuralAddressSum_eq_encodeBitInput (outputs : List ℕ)
    (width randomnessCode : ℕ) :
    ∀ (count cursor : ℕ),
      structuralAddressSum outputs width randomnessCode cursor count =
        encodeBitInput (n := count) (fun index =>
          structuralAddressBool outputs width randomnessCode
            (cursor + index.val)) := by
  intro count
  induction count with
  | zero => intro cursor; simp [structuralAddressSum, encodeBitInput]
  | succ count ih =>
      intro cursor
      rw [structuralAddressSum, encodeBitInput_succ, ih (cursor + 1),
        structuralAddressBit_eq_toNat]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
      have htail :
          (fun index : Fin count =>
              structuralAddressBool outputs width randomnessCode
                (cursor + (index.val + 1))) =
            fun index : Fin count =>
              structuralAddressBool outputs width randomnessCode
                (cursor + 1 + index.val) := by
        funext index
        congr 1
        omega
      rw [htail]

theorem structuralAddressFold_eq_sum (outputs : List ℕ)
    (width randomnessCode : ℕ) :
    ∀ (count place accumulated cursor : ℕ),
      structuralAddressFold outputs width randomnessCode count place
          accumulated cursor =
        accumulated +
          place * structuralAddressSum outputs width randomnessCode cursor
            count := by
  intro count
  induction count with
  | zero =>
      intro place accumulated cursor
      simp [structuralAddressFold, structuralAddressSum]
  | succ count ih =>
      intro place accumulated cursor
      rw [structuralAddressFold, ih, structuralAddressSum]
      cases hbit : structuralAddressBool outputs width randomnessCode cursor
      · rw [if_pos
          (show structuralAddressBit outputs width randomnessCode cursor = 0 by
            rw [structuralAddressBit_eq_toNat, hbit]
            rfl)]
        rw [structuralAddressBit_eq_toNat, hbit]
        simp only [Bool.toNat_false]
        ring
      · rw [if_neg
          (show ¬structuralAddressBit outputs width randomnessCode cursor = 0 by
            rw [structuralAddressBit_eq_toNat, hbit]
            simp)]
        rw [structuralAddressBit_eq_toNat, hbit]
        simp only [Bool.toNat_true]
        ring

/-- **The address controller's scheduling identity.**  The doubling
accumulation the controller performs is exactly the source compiler's projected
address for the same query. -/
theorem structuralAddressFold_eq_projectionTableAddress (outputs : List ℕ)
    (width query randomnessCode : ℕ) :
    structuralAddressFold outputs width randomnessCode width 1 0
        (projectionQueryOffset width query 0) =
      encodeBitInput
        (projectionTableAddress outputs width query
          (tableRandomness width randomnessCode)) := by
  rw [structuralAddressFold_eq_sum, structuralAddressSum_eq_encodeBitInput]
  rw [Nat.zero_add, Nat.one_mul]
  congr 1

theorem run_structuralTaggedLookupLoop_anyEntry
    (values : List ℕ) (index maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 2)
    (htable : state.registers 2 = encodeTaggedList values)
    (hindex : state.registers 3 = index)
    (htableBits : natBitLength (encodeTaggedList values) ≤ maximumBits)
    (hindexBits : natBitLength index ≤ maximumBits) :
    runNPOracleProgram structuralTaggedLookupProgram maximumBits
        (5 * index + 4) state =
      some (values.getD index 0) := by
  induction index generalizing values state with
  | zero =>
      cases values with
      | nil =>
          rw [show 5 * 0 + 4 = 3 + 1 by omega]
          rw [run_branchZero_instruction (by rfl) hpc]
          rw [show state.registers 3 = 0 by simpa using hindex, if_pos rfl]
          rw [show 3 = 2 + 1 by omega]
          rw [run_unpairRight_instruction (value := 0)
            (by rfl) rfl
            (by simp [NPOracleState.jump, htable, encodeTaggedList])
            (by simpa [encodeTaggedList] using htableBits)]
          rw [show 2 = 1 + 1 by omega]
          rw [run_unpairLeft_instruction (value := 0)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by simpa [encodeTaggedList] using htableBits)]
          exact run_halt_instruction (fuel := 0)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by simpa [encodeTaggedList] using htableBits)
      | cons value rest =>
          have hpayloadBits :
              natBitLength (Nat.pair value (encodeTaggedList rest)) ≤
                maximumBits :=
            (natBitLength_mono <|
              Nat.right_le_pair 1 (Nat.pair value (encodeTaggedList rest))).trans
              htableBits
          have hvalueBits : natBitLength value ≤ maximumBits :=
            (natBitLength_mono <|
              Nat.left_le_pair value (encodeTaggedList rest)).trans hpayloadBits
          rw [show 5 * 0 + 4 = 3 + 1 by omega]
          rw [run_branchZero_instruction (by rfl) hpc]
          rw [show state.registers 3 = 0 by simpa using hindex, if_pos rfl]
          rw [show 3 = 2 + 1 by omega]
          rw [run_unpairRight_instruction
            (value := Nat.pair value (encodeTaggedList rest))
            (by rfl) rfl
            (by simp [NPOracleState.jump, htable, encodeTaggedList])
            hpayloadBits]
          rw [show 2 = 1 + 1 by omega]
          rw [run_unpairLeft_instruction (value := value)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump])
            hvalueBits]
          exact run_halt_instruction (fuel := 0)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump])
            hvalueBits
  | succ index inductionHypothesis =>
      have hindexBitsDown : natBitLength index ≤ maximumBits :=
        (decrement_bits_le (index + 1)).trans hindexBits
      have hnonzero : state.registers 3 ≠ 0 := by
        rw [hindex]
        omega
      rw [show 5 * (index + 1) + 4 = (5 * index + 8) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [if_neg hnonzero]
      cases values with
      | nil =>
          have hzeroBits : natBitLength 0 ≤ maximumBits :=
            (natBitLength_mono (Nat.zero_le _)).trans htableBits
          rw [show 5 * index + 8 = (5 * index + 7) + 1 by omega]
          rw [run_unpairRight_instruction (value := 0)
            (by rfl) rfl
            (by simp [NPOracleState.jump, htable, encodeTaggedList])
            hzeroBits]
          rw [show 5 * index + 7 = (5 * index + 6) + 1 by omega]
          rw [run_unpairRight_instruction (value := 0)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump])
            hzeroBits]
          rw [show 5 * index + 6 = (5 * index + 5) + 1 by omega]
          rw [run_decrement_instruction (value := index)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, hindex])
            hindexBitsDown]
          rw [show 5 * index + 5 = (5 * index + 4) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) rfl]
          simp only [ite_self]
          exact inductionHypothesis [] _ rfl
            (by
              simp [NPOracleState.write, NPOracleState.jump, encodeTaggedList])
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by simpa [encodeTaggedList] using hzeroBits) hindexBitsDown
      | cons value rest =>
          have hpayloadBits :
              natBitLength (Nat.pair value (encodeTaggedList rest)) ≤
                maximumBits :=
            (natBitLength_mono <|
              Nat.right_le_pair 1 (Nat.pair value (encodeTaggedList rest))).trans
              htableBits
          have htailBits :
              natBitLength (encodeTaggedList rest) ≤ maximumBits :=
            (natBitLength_mono <|
              Nat.right_le_pair value (encodeTaggedList rest)).trans
              hpayloadBits
          rw [show 5 * index + 8 = (5 * index + 7) + 1 by omega]
          rw [run_unpairRight_instruction
            (value := Nat.pair value (encodeTaggedList rest))
            (by rfl) rfl
            (by simp [NPOracleState.jump, htable, encodeTaggedList])
            hpayloadBits]
          rw [show 5 * index + 7 = (5 * index + 6) + 1 by omega]
          rw [run_unpairRight_instruction (value := encodeTaggedList rest)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump])
            htailBits]
          rw [show 5 * index + 6 = (5 * index + 5) + 1 by omega]
          rw [run_decrement_instruction (value := index)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, hindex])
            hindexBitsDown]
          rw [show 5 * index + 5 = (5 * index + 4) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) rfl]
          simp only [ite_self]
          exact inductionHypothesis rest _ rfl
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump])
            htailBits hindexBitsDown

/-- **The private tagged lookup at an arbitrary entry state.** -/
theorem run_structuralTaggedLookupProgram_anyEntry
    (values : List ℕ) (index : ℕ) (entry : NPOracleState)
    (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        structuralTaggedLookupInput (encodeTaggedList values) index) :
    runNPOracleProgram structuralTaggedLookupProgram
        (structuralTaggedLookupBits values index)
        (structuralTaggedLookupFuel index) entry =
      some (values.getD index 0) := by
  have hinputBits :
      natBitLength
          (structuralTaggedLookupInput (encodeTaggedList values) index) ≤
        structuralTaggedLookupBits values index := by
    rfl
  have htableBits :
      natBitLength (encodeTaggedList values) ≤
        structuralTaggedLookupBits values index :=
    (natBitLength_mono <|
      Nat.left_le_pair (encodeTaggedList values) index).trans hinputBits
  have hindexBits :
      natBitLength index ≤ structuralTaggedLookupBits values index :=
    (natBitLength_mono <|
      Nat.right_le_pair (encodeTaggedList values) index).trans hinputBits
  rw [show structuralTaggedLookupFuel index = (5 * index + 5) + 1 by
    simp [structuralTaggedLookupFuel]]
  rw [run_unpairLeft_instruction (value := encodeTaggedList values)
    (by rfl) hentryPc
    (by simp [hentryInput, structuralTaggedLookupInput]) htableBits]
  rw [show 5 * index + 5 = (5 * index + 4) + 1 by omega]
  rw [run_unpairRight_instruction (value := index)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        structuralTaggedLookupInput])
    hindexBits]
  exact run_structuralTaggedLookupLoop_anyEntry values index _ _ rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump]) htableBits hindexBits

/-- **The clause-count fold at an arbitrary entry state.**  Its first
instruction writes the accumulator, and the loop reads only registers it has
already written. -/
theorem run_encodedListLengthProgram_anyEntry (code : ℕ)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput : entry.registers 0 = code) :
    runNPOracleProgram encodedListLengthProgram (encodedListLengthBits code)
        (encodedListLengthFuel code) entry =
      some (encodedListLength code) := by
  have hcodeBits : natBitLength code ≤ encodedListLengthBits code :=
    natBitLength_mono (Nat.le_max_left _ _)
  have hlengthBits :
      natBitLength (encodedListLength code) ≤ encodedListLengthBits code :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hzeroBits : natBitLength 0 ≤ encodedListLengthBits code :=
    (natBitLength_mono (Nat.zero_le code)).trans hcodeBits
  rw [show encodedListLengthFuel code = encodedListLengthLoopFuel code + 1 by
    rfl]
  rw [run_set_instruction (value := 0) (by rfl) hentryPc hzeroBits]
  simpa only [Nat.zero_add] using
    run_encodedListLengthLoop code 0 (encodedListLengthBits code)
      ((entry.write 2 0).jump 1) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hentryInput])
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcodeBits (by simpa using hlengthBits)

/-! ## 7. The two leaves that are still published at an initial state

`threeCNFLiteralProgram` and `projectedRandomBitProgram` are both
`linkPrograms` compositions.  A link's prologue copies register one — the public
input length — into its own saved slot and charges that copy against the
advertised register width, so neither program can be run from a *completely*
arbitrary entry state: the relocated frame's register one must still fit.  Every
other register is reset by the link before the second stage starts, and the
first stage of each of these two programs writes before it reads.

Each is therefore packaged as a one-field premise carrying exactly that side
condition.  This is the only obligation of levels 11 and 12 that this module
does not discharge, and it is shared: one witness closes both. -/

structure ThreeCNFLiteralEntryRunner where
  executes : ∀ (inputLength arity code clauseIndex position : ℕ),
    0 < arity → ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 = threeCNFLiteralInput arity code clauseIndex position →
    natBitLength (entry.registers 1) ≤
      threeCNFLiteralBits inputLength arity code clauseIndex position →
    runNPOracleProgram threeCNFLiteralProgram
        (threeCNFLiteralBits inputLength arity code clauseIndex position)
        (threeCNFLiteralFuel arity code clauseIndex position) entry =
      some (threeCNFLiteralOutput arity code clauseIndex position)

structure ProjectedRandomBitEntryRunner where
  executes : ∀ (inputLength width projectionCode randomnessCode : ℕ),
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      projectedRandomBitInput width projectionCode randomnessCode →
    natBitLength (entry.registers 1) ≤
      projectedRandomBitBits inputLength width projectionCode randomnessCode →
    runNPOracleProgram projectedRandomBitProgram
        (projectedRandomBitBits inputLength width projectionCode randomnessCode)
        (projectedRandomBitFuel width projectionCode randomnessCode) entry =
      some (projectedRandomBitOutput width projectionCode randomnessCode)

/-! ## 8. The three level runners

Every level of this tower is consumed one level up as a premise: interpreter
resources as functions of the compiled request only, and a run at an arbitrary
entry state, because each call starts on whatever registers the previous call
left in the callee's frame.  The three structures below are the shapes levels
`9` and `10` consume. -/

/-- The decoded clause a level-11 request names. -/
def selectiveClauseOf (literalArity : ℕ) (harity : 0 < literalArity)
    (decisionCode clauseIndex : ℕ) : Fin 3 → Literal literalArity :=
  (decodeThreeCNF literalArity decisionCode).clauses.getD clauseIndex
    (fun _ => decodeLiteral harity 0)

/-- **Level 11.**  The `241`-instruction clause compiler compiles one decoded
three-literal clause at its own ABI frame. -/
structure SelectiveClauseRunner (n literalArity : ℕ)
    (harity : 0 < literalArity) where
  bits : SelectiveState n → List ℕ → ℕ → ℕ → ℕ
  fuel : SelectiveState n → List ℕ → ℕ → ℕ → ℕ
  executes : ∀ (state : SelectiveState n) (values : List ℕ)
      (decisionCode clauseIndex : ℕ), selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveClauseInput (selectiveStateCode state) n
        (encodeTaggedList values) literalArity decisionCode clauseIndex →
    runNPOracleProgram selectiveClauseProgram
        (bits state values decisionCode clauseIndex)
        (fuel state values decisionCode clauseIndex) entry =
      some
        (selectiveWireCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode clauseIndex)))

/-- **Level 10.**  The `335`-instruction clause-list compiler compiles the whole
decoded clause list and its right-associated `and` suffix at its own ABI
frame. -/
structure SelectiveClausesRunner (n literalArity : ℕ) where
  bits : SelectiveState n → List ℕ → ℕ → ℕ
  fuel : SelectiveState n → List ℕ → ℕ → ℕ
  executes : ∀ (state : SelectiveState n) (values : List ℕ)
      (decisionCode : ℕ), selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveClausesInput (selectiveStateCode state) n
        (encodeTaggedList values) literalArity decisionCode →
    runNPOracleProgram selectiveClausesProgram (bits state values decisionCode)
        (fuel state values decisionCode) entry =
      some
        (selectiveWireCode
          (selectiveCompileClauses state values
            (decodeThreeCNF literalArity decisionCode).clauses))

/-- **Level 12.**  The `276`-instruction address evaluator returns one complete
projected query address at its own ABI frame.  It carries no compiler state, so
its request names only the table, the row width, the randomness row and the
row-major cursor at which the query's coordinates begin. -/
structure StructuralAddressRunner (outputs : List ℕ) (width : ℕ) where
  bits : ℕ → ℕ → ℕ
  fuel : ℕ → ℕ → ℕ
  executes : ∀ (query randomnessCode : ℕ),
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      structuralAddressInput (encodeTaggedList outputs) width randomnessCode
        (projectionQueryOffset width query 0) →
    runNPOracleProgram structuralAddressProgram (bits query randomnessCode)
        (fuel query randomnessCode) entry =
      some
        (encodeBitInput
          (projectionTableAddress outputs width query
            (tableRandomness width randomnessCode)))

/-! ## 9. Level 11's single shared call frame

The clause controller reaches the relocated append from three different phases —
the negation of a negative literal, the first `or` and the second `or` — but all
three arrive at the same physical block at `57`.  The block builds the callee's
request from the live state registers, runs the callee, and unpacks the returned
wire back into those same registers; it then falls through to the phase
dispatcher at `69`.  Every append in level 11 goes through this one lemma. -/

-- Five request-building steps around the relocated append, then seven steps
-- unpacking the returned wire back into the controller's live registers.
theorem run_selectiveClauseEmitCall {n : ℕ}
    (state : SelectiveState n) (node : BooleanNode n)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (arity values literalArity decisionCode clauseIndex position first
      firstOrSecond phase : ℕ)
    (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode node)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode (state.emit node))) ≤
        maximumBits)
    (hpc : machine.pc = 57)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hnode : machine.registers 23 = rawCircuitNodeCode node)
    (harity : machine.registers 8 = arity)
    (hvalues : machine.registers 10 = values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hclauseIndex : machine.registers 16 = clauseIndex)
    (hposition : machine.registers 17 = position)
    (hfirst : machine.registers 21 = first)
    (hfirstOrSecond : machine.registers 22 = firstOrSecond)
    (hzeroRegister : machine.registers 29 = 0)
    (hphase : machine.registers 30 = phase)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 69 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 2 = selectiveStateCode (state.emit node).state →
      resumed.registers 4 =
        (state.emit node).state.target - (state.emit node).state.next →
      resumed.registers 6 = (state.emit node).state.next →
      resumed.registers 7 =
        selectiveSelectedCode (state.emit node).state.selected →
      resumed.registers 20 = (state.emit node).output →
      resumed.registers 8 = arity →
      resumed.registers 10 = values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = clauseIndex →
      resumed.registers 17 = position →
      resumed.registers 21 = first →
      resumed.registers 22 = firstOrSecond →
      resumed.registers 29 = 0 →
      resumed.registers 30 = phase →
      runNPOracleProgram selectiveClauseProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClauseProgram maximumBits
        (5 + (emitFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm : ∀ candidate : SelectiveState n,
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hinputForm :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) =
        Nat.pair (selectiveStateCode state) (rawCircuitNodeCode node) := rfl
  have hinputFlat := hinputBits
  rw [hinputForm] at hinputFlat
  have hstateBits := natBitLength_pair_left hinputFlat
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  have hwireFlat := natBitLength_pair_right hwireBits
  have hwireParts := hwireFlat
  simp only [selectiveWireCode] at hwireParts
  have hemittedStateBits := natBitLength_pair_left hwireParts
  have hemittedOutputBits := natBitLength_pair_right hwireParts
  have hemittedStateFlat := hemittedStateBits
  rw [hstateForm (state.emit node).state] at hemittedStateFlat
  have hemittedRemainingBits := natBitLength_pair_left hemittedStateFlat
  have hemittedTailBits := natBitLength_pair_right hemittedStateFlat
  have hemittedNextBits := natBitLength_pair_left hemittedTailBits
  have hemittedSelectedBits := natBitLength_pair_right hemittedTailBits
  have hemitOutput :
      selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) =
        selectiveWireCode (state.emit node) :=
    selectiveEmitOutput_eq_wireCode state node hordered
  have hemitCalleeBits :
      selectiveEmitBits (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) ≤
        maximumBits := by
    unfold selectiveEmitBits selectiveEmitWorkBound
    rcases Nat.le_total
        (selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
        (selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
        with hle | hle
    · rw [max_eq_right hle, hemitOutput]
      exact hwireFlat
    · rw [max_eq_left hle]
      exact hinputBits
  rw [show 5 + (emitFuel + (7 + extraFuel)) =
    (4 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveClauseProgram_controllerAt (pc := 57) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 4 + (emitFuel + (7 + extraFuel)) =
    (3 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveClauseProgram_controllerAt (pc := 58) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 3 + (emitFuel + (7 + extraFuel)) =
    (2 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
    (selectiveClauseProgram_controllerAt (pc := 59) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [show 2 + (emitFuel + (7 + extraFuel)) =
    (1 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 60) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (7 + extraFuel)) =
    (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 61) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveClauseProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveEmitProgram_eq_emit state node hordered frame hframePc ?_)
      hemitCalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro emitHalt
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveWireCode (state.emit node))
      (selectiveClauseProgram_controllerAt (pc := 62) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveClauseProgram_controllerAt (pc := 63) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveClauseProgram_controllerAt (pc := 64) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (state.emit node).state.target - (state.emit node).state.next)
      (selectiveClauseProgram_controllerAt (pc := 65) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveClauseProgram_controllerAt (pc := 66) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveClauseProgram_controllerAt (pc := 67) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveClauseProgram_controllerAt (pc := 68) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hvalues, hliteralArity, hdecisionCode, hclauseIndex, hposition, hfirst,
        hfirstOrSecond, hzeroRegister, hphase]

/-! ## 10. Level 10's single shared call frame

The clause-list controller reaches the relocated append from two places — the
explicit `true` base case and every conjunction of the reverse pass — and both
arrive at the same physical block at `45`.  Unlike level 11 there is no phase
dispatcher afterwards: the block falls straight through into the reverse fold's
loop head at `57`. -/

theorem run_selectiveClausesEmitCall {n : ℕ}
    (state : SelectiveState n) (node : BooleanNode n)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (arity values literalArity decisionCode count clauseIndex spine : ℕ)
    (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode node)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode (state.emit node))) ≤
        maximumBits)
    (hpc : machine.pc = 45)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hnode : machine.registers 23 = rawCircuitNodeCode node)
    (harity : machine.registers 8 = arity)
    (hvalues : machine.registers 10 = values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hcount : machine.registers 16 = count)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine : machine.registers 18 = spine)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 57 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 2 = selectiveStateCode (state.emit node).state →
      resumed.registers 4 =
        (state.emit node).state.target - (state.emit node).state.next →
      resumed.registers 6 = (state.emit node).state.next →
      resumed.registers 7 =
        selectiveSelectedCode (state.emit node).state.selected →
      resumed.registers 20 = (state.emit node).output →
      resumed.registers 8 = arity →
      resumed.registers 10 = values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = count →
      resumed.registers 17 = clauseIndex →
      resumed.registers 18 = spine →
      resumed.registers 29 = 0 →
      runNPOracleProgram selectiveClausesProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClausesProgram maximumBits
        (5 + (emitFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm : ∀ candidate : SelectiveState n,
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hinputForm :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) =
        Nat.pair (selectiveStateCode state) (rawCircuitNodeCode node) := rfl
  have hinputFlat := hinputBits
  rw [hinputForm] at hinputFlat
  have hstateBits := natBitLength_pair_left hinputFlat
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  have hwireFlat := natBitLength_pair_right hwireBits
  have hwireParts := hwireFlat
  simp only [selectiveWireCode] at hwireParts
  have hemittedStateBits := natBitLength_pair_left hwireParts
  have hemittedOutputBits := natBitLength_pair_right hwireParts
  have hemittedStateFlat := hemittedStateBits
  rw [hstateForm (state.emit node).state] at hemittedStateFlat
  have hemittedRemainingBits := natBitLength_pair_left hemittedStateFlat
  have hemittedTailBits := natBitLength_pair_right hemittedStateFlat
  have hemittedNextBits := natBitLength_pair_left hemittedTailBits
  have hemittedSelectedBits := natBitLength_pair_right hemittedTailBits
  have hemitOutput :
      selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) =
        selectiveWireCode (state.emit node) :=
    selectiveEmitOutput_eq_wireCode state node hordered
  have hemitCalleeBits :
      selectiveEmitBits (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) ≤
        maximumBits := by
    unfold selectiveEmitBits selectiveEmitWorkBound
    rcases Nat.le_total
        (selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
        (selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
        with hle | hle
    · rw [max_eq_right hle, hemitOutput]
      exact hwireFlat
    · rw [max_eq_left hle]
      exact hinputBits
  rw [show 5 + (emitFuel + (7 + extraFuel)) =
    (4 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveClausesProgram_controllerAt (pc := 45) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 4 + (emitFuel + (7 + extraFuel)) =
    (3 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveClausesProgram_controllerAt (pc := 46) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 3 + (emitFuel + (7 + extraFuel)) =
    (2 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
    (selectiveClausesProgram_controllerAt (pc := 47) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [show 2 + (emitFuel + (7 + extraFuel)) =
    (1 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 48) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (7 + extraFuel)) =
    (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 49) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveClausesProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveEmitProgram_eq_emit state node hordered frame hframePc ?_)
      hemitCalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro emitHalt
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveWireCode (state.emit node))
      (selectiveClausesProgram_controllerAt (pc := 50) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveClausesProgram_controllerAt (pc := 51) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveClausesProgram_controllerAt (pc := 52) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (state.emit node).state.target - (state.emit node).state.next)
      (selectiveClausesProgram_controllerAt (pc := 53) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveClausesProgram_controllerAt (pc := 54) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveClausesProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveClausesProgram_controllerAt (pc := 56) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hvalues, hliteralArity, hdecisionCode, hcount, hclauseIndex, hspine,
        hzeroRegister]

/-! ## 11. Level 10's reverse conjunction fold

The retained clause outputs are consumed innermost first, one relocated append
per spine entry.  Both the fold itself and its register-width envelope are the
unary compiler's, since both levels append exactly `and` nodes against the same
spine encoding; only the clock differs, because this controller reaches its loop
head with no phase dispatch at all. -/

/-- Interpreter fuel of level 10's reverse fold: ten controller steps and one
relocated append per retained clause output. -/
def selectiveClausesFoldFuel {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      10 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              selectiveClausesFoldFuel
                (selectiveAnd state value accumulated).state
                (selectiveAnd state value accumulated).output rest)))

-- One fold iteration is ten controller steps around the shared call frame of
-- §10; the append returns directly to the loop head.
theorem run_selectiveClausesFoldStep {n : ℕ}
    (state : SelectiveState n) (accumulated value : ℕ) (rest : List ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (values literalArity decisionCode count clauseIndex : ℕ)
    (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hspineBits :
      natBitLength (selectiveCountCasesSpineCode (value :: rest)) ≤
        maximumBits)
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.and value accumulated))) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode (selectiveAnd state value accumulated))) ≤
        maximumBits)
    (hpc : machine.pc = 57)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hvalues : machine.registers 10 = values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hcount : machine.registers 16 = count)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine :
      machine.registers 18 = selectiveCountCasesSpineCode (value :: rest))
    (haccumulated : machine.registers 20 = accumulated)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 57 →
      resumed.registers 0 =
        selectiveWireCode (selectiveAnd state value accumulated) →
      resumed.registers 4 =
        (selectiveAnd state value accumulated).state.target -
          (selectiveAnd state value accumulated).state.next →
      resumed.registers 6 = (selectiveAnd state value accumulated).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveAnd state value accumulated).state.selected →
      resumed.registers 8 = n →
      resumed.registers 10 = values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = count →
      resumed.registers 17 = clauseIndex →
      resumed.registers 18 = selectiveCountCasesSpineCode rest →
      resumed.registers 20 = (selectiveAnd state value accumulated).output →
      resumed.registers 29 = 0 →
      runNPOracleProgram selectiveClausesProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClausesProgram maximumBits
        (10 + (5 + (emitFuel + (7 + extraFuel)))) machine =
      some finalOutput := by
  have hnodeCode :
      rawCircuitNodeCode (n := n) (.and value accumulated) =
        Nat.pair 3 (Nat.pair (n + value) (n + accumulated)) := rfl
  have hemitInput :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.and value accumulated)) =
        Nat.pair (selectiveStateCode state)
          (rawCircuitNodeCode (n := n) (.and value accumulated)) := rfl
  have hspineForm :
      selectiveCountCasesSpineCode (value :: rest) =
        Nat.pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest)) := rfl
  have hconsBits :
      natBitLength (Nat.pair value (selectiveCountCasesSpineCode rest)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hspineBits
    rw [hspineForm]
    exact Nat.right_le_pair 1 _
  have hvalueBits : natBitLength value ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair value _)).trans hconsBits
  have htailSpineBits :
      natBitLength (selectiveCountCasesSpineCode rest) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair value _)).trans hconsBits
  have hcodeBits :
      natBitLength (rawCircuitNodeCode (n := n) (.and value accumulated)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hinputBits
    rw [hemitInput]
    exact Nat.right_le_pair _ _
  have hchildrenBits :
      natBitLength (Nat.pair (n + value) (n + accumulated)) ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hcodeBits
    rw [hnodeCode]
    exact Nat.right_le_pair 3 _
  have hleftChildBits : natBitLength (n + value) ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hchildrenBits
  have hrightChildBits : natBitLength (n + accumulated) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hchildrenBits
  have hthreeBits : natBitLength 3 ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hcodeBits
    rw [hnodeCode]
    exact Nat.left_le_pair 3 _
  have hspineNonzero : machine.registers 18 ≠ 0 := by
    rw [hspine, hspineForm]
    have hone :=
      Nat.left_le_pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest))
    omega
  rw [show 10 + (5 + (emitFuel + (7 + extraFuel))) =
    (9 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 57) rfl) hpc]
  rw [if_neg hspineNonzero]
  rw [show 9 + (5 + (emitFuel + (7 + extraFuel))) =
    (8 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair value (selectiveCountCasesSpineCode rest))
    (selectiveClausesProgram_controllerAt (pc := 58) rfl) rfl
    (by simp [NPOracleState.jump, hspine, hspineForm]) hconsBits]
  rw [show 8 + (5 + (emitFuel + (7 + extraFuel))) =
    (7 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_unpairLeft_instruction (value := value)
    (selectiveClausesProgram_controllerAt (pc := 59) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
  rw [show 7 + (5 + (emitFuel + (7 + extraFuel))) =
    (6 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveCountCasesSpineCode rest)
    (selectiveClausesProgram_controllerAt (pc := 60) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
  rw [show 6 + (5 + (emitFuel + (7 + extraFuel))) =
    (5 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_add_instruction (value := n + value)
    (selectiveClausesProgram_controllerAt (pc := 61) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hleftChildBits]
  rw [show 5 + (5 + (emitFuel + (7 + extraFuel))) =
    (4 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_add_instruction (value := n + accumulated)
    (selectiveClausesProgram_controllerAt (pc := 62) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, haccumulated])
    hrightChildBits]
  rw [show 4 + (5 + (emitFuel + (7 + extraFuel))) =
    (3 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (n + value) (n + accumulated))
    (selectiveClausesProgram_controllerAt (pc := 63) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
  rw [show 3 + (5 + (emitFuel + (7 + extraFuel))) =
    (2 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 64) rfl) rfl hthreeBits]
  rw [show 2 + (5 + (emitFuel + (7 + extraFuel))) =
    (1 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.and value accumulated))
    (selectiveClausesProgram_controllerAt (pc := 65) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode]) hcodeBits]
  rw [show 1 + (5 + (emitFuel + (7 + extraFuel))) =
    (5 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 66) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveClausesEmitCall state (.and value accumulated) hordered
    maximumBits emitFuel extraFuel finalOutput n values literalArity
    decisionCode count clauseIndex (selectiveCountCasesSpineCode rest) _
    hemitFuel hinputBits hwireBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump, hremaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump, hnodeCode]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump, hvalues]
  · simp [NPOracleState.write, NPOracleState.jump, hliteralArity]
  · simp [NPOracleState.write, NPOracleState.jump, hdecisionCode]
  · simp [NPOracleState.write, NPOracleState.jump, hcount]
  · simp [NPOracleState.write, NPOracleState.jump, hclauseIndex]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, hzeroRegister]
  · intro resumed hresumedPc hresumedWire _ hresumedRemaining hresumedNext
      hresumedSelected hresumedOutput hresumedArity hresumedValues
      hresumedLiteralArity hresumedDecisionCode hresumedCount
      hresumedClauseIndex hresumedSpine hresumedZero
    refine hcontinue resumed hresumedPc ?_ ?_ ?_ ?_ hresumedArity hresumedValues
      hresumedLiteralArity hresumedDecisionCode hresumedCount
      hresumedClauseIndex hresumedSpine ?_ hresumedZero
    · simpa [selectiveAnd] using hresumedWire
    · simpa [selectiveAnd] using hresumedRemaining
    · simpa [selectiveAnd] using hresumedNext
    · simpa [selectiveAnd] using hresumedSelected
    · simpa [selectiveAnd] using hresumedOutput

-- The fold is one induction on the retained clause spine.
theorem run_selectiveClausesFoldLoop {n : ℕ}
    (spineValues : List ℕ) (state : SelectiveState n) (accumulated : ℕ)
    (hordered : selectiveStateOrdered state) (maximumBits : ℕ)
    (hbits :
      natBitLength
          (selectiveUnaryFoldWorkBound state accumulated spineValues) ≤
        maximumBits)
    (values literalArity decisionCode count clauseIndex : ℕ)
    (machine : NPOracleState) (hpc : machine.pc = 57)
    (hwire :
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hvalues : machine.registers 10 = values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hcount : machine.registers 16 = count)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine : machine.registers 18 = selectiveCountCasesSpineCode spineValues)
    (haccumulated : machine.registers 20 = accumulated)
    (hzeroRegister : machine.registers 29 = 0) :
    runNPOracleProgram selectiveClausesProgram maximumBits
        (selectiveClausesFoldFuel state accumulated spineValues) machine =
      some
        (selectiveWireCode
          (selectiveUnaryFold state accumulated spineValues)) := by
  induction spineValues generalizing state accumulated machine with
  | nil =>
      have hfuel :
          selectiveClausesFoldFuel state accumulated ([] : List ℕ) =
            (0 + 1) + 1 := rfl
      have hfoldNil :
          selectiveWireCode
              (selectiveUnaryFold state accumulated ([] : List ℕ)) =
            Nat.pair (selectiveStateCode state) accumulated := rfl
      rw [hfuel]
      rw [run_branchZero_instruction
        (selectiveClausesProgram_controllerAt (pc := 57) rfl) hpc]
      rw [if_pos (by rw [hspine]; rfl)]
      refine run_halt_instruction (fuel := 0)
        (selectiveClausesProgram_controllerAt (pc := 67) rfl) rfl ?_ ?_
      · rw [hfoldNil]
        exact hwire
      · rw [hfoldNil]
        exact hbits
  | cons value rest ih =>
      have hfuel :
          selectiveClausesFoldFuel state accumulated (value :: rest) =
            10 +
              (5 +
                (selectiveEmitFuel (state.target - state.next)
                    (selectiveSelectedCode state.selected) +
                  (7 +
                    selectiveClausesFoldFuel
                      (selectiveAnd state value accumulated).state
                      (selectiveAnd state value accumulated).output
                      rest))) := rfl
      have hworkCons :
          selectiveUnaryFoldWorkBound state accumulated (value :: rest) =
            max (selectiveCountCasesSpineCode (value :: rest))
              (max
                (selectiveEmitInput (state.target - state.next) state.next
                  (selectiveSelectedCode state.selected)
                  (rawCircuitNodeCode (n := n) (.and value accumulated)))
                (max
                  (Nat.pair 0
                    (selectiveWireCode (selectiveAnd state value accumulated)))
                  (selectiveUnaryFoldWorkBound
                    (selectiveAnd state value accumulated).state
                    (selectiveAnd state value accumulated).output rest))) := rfl
      rw [hworkCons] at hbits
      have hspineBits := (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
      have hbitsTail := (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
      have hinputBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTail
      have hbitsTailTwo :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTail
      have hwireBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTailTwo
      have hrecBits :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTailTwo
      rw [hfuel]
      refine run_selectiveClausesFoldStep state accumulated value rest hordered
        maximumBits _ _ _ values literalArity decisionCode count clauseIndex
        machine rfl hspineBits hinputBits hwireBits hpc hremaining hnext
        hselected harity hvalues hliteralArity hdecisionCode hcount
        hclauseIndex hspine haccumulated hzeroRegister ?_
      intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedValues hresumedLiteralArity
        hresumedDecisionCode hresumedCount hresumedClauseIndex hresumedSpine
        hresumedAccumulated hresumedZero
      exact ih _ _
        (selectiveState_emit_ordered state (.and value accumulated) hordered)
        hrecBits _ hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedValues hresumedLiteralArity
        hresumedDecisionCode hresumedCount hresumedClauseIndex hresumedSpine
        hresumedAccumulated hresumedZero

/-! ## 12. Level 10's forward clause pass

One iteration builds the level-11 request in place from the live registers, runs
the relocated clause compiler, and conses its output onto the private reverse
spine while advancing the clause cursor and countdown together.  The clause
compiler's own run is the single named level premise. -/

-- Ten controller steps into the relocated clause compiler, then a thirteen-step
-- tail that conses the compiled wire and advances both counters.
theorem run_selectiveClausesForwardStep {n literalArity : ℕ}
    {harity : 0 < literalArity}
    (runner : SelectiveClauseRunner n literalArity harity)
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex count : ℕ) (spine : List ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ)
    (machine : NPOracleState)
    (hcalleeFuel :
      calleeFuel = runner.fuel state values decisionCode clauseIndex)
    (hcalleeBits :
      runner.bits state values decisionCode clauseIndex ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveClauseInput (selectiveStateCode state) n
            (encodeTaggedList values) literalArity decisionCode clauseIndex) ≤
        maximumBits)
    (hheadBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileClause state values
                (selectiveClauseOf literalArity harity decisionCode
                  clauseIndex)))) ≤
        maximumBits)
    (hspineBits :
      natBitLength
          (selectiveCountCasesSpineCode
            ((selectiveCompileClause state values
                (selectiveClauseOf literalArity harity decisionCode
                  clauseIndex)).output :: spine)) ≤
        maximumBits)
    (hindexSuccBits : natBitLength (clauseIndex + 1) ≤ maximumBits)
    (hcountBits : natBitLength count ≤ maximumBits)
    (hcountNonzero : count ≠ 0)
    (hpc : machine.pc = 18)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harityRegister : machine.registers 8 = n)
    (hvalues : machine.registers 10 = encodeTaggedList values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hcount : machine.registers 16 = count)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine : machine.registers 18 = selectiveCountCasesSpineCode spine)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 18 →
      resumed.registers 4 =
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).state.target -
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.next →
      resumed.registers 6 =
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.selected →
      resumed.registers 8 = n →
      resumed.registers 10 = encodeTaggedList values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = Nat.pred count →
      resumed.registers 17 = clauseIndex + 1 →
      resumed.registers 18 =
        selectiveCountCasesSpineCode
          ((selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).output :: spine) →
      resumed.registers 29 = 0 →
      runNPOracleProgram selectiveClausesProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClausesProgram maximumBits
        (10 + (calleeFuel + (13 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm : ∀ candidate : SelectiveState n,
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestFlat := hrequestBits
  simp only [selectiveClauseInput] at hrequestFlat
  have hstateBits := natBitLength_pair_left hrequestFlat
  have hfield1 := natBitLength_pair_right hrequestFlat
  have hfield2 := natBitLength_pair_right hfield1
  have hfield3 := natBitLength_pair_right hfield2
  have hfield4 := natBitLength_pair_right hfield3
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hheadFlat := natBitLength_pair_right hheadBits
  have hheadParts := hheadFlat
  simp only [selectiveWireCode] at hheadParts
  have hheadStateBits := natBitLength_pair_left hheadParts
  have hheadOutputBits := natBitLength_pair_right hheadParts
  have hheadStateFlat := hheadStateBits
  rw [hstateForm
    (selectiveCompileClause state values
      (selectiveClauseOf literalArity harity decisionCode
        clauseIndex)).state] at hheadStateFlat
  have hheadRemainingBits := natBitLength_pair_left hheadStateFlat
  have hheadTailBits := natBitLength_pair_right hheadStateFlat
  have hheadNextBits := natBitLength_pair_left hheadTailBits
  have hheadSelectedBits := natBitLength_pair_right hheadTailBits
  have hspineFlat := hspineBits
  simp only [selectiveCountCasesSpineCode] at hspineFlat
  have honeBits := natBitLength_pair_left hspineFlat
  have hconsBits := natBitLength_pair_right hspineFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le 1)).trans honeBits
  have hnextCountBits : natBitLength (Nat.pred count) ≤ maximumBits :=
    (decrement_bits_le count).trans hcountBits
  rw [show 10 + (calleeFuel + (13 + extraFuel)) =
    (9 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 18) rfl) hpc]
  rw [if_neg (by rw [hcount]; exact hcountNonzero)]
  rw [show 9 + (calleeFuel + (13 + extraFuel)) =
    (8 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveClausesProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.jump, hnext, hselected]) hnextSelectedBits]
  rw [show 8 + (calleeFuel + (13 + extraFuel)) =
    (7 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveClausesProgram_controllerAt (pc := 20) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 7 + (calleeFuel + (13 + extraFuel)) =
    (6 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair decisionCode clauseIndex)
    (selectiveClausesProgram_controllerAt (pc := 21) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hdecisionCode,
        hclauseIndex])
    hfield4]
  rw [show 6 + (calleeFuel + (13 + extraFuel)) =
    (5 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair literalArity (Nat.pair decisionCode clauseIndex))
    (selectiveClausesProgram_controllerAt (pc := 22) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hliteralArity]) hfield3]
  rw [show 5 + (calleeFuel + (13 + extraFuel)) =
    (4 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (encodeTaggedList values)
        (Nat.pair literalArity (Nat.pair decisionCode clauseIndex)))
    (selectiveClausesProgram_controllerAt (pc := 23) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hvalues]) hfield2]
  rw [show 4 + (calleeFuel + (13 + extraFuel)) =
    (3 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair n
        (Nat.pair (encodeTaggedList values)
          (Nat.pair literalArity (Nat.pair decisionCode clauseIndex))))
    (selectiveClausesProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harityRegister]) hfield1]
  rw [show 3 + (calleeFuel + (13 + extraFuel)) =
    (2 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveClauseInput (selectiveStateCode state) n
        (encodeTaggedList values) literalArity decisionCode clauseIndex)
    (selectiveClausesProgram_controllerAt (pc := 25) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectiveClauseInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + (13 + extraFuel)) =
    (1 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 26) rfl) rfl hzeroBits]
  rw [show 1 + (calleeFuel + (13 + extraFuel)) =
    (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 27) rfl) rfl]
  simp only [ite_self]
  rw [hcalleeFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveClauseProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode clauseIndex)))
    selectiveClausesProgram_clauseCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro entry hentryPc hentryInput
    refine run_bits_mono
      (runner.executes state values decisionCode clauseIndex hordered entry
        hentryPc ?_) hcalleeBits
    rw [hentryInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hheadBits
  · intro haltState
    rw [show (13 : ℕ) + extraFuel = (12 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode clauseIndex)))
      (selectiveClausesProgram_controllerAt (pc := 28) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hheadFlat]
    rw [show (12 : ℕ) + extraFuel = (11 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state)
      (selectiveClausesProgram_controllerAt (pc := 29) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hheadStateBits]
    rw [show (11 : ℕ) + extraFuel = (10 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).output)
      (selectiveClausesProgram_controllerAt (pc := 30) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hheadOutputBits]
    rw [show (10 : ℕ) + extraFuel = (9 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).state.target -
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.next)
      (selectiveClausesProgram_controllerAt (pc := 31) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm
            (selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).state])
      hheadRemainingBits]
    rw [show (9 : ℕ) + extraFuel = (8 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.next
          (selectiveSelectedCode
            (selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).state.selected))
      (selectiveClausesProgram_controllerAt (pc := 32) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm
            (selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).state])
      hheadTailBits]
    rw [show (8 : ℕ) + extraFuel = (7 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).state.next)
      (selectiveClausesProgram_controllerAt (pc := 33) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hheadNextBits]
    rw [show (7 : ℕ) + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveSelectedCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.selected)
      (selectiveClausesProgram_controllerAt (pc := 34) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hheadSelectedBits]
    rw [show (6 : ℕ) + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).output (selectiveCountCasesSpineCode spine))
      (selectiveClausesProgram_controllerAt (pc := 35) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hspine])
      hconsBits]
    rw [show (5 : ℕ) + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_set_instruction
      (selectiveClausesProgram_controllerAt (pc := 36) rfl) rfl honeBits]
    rw [show (4 : ℕ) + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        selectiveCountCasesSpineCode
          ((selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).output :: spine))
      (selectiveClausesProgram_controllerAt (pc := 37) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          selectiveCountCasesSpineCode])
      hspineBits]
    rw [show (3 : ℕ) + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_increment_instruction (value := clauseIndex + 1)
      (selectiveClausesProgram_controllerAt (pc := 38) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hclauseIndex])
      hindexSuccBits]
    rw [show (2 : ℕ) + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := Nat.pred count)
      (selectiveClausesProgram_controllerAt (pc := 39) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hcount])
      hnextCountBits]
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveClausesProgram_controllerAt (pc := 40) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState,
        harityRegister, hvalues, hliteralArity, hdecisionCode, hzeroRegister]

/-! ## 13. The forward pass's reachability invariant

The controller never materializes the decoded clause list: it walks a cursor and
asks the level-11 callee for one clause at a time.  The predicate below is the
schedule that walk realizes, and it is inhabited by every suffix of the decoded
list — this is the clause-level analogue of the unary compiler's literal
schedule, and it is what a forward-loop induction consumes. -/

/-- The clause schedule a forward pass walks from one starting cursor. -/
inductive SelectiveClausesFrom (literalArity : ℕ) (harity : 0 < literalArity)
    (decisionCode : ℕ) : ℕ → List (Fin 3 → Literal literalArity) → Prop
  | nil (clauseIndex : ℕ) :
      SelectiveClausesFrom literalArity harity decisionCode clauseIndex []
  | cons {clauseIndex : ℕ} {rest : List (Fin 3 → Literal literalArity)}
      (hrest :
        SelectiveClausesFrom literalArity harity decisionCode (clauseIndex + 1)
          rest) :
      SelectiveClausesFrom literalArity harity decisionCode clauseIndex
        (selectiveClauseOf literalArity harity decisionCode clauseIndex :: rest)

private theorem selectiveClausesFrom_drop_aux (literalArity : ℕ)
    (harity : 0 < literalArity) (decisionCode : ℕ) :
    ∀ (budget clauseIndex : ℕ),
      (decodeThreeCNF literalArity decisionCode).clauses.length - clauseIndex ≤
          budget →
      SelectiveClausesFrom literalArity harity decisionCode clauseIndex
        ((decodeThreeCNF literalArity decisionCode).clauses.drop
          clauseIndex) := by
  intro budget
  induction budget with
  | zero =>
      intro clauseIndex hbudget
      rw [List.drop_eq_nil_of_le (by omega)]
      exact .nil _
  | succ budget ih =>
      intro clauseIndex hbudget
      by_cases hlt :
          clauseIndex < (decodeThreeCNF literalArity decisionCode).clauses.length
      · have hget :
            (decodeThreeCNF literalArity decisionCode).clauses[clauseIndex] =
              selectiveClauseOf literalArity harity decisionCode clauseIndex := by
          rw [selectiveClauseOf, List.getD_eq_getElem _ _ hlt]
        rw [List.drop_eq_getElem_cons hlt, hget]
        exact .cons (ih (clauseIndex + 1) (by omega))
      · rw [List.drop_eq_nil_of_le (by omega)]
        exact .nil _

/-- **The forward pass's schedule, inhabited.**  Every suffix of the decoded
clause list is exactly what the controller's cursor enumerates from the matching
starting index. -/
theorem selectiveClausesFrom_drop (literalArity : ℕ)
    (harity : 0 < literalArity) (decisionCode clauseIndex : ℕ) :
    SelectiveClausesFrom literalArity harity decisionCode clauseIndex
      ((decodeThreeCNF literalArity decisionCode).clauses.drop clauseIndex) :=
  selectiveClausesFrom_drop_aux literalArity harity decisionCode
    ((decodeThreeCNF literalArity decisionCode).clauses.length - clauseIndex)
    clauseIndex (Nat.le_refl _)

/-- The whole decoded clause list is the schedule from cursor zero. -/
theorem selectiveClausesFrom_zero (literalArity : ℕ)
    (harity : 0 < literalArity) (decisionCode : ℕ) :
    SelectiveClausesFrom literalArity harity decisionCode 0
      (decodeThreeCNF literalArity decisionCode).clauses := by
  simpa using selectiveClausesFrom_drop literalArity harity decisionCode 0

end NearCubicWires.BoundedOracleStructuralSelectiveProgram

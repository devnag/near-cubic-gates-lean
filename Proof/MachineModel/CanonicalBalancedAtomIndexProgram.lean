import Proof.Circuits.CanonicalBalancedTraversal

/-!
# Indexed access to the atoms of an arbitrary balanced tree

`CanonicalBalancedValidationProgram`'s midpoint canonicalizer flattens a
structural balanced tree to `encodeTaggedList tree.atoms` before rebuilding.
`ValidatorTaggedIntermediateVerdict` §3 shows that intermediate is fatal: the
tagged codec nests one pairing per *public* atom, so the canonicalizer's charge
is at least `2 ^ tree.atoms.length` at a value the flattener actually returns.

The repair replaces the linked intermediate by **indexing**.  This module
supplies the two traversal-driven stages that make indexing possible without
ever materializing a cons list:

* `balancedAtomCountProgram` — the atom count, folded off the shared
  `balancedTraversalController`, returned paired with the untouched input code;

* `balancedAtomSelectProgram` — the atom at one index, with the index arriving
  in the traversal's *native input length* register.  That is the register the
  balanced-call request ABI writes from a request's left component, so the
  selector is a drop-in callee of `CanonicalBalancedCall`.

Both stages thread exactly one fold register, so both are enterable at `pc = 0`
from `initialNPOracleState` and neither needs a prologue.  The counting state
is a bare counter and the selecting state is the packed pair

> `r9 = Nat.pair (atoms seen so far) (the atom chosen so far)`,

whose zero value `Nat.pair 0 0 = 0` is exactly the machine's zero-initialised
register.

Neither charge mentions `encodeTaggedList` of a public-length list: the only
list-shaped value either program materializes is the traversal's own
continuation stack, whose depth is the input tree's height.

* §1 shared machinery: the controller's terminal branch.

* §2 the atom counter.

* §3 the atom selector, and the pure list semantics of its fold.
-/

namespace NearCubicWires.CanonicalBalancedAtomIndexProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces

private theorem natBitLength_mono' {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.succ_le_succ (Nat.log_mono_right hle)

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

private theorem pair_zero_zero : Nat.pair 0 0 = 0 := by
  simp [Nat.pair]

theorem map_self_code (tree : BalancedTraversalTree) :
    (tree.map fun value => value).code = tree.code := by
  induction tree with
  | empty => rfl
  | leaf atom => rfl
  | branch left right leftHypothesis rightHypothesis =>
      simp only [BalancedTraversalTree.map, BalancedTraversalTree.code,
        leftHypothesis, rightHypothesis]

/-! ## §1 The controller's terminal branch -/

/-- `run_balancedTraversalFold_subtreeWithin` stops at the controller's empty
stack test.  One further instruction takes it to the consumer's `donePc`. -/
theorem runsTo_doneBranch
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 15) (hstack : state.registers 2 = 0) :
    RunsToIn program maximumBits 1 state (state.jump donePc) := by
  have hlookup : program[15]? = some (.branchZero 2 donePc 16) :=
    hat 15 _ (balancedTraversalController_doneBranch leafPc donePc)
  intro extra
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_branchZero_instruction hlookup hpc]
  rw [hstack]
  simp

/-! ## §2 The atom counter -/

/-- Counting needs no packing: the fold register is the count itself, and the
machine's zero register is the correct empty count. -/
def atomCountFoldStep (packed _atom : ℕ) : ℕ := packed + 1

def atomCountLeafBudget (_packed _atom : ℕ) : ℕ := 1

def atomCountLeafRequiredBits (packed _atom : ℕ) : ℕ :=
  natBitLength (packed + 1)

theorem foldl_atomCountFoldStep (atoms : List ℕ) (start : ℕ) :
    atoms.foldl atomCountFoldStep start = start + atoms.length := by
  induction atoms generalizing start with
  | nil => simp
  | cons atom rest inductionHypothesis =>
      simp only [List.foldl_cons, atomCountFoldStep, List.length_cons]
      rw [inductionHypothesis]
      omega

theorem balancedFoldLeafSteps_atomCount (atoms : List ℕ) (start : ℕ) :
    balancedFoldLeafSteps atomCountFoldStep atomCountLeafBudget start atoms =
      atoms.length := by
  induction atoms generalizing start with
  | nil => simp [balancedFoldLeafSteps]
  | cons atom rest inductionHypothesis =>
      simp only [balancedFoldLeafSteps, atomCountLeafBudget, List.length_cons]
      rw [inductionHypothesis]
      omega

/-- The shared controller, a one-instruction leaf handler, and a two
instruction epilogue that returns the count beside the untouched input. -/
def balancedAtomCountProgram : NPOracleProgram :=
  balancedTraversalController 34 35 ++
    [ .increment 9 balancedTraversalLeafReturnPc
    , .pair 9 0 0 36
    , .halt 0
    ]

@[simp] theorem balancedAtomCountProgram_oracleFree :
    OracleFree balancedAtomCountProgram := by
  rfl

theorem balancedAtomCountProgram_controllerAt :
    BalancedTraversalControllerAt balancedAtomCountProgram 34 35 := by
  intro pc instruction hlookup
  have hpc : pc < (balancedTraversalController 34 35).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [balancedAtomCountProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

private theorem run_atomCountLeaf
    {maximumBits : ℕ} (entry : NPOracleState) (atom : ℕ)
    (hpc : entry.pc = 34)
    (hatom : entry.registers 3 = atom)
    (hbits :
      atomCountLeafRequiredBits (entry.registers 9) atom ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedAtomCountProgram maximumBits 1 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 0 = entry.registers 0 ∧
      finish.registers 2 = entry.registers 2 ∧
      finish.registers 3 = atom ∧
      finish.registers 9 = atomCountFoldStep (entry.registers 9) atom ∧
      SameTraversalContextFrom 10 entry finish := by
  let finish :=
    (entry.write 9 (entry.registers 9 + 1)).jump balancedTraversalLeafReturnPc
  have hruns :
      RunsToIn balancedAtomCountProgram maximumBits 1 entry finish := by
    intro extra
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_increment_instruction (fuel := extra)
      (value := entry.registers 9 + 1) (by rfl) hpc rfl
      (by simpa [atomCountLeafRequiredBits] using hbits)]
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · simp [finish, NPOracleState.write, NPOracleState.jump, hatom]
  · simp [finish, NPOracleState.write, NPOracleState.jump, atomCountFoldStep]
  · refine ⟨?_, ?_⟩
    · simp [finish, NPOracleState.write, NPOracleState.jump]
    · intro register hregister
      have hnine : register ≠ 9 := by omega
      simp [finish, NPOracleState.write, NPOracleState.jump, hnine]

private theorem atomCountFoldFits
    (maximumBits : ℕ) (atoms : List ℕ) (start : ℕ)
    (hbits : natBitLength (start + atoms.length) ≤ maximumBits) :
    BalancedFoldFits maximumBits atomCountFoldStep start atoms ∧
      BalancedFoldLeafFits maximumBits atomCountFoldStep
        atomCountLeafRequiredBits start atoms := by
  induction atoms generalizing start with
  | nil =>
      refine ⟨?_, trivial⟩
      simpa [BalancedFoldFits] using hbits
  | cons atom rest inductionHypothesis =>
      simp only [List.length_cons] at hbits
      have hstart : natBitLength start ≤ maximumBits :=
        (natBitLength_mono' (by omega)).trans hbits
      have hnext : natBitLength (start + 1) ≤ maximumBits :=
        (natBitLength_mono' (by omega)).trans hbits
      have htail : natBitLength (start + 1 + rest.length) ≤ maximumBits := by
        rw [show start + 1 + rest.length = start + (rest.length + 1) by omega]
        exact hbits
      rcases inductionHypothesis (start + 1) htail with ⟨hfold, hleaf⟩
      refine ⟨?_, ?_⟩
      · simp only [BalancedFoldFits, atomCountFoldStep]
        exact ⟨hstart, hnext, hfold⟩
      · simp only [BalancedFoldLeafFits, atomCountFoldStep,
          atomCountLeafRequiredBits]
        exact ⟨hnext, hleaf⟩

def balancedAtomCountFuel (tree : BalancedTraversalTree) : ℕ :=
  balancedTraversalStructuralSteps tree + tree.atoms.length + 3

/-- The counter's charge: one balanced-traversal charge over the input tree,
the count, and the returned pair.  No tagged public list appears. -/
def balancedAtomCountBits
    (inputLength : ℕ) (tree : BalancedTraversalTree) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedTraversalRequiredBits (fun value => value) tree []) <|
      max (natBitLength tree.atoms.length)
        (natBitLength (Nat.pair tree.atoms.length tree.code))

/-- **The atom counter, executed.**  The input code is returned untouched
beside its atom count, which is exactly `generatedBalancedRangeInput`. -/
theorem run_balancedAtomCountProgram
    (inputLength : ℕ) (tree : BalancedTraversalTree) :
    runNPOracleProgram balancedAtomCountProgram
        (balancedAtomCountBits inputLength tree)
        (balancedAtomCountFuel tree)
        (initialNPOracleState inputLength tree.code) =
      some (Nat.pair tree.atoms.length tree.code) := by
  let maximumBits := balancedAtomCountBits inputLength tree
  let initial := initialNPOracleState inputLength tree.code
  have hnine : initial.registers 9 = 0 := by
    simp [initial, initialNPOracleState]
  have hrequired :
      balancedTraversalRequiredBits (fun value => value) tree [] ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfit :
      BalancedTraversalFits maximumBits (fun value => value) tree [] :=
    (balancedTraversalRequiredBits_le_iff maximumBits (fun value => value)
      tree []).mp hrequired
  have hcount : natBitLength tree.atoms.length ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have houtput :
      natBitLength (Nat.pair tree.atoms.length tree.code) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  rcases atomCountFoldFits maximumBits tree.atoms 0 (by simpa using hcount)
    with ⟨hfoldFit, hleafFit⟩
  have hwithin :=
    run_balancedTraversalFold_subtreeWithin atomCountFoldStep
      atomCountLeafBudget atomCountLeafRequiredBits tree [] initial
      inputLength 10 (le_refl 10)
      balancedAtomCountProgram_controllerAt
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      (by
        simp [initial, initialNPOracleState, encodeBalancedTraversalStack,
          encodeTaggedList])
      (by simp [initial, initialNPOracleState])
      hfit
      (by rw [hnine]; exact hfoldFit)
      (by rw [hnine]; exact hleafFit)
      (by
        intro atom _hmem entry hentryPc _hcurrent hatom _hinputLength
          _haccumulator _hresult hleafRequired
        rcases run_atomCountLeaf (maximumBits := maximumBits) entry atom
            hentryPc hatom hleafRequired with
          ⟨finish, hruns, hfinishPc, hzero, htwo, hthree, hnineValue,
            hcontext⟩
        refine hruns.toRunsWithin.mono ?_
        intro candidate hcandidate
        subst candidate
        exact ⟨hfinishPc, hzero, htwo, hthree, hnineValue, hcontext⟩)
  rw [hnine] at hwithin
  rw [balancedFoldLeafSteps_atomCount tree.atoms 0] at hwithin
  change
    runNPOracleProgram balancedAtomCountProgram maximumBits
        (balancedAtomCountFuel tree) initial =
      some (Nat.pair tree.atoms.length tree.code)
  rw [show balancedAtomCountFuel tree =
      (balancedTraversalStructuralSteps tree + tree.atoms.length) + 3 by
    simp [balancedAtomCountFuel]]
  apply hwithin 3 (Nat.pair tree.atoms.length tree.code)
  intro finish unused hfinish
  have hstack : finish.registers 2 = 0 := by
    simpa [encodeBalancedTraversalStack, encodeTaggedList] using
      hfinish.2.2.1
  have hcode : finish.registers 0 = tree.code := by
    rw [hfinish.2.1, map_self_code]
  have hcounter : finish.registers 9 = tree.atoms.length := by
    rw [hfinish.2.2.2.1, foldl_atomCountFoldStep]
    omega
  rw [show unused + 3 = ((unused + 1) + 1) + 1 by omega]
  rw [run_branchZero_instruction (fuel := (unused + 1) + 1) (by rfl) hfinish.1]
  rw [hstack]
  rw [run_pair_instruction (fuel := unused + 1)
    (value := Nat.pair tree.atoms.length tree.code) (by rfl) rfl
    (by simp only [NPOracleState.jump]; rw [hcounter, hcode]) houtput]
  exact run_halt_instruction (fuel := unused) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## §3 The atom selector -/

/-- The packed selecting state: the number of atoms visited so far and the
atom chosen so far.  `Nat.pair 0 0 = 0`, so the machine's zero register is the
correct starting state. -/
def atomSelectFoldStep (index packed atom : ℕ) : ℕ :=
  Nat.pair ((Nat.unpair packed).1 + 1)
    (if (Nat.unpair packed).1 = index then atom else (Nat.unpair packed).2)

/-- The chosen atom, as a pure function of the visited list. -/
def atomSelectValue (index : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | _seen, result, [] => result
  | seen, result, atom :: atoms =>
      atomSelectValue index (seen + 1)
        (if seen = index then atom else result) atoms

theorem foldl_atomSelectFoldStep
    (index : ℕ) (atoms : List ℕ) (seen result : ℕ) :
    atoms.foldl (atomSelectFoldStep index) (Nat.pair seen result) =
      Nat.pair (seen + atoms.length)
        (atomSelectValue index seen result atoms) := by
  induction atoms generalizing seen result with
  | nil => simp [atomSelectValue]
  | cons atom rest inductionHypothesis =>
      simp only [List.foldl_cons, atomSelectFoldStep, Nat.unpair_pair,
        List.length_cons, atomSelectValue]
      rw [inductionHypothesis]
      congr 1
      omega

theorem foldl_atomSelectFoldStep_zero (index : ℕ) (atoms : List ℕ) :
    atoms.foldl (atomSelectFoldStep index) 0 =
      Nat.pair atoms.length (atomSelectValue index 0 0 atoms) := by
  have hfold := foldl_atomSelectFoldStep index atoms 0 0
  rw [pair_zero_zero] at hfold
  simpa using hfold

theorem atomSelectValue_of_lt
    (index : ℕ) (atoms : List ℕ) (seen result : ℕ) (hlt : index < seen) :
    atomSelectValue index seen result atoms = result := by
  induction atoms generalizing seen result with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp only [atomSelectValue, if_neg (by omega : ¬ seen = index)]
      exact inductionHypothesis (seen + 1) result (by omega)

theorem atomSelectValue_getD
    (index : ℕ) (atoms : List ℕ) (seen result : ℕ)
    (hlow : seen ≤ index) (hhigh : index < seen + atoms.length) :
    atomSelectValue index seen result atoms = atoms.getD (index - seen) 0 := by
  induction atoms generalizing seen result with
  | nil => simp at hhigh; omega
  | cons atom rest inductionHypothesis =>
      simp only [List.length_cons] at hhigh
      by_cases hequal : seen = index
      · have hzero : index - seen = 0 := by omega
        simp only [atomSelectValue, if_pos hequal]
        rw [atomSelectValue_of_lt index rest (seen + 1) atom (by omega)]
        rw [hzero]
        simp
      · have hstrict : seen + 1 ≤ index := by omega
        simp only [atomSelectValue, if_neg hequal]
        rw [inductionHypothesis (seen + 1) result hstrict (by omega)]
        have hpositive : 0 < index - seen := by omega
        rw [show index - seen = (index - (seen + 1)) + 1 by omega]
        simp [List.getD]

/-- The chosen atom at the machine's zero starting state. -/
theorem atomSelectValue_zero
    (index : ℕ) (atoms : List ℕ) (hindex : index < atoms.length) :
    atomSelectValue index 0 0 atoms = atoms.getD index 0 := by
  have hvalue := atomSelectValue_getD index atoms 0 0 (Nat.zero_le _) (by omega)
  simpa using hvalue

/-- Reading every index of a list rebuilds the list. -/
theorem map_range_getD (atoms : List ℕ) :
    (List.range atoms.length).map (fun index => atoms.getD index 0) =
      atoms := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using hright)]

private def atomSelectWidths (index packed atom : ℕ) : List ℕ :=
  [ natBitLength packed
  , natBitLength (Nat.unpair packed).1
  , natBitLength (Nat.unpair packed).2
  , natBitLength ((Nat.unpair packed).1 - index)
  , natBitLength (index - (Nat.unpair packed).1)
  , natBitLength
      (((Nat.unpair packed).1 - index) + (index - (Nat.unpair packed).1))
  , natBitLength atom
  , natBitLength ((Nat.unpair packed).1 + 1)
  , natBitLength (atomSelectFoldStep index packed atom)
  ]

/-- Every register width the selecting leaf handler demands. -/
def atomSelectLeafRequiredBits (index packed atom : ℕ) : ℕ :=
  (atomSelectWidths index packed atom).foldr max 0

def atomSelectLeafBudget (_packed _atom : ℕ) : ℕ := 9

private theorem atomSelectWidth_le
    {index packed atom maximumBits width : ℕ}
    (hmem : width ∈ atomSelectWidths index packed atom)
    (hbits : atomSelectLeafRequiredBits index packed atom ≤ maximumBits) :
    width ≤ maximumBits :=
  (le_foldr_max_of_mem hmem).trans hbits

/-- The shared controller, a nine-instruction leaf handler that compares the
visit counter with the native input length, and a two-instruction epilogue
projecting the chosen atom out of the packed register. -/
def balancedAtomSelectProgram : NPOracleProgram :=
  balancedTraversalController 34 44 ++
    [ .unpairLeft 9 4 35
    , .unpairRight 9 5 36
    , .subtract 4 1 6 37
    , .subtract 1 4 7 38
    , .add 6 7 6 39
    , .branchZero 6 40 41
    , .copy 3 5 42
    , .branchZero 6 42 42
    , .increment 4 43
    , .pair 4 5 9 balancedTraversalLeafReturnPc
    , .unpairRight 9 0 45
    , .halt 0
    ]

@[simp] theorem balancedAtomSelectProgram_oracleFree :
    OracleFree balancedAtomSelectProgram := by
  rfl

theorem balancedAtomSelectProgram_controllerAt :
    BalancedTraversalControllerAt balancedAtomSelectProgram 34 44 := by
  intro pc instruction hlookup
  have hpc : pc < (balancedTraversalController 34 44).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [balancedAtomSelectProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

private theorem run_atomSelectTail
    {maximumBits : ℕ} (entry : NPOracleState) (seen chosen : ℕ)
    (hpc : entry.pc = 42)
    (hseen : entry.registers 4 = seen)
    (hchosen : entry.registers 5 = chosen)
    (hsucc : natBitLength (seen + 1) ≤ maximumBits)
    (hpacked : natBitLength (Nat.pair (seen + 1) chosen) ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedAtomSelectProgram maximumBits 2 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 9 = Nat.pair (seen + 1) chosen ∧
      ∀ register, register ≠ 4 → register ≠ 9 →
        finish.registers register = entry.registers register := by
  let state1 := (entry.write 4 (seen + 1)).jump 43
  let finish :=
    (state1.write 9 (Nat.pair (seen + 1) chosen)).jump
      balancedTraversalLeafReturnPc
  have hruns :
      RunsToIn balancedAtomSelectProgram maximumBits 2 entry finish := by
    intro extra
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_increment_instruction (fuel := 1 + extra) (value := seen + 1)
      (by rfl) hpc (by rw [hseen]) hsucc]
    change
      runNPOracleProgram balancedAtomSelectProgram maximumBits
          (1 + extra) state1 =
        runNPOracleProgram balancedAtomSelectProgram maximumBits extra finish
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_pair_instruction (fuel := extra)
      (value := Nat.pair (seen + 1) chosen) (by rfl) rfl
      (by
        simp [state1, NPOracleState.write, NPOracleState.jump, hchosen])
      hpacked]
  refine ⟨finish, hruns, rfl, ?_, ?_⟩
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · intro register hfour hnine
    simp [finish, state1, NPOracleState.write, NPOracleState.jump, hfour,
      hnine]

private theorem run_atomSelectLeaf
    {maximumBits : ℕ} (entry : NPOracleState) (index atom : ℕ)
    (hpc : entry.pc = 34)
    (hatom : entry.registers 3 = atom)
    (hindex : entry.registers 1 = index)
    (hbits :
      atomSelectLeafRequiredBits index (entry.registers 9) atom ≤
        maximumBits) :
    ∃ finish,
      RunsToIn balancedAtomSelectProgram maximumBits 9 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 0 = entry.registers 0 ∧
      finish.registers 2 = entry.registers 2 ∧
      finish.registers 3 = atom ∧
      finish.registers 9 = atomSelectFoldStep index (entry.registers 9) atom ∧
      SameTraversalContextFrom 10 entry finish := by
  set packed := entry.registers 9 with hpacked
  set seen := (Nat.unpair packed).1 with hseen
  set result := (Nat.unpair packed).2 with hresult
  have hseenBits : natBitLength seen ≤ maximumBits :=
    atomSelectWidth_le (by simp [atomSelectWidths, hseen]) hbits
  have hresultBits : natBitLength result ≤ maximumBits :=
    atomSelectWidth_le (by simp [atomSelectWidths, hresult]) hbits
  have hleftBits : natBitLength (seen - index) ≤ maximumBits :=
    atomSelectWidth_le (by simp [atomSelectWidths, hseen]) hbits
  have hrightBits : natBitLength (index - seen) ≤ maximumBits :=
    atomSelectWidth_le (by simp [atomSelectWidths, hseen]) hbits
  have hgapBits :
      natBitLength ((seen - index) + (index - seen)) ≤ maximumBits :=
    atomSelectWidth_le (by simp [atomSelectWidths, hseen]) hbits
  have hatomBits : natBitLength atom ≤ maximumBits :=
    atomSelectWidth_le (by simp [atomSelectWidths]) hbits
  have hsuccBits : natBitLength (seen + 1) ≤ maximumBits :=
    atomSelectWidth_le (by simp [atomSelectWidths, hseen]) hbits
  have hstepBits :
      natBitLength (atomSelectFoldStep index packed atom) ≤ maximumBits :=
    atomSelectWidth_le (by simp [atomSelectWidths]) hbits
  let state1 := (entry.write 4 seen).jump 35
  let state2 := (state1.write 5 result).jump 36
  let state3 := (state2.write 6 (seen - index)).jump 37
  let state4 := (state3.write 7 (index - seen)).jump 38
  let state5 := (state4.write 6 ((seen - index) + (index - seen))).jump 39
  have hprefix :
      RunsToIn balancedAtomSelectProgram maximumBits 5 entry state5 := by
    intro extra
    rw [show 5 + extra = (4 + extra) + 1 by omega]
    rw [run_unpairLeft_instruction (fuel := 4 + extra) (value := seen)
      (by rfl) hpc rfl hseenBits]
    change
      runNPOracleProgram balancedAtomSelectProgram maximumBits
          (4 + extra) state1 =
        runNPOracleProgram balancedAtomSelectProgram maximumBits extra state5
    rw [show 4 + extra = (3 + extra) + 1 by omega]
    rw [run_unpairRight_instruction (fuel := 3 + extra) (value := result)
      (by rfl) rfl
      (by
        simp [state1, NPOracleState.write, NPOracleState.jump, hresult,
          hpacked])
      hresultBits]
    change
      runNPOracleProgram balancedAtomSelectProgram maximumBits
          (3 + extra) state2 =
        runNPOracleProgram balancedAtomSelectProgram maximumBits extra state5
    rw [show 3 + extra = (2 + extra) + 1 by omega]
    rw [run_subtract_instruction (fuel := 2 + extra) (value := seen - index)
      (by rfl) rfl
      (by
        simp [state2, state1, NPOracleState.write, NPOracleState.jump,
          hindex])
      hleftBits]
    change
      runNPOracleProgram balancedAtomSelectProgram maximumBits
          (2 + extra) state3 =
        runNPOracleProgram balancedAtomSelectProgram maximumBits extra state5
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_subtract_instruction (fuel := 1 + extra) (value := index - seen)
      (by rfl) rfl
      (by
        simp [state3, state2, state1, NPOracleState.write,
          NPOracleState.jump, hindex])
      hrightBits]
    change
      runNPOracleProgram balancedAtomSelectProgram maximumBits
          (1 + extra) state4 =
        runNPOracleProgram balancedAtomSelectProgram maximumBits extra state5
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_add_instruction (fuel := extra)
      (value := (seen - index) + (index - seen)) (by rfl) rfl
      (by
        simp [state4, state3, state2, state1, NPOracleState.write,
          NPOracleState.jump])
      hgapBits]
  have hstate5Gap :
      state5.registers 6 = (seen - index) + (index - seen) := by
    simp [state5, NPOracleState.write, NPOracleState.jump]
  have hstate5Seen : state5.registers 4 = seen := by
    simp [state5, state4, state3, state2, state1, NPOracleState.write,
      NPOracleState.jump]
  have hstate5Result : state5.registers 5 = result := by
    simp [state5, state4, state3, state2, state1, NPOracleState.write,
      NPOracleState.jump]
  have hstate5Atom : state5.registers 3 = atom := by
    simp [state5, state4, state3, state2, state1, NPOracleState.write,
      NPOracleState.jump, hatom]
  by_cases hequal : seen = index
  · let state6 := state5.jump 40
    let state7 := (state6.write 5 atom).jump 42
    have hzeroGap : (seen - index) + (index - seen) = 0 := by omega
    have hbranch :
        RunsToIn balancedAtomSelectProgram maximumBits 2 state5 state7 := by
      intro extra
      rw [show 2 + extra = (1 + extra) + 1 by omega]
      rw [run_branchZero_instruction (fuel := 1 + extra) (by rfl) rfl]
      rw [hstate5Gap, hzeroGap]
      change
        runNPOracleProgram balancedAtomSelectProgram maximumBits
            (1 + extra) state6 =
          runNPOracleProgram balancedAtomSelectProgram maximumBits extra
            state7
      rw [show 1 + extra = extra + 1 by omega]
      rw [run_copy_instruction (fuel := extra) (value := atom) (by rfl) rfl
        (by simp [state6, NPOracleState.jump, hstate5Atom]) hatomBits]
    rcases run_atomSelectTail (maximumBits := maximumBits) state7 seen atom
        rfl
        (by
          simp [state7, state6, NPOracleState.write, NPOracleState.jump,
            hstate5Seen])
        (by simp [state7, NPOracleState.write, NPOracleState.jump])
        hsuccBits
        (by
          have hstep :
              atomSelectFoldStep index packed atom =
                Nat.pair (seen + 1) atom := by
            simp only [atomSelectFoldStep, ← hseen, ← hresult, if_pos hequal]
          rwa [hstep] at hstepBits) with
      ⟨finish, htailRuns, hfinishPc, hfinishNine, hfinishOther⟩
    refine ⟨finish, ?_, hfinishPc, ?_, ?_, ?_, ?_, ?_⟩
    · have hcombined := (hprefix.trans hbranch).trans htailRuns
      simpa using hcombined
    · rw [hfinishOther 0 (by omega) (by omega)]
      simp [state7, state6, state5, state4, state3, state2, state1,
        NPOracleState.write, NPOracleState.jump]
    · rw [hfinishOther 2 (by omega) (by omega)]
      simp [state7, state6, state5, state4, state3, state2, state1,
        NPOracleState.write, NPOracleState.jump]
    · rw [hfinishOther 3 (by omega) (by omega)]
      simp [state7, state6, NPOracleState.write, NPOracleState.jump,
        hstate5Atom]
    · rw [hfinishNine]
      simp only [atomSelectFoldStep, ← hseen, ← hresult, if_pos hequal]
    · refine ⟨?_, ?_⟩
      · rw [hfinishOther 1 (by omega) (by omega)]
        simp [state7, state6, state5, state4, state3, state2, state1,
          NPOracleState.write, NPOracleState.jump]
      · intro register hregister
        rw [hfinishOther register (by omega) (by omega)]
        simp [state7, state6, state5, state4, state3, state2, state1,
          NPOracleState.write, NPOracleState.jump,
          show register ≠ 4 by omega, show register ≠ 5 by omega,
          show register ≠ 6 by omega, show register ≠ 7 by omega]
  · let state6 := state5.jump 41
    let state7 := state6.jump 42
    have hnonzeroGap : (seen - index) + (index - seen) ≠ 0 := by omega
    have hbranch :
        RunsToIn balancedAtomSelectProgram maximumBits 2 state5 state7 := by
      intro extra
      rw [show 2 + extra = (1 + extra) + 1 by omega]
      rw [run_branchZero_instruction (fuel := 1 + extra) (by rfl) rfl]
      rw [hstate5Gap]
      simp only [if_neg hnonzeroGap]
      change
        runNPOracleProgram balancedAtomSelectProgram maximumBits
            (1 + extra) state6 =
          runNPOracleProgram balancedAtomSelectProgram maximumBits extra
            state7
      rw [show 1 + extra = extra + 1 by omega]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
      simp only [state7]
      congr 1
      simp [state6, NPOracleState.jump]
    rcases run_atomSelectTail (maximumBits := maximumBits) state7 seen result
        rfl
        (by simp [state7, state6, NPOracleState.jump, hstate5Seen])
        (by simp [state7, state6, NPOracleState.jump, hstate5Result])
        hsuccBits
        (by
          have hstep :
              atomSelectFoldStep index packed atom =
                Nat.pair (seen + 1) result := by
            simp only [atomSelectFoldStep, ← hseen, ← hresult, if_neg hequal]
          rwa [hstep] at hstepBits) with
      ⟨finish, htailRuns, hfinishPc, hfinishNine, hfinishOther⟩
    refine ⟨finish, ?_, hfinishPc, ?_, ?_, ?_, ?_, ?_⟩
    · have hcombined := (hprefix.trans hbranch).trans htailRuns
      simpa using hcombined
    · rw [hfinishOther 0 (by omega) (by omega)]
      simp [state7, state6, state5, state4, state3, state2, state1,
        NPOracleState.write, NPOracleState.jump]
    · rw [hfinishOther 2 (by omega) (by omega)]
      simp [state7, state6, state5, state4, state3, state2, state1,
        NPOracleState.write, NPOracleState.jump]
    · rw [hfinishOther 3 (by omega) (by omega)]
      simp [state7, state6, NPOracleState.jump, hstate5Atom]
    · rw [hfinishNine]
      simp only [atomSelectFoldStep, ← hseen, ← hresult, if_neg hequal]
    · refine ⟨?_, ?_⟩
      · rw [hfinishOther 1 (by omega) (by omega)]
        simp [state7, state6, state5, state4, state3, state2, state1,
          NPOracleState.write, NPOracleState.jump]
      · intro register hregister
        rw [hfinishOther register (by omega) (by omega)]
        simp [state7, state6, state5, state4, state3, state2, state1,
          NPOracleState.write, NPOracleState.jump,
          show register ≠ 4 by omega, show register ≠ 5 by omega,
          show register ≠ 6 by omega, show register ≠ 7 by omega]

theorem balancedFoldLeafSteps_atomSelect
    (index : ℕ) (atoms : List ℕ) (packed : ℕ) :
    balancedFoldLeafSteps (atomSelectFoldStep index) atomSelectLeafBudget
        packed atoms =
      9 * atoms.length := by
  induction atoms generalizing packed with
  | nil => simp [balancedFoldLeafSteps]
  | cons atom rest inductionHypothesis =>
      simp only [balancedFoldLeafSteps, atomSelectLeafBudget, List.length_cons]
      rw [inductionHypothesis]
      ring

/-- Every register width the selecting fold materializes along its own
accumulator trace. -/
def atomSelectTraceBits (index : ℕ) : ℕ → List ℕ → ℕ
  | packed, [] => natBitLength packed
  | packed, atom :: atoms =>
      max (atomSelectLeafRequiredBits index packed atom)
        (atomSelectTraceBits index (atomSelectFoldStep index packed atom)
          atoms)

private theorem atomSelectTraceFits
    (index maximumBits packed : ℕ) (atoms : List ℕ)
    (htrace : atomSelectTraceBits index packed atoms ≤ maximumBits) :
    BalancedFoldFits maximumBits (atomSelectFoldStep index) packed atoms ∧
      BalancedFoldLeafFits maximumBits (atomSelectFoldStep index)
        (atomSelectLeafRequiredBits index) packed atoms := by
  induction atoms generalizing packed with
  | nil =>
      simpa [atomSelectTraceBits, BalancedFoldFits, BalancedFoldLeafFits]
        using htrace
  | cons atom rest inductionHypothesis =>
      have hrequired :
          atomSelectLeafRequiredBits index packed atom ≤ maximumBits :=
        (Nat.le_max_left _ _).trans htrace
      have htail :
          atomSelectTraceBits index (atomSelectFoldStep index packed atom)
              rest ≤ maximumBits :=
        (Nat.le_max_right _ _).trans htrace
      have hpackedBits : natBitLength packed ≤ maximumBits :=
        atomSelectWidth_le (by simp [atomSelectWidths]) hrequired
      have hstepBits :
          natBitLength (atomSelectFoldStep index packed atom) ≤ maximumBits :=
        atomSelectWidth_le (by simp [atomSelectWidths]) hrequired
      rcases inductionHypothesis (atomSelectFoldStep index packed atom) htail
        with ⟨hfoldTail, hleafTail⟩
      exact
        ⟨by
          simp only [BalancedFoldFits]
          exact ⟨hpackedBits, hstepBits, hfoldTail⟩,
        by
          simp only [BalancedFoldLeafFits]
          exact ⟨hrequired, hleafTail⟩⟩

def balancedAtomSelectFuel (tree : BalancedTraversalTree) : ℕ :=
  balancedTraversalStructuralSteps tree + 9 * tree.atoms.length + 3

/-- The selector's charge: one balanced-traversal charge over the input tree
and one fold trace.  Neither mentions `encodeTaggedList` of the atom list. -/
def balancedAtomSelectBits
    (index : ℕ) (tree : BalancedTraversalTree) : ℕ :=
  max 1 <| max (natBitLength index) <|
    max (balancedTraversalRequiredBits (fun value => value) tree [])
      (atomSelectTraceBits index 0 tree.atoms)

/-- **The atom selector, executed.**  The index arrives as the native input
length, which is exactly what the balanced-call request ABI writes from a
request's left component. -/
theorem run_balancedAtomSelectProgram
    (index : ℕ) (tree : BalancedTraversalTree) :
    runNPOracleProgram balancedAtomSelectProgram
        (balancedAtomSelectBits index tree)
        (balancedAtomSelectFuel tree)
        (initialNPOracleState index tree.code) =
      some (atomSelectValue index 0 0 tree.atoms) := by
  let maximumBits := balancedAtomSelectBits index tree
  let initial := initialNPOracleState index tree.code
  have hnine : initial.registers 9 = 0 := by
    simp [initial, initialNPOracleState]
  have hrequired :
      balancedTraversalRequiredBits (fun value => value) tree [] ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfit :
      BalancedTraversalFits maximumBits (fun value => value) tree [] :=
    (balancedTraversalRequiredBits_le_iff maximumBits (fun value => value)
      tree []).mp hrequired
  have htrace : atomSelectTraceBits index 0 tree.atoms ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  rcases atomSelectTraceFits index maximumBits 0 tree.atoms htrace with
    ⟨hfoldFit, hleafFit⟩
  have hfinalBits :
      natBitLength (atomSelectValue index 0 0 tree.atoms) ≤ maximumBits := by
    have hfold := hfoldFit.final
    rw [foldl_atomSelectFoldStep_zero] at hfold
    exact (natBitLength_mono' (Nat.right_le_pair _ _)).trans hfold
  have hwithin :=
    run_balancedTraversalFold_subtreeWithin (atomSelectFoldStep index)
      atomSelectLeafBudget (atomSelectLeafRequiredBits index) tree []
      initial index 10 (le_refl 10)
      balancedAtomSelectProgram_controllerAt
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      (by
        simp [initial, initialNPOracleState, encodeBalancedTraversalStack,
          encodeTaggedList])
      (by simp [initial, initialNPOracleState])
      hfit
      (by rw [hnine]; exact hfoldFit)
      (by rw [hnine]; exact hleafFit)
      (by
        intro atom _hmem entry hentryPc _hcurrent hatom hinputLength
          _haccumulator _hresult hleafRequired
        rcases run_atomSelectLeaf (maximumBits := maximumBits) entry index atom
            hentryPc hatom hinputLength hleafRequired with
          ⟨finish, hruns, hfinishPc, hzero, htwo, hthree, hnineValue,
            hcontext⟩
        refine hruns.toRunsWithin.mono ?_
        intro candidate hcandidate
        subst candidate
        exact ⟨hfinishPc, hzero, htwo, hthree, hnineValue, hcontext⟩)
  rw [hnine] at hwithin
  rw [balancedFoldLeafSteps_atomSelect index tree.atoms 0] at hwithin
  change
    runNPOracleProgram balancedAtomSelectProgram maximumBits
        (balancedAtomSelectFuel tree) initial =
      some (atomSelectValue index 0 0 tree.atoms)
  rw [show balancedAtomSelectFuel tree =
      (balancedTraversalStructuralSteps tree + 9 * tree.atoms.length) + 3 by
    simp [balancedAtomSelectFuel]]
  apply hwithin 3 (atomSelectValue index 0 0 tree.atoms)
  intro finish unused hfinish
  have hstack : finish.registers 2 = 0 := by
    simpa [encodeBalancedTraversalStack, encodeTaggedList] using
      hfinish.2.2.1
  have hchosen :
      (Nat.unpair (finish.registers 9)).2 =
        atomSelectValue index 0 0 tree.atoms := by
    rw [hfinish.2.2.2.1, foldl_atomSelectFoldStep_zero]
    simp
  rw [show unused + 3 = ((unused + 1) + 1) + 1 by omega]
  rw [run_branchZero_instruction (fuel := (unused + 1) + 1) (by rfl) hfinish.1]
  rw [hstack]
  rw [run_unpairRight_instruction (fuel := unused + 1)
    (value := atomSelectValue index 0 0 tree.atoms) (by rfl) rfl
    (by simp only [NPOracleState.jump]; exact hchosen) hfinalBits]
  exact run_halt_instruction (fuel := unused) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfinalBits

/-! ### The selecting trace is not geometric

Every value the selecting fold materializes is a visit counter, an index, an
atom of the input, or a pair of two of those.  So the whole fold trace is
twice one width that already bounds the count, the index and every atom —
there is no `encodeTaggedList` of a public-length list anywhere in it. -/

private theorem atomSelectTraceBits_le_aux :
    ∀ (atoms : List ℕ) (index seen result bound : ℕ),
      natBitLength (seen + atoms.length) ≤ bound →
      natBitLength index ≤ bound →
      natBitLength result ≤ bound →
      (∀ atom ∈ atoms, natBitLength atom ≤ bound) →
      atomSelectTraceBits index (Nat.pair seen result) atoms ≤ 2 * bound := by
  intro atoms
  induction atoms with
  | nil =>
      intro index seen result bound hlength _hindex hresult _hatoms
      have hseen : natBitLength seen ≤ bound :=
        (natBitLength_mono' (by simp)).trans hlength
      have hpair :=
        pairCodeBits_le seen result
      have hmax : max (natBitLength seen) (natBitLength result) ≤ bound :=
        max_le hseen hresult
      simp only [atomSelectTraceBits]
      omega
  | cons atom rest inductionHypothesis =>
      intro index seen result bound hlength hindex hresult hatoms
      simp only [List.length_cons] at hlength
      have hseen : natBitLength seen ≤ bound :=
        (natBitLength_mono' (by omega)).trans hlength
      have hsucc : natBitLength (seen + 1) ≤ bound :=
        (natBitLength_mono' (by omega)).trans hlength
      have hatom : natBitLength atom ≤ bound := hatoms atom (by simp)
      have hleft : natBitLength (seen - index) ≤ bound :=
        (natBitLength_mono' (by omega)).trans hseen
      have hright : natBitLength (index - seen) ≤ bound :=
        (natBitLength_mono' (by omega)).trans hindex
      have hgap :
          natBitLength ((seen - index) + (index - seen)) ≤ bound := by
        rcases Nat.le_total seen index with hle | hle
        · exact (natBitLength_mono'
            (by omega : (seen - index) + (index - seen) ≤ index)).trans hindex
        · exact (natBitLength_mono'
            (by omega : (seen - index) + (index - seen) ≤ seen)).trans hseen
      have hchosen :
          natBitLength (if seen = index then atom else result) ≤ bound := by
        split
        · exact hatom
        · exact hresult
      have hpacked := pairCodeBits_le seen result
      have hpackedMax : max (natBitLength seen) (natBitLength result) ≤ bound :=
        max_le hseen hresult
      have hstep :
          natBitLength (atomSelectFoldStep index (Nat.pair seen result) atom) ≤
            2 * bound := by
        simp only [atomSelectFoldStep, Nat.unpair_pair]
        have hnext :=
          pairCodeBits_le (seen + 1) (if seen = index then atom else result)
        have hnextMax :
            max (natBitLength (seen + 1))
              (natBitLength (if seen = index then atom else result)) ≤ bound :=
          max_le hsucc hchosen
        omega
      have hleaf :
          atomSelectLeafRequiredBits index (Nat.pair seen result) atom ≤
            2 * bound := by
        simp only [atomSelectLeafRequiredBits, atomSelectWidths,
          Nat.unpair_pair, List.foldr_cons, List.foldr_nil]
        exact max_le (by omega) (max_le (by omega) (max_le (by omega)
          (max_le (by omega) (max_le (by omega) (max_le (by omega)
            (max_le (by omega) (max_le (by omega)
              (max_le hstep (Nat.zero_le _)))))))))
      have htail :
          atomSelectTraceBits index
              (atomSelectFoldStep index (Nat.pair seen result) atom) rest ≤
            2 * bound := by
        have hnextState :
            atomSelectFoldStep index (Nat.pair seen result) atom =
              Nat.pair (seen + 1) (if seen = index then atom else result) := by
          simp only [atomSelectFoldStep, Nat.unpair_pair]
        rw [hnextState]
        refine inductionHypothesis index (seen + 1)
          (if seen = index then atom else result) bound ?_ hindex hchosen ?_
        · rw [show seen + 1 + rest.length = seen + (rest.length + 1) by omega]
          exact hlength
        · intro candidate hcandidate
          exact hatoms candidate (by simp [hcandidate])
      simp only [atomSelectTraceBits]
      exact max_le hleaf htail

/-- **The selecting fold trace, from above.**  Twice any width that bounds the
atom count, the requested index and every atom of the input. -/
theorem atomSelectTraceBits_zero_le
    (index : ℕ) (atoms : List ℕ) (bound : ℕ)
    (hone : 1 ≤ bound)
    (hlength : natBitLength atoms.length ≤ bound)
    (hindex : natBitLength index ≤ bound)
    (hatoms : ∀ atom ∈ atoms, natBitLength atom ≤ bound) :
    atomSelectTraceBits index 0 atoms ≤ 2 * bound := by
  have hzero : natBitLength 0 ≤ bound := by
    unfold natBitLength
    simpa using hone
  have haux :=
    atomSelectTraceBits_le_aux atoms index 0 0 bound (by simpa using hlength)
      hindex hzero hatoms
  rwa [pair_zero_zero] at haux

/-- **The selector's whole charge, from above.**  One balanced-traversal
charge over the input tree bounds every other summand up to a factor of two. -/
theorem balancedAtomSelectBits_le
    (index : ℕ) (tree : BalancedTraversalTree) (bound : ℕ)
    (hone : 1 ≤ bound)
    (hindex : natBitLength index ≤ bound)
    (hlength : natBitLength tree.atoms.length ≤ bound)
    (htraversal :
      balancedTraversalRequiredBits (fun value => value) tree [] ≤ bound) :
    balancedAtomSelectBits index tree ≤ 2 * bound := by
  have hatoms : ∀ atom ∈ tree.atoms, natBitLength atom ≤ bound := by
    intro atom hatom
    exact (balancedTraversalRequiredBits_atom
      (f := fun value => value) (frames := []) hatom).trans htraversal
  have htrace :=
    atomSelectTraceBits_zero_le index tree.atoms bound hone hlength hindex
      hatoms
  simp only [balancedAtomSelectBits]
  omega

end NearCubicWires.CanonicalBalancedAtomIndexProgram

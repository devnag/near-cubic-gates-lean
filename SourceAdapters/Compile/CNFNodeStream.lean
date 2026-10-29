import SourceAdapters.Compile.BoundedCNFValues

/-!
# The node stream of the request circuit, as plain recursion

proof of `lem:multitape-refuter` (the tableau circuit of the bounded computation and its 3-CNF) and proof of `lem:multitape-refuter` (the query is
written). The printing program of `CNFAssembly.CNFProgramRuns` must print the Tseitin clauses of exactly the nodes of
`requestCircuit r`. Those nodes are produced by dependent builder records (`compileOnWires`, `compileExpr`,
`compileVectorOnWires`, `compileExternalVector`, `compileTransitionRounds`); this module restates every appended
suffix and every output index as a plain function of the base length and the referenced wire indices, so that a
printer can be checked against it.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
  NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource
set_option autoImplicit false

/-- Nodes appended by `compileOnWires` from base length `base`, with wire `i` at index `wire i`; and the output. -/
def wireStream {n width : ℕ} (base : ℕ) (wire : Fin width → ℕ) :
    BoolExpr width → List (BooleanNode n) × ℕ
  | .const value => ([.const value], base)
  | .input index => ([], wire index)
  | .not child =>
      let p := wireStream base wire child
      (p.1 ++ [.not p.2], base + p.1.length)
  | .and left right =>
      let p := wireStream base wire left
      let q := wireStream (base + p.1.length) wire right
      (p.1 ++ q.1 ++ [.and p.2 q.2], base + p.1.length + q.1.length)
  | .or left right =>
      let p := wireStream base wire left
      let q := wireStream (base + p.1.length) wire right
      (p.1 ++ q.1 ++ [.or p.2 q.2], base + p.1.length + q.1.length)

theorem compileOnWires_stream {n width : ℕ} (expression : BoolExpr width) :
    ∀ (builder : BooleanDAGBuilder n) (wires : Fin width → LiveWire builder),
      (compileOnWires builder wires expression).extension.suffix =
          (wireStream (n := n) builder.nodes.length (fun i => (wires i).output.val) expression).1 ∧
        (compileOnWires builder wires expression).output.val =
          (wireStream (n := n) builder.nodes.length (fun i => (wires i).output.val) expression).2 := by
  induction expression with
  | const value =>
      intro builder wires
      exact ⟨rfl, rfl⟩
  | input index =>
      intro builder wires
      exact ⟨rfl, rfl⟩
  | not child ih =>
      intro builder wires
      obtain ⟨h1, h2⟩ := ih builder wires
      have hl := (compileOnWires builder wires child).extension.length_eq
      refine ⟨?_, ?_⟩
      · simp only [compileOnWires, CompiledWire.not, BooleanDAGExtension.trans, BooleanDAGExtension.single,
          wireStream]
        rw [h1, h2]
      · simp only [compileOnWires, CompiledWire.not, BooleanDAGBuilder.newest, wireStream]
        rw [hl, h1]
  | and left right ihl ihr =>
      intro builder wires
      obtain ⟨h1, h2⟩ := ihl builder wires
      obtain ⟨h3, h4⟩ := ihr (compileOnWires builder wires left).final
        (fun i => (wires i).lift (compileOnWires builder wires left).extension)
      have hl := (compileOnWires builder wires left).extension.length_eq
      have hr := (compileOnWires (compileOnWires builder wires left).final
        (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).extension.length_eq
      change _ = (wireStream (n := n) (compileOnWires builder wires left).final.nodes.length
        (fun i => (wires i).output.val) right).1 at h3
      change _ = (wireStream (n := n) (compileOnWires builder wires left).final.nodes.length
        (fun i => (wires i).output.val) right).2 at h4
      rw [hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show (compileOnWires builder wires left).extension.suffix ++
          ((compileOnWires (compileOnWires builder wires left).final
            (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).extension.suffix ++
          [BooleanNode.and (compileOnWires builder wires left).output.val
            (compileOnWires (compileOnWires builder wires left).final
              (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).output.val]) = _
        rw [h1, h2, h3, h4]
        simp [wireStream]
      · show (compileOnWires (compileOnWires builder wires left).final
          (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).final.nodes.length = _
        rw [hr, hl, h1, h3]
        simp [wireStream]

  | or left right ihl ihr =>
      intro builder wires
      obtain ⟨h1, h2⟩ := ihl builder wires
      obtain ⟨h3, h4⟩ := ihr (compileOnWires builder wires left).final
        (fun i => (wires i).lift (compileOnWires builder wires left).extension)
      have hl := (compileOnWires builder wires left).extension.length_eq
      have hr := (compileOnWires (compileOnWires builder wires left).final
        (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).extension.length_eq
      change _ = (wireStream (n := n) (compileOnWires builder wires left).final.nodes.length
        (fun i => (wires i).output.val) right).1 at h3
      change _ = (wireStream (n := n) (compileOnWires builder wires left).final.nodes.length
        (fun i => (wires i).output.val) right).2 at h4
      rw [hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show (compileOnWires builder wires left).extension.suffix ++
          ((compileOnWires (compileOnWires builder wires left).final
            (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).extension.suffix ++
          [BooleanNode.or (compileOnWires builder wires left).output.val
            (compileOnWires (compileOnWires builder wires left).final
              (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).output.val]) = _
        rw [h1, h2, h3, h4]
        simp [wireStream]
      · show (compileOnWires (compileOnWires builder wires left).final
          (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).final.nodes.length = _
        rw [hr, hl, h1, h3]
        simp [wireStream]


/-- Nodes appended by `compileExpr` (free circuit inputs become `input` nodes) and the output. -/
def exprStream {n : ℕ} (base : ℕ) : BoolExpr n → List (BooleanNode n) × ℕ
  | .const value => ([.const value], base)
  | .input index => ([.input index], base)
  | .not child =>
      let p := exprStream base child
      (p.1 ++ [.not p.2], base + p.1.length)
  | .and left right =>
      let p := exprStream base left
      let q := exprStream (base + p.1.length) right
      (p.1 ++ q.1 ++ [.and p.2 q.2], base + p.1.length + q.1.length)
  | .or left right =>
      let p := exprStream base left
      let q := exprStream (base + p.1.length) right
      (p.1 ++ q.1 ++ [.or p.2 q.2], base + p.1.length + q.1.length)

theorem compileExpr_stream {n : ℕ} (expression : BoolExpr n) :
    ∀ builder : BooleanDAGBuilder n,
      (compileExpr builder expression).extension.suffix = (exprStream builder.nodes.length expression).1 ∧
        (compileExpr builder expression).output.val = (exprStream builder.nodes.length expression).2 := by
  induction expression with
  | const value =>
      intro builder
      exact ⟨rfl, rfl⟩
  | input index =>
      intro builder
      exact ⟨rfl, rfl⟩
  | not child ih =>
      intro builder
      obtain ⟨h1, h2⟩ := ih builder
      have hl := (compileExpr builder child).extension.length_eq
      refine ⟨?_, ?_⟩
      · show (compileExpr builder child).extension.suffix ++ [BooleanNode.not (compileExpr builder child).output.val] = _
        rw [h1, h2]
        rfl
      · show (compileExpr builder child).final.nodes.length = _
        rw [hl, h1]
        rfl
  | and left right ihl ihr =>
      intro builder
      obtain ⟨h1, h2⟩ := ihl builder
      obtain ⟨h3, h4⟩ := ihr (compileExpr builder left).final
      have hl := (compileExpr builder left).extension.length_eq
      have hr := (compileExpr (compileExpr builder left).final right).extension.length_eq
      rw [hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show (compileExpr builder left).extension.suffix ++
          ((compileExpr (compileExpr builder left).final right).extension.suffix ++
          [BooleanNode.and (compileExpr builder left).output.val
            (compileExpr (compileExpr builder left).final right).output.val]) = _
        rw [h1, h2, h3, h4]
        simp [exprStream]
      · show (compileExpr (compileExpr builder left).final right).final.nodes.length = _
        rw [hr, hl, h1, h3]
        simp [exprStream]
  | or left right ihl ihr =>
      intro builder
      obtain ⟨h1, h2⟩ := ihl builder
      obtain ⟨h3, h4⟩ := ihr (compileExpr builder left).final
      have hl := (compileExpr builder left).extension.length_eq
      have hr := (compileExpr (compileExpr builder left).final right).extension.length_eq
      rw [hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show (compileExpr builder left).extension.suffix ++
          ((compileExpr (compileExpr builder left).final right).extension.suffix ++
          [BooleanNode.or (compileExpr builder left).output.val
            (compileExpr (compileExpr builder left).final right).output.val]) = _
        rw [h1, h2, h3, h4]
        simp [exprStream]
      · show (compileExpr (compileExpr builder left).final right).final.nodes.length = _
        rw [hr, hl, h1, h3]
        simp [exprStream]

/-- Nodes appended by `compileVectorOnWires` and the output index of each entry. -/
def vectorStream {n width : ℕ} (base : ℕ) (wire : Fin width → ℕ) :
    (count : ℕ) → (Fin count → BoolExpr width) → List (BooleanNode n) × (Fin count → ℕ)
  | 0, _ => ([], Fin.elim0)
  | count + 1, expressions =>
      let p := wireStream (n := n) base wire (expressions 0)
      let q := vectorStream (base + p.1.length) wire count (fun i => expressions i.succ)
      (p.1 ++ q.1, Fin.cases p.2 q.2)

theorem compileVectorOnWires_stream {n width : ℕ} (count : ℕ) :
    ∀ (builder : BooleanDAGBuilder n) (wires : Fin width → LiveWire builder)
      (expressions : Fin count → BoolExpr width),
      (compileVectorOnWires builder wires count expressions).extension.suffix =
          (vectorStream (n := n) builder.nodes.length (fun i => (wires i).output.val) count expressions).1 ∧
        ∀ j, ((compileVectorOnWires builder wires count expressions).output j).val =
          (vectorStream (n := n) builder.nodes.length (fun i => (wires i).output.val) count expressions).2 j := by
  induction count with
  | zero =>
      intro builder wires expressions
      exact ⟨rfl, fun j => Fin.elim0 j⟩
  | succ count ih =>
      intro builder wires expressions
      obtain ⟨h1, h2⟩ := compileOnWires_stream (expressions 0) builder wires
      obtain ⟨h3, h4⟩ := ih (compileOnWires builder wires (expressions 0)).final
        (fun i => (wires i).lift (compileOnWires builder wires (expressions 0)).extension)
        (fun i => expressions i.succ)
      have hl := (compileOnWires builder wires (expressions 0)).extension.length_eq
      change _ = (vectorStream (n := n) (compileOnWires builder wires (expressions 0)).final.nodes.length
        (fun i => (wires i).output.val) count (fun i => expressions i.succ)).1 at h3
      change ∀ j, _ = (vectorStream (n := n) (compileOnWires builder wires (expressions 0)).final.nodes.length
        (fun i => (wires i).output.val) count (fun i => expressions i.succ)).2 j at h4
      rw [hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show (compileOnWires builder wires (expressions 0)).extension.suffix ++
          (compileVectorOnWires (compileOnWires builder wires (expressions 0)).final
            (fun i => (wires i).lift (compileOnWires builder wires (expressions 0)).extension) count
            (fun i => expressions i.succ)).extension.suffix = _
        rw [h1, h3]
        rfl
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · show (compileOnWires builder wires (expressions 0)).output.val = _
          rw [h2]
          rfl
        · show ((compileVectorOnWires (compileOnWires builder wires (expressions 0)).final
            (fun i => (wires i).lift (compileOnWires builder wires (expressions 0)).extension) count
            (fun i => expressions i.succ)).output i).val = _
          rw [h4 i]
          rfl

/-- Nodes appended by `compileExternalVector` and the output index of each entry. -/
def externalStream {n : ℕ} (base : ℕ) :
    (count : ℕ) → (Fin count → BoolExpr n) → List (BooleanNode n) × (Fin count → ℕ)
  | 0, _ => ([], Fin.elim0)
  | count + 1, expressions =>
      let p := exprStream base (expressions 0)
      let q := externalStream (base + p.1.length) count (fun i => expressions i.succ)
      (p.1 ++ q.1, Fin.cases p.2 q.2)

theorem compileExternalVector_stream {n : ℕ} (count : ℕ) :
    ∀ (builder : BooleanDAGBuilder n) (expressions : Fin count → BoolExpr n),
      (compileExternalVector builder count expressions).extension.suffix =
          (externalStream builder.nodes.length count expressions).1 ∧
        ∀ j, ((compileExternalVector builder count expressions).output j).val =
          (externalStream builder.nodes.length count expressions).2 j := by
  induction count with
  | zero =>
      intro builder expressions
      exact ⟨rfl, fun j => Fin.elim0 j⟩
  | succ count ih =>
      intro builder expressions
      obtain ⟨h1, h2⟩ := compileExpr_stream (expressions 0) builder
      obtain ⟨h3, h4⟩ := ih (compileExpr builder (expressions 0)).final (fun i => expressions i.succ)
      have hl := (compileExpr builder (expressions 0)).extension.length_eq
      rw [hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show (compileExpr builder (expressions 0)).extension.suffix ++
          (compileExternalVector (compileExpr builder (expressions 0)).final count
            (fun i => expressions i.succ)).extension.suffix = _
        rw [h1, h3]
        rfl
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · show (compileExpr builder (expressions 0)).output.val = _
          rw [h2]
          rfl
        · show ((compileExternalVector (compileExpr builder (expressions 0)).final count
            (fun i => expressions i.succ)).output i).val = _
          rw [h4 i]
          rfl

/-- Nodes appended by `compileTransitionRounds`: one transition vector per round, each reading the previous
round's outputs; and the final outputs. -/
def roundsStream {n t s width : ℕ} (machine : Machine t s) :
    ℕ → (Fin (windowBits t s width) → ℕ) → ℕ →
      List (BooleanNode n) × (Fin (windowBits t s width) → ℕ)
  | _, wire, 0 => ([], wire)
  | base, wire, fuel + 1 =>
      let p := vectorStream (n := n) base wire (windowBits t s width) (transitionExpression machine)
      let q := roundsStream machine (base + p.1.length) p.2 fuel
      (p.1 ++ q.1, q.2)

theorem compileTransitionRounds_stream {n t s width : ℕ} (machine : Machine t s) (fuel : ℕ) :
    ∀ (builder : BooleanDAGBuilder n) (wires : Fin (windowBits t s width) → LiveWire builder),
      (compileTransitionRounds machine builder wires fuel).extension.suffix =
          (roundsStream (n := n) machine builder.nodes.length (fun i => (wires i).output.val) fuel).1 ∧
        ∀ j, ((compileTransitionRounds machine builder wires fuel).output j).val =
          (roundsStream (n := n) machine builder.nodes.length (fun i => (wires i).output.val) fuel).2 j := by
  induction fuel with
  | zero =>
      intro builder wires
      exact ⟨rfl, fun j => rfl⟩
  | succ fuel ih =>
      intro builder wires
      obtain ⟨h1, h2⟩ := compileVectorOnWires_stream (windowBits t s width) builder wires
        (transitionExpression machine)
      set first := compileVectorOnWires builder wires (windowBits t s width) (transitionExpression machine)
      obtain ⟨h3, h4⟩ := ih first.final first.live
      have hl := first.extension.length_eq
      have hw : (fun i => (first.live i).output.val) =
          (vectorStream (n := n) builder.nodes.length (fun i => (wires i).output.val) (windowBits t s width)
            (transitionExpression machine)).2 := funext h2
      rw [hw, hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show first.extension.suffix ++ (compileTransitionRounds machine first.final first.live fuel).extension.suffix = _
        rw [h1, h3]
        rfl
      · intro j
        show ((compileTransitionRounds machine first.final first.live fuel).output j).val = _
        rw [h4 j]
        rfl

/-- **The node stream of the request circuit** (proof of `lem:multitape-refuter`): initial window vector, `fuel` transition
rounds, the acceptance test, the half-open rank comparator, and the final conjunction; with its output index. -/
def requestStream (r : CNFCompilationRequest) : List (BooleanNode r.witnessLength) × ℕ :=
  let v := r.verifier
  let i := externalStream (n := r.witnessLength) 0 (windowBits v.tapeCount v.stateCount (r.fuel + 1))
    (verifierInitialExpression v r.input r.witnessLength r.fuel)
  let ro := roundsStream (n := r.witnessLength) v.machine i.1.length i.2 r.fuel
  let ac := wireStream (n := r.witnessLength) (i.1.length + ro.1.length) ro.2
    (acceptanceExpression v.machine v.accepting)
  let rk := exprStream (i.1.length + ro.1.length + ac.1.length) (rankLessExpression r.witnessLength r.high)
  (i.1 ++ ro.1 ++ ac.1 ++ rk.1 ++ [.and ac.2 rk.2], i.1.length + ro.1.length + ac.1.length + rk.1.length)

theorem requestCircuit_stream (r : CNFCompilationRequest) :
    (requestCircuit r).nodes = (requestStream r).1 ∧ (requestCircuit r).output.val = (requestStream r).2 := by
  obtain ⟨hi1, hi2⟩ := compileExternalVector_stream
    (windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1)) (BooleanDAGBuilder.empty r.witnessLength)
    (verifierInitialExpression r.verifier r.input r.witnessLength r.fuel)
  have hI : (verifierInitialValues r.verifier r.input r.witnessLength r.fuel).final.nodes =
      (externalStream (n := r.witnessLength) 0 (windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1))
        (verifierInitialExpression r.verifier r.input r.witnessLength r.fuel)).1 := by
    rw [(verifierInitialValues r.verifier r.input r.witnessLength r.fuel).extension.nodes_eq]
    exact hi1
  obtain ⟨hr1, hr2⟩ := compileTransitionRounds_stream r.verifier.machine r.fuel
    (verifierInitialValues r.verifier r.input r.witnessLength r.fuel).final
    (verifierInitialValues r.verifier r.input r.witnessLength r.fuel).live
  have hwI : (fun j => ((verifierInitialValues r.verifier r.input r.witnessLength r.fuel).live j).output.val) =
      (externalStream (n := r.witnessLength) 0 (windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1))
        (verifierInitialExpression r.verifier r.input r.witnessLength r.fuel)).2 := funext hi2
  rw [hwI, hI] at hr1 hr2
  obtain ⟨ha1, ha2⟩ := compileOnWires_stream (acceptanceExpression r.verifier.machine r.verifier.accepting)
    (verifierRoundValues r.verifier r.input r.witnessLength r.fuel).final
    (verifierRoundValues r.verifier r.input r.witnessLength r.fuel).live
  have hwR : (fun j => ((verifierRoundValues r.verifier r.input r.witnessLength r.fuel).live j).output.val) =
      _ := funext hr2
  have hRn : (verifierRoundValues r.verifier r.input r.witnessLength r.fuel).final.nodes =
      (externalStream (n := r.witnessLength) 0 (windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1))
        (verifierInitialExpression r.verifier r.input r.witnessLength r.fuel)).1 ++
      (roundsStream (n := r.witnessLength) r.verifier.machine
        (externalStream (n := r.witnessLength) 0 (windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1))
          (verifierInitialExpression r.verifier r.input r.witnessLength r.fuel)).1.length
        (externalStream (n := r.witnessLength) 0 (windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1))
          (verifierInitialExpression r.verifier r.input r.witnessLength r.fuel)).2 r.fuel).1 := by
    rw [(verifierRoundValues r.verifier r.input r.witnessLength r.fuel).extension.nodes_eq, ← hr1, ← hI]
    rfl
  rw [hwR, hRn, List.length_append] at ha1 ha2
  have hV : (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).final.nodes =
      (verifierRoundValues r.verifier r.input r.witnessLength r.fuel).final.nodes ++
        (compileOnWires (verifierRoundValues r.verifier r.input r.witnessLength r.fuel).final
          (verifierRoundValues r.verifier r.input r.witnessLength r.fuel).live
          (acceptanceExpression r.verifier.machine r.verifier.accepting)).extension.suffix :=
    (compileOnWires (verifierRoundValues r.verifier r.input r.witnessLength r.fuel).final
      (verifierRoundValues r.verifier r.input r.witnessLength r.fuel).live
      (acceptanceExpression r.verifier.machine r.verifier.accepting)).extension.nodes_eq
  rw [hRn, ha1] at hV
  obtain ⟨hk1, hk2⟩ := compileExpr_stream (rankLessExpression r.witnessLength r.high)
    (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).final
  rw [hV] at hk1 hk2
  have hK := (compileExpr (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).final
    (rankLessExpression r.witnessLength r.high)).extension.nodes_eq
  have hKl := (compileExpr (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).final
    (rankLessExpression r.witnessLength r.high)).extension.length_eq
  rw [hV, hk1] at hK
  rw [hV, hk1] at hKl
  refine ⟨?_, ?_⟩
  · show (compileExpr (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).final
        (rankLessExpression r.witnessLength r.high)).final.nodes ++
      [BooleanNode.and (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).output.val
        (compileExpr (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).final
          (rankLessExpression r.witnessLength r.high)).output.val] = _
    have hva : (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).output.val = _ := ha2
    rw [hk2, hva, hK]
    simp [requestStream, List.length_append, Nat.add_assoc]
  · show (compileExpr (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).final
        (rankLessExpression r.witnessLength r.high)).final.nodes.length = _
    rw [hKl]
    simp [requestStream, List.length_append, Nat.add_assoc]

open NearCubicWires.CircuitInputCNF NearCubicWires.TseitinCNF in
/-- The request formula as the Tseitin clauses of the node stream (proof of `lem:multitape-refuter`). -/
theorem requestFormula_stream (r : CNFCompilationRequest) :
    requestFormula r = circuitInputTautologies r.witnessLength ++
      (circuitInputNodesClausesFrom 0 (requestStream r).1 ++
        [positiveUnit (circuitInputGateVariable r.witnessLength (requestStream r).2)]) := by
  obtain ⟨h1, h2⟩ := requestCircuit_stream r
  rw [requestFormula, circuitInputFormula, h2, h1]

end NearCubicGates.Adapters.Compile

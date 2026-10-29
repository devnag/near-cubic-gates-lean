import SourceAdapters.Compile.OracleCircuit

/-!
proof of `thm:short-pcp-ours`, Step 4: exact plain-recursive node streams and references for the
concrete shared oracle DAG. This exposes the object the physical ordinary
printer must write; it is not itself a machine realization claim.
-/
namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.RepairSource
  NearCubicWires.FinitePredicateCircuit OracleExecution
set_option autoImplicit false

/-- Nodes appended by `compileOnWires` from base length `base`, with wire `i` at index `wire i`; and the output. -/
def wireStream {n arity width : ℕ} (base : ℕ) (wire : Fin width → ℕ) :
    BoolExpr width → List (OracleNode n arity) × ℕ
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

theorem compileOnWires_stream {n arity width : ℕ} (expression : BoolExpr width) :
    ∀ (builder : OracleDAGBuilder n arity) (wires : Fin width → LiveWire builder),
      (compileOnWires builder wires expression).extension.suffix =
          (wireStream (n := n) (arity := arity) builder.nodes.length (fun i => (wires i).output.val) expression).1 ∧
        (compileOnWires builder wires expression).output.val =
          (wireStream (n := n) (arity := arity) builder.nodes.length (fun i => (wires i).output.val) expression).2 := by
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
      · simp only [compileOnWires, CompiledWire.not, OracleDAGExtension.trans, OracleDAGExtension.single,
          wireStream]
        rw [h1, h2]
      · simp only [compileOnWires, CompiledWire.not, OracleDAGBuilder.newest, wireStream]
        rw [hl, h1]
  | and left right ihl ihr =>
      intro builder wires
      obtain ⟨h1, h2⟩ := ihl builder wires
      obtain ⟨h3, h4⟩ := ihr (compileOnWires builder wires left).final
        (fun i => (wires i).lift (compileOnWires builder wires left).extension)
      have hl := (compileOnWires builder wires left).extension.length_eq
      have hr := (compileOnWires (compileOnWires builder wires left).final
        (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).extension.length_eq
      change _ = (wireStream (n := n) (arity := arity) (compileOnWires builder wires left).final.nodes.length
        (fun i => (wires i).output.val) right).1 at h3
      change _ = (wireStream (n := n) (arity := arity) (compileOnWires builder wires left).final.nodes.length
        (fun i => (wires i).output.val) right).2 at h4
      rw [hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show (compileOnWires builder wires left).extension.suffix ++
          ((compileOnWires (compileOnWires builder wires left).final
            (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).extension.suffix ++
          [OracleNode.and (compileOnWires builder wires left).output.val
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
      change _ = (wireStream (n := n) (arity := arity) (compileOnWires builder wires left).final.nodes.length
        (fun i => (wires i).output.val) right).1 at h3
      change _ = (wireStream (n := n) (arity := arity) (compileOnWires builder wires left).final.nodes.length
        (fun i => (wires i).output.val) right).2 at h4
      rw [hl, h1] at h3 h4
      refine ⟨?_, ?_⟩
      · show (compileOnWires builder wires left).extension.suffix ++
          ((compileOnWires (compileOnWires builder wires left).final
            (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).extension.suffix ++
          [OracleNode.or (compileOnWires builder wires left).output.val
            (compileOnWires (compileOnWires builder wires left).final
              (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).output.val]) = _
        rw [h1, h2, h3, h4]
        simp [wireStream]
      · show (compileOnWires (compileOnWires builder wires left).final
          (fun i => (wires i).lift (compileOnWires builder wires left).extension) right).final.nodes.length = _
        rw [hr, hl, h1, h3]
        simp [wireStream]


/-- Nodes appended by `compileVectorOnWires` and the output index of each entry. -/
def vectorStream {n arity width : ℕ} (base : ℕ) (wire : Fin width → ℕ) :
    (count : ℕ) → (Fin count → BoolExpr width) → List (OracleNode n arity) × (Fin count → ℕ)
  | 0, _ => ([], Fin.elim0)
  | count + 1, expressions =>
      let p := wireStream (n := n) (arity := arity) base wire (expressions 0)
      let q := vectorStream (base + p.1.length) wire count (fun i => expressions i.succ)
      (p.1 ++ q.1, Fin.cases p.2 q.2)

theorem compileVectorOnWires_stream {n arity width : ℕ} (count : ℕ) :
    ∀ (builder : OracleDAGBuilder n arity) (wires : Fin width → LiveWire builder)
      (expressions : Fin count → BoolExpr width),
      (compileVectorOnWires builder wires count expressions).extension.suffix =
          (vectorStream (n := n) (arity := arity) builder.nodes.length (fun i => (wires i).output.val) count expressions).1 ∧
        ∀ j, ((compileVectorOnWires builder wires count expressions).output j).val =
          (vectorStream (n := n) (arity := arity) builder.nodes.length (fun i => (wires i).output.val) count expressions).2 j := by
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
      change _ = (vectorStream (n := n) (arity := arity) (compileOnWires builder wires (expressions 0)).final.nodes.length
        (fun i => (wires i).output.val) count (fun i => expressions i.succ)).1 at h3
      change ∀ j, _ = (vectorStream (n := n) (arity := arity) (compileOnWires builder wires (expressions 0)).final.nodes.length
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


/-- Allocate the external seed input gates in their actual compiler order. -/
def inputsStream {n arity : ℕ} (base : ℕ) :
    (count : ℕ) → (Fin count → Fin n) → List (OracleNode n arity) × (Fin count → ℕ)
  | 0, _ => ([],Fin.elim0)
  | count+1, indices =>
      let rest := inputsStream (base+1) count (fun i => indices i.succ)
      (.input (indices 0)::rest.1,Fin.cases base rest.2)

theorem compileInputs_stream {n arity : ℕ} (count : ℕ) :
    ∀ (builder : OracleDAGBuilder n arity) (indices : Fin count → Fin n),
      (compileInputs builder count indices).extension.suffix =
        (inputsStream (arity := arity) builder.nodes.length count indices).1 ∧
      ∀ j, ((compileInputs builder count indices).output j).val =
        (inputsStream (arity := arity) builder.nodes.length count indices).2 j := by
  induction count with
  | zero => intro builder indices; exact ⟨rfl,fun j => Fin.elim0 j⟩
  | succ count ih =>
    intro builder indices
    obtain ⟨hs,ho⟩ := ih (compileInput builder (indices 0)).final (fun i => indices i.succ)
    have hl : (compileInput builder (indices 0)).final.nodes.length=builder.nodes.length+1 := by
      simp [compileInput]
    rw [hl] at hs ho
    constructor
    · change [.input (indices 0)]++(compileInputs (compileInput builder (indices 0)).final
        count (fun i => indices i.succ)).extension.suffix=_
      rw [hs]
      rfl
    · intro j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro i
        exact ho i

/-- Compute all address bits and append one genuine arity-input oracle node. -/
def queryStream {n arity : ℕ} (base width : ℕ) (wire : Fin (queryWordBits width) → ℕ) :
    List (OracleNode n arity) × ℕ :=
  let addresses := vectorStream (n := n) (arity := arity) base wire arity
    (fun bit => queryAddressExpression width bit.val)
  (addresses.1++[.oracle addresses.2],base+addresses.1.length)

theorem compileQuery_stream {n arity : ℕ} (builder : OracleDAGBuilder n arity) (width : ℕ)
    (wires : Fin (queryWordBits width) → LiveWire builder) :
    (compileQuery builder width wires).extension.suffix=
      (queryStream (n := n) (arity := arity) builder.nodes.length width (fun i => (wires i).output.val)).1 ∧
    (compileQuery builder width wires).output.val=
      (queryStream (n := n) (arity := arity) builder.nodes.length width (fun i => (wires i).output.val)).2 := by
  let addresses := compileVectorOnWires builder wires arity (fun bit => queryAddressExpression width bit.val)
  obtain ⟨hs,ho⟩ := compileVectorOnWires_stream arity builder wires (fun bit => queryAddressExpression width bit.val)
  have hw : (fun j => (addresses.live j).output.val)=
      (vectorStream (n := n) (arity := arity) builder.nodes.length (fun i => (wires i).output.val)
        arity (fun bit => queryAddressExpression width bit.val)).2 := funext ho
  constructor
  · change addresses.extension.suffix++[.oracle (fun j => (addresses.live j).output.val)]=_
    rw [hs,hw]
    rfl
  · change addresses.final.nodes.length=_
    rw [addresses.extension.length_eq,hs]
    rfl

def roundStream {n arity : ℕ} (p : OrdinaryOracleProgram) (width cap base : ℕ)
    (wire : Fin (clockBits p width cap) → ℕ) : List (OracleNode n arity) × (Fin (clockBits p width cap) → ℕ) :=
  let query := queryStream (n := n) (arity := arity) base width (fun i => wire (queryInputIndex p width cap i))
  let output := vectorStream (n := n) (arity := arity) (base+query.1.length)
    (Fin.addCases wire (fun _ : Fin 1 => query.2)) (clockBits p width cap) (clockTransitionExpression p width cap)
  (query.1++output.1,output.2)

theorem roundAnswerWires_outputs {n arity count : ℕ} {builder : OracleDAGBuilder n arity}
    (wires : Fin count → LiveWire builder) {function : OracleFunction n arity}
    (answer : CompiledWire builder function) :
    (fun i => (roundAnswerWires wires answer i).output.val)=
      Fin.addCases (fun i => (wires i).output.val) (fun _ : Fin 1 => answer.output.val) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [roundAnswerWires,Fin.addCases_left]; rfl
  · intro j; simp only [roundAnswerWires,Fin.addCases_right]; rfl

theorem compileClockRound_stream {n arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (builder : OracleDAGBuilder n arity) (wires : Fin (clockBits p width cap) → LiveWire builder) :
    (compileClockRound p width cap builder wires).extension.suffix=
      (roundStream (n := n) (arity := arity) p width cap builder.nodes.length (fun i => (wires i).output.val)).1 ∧
    ∀ j, ((compileClockRound p width cap builder wires).output j).val=
      (roundStream (n := n) (arity := arity) p width cap builder.nodes.length (fun i => (wires i).output.val)).2 j := by
  let answer := compileQuery builder width (fun i => wires (queryInputIndex p width cap i))
  obtain ⟨hq1,hq2⟩ := compileQuery_stream builder width (fun i => wires (queryInputIndex p width cap i))
  obtain ⟨hv1,hv2⟩ := compileVectorOnWires_stream (clockBits p width cap) answer.final
    (roundAnswerWires wires answer) (clockTransitionExpression p width cap)
  rw [roundAnswerWires_outputs,hq2,answer.extension.length_eq,hq1] at hv1 hv2
  constructor
  · change answer.extension.suffix++
      (compileVectorOnWires answer.final (roundAnswerWires wires answer)
        (clockBits p width cap) (clockTransitionExpression p width cap)).extension.suffix=_
    rw [hq1,hv1]
    rfl
  · intro j
    exact hv2 j

def roundsStream {n arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ) :
    ℕ → (Fin (clockBits p width cap) → ℕ) → ℕ →
      List (OracleNode n arity) × (Fin (clockBits p width cap) → ℕ)
  | _, wire, 0 => ([],wire)
  | base, wire, fuel+1 =>
      let first := roundStream (n := n) (arity := arity) p width cap base wire
      let rest := roundsStream p width cap (base+first.1.length) first.2 fuel
      (first.1++rest.1,rest.2)

theorem compileClockRounds_stream {n arity : ℕ} (p : OrdinaryOracleProgram) (width cap fuel : ℕ) :
    ∀ (builder : OracleDAGBuilder n arity) (wires : Fin (clockBits p width cap) → LiveWire builder),
      (compileClockRounds p width cap builder wires fuel).extension.suffix=
        (roundsStream (n := n) (arity := arity) p width cap builder.nodes.length (fun i => (wires i).output.val) fuel).1 ∧
      ∀ j, ((compileClockRounds p width cap builder wires fuel).output j).val=
        (roundsStream (n := n) (arity := arity) p width cap builder.nodes.length (fun i => (wires i).output.val) fuel).2 j := by
  induction fuel with
  | zero => intro builder wires; exact ⟨rfl,fun j => rfl⟩
  | succ fuel ih =>
    intro builder wires
    obtain ⟨h1,h2⟩ := compileClockRound_stream p width cap builder wires
    let first := compileClockRound p width cap builder wires
    obtain ⟨h3,h4⟩ := ih first.final first.live
    have hw : (fun i => (first.live i).output.val)=
      (roundStream (n := n) (arity := arity) p width cap builder.nodes.length (fun i => (wires i).output.val)).2 := funext h2
    rw [hw,first.extension.length_eq,h1] at h3 h4
    constructor
    · change first.extension.suffix++(compileClockRounds p width cap first.final first.live fuel).extension.suffix=_
      rw [h1,h3]
      rfl
    · intro j
      exact h4 j

/-- Exact plain recursion to be implemented by the native physical printer. -/
def requestStream (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    List (OracleNode r.ell r.ell) × ℕ :=
  let inputs := inputsStream (arity := r.ell) 0 r.ell id
  let initial := vectorStream (n := r.ell) (arity := r.ell) inputs.1.length inputs.2
    (clockBits p (requestWidth r) r.fuel) (initialExpression p r)
  let rounds := roundsStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel
    (inputs.1.length+initial.1.length) initial.2 r.fuel
  let verdict := wireStream (n := r.ell) (arity := r.ell)
    (inputs.1.length+initial.1.length+rounds.1.length) rounds.2
    (verdictExpression p (requestWidth r) r.fuel (by unfold requestWidth; omega))
  (inputs.1++initial.1++rounds.1++verdict.1,verdict.2)

theorem requestCircuit_stream (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (requestCircuit p r).nodes=(requestStream p r).1 ∧
    (requestCircuit p r).output.val=(requestStream p r).2 := by
  let start := OracleDAGBuilder.empty r.ell r.ell
  let inputs := compileInputs start r.ell id
  let si := inputsStream (arity := r.ell) 0 r.ell id
  obtain ⟨hi1,hi2⟩ := compileInputs_stream r.ell start id
  change inputs.extension.suffix=si.1 at hi1
  have hwi : (fun i => (inputs.live i).output.val)=si.2 := funext hi2
  have hli : inputs.final.nodes.length=si.1.length := by
    rw [inputs.extension.length_eq]
    change 0+inputs.extension.suffix.length=_
    rw [hi1,Nat.zero_add]
  let initial := compileVectorOnWires inputs.final inputs.live
    (clockBits p (requestWidth r) r.fuel) (initialExpression p r)
  let sa := vectorStream (n := r.ell) (arity := r.ell) si.1.length si.2
    (clockBits p (requestWidth r) r.fuel) (initialExpression p r)
  obtain ⟨ha1,ha2⟩ := compileVectorOnWires_stream (clockBits p (requestWidth r) r.fuel)
    inputs.final inputs.live (initialExpression p r)
  rw [hwi,hli] at ha1 ha2
  change initial.extension.suffix=sa.1 at ha1
  have hwa : (fun i => (initial.live i).output.val)=sa.2 := funext ha2
  have hla : initial.final.nodes.length=si.1.length+sa.1.length := by
    rw [initial.extension.length_eq,hli,ha1]
  let rounds := compileClockRounds p (requestWidth r) r.fuel initial.final initial.live r.fuel
  let sr := roundsStream (n := r.ell) (arity := r.ell) p (requestWidth r) r.fuel
    (si.1.length+sa.1.length) sa.2 r.fuel
  obtain ⟨hr1,hr2⟩ := compileClockRounds_stream p (requestWidth r) r.fuel r.fuel initial.final initial.live
  rw [hwa,hla] at hr1 hr2
  change rounds.extension.suffix=sr.1 at hr1
  have hwr : (fun i => (rounds.live i).output.val)=sr.2 := funext hr2
  have hlr : rounds.final.nodes.length=si.1.length+sa.1.length+sr.1.length := by
    rw [rounds.extension.length_eq,hla,hr1]
  let verdict := compileOnWires rounds.final rounds.live
    (verdictExpression p (requestWidth r) r.fuel (by unfold requestWidth; omega))
  obtain ⟨hv1,hv2⟩ := compileOnWires_stream
    (verdictExpression p (requestWidth r) r.fuel (by unfold requestWidth; omega)) rounds.final rounds.live
  rw [hwr,hlr] at hv1 hv2
  constructor
  · change verdict.final.nodes=_
    rw [verdict.extension.nodes_eq,rounds.extension.nodes_eq,initial.extension.nodes_eq,inputs.extension.nodes_eq]
    change []++inputs.extension.suffix++initial.extension.suffix++rounds.extension.suffix++verdict.extension.suffix=_
    rw [hi1,ha1,hr1,hv1,List.nil_append]
    rfl
  · exact hv2

end NearCubicGates.Adapters.Compile.OracleExpressions

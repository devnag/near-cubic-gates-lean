import SourceAdapters.Compile.CNFNodeStream

/-!
# The postfix token machine of the request circuit

proof of `lem:multitape-refuter` (the tableau circuit of the bounded computation and its free-input Tseitin 3-CNF) and
 (the query is actually written). The printing program of `CNFAssembly.CNFProgramRuns` does not
build the dependent DAG records; it writes a stream of postfix tokens and interprets them with a stack. This module
is the pure semantics of that stream:

* `RS.step` is one token (constant/input/wire reference/negation/conjunction/disjunction/save/swap) acting on the
  node counter, the index stack, the current wire map, the next wire map and the emitted nodes;
* `run_postW`, `run_postE`: the postfix tokens of an expression emit exactly `wireStream`/`exprStream`
  (`CNFNodeStream`), so the token stream `requestToks r` emits exactly the nodes of `requestStream r`
  (`run_requestToks`), hence of `requestCircuit r`;
* `rcl`/`rclFrom`: the free-input Tseitin clauses of a raw node, equal to `circuitInputNodeClauses`
  (`requestFormula_rcl`).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
  NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource
set_option autoImplicit false

/-- Postfix tokens. `wir k` pushes entry `k` of the current wire map; `save` moves the top of the stack to the next
wire map; `swap` makes the next wire map current. -/
inductive RTok where
  | cst (b : Bool)
  | inp (j : ℕ)
  | wir (k : ℕ)
  | neg
  | conj
  | disj
  | save
  | swap
  deriving DecidableEq

/-- A circuit node with its input index as a number. -/
inductive RNode where
  | cst (b : Bool)
  | inp (j : ℕ)
  | neg (c : ℕ)
  | conj (l r : ℕ)
  | disj (l r : ℕ)
  deriving DecidableEq

def RNode.ofNode {n : ℕ} : BooleanNode n → RNode
  | .const b => .cst b
  | .input i => .inp i.val
  | .not c => .neg c
  | .and l r => .conj l r
  | .or l r => .disj l r

/-- The machine state: node counter, index stack (top first), current and next wire maps, emitted nodes. -/
structure RS where
  idx : ℕ
  stk : List ℕ
  wires : List ℕ
  next : List ℕ
  nodes : List RNode

/-- Pop with `0` from an empty stack (the printing program does the same). -/
def popS : List ℕ → ℕ × List ℕ
  | [] => (0, [])
  | x :: r => (x, r)

/-- Emit node `x` at the counter and push its index on `stk`. -/
def RS.push (S : RS) (stk : List ℕ) (x : RNode) : RS :=
  { S with idx := S.idx + 1, stk := S.idx :: stk, nodes := S.nodes ++ [x] }

def RS.step (S : RS) : RTok → RS
  | .cst b => S.push S.stk (.cst b)
  | .inp j => S.push S.stk (.inp j)
  | .wir k => { S with stk := S.wires.getD k 0 :: S.stk }
  | .neg => S.push (popS S.stk).2 (.neg (popS S.stk).1)
  | .conj => S.push (popS (popS S.stk).2).2 (.conj (popS (popS S.stk).2).1 (popS S.stk).1)
  | .disj => S.push (popS (popS S.stk).2).2 (.disj (popS (popS S.stk).2).1 (popS S.stk).1)
  | .save => { S with stk := (popS S.stk).2, next := S.next ++ [(popS S.stk).1] }
  | .swap => { S with wires := S.next, next := [] }

def RS.run (S : RS) (toks : List RTok) : RS := toks.foldl RS.step S

@[simp] theorem RS.run_nil (S : RS) : S.run [] = S := rfl
@[simp] theorem RS.run_cons (S : RS) (t : RTok) (l : List RTok) : S.run (t :: l) = (S.step t).run l := rfl
theorem RS.run_append (S : RS) (a b : List RTok) : S.run (a ++ b) = (S.run a).run b := List.foldl_append

/-- Postfix tokens over wires. -/
def postW {w : ℕ} : BoolExpr w → List RTok
  | .const b => [.cst b]
  | .input i => [.wir i.val]
  | .not c => postW c ++ [.neg]
  | .and l r => postW l ++ postW r ++ [.conj]
  | .or l r => postW l ++ postW r ++ [.disj]

/-- Postfix tokens over external circuit inputs. -/
def postE {n : ℕ} : BoolExpr n → List RTok
  | .const b => [.cst b]
  | .input i => [.inp i.val]
  | .not c => postE c ++ [.neg]
  | .and l r => postE l ++ postE r ++ [.conj]
  | .or l r => postE l ++ postE r ++ [.disj]

/-- The effect of emitting a block of nodes `l` whose output is `o`. -/
def RS.emitBlock {n : ℕ} (S : RS) (l : List (BooleanNode n)) (o : ℕ) : RS :=
  { S with idx := S.idx + l.length, stk := o :: S.stk, nodes := S.nodes ++ l.map RNode.ofNode }

theorem run_postW {n w : ℕ} (wire : Fin w → ℕ) (e : BoolExpr w) :
    ∀ S : RS, (∀ i : Fin w, S.wires.getD i.val 0 = wire i) →
      S.run (postW e) = S.emitBlock (wireStream (n := n) S.idx wire e).1 (wireStream (n := n) S.idx wire e).2 := by
  induction e with
  | const b =>
      intro S _
      rfl
  | input i =>
      intro S hw
      have h := hw i
      simp only [postW, RS.run_cons, RS.run_nil, RS.step, RS.emitBlock, wireStream, h]
      simp
  | not c ih =>
      intro S hw
      rw [postW, RS.run_append, ih S hw]
      simp [RS.step, RS.emitBlock, RS.push, wireStream, popS, RNode.ofNode, Nat.add_assoc]
  | and l r ihl ihr =>
      intro S hw
      have hw' : ∀ i : Fin w, (S.emitBlock (wireStream (n := n) S.idx wire l).1
          (wireStream (n := n) S.idx wire l).2).wires.getD i.val 0 = wire i := hw
      rw [postW, RS.run_append, RS.run_append, ihl S hw, ihr _ hw']
      simp [RS.step, RS.emitBlock, RS.push, wireStream, popS, RNode.ofNode, Nat.add_assoc]
  | or l r ihl ihr =>
      intro S hw
      have hw' : ∀ i : Fin w, (S.emitBlock (wireStream (n := n) S.idx wire l).1
          (wireStream (n := n) S.idx wire l).2).wires.getD i.val 0 = wire i := hw
      rw [postW, RS.run_append, RS.run_append, ihl S hw, ihr _ hw']
      simp [RS.step, RS.emitBlock, RS.push, wireStream, popS, RNode.ofNode, Nat.add_assoc]

theorem run_postE {n : ℕ} (e : BoolExpr n) :
    ∀ S : RS, S.run (postE e) = S.emitBlock (exprStream S.idx e).1 (exprStream S.idx e).2 := by
  induction e with
  | const b =>
      intro S
      rfl
  | input i =>
      intro S
      rfl
  | not c ih =>
      intro S
      rw [postE, RS.run_append, ih S]
      simp [RS.step, RS.emitBlock, RS.push, exprStream, popS, RNode.ofNode, Nat.add_assoc]
  | and l r ihl ihr =>
      intro S
      rw [postE, RS.run_append, RS.run_append, ihl S, ihr _]
      simp [RS.step, RS.emitBlock, RS.push, exprStream, popS, RNode.ofNode, Nat.add_assoc]
  | or l r ihl ihr =>
      intro S
      rw [postE, RS.run_append, RS.run_append, ihl S, ihr _]
      simp [RS.step, RS.emitBlock, RS.push, exprStream, popS, RNode.ofNode, Nat.add_assoc]

/-- A vector over wires: each entry's tokens, then `save`. -/
def vecW {w : ℕ} (count : ℕ) (exprs : Fin count → BoolExpr w) : List RTok :=
  (List.ofFn fun j => postW (exprs j) ++ [.save]).flatten

/-- A vector over external inputs. -/
def vecE {n : ℕ} (count : ℕ) (exprs : Fin count → BoolExpr n) : List RTok :=
  (List.ofFn fun j => postE (exprs j) ++ [.save]).flatten

/-- The effect of a vector block: nodes `l` appended, outputs `o` appended to the next wire map. -/
def RS.vecBlock {n count : ℕ} (S : RS) (l : List (BooleanNode n)) (o : Fin count → ℕ) : RS :=
  { S with idx := S.idx + l.length, next := S.next ++ List.ofFn o, nodes := S.nodes ++ l.map RNode.ofNode }

theorem run_vecW {n w : ℕ} (wire : Fin w → ℕ) (count : ℕ) :
    ∀ (exprs : Fin count → BoolExpr w) (S : RS), (∀ i : Fin w, S.wires.getD i.val 0 = wire i) →
      S.run (vecW count exprs) =
        S.vecBlock (vectorStream (n := n) S.idx wire count exprs).1 (vectorStream (n := n) S.idx wire count exprs).2 := by
  induction count with
  | zero =>
      intro exprs S _
      simp [vecW, RS.vecBlock, vectorStream]
  | succ count ih =>
      intro exprs S hw
      have e1 : vecW (count + 1) exprs = postW (exprs 0) ++ [.save] ++ vecW count (fun j => exprs j.succ) := by
        simp [vecW, List.ofFn_succ]
      rw [e1, RS.run_append, RS.run_append, run_postW (n := n) wire _ S hw]
      rw [ih _ _ (by simpa [RS.emitBlock, RS.step] using hw)]
      simp [RS.step, RS.emitBlock, RS.vecBlock, vectorStream, popS, List.ofFn_succ, Nat.add_assoc]

theorem run_vecE {n : ℕ} (count : ℕ) :
    ∀ (exprs : Fin count → BoolExpr n) (S : RS),
      S.run (vecE count exprs) =
        S.vecBlock (externalStream S.idx count exprs).1 (externalStream S.idx count exprs).2 := by
  induction count with
  | zero =>
      intro exprs S
      simp [vecE, RS.vecBlock, externalStream]
  | succ count ih =>
      intro exprs S
      have e1 : vecE (count + 1) exprs = postE (exprs 0) ++ [.save] ++ vecE count (fun j => exprs j.succ) := by
        simp [vecE, List.ofFn_succ]
      rw [e1, RS.run_append, RS.run_append, run_postE _ S, ih]
      simp [RS.step, RS.emitBlock, RS.vecBlock, externalStream, popS, List.ofFn_succ, Nat.add_assoc]

/-- The tokens of one transition round (`windowBits` saved entries, then `swap`). -/
def roundToks {t s : ℕ} (width : ℕ) (machine : Machine t s) : List RTok :=
  vecW (windowBits t s width) (transitionExpression (width := width) machine) ++ [.swap]

theorem getD_ofFn {k : ℕ} (f : Fin k → ℕ) (i : Fin k) : (List.ofFn f).getD i.val 0 = f i := by
  simp [List.getD_eq_getElem?_getD]

/-- The effect of whole rounds: nodes `l` appended, the wire map replaced by `o`. -/
def RS.roundBlock {n count : ℕ} (S : RS) (l : List (BooleanNode n)) (o : Fin count → ℕ) : RS :=
  { S with idx := S.idx + l.length, wires := List.ofFn o, nodes := S.nodes ++ l.map RNode.ofNode }

theorem run_rounds {n t s width : ℕ} (machine : Machine t s) (fuel : ℕ) :
    ∀ (wire : Fin (windowBits t s width) → ℕ) (S : RS), S.wires = List.ofFn wire → S.next = [] →
      S.run (List.replicate fuel (roundToks width machine)).flatten =
        S.roundBlock (roundsStream (n := n) machine S.idx wire fuel).1
          (roundsStream (n := n) machine S.idx wire fuel).2 := by
  induction fuel with
  | zero =>
      intro wire S hw hn
      cases S
      simp_all [roundsStream, RS.roundBlock]
  | succ fuel ih =>
      intro wire S hw hn
      set p := vectorStream (n := n) S.idx wire (windowBits t s width)
        (transitionExpression (width := width) machine) with hp
      have h1 : S.run (roundToks width machine) =
          { S with
            idx := S.idx + p.1.length
            wires := List.ofFn p.2
            next := []
            nodes := S.nodes ++ p.1.map RNode.ofNode } := by
        rw [roundToks, RS.run_append, run_vecW (n := n) wire _ _ S (fun i => by rw [hw]; exact getD_ofFn wire i)]
        simp [RS.step, RS.vecBlock, hn, hp]
      rw [List.replicate_succ, List.flatten_cons, RS.run_append, h1, ih p.2 _ rfl rfl]
      obtain ⟨idx, stk, wires, next, nodes⟩ := S
      simp only at hn
      subst hn
      simp [RS.roundBlock, roundsStream, hp, Nat.add_assoc]

/-- The whole token stream of the request circuit (proof of `lem:multitape-refuter`): the initial vector, `fuel` rounds, the
acceptance test over the last round, the rank comparator over the witness inputs, and the final conjunction. -/
def requestToks (r : CNFCompilationRequest) : List RTok :=
  vecE (windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1))
      (verifierInitialExpression r.verifier r.input r.witnessLength r.fuel) ++ [.swap] ++
    (List.replicate r.fuel (roundToks (r.fuel + 1) r.verifier.machine)).flatten ++
    postW (acceptanceExpression (width := r.fuel + 1) r.verifier.machine r.verifier.accepting) ++
    postE (rankLessExpression r.witnessLength r.high) ++ [.conj]

/-- The empty machine state. -/
def RS.init : RS := ⟨0, [], [], [], []⟩

theorem run_requestToks (r : CNFCompilationRequest) :
    (RS.init.run (requestToks r)).nodes = (requestStream r).1.map RNode.ofNode ∧
      (RS.init.run (requestToks r)).stk = [(requestStream r).2] ∧
      (RS.init.run (requestToks r)).idx = (requestStream r).1.length := by
  set v := r.verifier
  set i := externalStream (n := r.witnessLength) 0 (windowBits v.tapeCount v.stateCount (r.fuel + 1))
    (verifierInitialExpression v r.input r.witnessLength r.fuel) with hi
  set ro := roundsStream (n := r.witnessLength) v.machine i.1.length i.2 r.fuel with hro
  set ac := wireStream (n := r.witnessLength) (i.1.length + ro.1.length) ro.2
    (acceptanceExpression v.machine v.accepting) with hac
  set rk := exprStream (i.1.length + ro.1.length + ac.1.length) (rankLessExpression r.witnessLength r.high) with hrk
  have h1 : RS.init.run (vecE (windowBits v.tapeCount v.stateCount (r.fuel + 1))
      (verifierInitialExpression v r.input r.witnessLength r.fuel) ++ [.swap]) =
      ⟨i.1.length, [], List.ofFn i.2, [], i.1.map RNode.ofNode⟩ := by
    rw [RS.run_append, run_vecE]
    simp [RS.init, RS.vecBlock, RS.step, hi]
  have h2 : (⟨i.1.length, [], List.ofFn i.2, [], i.1.map RNode.ofNode⟩ : RS).run
      (List.replicate r.fuel (roundToks (r.fuel + 1) v.machine)).flatten =
      ⟨i.1.length + ro.1.length, [], List.ofFn ro.2, [], (i.1 ++ ro.1).map RNode.ofNode⟩ := by
    rw [run_rounds (n := r.witnessLength) v.machine r.fuel i.2 _ rfl rfl]
    simp [hro, RS.roundBlock]
  have h3 : (⟨i.1.length + ro.1.length, [], List.ofFn ro.2, [], (i.1 ++ ro.1).map RNode.ofNode⟩ : RS).run
      (postW (acceptanceExpression (width := r.fuel + 1) v.machine v.accepting)) =
      ⟨i.1.length + ro.1.length + ac.1.length, [ac.2], List.ofFn ro.2, [],
        (i.1 ++ ro.1 ++ ac.1).map RNode.ofNode⟩ := by
    rw [run_postW (n := r.witnessLength) ro.2 _ _ (fun j => getD_ofFn ro.2 j)]
    simp [RS.emitBlock, hac]
  have h4 : (⟨i.1.length + ro.1.length + ac.1.length, [ac.2], List.ofFn ro.2, [],
        (i.1 ++ ro.1 ++ ac.1).map RNode.ofNode⟩ : RS).run (postE (rankLessExpression r.witnessLength r.high)) =
      ⟨i.1.length + ro.1.length + ac.1.length + rk.1.length, [rk.2, ac.2], List.ofFn ro.2, [],
        (i.1 ++ ro.1 ++ ac.1 ++ rk.1).map RNode.ofNode⟩ := by
    rw [run_postE]
    simp [RS.emitBlock, hrk]
  have e : requestToks r = (vecE (windowBits v.tapeCount v.stateCount (r.fuel + 1))
      (verifierInitialExpression v r.input r.witnessLength r.fuel) ++ [.swap]) ++
      (List.replicate r.fuel (roundToks (r.fuel + 1) v.machine)).flatten ++
      postW (acceptanceExpression (width := r.fuel + 1) v.machine v.accepting) ++
      postE (rankLessExpression r.witnessLength r.high) ++ [.conj] := by
    simp [requestToks, v, List.append_assoc]
  rw [e, RS.run_append, RS.run_append, RS.run_append, RS.run_append, h1, h2, h3, h4]
  simp [RS.step, RS.push, popS, requestStream, ← hi, ← hro, ← hac, ← hrk, RNode.ofNode, v]
  omega

open NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF

/-- The free-input Tseitin clauses of a raw node at position `i` (inputs `0..n-1`, gates from `n`). -/
def rcl (n i : ℕ) : RNode → EncodedCNF
  | .cst true => [positiveUnit (n + i)]
  | .cst false => [negativeUnit (n + i)]
  | .inp j => [triple (negative (n + i)) (positive j) (positive j), triple (positive (n + i)) (negative j) (negative j)]
  | .neg c => [triple (negative (n + i)) (negative (n + c)) (negative (n + c)),
      triple (positive (n + i)) (positive (n + c)) (positive (n + c))]
  | .conj l r => [triple (negative (n + i)) (positive (n + l)) (positive (n + l)),
      triple (negative (n + i)) (positive (n + r)) (positive (n + r)),
      triple (positive (n + i)) (negative (n + l)) (negative (n + r))]
  | .disj l r => [triple (positive (n + i)) (negative (n + l)) (negative (n + l)),
      triple (positive (n + i)) (negative (n + r)) (negative (n + r)),
      triple (negative (n + i)) (positive (n + l)) (positive (n + r))]

theorem rcl_ofNode {n : ℕ} (i : ℕ) (node : BooleanNode n) :
    circuitInputNodeClauses i node = rcl n i (RNode.ofNode node) := by
  cases node with
  | const b => cases b <;> rfl
  | input j => rfl
  | not c => rfl
  | and l r => rfl
  | or l r => rfl

/-- The clauses of a node list from position `start`. -/
def rclFrom (n start : ℕ) (l : List RNode) : EncodedCNF :=
  (List.range l.length).flatMap fun k => rcl n (start + k) (l.getD k (.cst false))

theorem rclFrom_nil (n start : ℕ) : rclFrom n start [] = [] := rfl

theorem rclFrom_concat (n start : ℕ) (l : List RNode) (x : RNode) :
    rclFrom n start (l ++ [x]) = rclFrom n start l ++ rcl n (start + l.length) x := by
  unfold rclFrom
  rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append]
  congr 1
  · apply List.flatMap_congr
    intro k hk
    rw [List.mem_range] at hk
    rw [List.getD_append _ _ _ _ hk]
  · simp

theorem nodesClausesFrom_rcl {n : ℕ} (nodes : List (BooleanNode n)) :
    ∀ start, circuitInputNodesClausesFrom start nodes = rclFrom n start (nodes.map RNode.ofNode) := by
  induction nodes using List.reverseRecOn with
  | nil => intro start; rfl
  | append_singleton l x ih =>
      intro start
      have hsplit : ∀ (m : List (BooleanNode n)) (st : ℕ), circuitInputNodesClausesFrom st (m ++ [x]) =
          circuitInputNodesClausesFrom st m ++ circuitInputNodeClauses (st + m.length) x := by
        intro m
        induction m with
        | nil => intro st; simp [circuitInputNodesClausesFrom]
        | cons y m ihm =>
            intro st
            simp only [List.cons_append, circuitInputNodesClausesFrom, ihm, List.append_assoc, List.length_cons]
            rw [show st + 1 + m.length = st + (m.length + 1) by omega]
      rw [hsplit, ih, List.map_append, List.map_singleton, rclFrom_concat, rcl_ofNode, List.length_map]

/-- **The request formula from the token run** (proof of `lem:multitape-refuter`). -/
theorem requestFormula_rcl (r : CNFCompilationRequest) :
    requestFormula r = circuitInputTautologies r.witnessLength ++
      (rclFrom r.witnessLength 0 (RS.init.run (requestToks r)).nodes ++
        [positiveUnit (r.witnessLength + (popS (RS.init.run (requestToks r)).stk).1)]) := by
  obtain ⟨h1, h2, _⟩ := run_requestToks r
  rw [requestFormula_stream, h1, h2, nodesClausesFrom_rcl]
  rfl

end NearCubicGates.Adapters.Compile

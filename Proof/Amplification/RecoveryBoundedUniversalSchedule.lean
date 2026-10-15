import Proof.Amplification.RecoveryBoundedNativeExpr

/-! The original shared-wire universal selector's exact append schedule. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversal
open SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def choices {n : ℕ} {b : BooleanDAGBuilder n}
    (xs : List (GuardedChoice b)) : List (BoolExpr n × ℕ) :=
  xs.map fun x => (x.condition, x.value.output.val)

def guardCount {n : ℕ} : List (BoolExpr n × ℕ) → ℕ
  | [] => 1
  | (e, _) :: rest => e.nodeCount + 2 + guardCount rest

def guardNodes {n : ℕ} (base : ℕ) :
    List (BoolExpr n × ℕ) → List (BooleanNode n)
  | [] => [.const false]
  | (e, value) :: rest =>
      exprNodes base e ++ [.and (base + e.nodeCount - 1) value] ++
      guardNodes (base + e.nodeCount + 1) rest ++
      [.or (base + e.nodeCount)
        (base + e.nodeCount + 1 + guardCount rest - 1)]

theorem choices_lift {n : ℕ} {b c : BooleanDAGBuilder n}
    (ex : BooleanDAGExtension b c) (xs : List (GuardedChoice b)) :
    choices (xs.map (GuardedChoice.lift ex)) = choices xs := by
  simp only [choices, List.map_map]
  rfl

theorem guardCount_choices {n : ℕ} {b : BooleanDAGBuilder n}
    (xs : List (GuardedChoice b)) :
    guardCount (choices xs) = guardedAnyNodeCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [choices, List.map_cons, guardCount, guardedAnyNodeCount] using
      congrArg (x.condition.nodeCount + 2 + ·) ih

theorem guardNodes_length {n : ℕ} (base : ℕ) (xs : List (BoolExpr n × ℕ)) :
    (guardNodes base xs).length = guardCount xs := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨e, v⟩
    simp only [guardNodes, List.length_append, List.length_singleton,
      exprNodes_length, ih, guardCount]
    omega

theorem compileGuardedAny_length {n : ℕ} (b : BooleanDAGBuilder n)
    (xs : List (GuardedChoice b)) :
    (compileGuardedAny b xs).final.nodes.length =
      b.nodes.length + guardCount (choices xs) := by
  rw [(compileGuardedAny b xs).extension.nodes_eq, List.length_append,
    compileGuardedAny_addedNodes, guardCount_choices]

theorem compileAnd_nodes {n : ℕ} (b : BooleanDAGBuilder n)
    (l r : LiveWire b) :
    (compileAnd b l r).extension.suffix = [.and l.output.val r.output.val] := rfl

theorem compileOr_nodes {n : ℕ} (b : BooleanDAGBuilder n)
    (l r : LiveWire b) :
    (compileOr b l r).extension.suffix = [.or l.output.val r.output.val] := rfl

theorem compileAnd_length {n : ℕ} (b : BooleanDAGBuilder n)
    (l r : LiveWire b) :
    (compileAnd b l r).final.nodes.length = b.nodes.length + 1 := by
  rw [(compileAnd b l r).extension.nodes_eq, List.length_append, compileAnd_addedNodes]

theorem compileGuardedAny_output {n : ℕ} (b : BooleanDAGBuilder n)
    (xs : List (GuardedChoice b)) :
    (compileGuardedAny b xs).output.val =
      b.nodes.length + guardCount (choices xs) - 1 := by
  fun_induction compileGuardedAny
  · rfl
  · rename_i b x rest condition guarded ex liftedRest tail merged result ihTail ihRecursive
    change tail.final.nodes.length = _
    change (compileGuardedAny guarded.final liftedRest).final.nodes.length = _
    rw [compileGuardedAny_length]
    simp only [liftedRest, choices_lift]
    change (compileAnd condition.final condition.live
      (x.value.lift condition.extension)).final.nodes.length + _ = _
    rw [compileAnd_length]
    change (compileExpr b x.condition).final.nodes.length + 1 + _ = _
    rw [compileExpr_length]
    simp only [choices, List.map_cons, guardCount]
    omega

theorem compileGuardedAny_nodes {n : ℕ} (b : BooleanDAGBuilder n)
    (xs : List (GuardedChoice b)) :
    (compileGuardedAny b xs).extension.suffix =
      guardNodes b.nodes.length (choices xs) := by
  fun_induction compileGuardedAny
  · rfl
  · rename_i b x rest condition guarded ex liftedRest tail merged result ihTail ihRecursive
    change (((condition.extension.trans guarded.extension).trans
      tail.extension).trans merged.extension).suffix = _
    simp only [BooleanDAGExtension.trans]
    change (compileExpr b x.condition).extension.suffix ++
      (compileAnd condition.final condition.live
        (x.value.lift condition.extension)).extension.suffix ++
      (compileGuardedAny guarded.final liftedRest).extension.suffix ++
      (compileOr tail.final (guarded.live.lift tail.extension) tail.live).extension.suffix = _
    rw [compileExpr_nodes, compileAnd_nodes, ihTail, compileOr_nodes]
    simp only [liftedRest, choices_lift]
    change exprNodes b.nodes.length x.condition ++
      [.and (compileExpr b x.condition).output.val x.value.output.val] ++
      guardNodes guarded.final.nodes.length (choices rest) ++
      [.or condition.final.nodes.length (compileGuardedAny guarded.final liftedRest).output.val] = _
    rw [compileExpr_output, compileGuardedAny_output]
    simp only [liftedRest, choices_lift]
    change exprNodes b.nodes.length x.condition ++ _ ++
      guardNodes (compileAnd condition.final condition.live
        (x.value.lift condition.extension)).final.nodes.length (choices rest) ++
      [.or (compileExpr b x.condition).final.nodes.length
        ((compileAnd condition.final condition.live
          (x.value.lift condition.extension)).final.nodes.length +
            guardCount (choices rest) - 1)] = _
    rw [compileAnd_length, compileExpr_length]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversal

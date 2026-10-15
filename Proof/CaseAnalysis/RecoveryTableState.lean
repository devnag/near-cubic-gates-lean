import Proof.CaseAnalysis.RecoveryTableNodeRun

/-! The actual original table prefix is the invariant of the paid repeat
driver. Native words and references are those of compileUniversalNodes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTable
open LocalBitMultitape RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedUniversalNodeBank
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def index (n bound k start : ℕ):=k*rowWidth n bound+start
def native {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (k : ℕ) (hk : k ≤ bound):=
  (compileUniversalNodes b address k hk).extension.suffix.flatMap PCPPRequestNodeSchema.native
def references {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (k : ℕ) (hk : k ≤ bound):=
  (compileUniversalNodes b address k hk).values.map (fun w=>w.output.val)

noncomputable def entry {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (W D L : ℕ) (out addressTail : List Bool) (k : ℕ) (hk : k ≤ bound):=
  let table:=compileUniversalNodes b address k hk
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let result:=out++native b address k hk
  (⟨RecoveryBoundedTableNode.machine.start,heads result,
    data (index n bound k 6) table.final.nodes.length (capacity W) D 0 F k L result
      (ZeroPadding.pad (capacity W) (sourceWord (references b address k hk)))
      (index n bound k (6+F)) (index n bound k 0) 0 0 0 (List.ofFn address++addressTail) n []⟩ :
    Configuration 55 _)

theorem index_succ (n bound k start : ℕ) :
    index n bound k start+(2*OuterPCPRecovery.boundedCircuitFieldLimit n bound+6)=
      index n bound (k+1) start := by
  unfold index rowWidth
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem native_succ {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (k : ℕ) (hk : k+1 ≤ bound) :
    let before:=compileUniversalNodes b address k (by omega)
    let node:=compileUniversalNode before.final ⟨k,by omega⟩ address before.values
    native b address (k+1) hk=native b address k (by omega)++
      node.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native := by
  dsimp only [native,compileUniversalNodes,BooleanDAGExtension.trans]
  rw [List.flatMap_append]

theorem references_succ {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (k : ℕ) (hk : k+1 ≤ bound) :
    let before:=compileUniversalNodes b address k (by omega)
    let node:=compileUniversalNode before.final ⟨k,by omega⟩ address before.values
    references b address (k+1) hk=references b address k (by omega)++[node.compiled.output.val] := by
  dsimp only [references,compileUniversalNodes]
  rw [List.map_append,RecoveryBoundedSelectorLoop.raw_lift]
  rfl

theorem final_succ {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (k : ℕ) (hk : k+1 ≤ bound) :
    let before:=compileUniversalNodes b address k (by omega)
    let node:=compileUniversalNode before.final ⟨k,by omega⟩ address before.values
    (compileUniversalNodes b address (k+1) hk).final=node.compiled.final := by rfl

theorem references_length {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (k : ℕ) (hk : k ≤ bound) :
    (references b address k hk).length=k := by
  simp only [references,List.length_map,compileUniversalNodes_values_length]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTable

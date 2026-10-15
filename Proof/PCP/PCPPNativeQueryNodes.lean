import Proof.PCP.PCPPNativeCopyNodes

namespace NearCubicWires.RepairOrdinary.PCPPNative
open SourceInterfaces PCPPSubstitution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def queryNodesPrefix {n r q : ℕ} (base : ℕ) (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (count : ℕ) : List (BooleanNode r) :=
  (List.range count).flatMap fun j => queryNodes (base+j*(2*oracle.size+1)) oracle
    (((List.ofFn projections)[j]?).getD (fun _ => .constant false))

theorem queryNodesPrefix_succ {n r q : ℕ} (base : ℕ) (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (count : ℕ) (hc : count < q) :
    queryNodesPrefix base oracle projections (count+1)=queryNodesPrefix base oracle projections count++
      queryNodes (base+count*(2*oracle.size+1)) oracle (projections ⟨count,hc⟩) := by
  simp [queryNodesPrefix,List.range_succ,List.flatMap_append,List.getElem?_ofFn,hc]

theorem queryPrefix_nodes {n r q : ℕ} (prior : BooleanDAGBuilder r) (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (count : ℕ) (hc : count ≤ q) :
    (queryPrefix prior oracle projections count hc).builder.nodes=
      prior.nodes++queryNodesPrefix prior.nodes.length oracle projections count := by
  induction count with
  | zero => simp [queryPrefix,queryNodesPrefix]
  | succ count ih =>
    simp only [queryPrefix]
    rw [copyQuery_nodes,(queryPrefix prior oracle projections count (by omega)).length,ih,
      queryNodesPrefix_succ _ _ _ count (by omega),List.append_assoc]

theorem queryBank_nodes {n r q : ℕ} (prior : BooleanDAGBuilder r) (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) :
    (queryBank prior oracle projections).nodes=
      prior.nodes++queryNodesPrefix prior.nodes.length oracle projections q :=
  queryPrefix_nodes prior oracle projections q (by omega)

end NearCubicWires.RepairOrdinary.PCPPNative

import Proof.CaseAnalysis.RecoveryWorkspace

/-! Discharge the complete original universal-table/query allocation tree
from its final graph bound. No intermediate graph counts are computed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open BoundedOracleStructuralCircuit FinitePredicateCircuit OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_prefix_le {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total : ℕ) (ht : total ≤ bound)
    (k : ℕ) (hk : k ≤ total) :
    (compileUniversalNodes b address k (hk.trans ht)).final.nodes.length ≤
      (compileUniversalNodes b address total ht).final.nodes.length := by
  induction total generalizing k with
  | zero=>
    have he : k=0 := by omega
    subst k
    exact le_rfl
  | succ total ih=>
    by_cases hkt : k ≤ total
    · let before:=compileUniversalNodes b address total (by omega)
      let node:=compileUniversalNode before.final ⟨total,by omega⟩ address before.values
      have hp:=ih (by omega) k hkt
      exact hp.trans node.compiled.extension.length_le
    · have he : k=total+1 := by omega
      subst k
      exact le_rfl

theorem output_table_le {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total : ℕ) (ht : total ≤ bound) :
    (compileUniversalNodes b address total ht).final.nodes.length ≤
      (compileUniversalOutput b address total ht).compiled.final.nodes.length := by
  let table:=compileUniversalNodes b address total ht
  exact (compileFirstFieldSelect table.final ⟨total,by omega⟩ table.values).extension.length_le

theorem table_fits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total G : ℕ) (ht : total ≤ bound)
    (hg : (compileUniversalOutput b address total ht).compiled.final.nodes.length ≤ G) :
    RecoveryBoundedTable.Fits b address total (workspace n bound G) ht := by
  intro k hk
  let before:=compileUniversalNodes b address k (by omega)
  apply node_fits before.final ⟨k,by omega⟩ address before.values G
  · have he:=compileUniversalNodes_values_length b address k (by omega : k ≤ bound)
    change before.values.length=k at he
    omega
  · have hp:=(table_prefix_le b address total ht (k+1) (by omega)).trans
      ((output_table_le b address total ht).trans hg)
    rw [RecoveryBoundedTable.final_succ b address k (by omega)] at hp
    exact hp

theorem output_fits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total G : ℕ) (ht : total ≤ bound)
    (hg : (compileUniversalOutput b address total ht).compiled.final.nodes.length ≤ G) :
    RecoveryBoundedTableOutput.Fits b address total (workspace n bound G) ht := by
  let row : Fin (bound+1):=⟨total,by omega⟩
  have hi:=index_le_workspace (n:=n) (G:=G) row 6 (by unfold rowWidth; omega)
  have hF : boundedCircuitFieldLimit n bound ≤ rowWidth n bound := by unfold rowWidth; omega
  have hstart : RecoveryBoundedTable.index n bound total 6=
      RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6 := rfl
  have htable:=(output_table_le b address total ht).trans hg
  have hw:=(workspace_bounds n bound G).2.2.2
  refine ⟨?_,temporary_le_workspace htable (by omega),graph_le_workspace hg,by omega⟩
  rw [hstart]
  omega

/-- Every physical query allocation follows from the final original query
graph size, including every reusable-table temporary-position premise. -/
theorem queries_fits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total G : ℕ) (ht : total ≤ bound) (addresses : List (BitInput n))
    (hg : (compileUniversalOutputs b total ht addresses).final.nodes.length ≤ G) :
    RecoveryBoundedQueries.Fits b total (workspace n bound G) ht addresses := by
  induction addresses generalizing b with
  | nil=>exact True.intro
  | cons address rest ih=>
    let first:=compileUniversalOutput b address total ht
    let tail:=compileUniversalOutputs first.compiled.final total ht rest
    have htail : tail.final.nodes.length ≤ G := hg
    have hfirst : first.compiled.final.nodes.length ≤ G := tail.extension.length_le.trans htail
    exact ⟨table_fits b address total G ht hfirst,
      output_fits b address total G ht hfirst,ih first.compiled.final htail⟩

end NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace

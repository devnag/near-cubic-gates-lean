import Proof.CaseAnalysis.RecoveryRowLoopFollow

/-! The original verifier-row recursion and its saved-reference spine.
The spine records calls to compileVerifierRow itself, including their exact
builders; the existing reverse AND fold supplies only the deferred nodes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open SourceInterfaces RepairSource CanonicalRecoveryLanguage
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {machine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
variable (pcp : ProjectionPCP machine timeBound) {n bound : ℕ} (x : BitInput n)
variable (count : ℕ) (hc : count≤bound)

theorem nil_nodes (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)) :
    (compileVerifierRows pcp x count hc b []).final.nodes=b.nodes++[.const true] := rfl
theorem nil_output (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)) :
    (compileVerifierRows pcp x count hc b []).output.val=b.nodes.length := rfl
theorem cons_nodes (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (r : BitInput (pcp.nativeWidth n)) (rows : List (BitInput (pcp.nativeWidth n))) :
    let head:=compileVerifierRow pcp x b count hc r
    let tail:=compileVerifierRows pcp x count hc head.compiled.final rows
    (compileVerifierRows pcp x count hc b (r::rows)).final.nodes=
      tail.final.nodes++[.and head.compiled.output.val tail.output.val] := rfl
theorem cons_output (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (r : BitInput (pcp.nativeWidth n)) (rows : List (BitInput (pcp.nativeWidth n))) :
    (compileVerifierRows pcp x count hc b (r::rows)).output.val=
      (compileVerifierRows pcp x count hc (compileVerifierRow pcp x b count hc r).compiled.final rows).final.nodes.length := rfl
theorem tail_bound (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (r : BitInput (pcp.nativeWidth n)) (rows : List (BitInput (pcp.nativeWidth n))) (G : ℕ)
    (h : (compileVerifierRows pcp x count hc b (r::rows)).final.nodes.length≤G) :
    (compileVerifierRows pcp x count hc (compileVerifierRow pcp x b count hc r).compiled.final rows).final.nodes.length≤G := by
  rw [cons_nodes,List.length_append,List.length_singleton] at h
  omega
theorem head_bound (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (r : BitInput (pcp.nativeWidth n)) (rows : List (BitInput (pcp.nativeWidth n))) (G : ℕ)
    (h : (compileVerifierRows pcp x count hc b (r::rows)).final.nodes.length≤G) :
    (compileVerifierRow pcp x b count hc r).compiled.final.nodes.length≤G :=
  (compileVerifierRows pcp x count hc _ rows).extension.length_le.trans (tail_bound pcp x count hc b r rows G h)

inductive Spine : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound) →
    List (BitInput (pcp.nativeWidth n)) → BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound) → List ℕ → Prop
  | nil (b) : Spine b [] b []
  | cons (b r rows next refs) :
      Spine (compileVerifierRow pcp x b count hc r).compiled.final rows next refs →
      Spine b (r::rows) next ((compileVerifierRow pcp x b count hc r).compiled.output.val::refs)

theorem Spine.append {b c d} {rows rest refs saved}
    (h : Spine pcp x count hc b rows c refs) (g : Spine pcp x count hc c rest d saved) :
    Spine pcp x count hc b (rows++rest) d (refs++saved) := by
  induction h with
  | nil=>exact g
  | cons b r rows next refs h ih=>exact .cons b r (rows++rest) d (refs++saved) (ih g)

theorem Spine.original {b c rows refs} (h : Spine pcp x count hc b rows c refs) :
    (compileVerifierRows pcp x count hc b rows).final.nodes=c.nodes++allSuffix c.nodes.length refs ∧
    (compileVerifierRows pcp x count hc b rows).output.val=c.nodes.length+refs.length := by
  induction h with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b r rows next refs h ih=>
    constructor
    · rw [cons_nodes,ih.2,ih.1]
      simp only [allSuffix,List.append_assoc]
    · rw [cons_output,ih.1,List.length_append,RecoveryBoundedClauseList.allSuffix_length,List.length_cons]

def randomnesses (R k total : ℕ):=(List.range' k total).map (bitInputOfCode R)
theorem randomnesses_cons (R k total : ℕ) :
    randomnesses R k (total+1)=bitInputOfCode R k::randomnesses R (k+1) total := by
  simp only [randomnesses,List.range'_succ,List.map_cons]
theorem randomnesses_append (R k total : ℕ) :
    randomnesses R k (total+1)=randomnesses R k total++[bitInputOfCode R (k+total)] := by
  simp only [randomnesses,List.range'_1_concat,List.map_append,List.map_cons,List.map_nil]
theorem randomnesses_all (R : ℕ) : randomnesses R 0 (2^R)=allRandomness R := by
  simp only [randomnesses,allRandomness,List.range_eq_range']
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows

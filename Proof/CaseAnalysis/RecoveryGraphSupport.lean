import Proof.CaseAnalysis.RecoveryWorkspacePolynomial
import Proof.PCP.PCPPRequestSourceRuntime

/-! Uniform support for the original builder's retained native graph.
The builder's own well-formedness bounds every reference; no graph prepass
or separate traversal of the emitted bytes is introduced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryGraphSupport
open PaddedRunnerBudgetClosure
open private stream_length_le from Proof.PCP.PCPPRequestSourceRuntime
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stream_bound {n : ℕ} (b : BooleanDAGBuilder n) (G : ℕ)
    (hg : b.nodes.length ≤ G) :
    (b.nodes.flatMap PCPPRequestNodeSchema.native).length ≤ G*(6*(n+G+5)+3) := by
  have h : (b.nodes.flatMap PCPPRequestNodeSchema.native).length ≤
      b.nodes.length*(6*(n+b.nodes.length+5)+3) := by
    apply stream_length_le
    intro node hn
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hn
    rw [←hi]
    exact PCPPRequestRuntime.native_width (b.finish i) i
  exact h.trans (Nat.mul_le_mul hg (by omega))

theorem word_bound {n : ℕ} (b : BooleanDAGBuilder n) (G P : ℕ)
    (pre : List Bool) (hg : b.nodes.length ≤ G) (hp : pre.length ≤ P) :
    (pre++b.nodes.flatMap PCPPRequestNodeSchema.native).length ≤
      P+G*(6*(n+G+5)+3) := by
  rw [List.length_append]
  exact Nat.add_le_add hp (stream_bound b G hg)

theorem workspace_word_bound {n W : ℕ} (b : BooleanDAGBuilder n) (P : ℕ)
    (pre : List Bool) (hn : n ≤ W) (hg : b.nodes.length ≤ W) (hp : pre.length ≤ P) :
    (pre++b.nodes.flatMap PCPPRequestNodeSchema.native).length ≤
      P+W*(6*(W+W+5)+3) := by
  exact (word_bound b W P pre hg hp).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left W (by omega)) P)

theorem word_sourcePoly {arity graph preCap : ℕ → ℕ}
    (ha : SourcePoly arity) (hg : SourcePoly graph) (hp : SourcePoly preCap) :
    SourcePoly (fun n => preCap n+graph n*(6*(arity n+graph n+5)+3)) :=
  hp.add (hg.mul ((((ha.add hg).add (polyDominated_const 5)).const_mul 6).add
    (polyDominated_const 3)))

end NearCubicWires.RepairOrdinary.CloseoutRecoveryGraphSupport

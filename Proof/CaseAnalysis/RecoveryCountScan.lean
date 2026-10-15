import Proof.CaseAnalysis.RecoveryCountForward

/-! The actual original fixed-count compiler supplies every finite count
iteration. The driver is the original full bound, including every saved ref. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedClauseList (stackWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

def scanHeads (H : Fin 152→ℕ) (pos : ℕ) : Fin 153→ℕ:=
  Fin.addCases (m:=152) (n:=1) (motive:=fun _=>ℕ) H (fun _=>pos)
def scanData (A : Fin 152→List Bool) (total : ℕ) : Fin 153→List Bool:=
  Fin.addCases (m:=152) (n:=1) (motive:=fun _=>List Bool) A (fun _=>CompareMachine.word total)

theorem Driver.configuration_heads {s : ℕ} (worker : Machine 152 s) (phase : Fin 5)
    (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool)
    (extra : Fin 12→List Bool) (driver : ℕ) :
    (configuration worker phase z b k stack extra driver).heads=scanHeads (z.heads b stack) driver := rfl
theorem Driver.configuration_tapes {s : ℕ} (worker : Machine 152 s) (phase : Fin 5)
    (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool)
    (extra : Fin 12→List Bool) (driver : ℕ) :
    (configuration worker phase z b k stack extra driver).tapes=scanData (z.bank b k stack extra) bound := rfl
theorem Driver.configuration_start {s : ℕ} (worker : Machine 152 s)
    (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool)
    (extra : Fin 12→List Bool) (driver : ℕ) :
    (configuration worker 0 z b k stack extra driver).control=(machine worker).start := rfl

noncomputable def scanMachine:=Driver.machine RecoveryBoundedCountPipeline.machine
def scanBudget (B W R bound : ℕ):=bound*(bodyBudget B W R+2)+bound+3

theorem scan_run (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (extra : Fin 12→List Bool)
    (rawWidth : extra 0=RecoveryBoundedGrammarScalarAdd.unary z.base.B (rowWidth R bound))
    (rawQ : extra 3=RecoveryBoundedGrammarScalarAdd.unary z.base.B Q)
    (rawClauses : extra 4=RecoveryBoundedGrammarScalarAdd.unary z.base.B (Codec.clauses p).length)
    (rawR : extra 5=RecoveryBoundedGrammarScalarAdd.unary z.base.B (R+1))
    (hS : stack.length+(bound+z.base.W)*(2*z.base.W+1)≤z.base.S)
    (hP : stack.length+(bound+2^R+1)*(2*z.base.W+1)≤z.P)
    (hFinal : (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b
      (List.finRange bound)).final.nodes.length≤z.base.G) :
    ∃ f : Forward z b (List.finRange bound), ∃ r,
      runFrom scanMachine (scanBudget z.base.B z.base.W R bound)
        (Driver.configuration RecoveryBoundedCountPipeline.machine 0 z b 0 stack extra 1)=some r ∧
      r.final=Driver.configuration RecoveryBoundedCountPipeline.machine 3 z f.next bound
        (stack++stackWord f.refs) extra 1 ∧ r.steps ≤ scanBudget z.base.B z.base.W R bound := by
  have supplier:=fun b count stack hs hg hp=>z.body_run b count stack extra rawWidth rawQ rawClauses rawR hs hg hp
  have h:=Driver.forward_run RecoveryBoundedCountPipeline.machine z extra supplier b bound 0 stack
    (by omega) hS hP (by simpa only [List.drop_zero] using hFinal)
  simpa only [scanMachine,scanBudget,List.drop_zero] using h

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform

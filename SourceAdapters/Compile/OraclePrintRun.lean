import SourceAdapters.Compile.OraclePrintEmit

/-!
# The whole printing run

proof of `thm:short-pcp-ours`; proof of `cor:short-pcp-clock`: one fixed program reads the request, builds the circuit node by node (input gates,
initial formulas, `fuel` rounds, verdict) and writes its native word. `mainP p T` is that program; **`mainP_spec`**:
from the initial state on the entry word `LengthPrefix.wrapped r.word`, it writes exactly
`OracleOutput.word ⟨r.ell, requestCircuit p r⟩` within `runCost` steps, under the run-wide side conditions `Cfg` and
the register-width conditions of the parse and of the node printer.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.Bindings.MW20 NearCubicWires.RepairSource
open NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Compile (OracleCompilationRequest)
open NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicGates.Adapters.Compile.OracleExpressions (requestStream requestCircuit requestCircuit_stream)

set_option autoImplicit false

/-- **The printing program** of a fixed oracle program `p` (its two template families `T`). -/
def mainP (p : OrdinaryOracleProgram) (T : Templates p) : St VV MM :=
  .seq (parse p.base.tapeCount p.base.stateCount) (.seq inputsP (.seq (vecCopyP T.init)
    (.seq (roundsP T.trans (addrT p)) (.seq (verdictP (verdU p)) printP))))

/-- The step bound of the printing run. -/
def runCost (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) (L : ℕ) : ℕ :=
  parseCost p r + (15 * r.ell + 4) + ((T.init.ucost + Qc L) * L + (12 * L + 40) * L + 10 * L + 30) +
    (r.fuel * (roundCost (addrT p).ucost T.trans.ucost L + 4) + 4) + (((verdU p).ucost + Qc L) * L + 12 * L + 40) +
    printCost r.ell (requestStream p r).1.length ((requestStream p r).1.flatMap nodeRec).length
      (natBitLength (r.ell + (requestStream p r).1.length + 5)) + 10

variable {C : Ctx}

theorem mainP_spec (p : OrdinaryOracleProgram) (T : Templates p) (r : OracleCompilationRequest) {V L : ℕ}
    (hinp : C.inp = Proximity.LengthPrefix.wrapped r.word) (cf : Cfg C p T r V L) (B : ℕ)
    (hB : 2 * B + 2 ≤ 2 ^ C.Wd) (hX : parseX p r ^ 20 ≤ B) (hnb : natBitLength r.word.length + 2 ≤ C.Wd)
    (hW3 : 3 ≤ C.Wd) (hE : natBitLength (r.ell + (requestStream p r).1.length + 5) + 2 < 2 ^ C.Wd) :
    Hx C (mainP p T) a0 (fun b n => b.out = OracleOutput.word ⟨r.ell, requestCircuit p r⟩ ∧ n ≤ runCost p T r L) := by
  have hLN := cf.hLN
  have hLW := cf.hL
  obtain ⟨n1, n2, n3⟩ := plan_eq p T r
  -- parse
  refine Hx.seq' (Hx.ofHs (parse_spec p r hinp B hB hX hnb)) (fun b1 c1 ⟨hc1, r1, g1, w1⟩ => ?_)
  -- input gates
  refine Hx.seq' (Hx.ofHs (inputsP_spec (C := C) p r b1 r1 g1 (by omega))) (fun b2 c2 ⟨hc2, r2, g2, w2⟩ => ?_)
  -- the initial vector
  have hti : ∀ j : Fin (clockBits p (requestWidth r) r.fuel), tokF T.init (reqD r) (reqEnv r) j.val =
      postR (fun i => i.val) (initialExpression p r j) := fun j => (T.init_eq r j).symm
  have htokI := vec_tok_le (List.range r.ell) (fun i : Fin r.ell => i.val) (clockBits p (requestWidth r) r.fuel)
    (initialExpression p r) (tokF T.init (reqD r) (reqEnv r)) (initPS r.ell) hti
  have hst : (startPS p T r).1.cnt ≤ (planPS p T r).cnt := by
    have m := roundsPS_cnt_mono (p := p) (T := T) (r := r) 0 r.fuel (startPS p T r)
    rw [Nat.zero_add] at m
    exact m.trans roundsEnd_le_plan
  have hst' : (PS.vec (List.range r.ell) (tokF T.init (reqD r) (reqEnv r)) (clockBits p (requestWidth r) r.fuel)
      (initPS r.ell)).1.cnt ≤ (planPS p T r).cnt := hst
  refine Hx.seq' (vecCopy_spec cf T.init (by have := T.init_depth; omega) T.init_tneed cf.okI (initPS r.ell)
    (List.range r.ell) b2 r2 g2 (by simp; omega) (by rw [w2, w1]; omega) (by omega)
    (by simp only [initPS, List.length_nil, Nat.zero_add]; have : (initPS r.ell).cnt = r.ell := rfl; omega))
    (fun b3 c3 ⟨r3, g3, w3, _, hc3⟩ => ?_)
  -- the rounds
  refine Hx.seq' (roundsP_spec cf b3 r3 g3 (by rw [w3]; omega)) (fun b4 c4 ⟨r4, g4, hc4⟩ => ?_)
  -- the verdict
  refine Hx.seq' (verdictP_spec cf b4 r4 g4) (fun b5 c5 ⟨v1, v2, v3, v4, g5, v6, hc5⟩ => ?_)
  -- the word
  obtain ⟨s1, s2⟩ := requestCircuit_stream p r
  have hsize : (requestCircuit p r).size = (requestStream p r).1.length := by
    show (requestCircuit p r).nodes.length = _; rw [s1]
  refine Hx.mono' (printP_spec (requestCircuit p r) b5 v6 (by rw [v1, s1]) (by rw [v3, s1]) g5.ell (by rw [v4, s2])
    g5.out hW3 (by omega) (by rw [hsize]; exact hE) (by rw [s1]; omega)) (fun b6 c6 ⟨p1, p2⟩ => ⟨p1, ?_⟩)
  rw [v2, v1, hsize, s1] at p2
  unfold runCost
  omega

end NearCubicGates.Adapters.Compile.OraclePrint

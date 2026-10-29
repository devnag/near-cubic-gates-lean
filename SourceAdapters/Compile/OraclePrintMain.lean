import SourceAdapters.Compile.OraclePrintRun
import SourceAdapters.Compile.OraclePrintAssembly
import SourceAdapters.Compile.OraclePrintTransResources

/-!
# X5(a): the join `ComputationToCircuit`

Paper context: proof of `thm:short-pcp-ours`, Step 4. Circuit conversion replaces proof reads by oracle
gates; the algorithm computes `T`, the affine instance `I_x`, `S` and `C^O_x` in polynomial time in `n` and
`log T`. `cor:short-pcp-clock` supplies the clock as an input integer.

For a fixed program `p`: the two template families are `Ti p`, `Tt p` (`Ti_eq_nat`, `Tt_eq_nat`); the run-wide
numbers are explicit polynomials in the request measure (`valueBound`, `tokenBound`); the register width
`2^(c·|natWord|w||)·a` of the cell context exceeds them for the constants `progA p`, `progC p`; the step count
`runCost` is at most `costCoefficient p · measure^15`. With `computationToCircuit_of_programs` this is
the whole join. **`computationToCircuit`** : `ComputationToCircuit`.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Compile (OracleCompilationRequest ComputationToCircuit)
open NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicGates.Adapters.Compile.OracleExpressions (requestStream requestCircuit requestCircuit_stream
  requestCircuit_false_iff requestStream_size requestCircuit_size_polynomial)
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

set_option autoImplicit false

/-! ## The template families (A1/A3) -/

/-- The initial and transition templates of `p` (`Ti`, `Tt`). -/
def templatesOf (p : OrdinaryOracleProgram) : Templates p where
  init := Ti p
  trans := Tt p
  init_eq r j := Ti_eq_nat p r j.val j.isLt
  trans_eq r j := Tt_eq_nat p r j.val j.isLt
  init_depth := Ti_depth p
  init_tneed := Ti_tneed p
  trans_depth := Tt_depth p
  trans_tneed := Tt_tneed p

/-! ## The run-wide numbers -/

section Numbers

variable (p : OrdinaryOracleProgram)

/-- Scale of the clock-wire count. -/
def kcOf : ℕ := 20 * (p.base.tapeCount + p.base.stateCount + 1)

/-- A bound on every constant of the four templates. -/
def kmaxOf : ℕ := (Ti p).kmax + (Tt p).kmax + (addrT p).kmax + (verdU p).kmax

/-- The value exponent of the four templates. -/
def evOf : ℕ := U.vx 1 (Ti p) + U.vx 1 (Tt p) + U.vx 1 (addrT p) + U.vx 1 (verdU p) + 1

/-- The value base. -/
def xOf (r : OracleCompilationRequest) : ℕ := (kcOf p + 1) * r.measure + kmaxOf p + 2

/-- The value bound `V`. -/
def valueBound (r : OracleCompilationRequest) : ℕ := xOf p r ^ evOf p

/-- The token bound `L`. -/
def tokenBound (r : OracleCompilationRequest) : ℕ :=
  2 * circuitCoefficient p.base.tapeCount p.base.stateCount * r.measure ^ 5 + (kcOf p + 3) * r.measure + 5

end Numbers

theorem measure_one (r : OracleCompilationRequest) : 1 ≤ r.measure := by
  unfold OracleCompilationRequest.measure; omega

theorem cb_le (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    clockBits p (requestWidth r) r.fuel ≤ kcOf p * r.measure := by
  have hw := requestWidth_bound r
  have hm := measure_one r
  have hf : r.fuel ≤ r.measure := by unfold OracleCompilationRequest.measure; omega
  unfold clockBits windowBits kcOf
  set t := p.base.tapeCount
  set s := p.base.stateCount
  set W := requestWidth r
  set m := r.measure
  have e1 : t * W ≤ t * (6 * m) := Nat.mul_le_mul_left _ hw
  have e2 : t * (W + 1) ≤ t * (6 * m + m) := Nat.mul_le_mul_left _ (by omega)
  have e3 : s ≤ s * m := Nat.le_mul_of_pos_right _ hm
  nlinarith

theorem ell_le (r : OracleCompilationRequest) : r.ell ≤ r.measure := by
  unfold OracleCompilationRequest.measure; omega

theorem nodes_le (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (requestStream p r).1.length ≤ circuitCoefficient p.base.tapeCount p.base.stateCount * r.measure ^ 5 :=
  requestStream_size p r

theorem plan_cnt (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (planPS p (templatesOf p) r).cnt = (requestStream p r).1.length := (plan_eq p (templatesOf p) r).2.2

/-! ## The run configuration holds -/

theorem cfg_ok (C : Ctx) (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (hV : 2 * valueBound p r + 2 ≤ 2 ^ C.Wd) (hL : 2 * tokenBound p r + 2 ≤ 2 ^ C.Wd) (h8 : 8 ≤ 2 ^ C.Wd) :
    Cfg C p (templatesOf p) r (valueBound p r) (tokenBound p r) := by
  set m := r.measure with hmdef
  have hm := measure_one r
  have hcb := cb_le p r
  have hell := ell_le r
  have hX : kmaxOf p + 2 ≤ xOf p r := by unfold xOf; omega
  have hX1 : 1 ≤ xOf p r := by omega
  have hX2 : 2 ≤ xOf p r := by omega
  have hcbX : clockBits p (requestWidth r) r.fuel + r.ell ≤ xOf p r := by
    unfold xOf; rw [← hmdef]; nlinarith
  have henv : ∀ j, (reqEnv r).getD j 0 ≤ xOf p r := fun j => by
    have := reqEnv_le r j; unfold xOf kcOf; rw [← hmdef]; nlinarith
  have hsnoc : ∀ x, x ≤ xOf p r → ∀ j, (reqEnv r ++ [x]).getD j 0 ≤ xOf p r ^ 1 := fun x hx j => by
    rw [pow_one]; exact getD_snoc_le _ _ _ henv hx j
  have hVle : ∀ u, U.vx 1 u ≤ evOf p → xOf p r ^ U.vx 1 u ≤ valueBound p r := fun u hu =>
    Nat.pow_le_pow_right hX1 hu
  have kTi : (Ti p).kmax ≤ kmaxOf p := by unfold kmaxOf; omega
  have kTt : (Tt p).kmax ≤ kmaxOf p := by unfold kmaxOf; omega
  have kA : (addrT p).kmax ≤ kmaxOf p := by unfold kmaxOf; omega
  have kV : (verdU p).kmax ≤ kmaxOf p := by unfold kmaxOf; omega
  have vTi : U.vx 1 (Ti p) ≤ evOf p := by unfold evOf; omega
  have vTt : U.vx 1 (Tt p) ≤ evOf p := by unfold evOf; omega
  have vA : U.vx 1 (addrT p) ≤ evOf p := by unfold evOf; omega
  have vV : U.vx 1 (verdU p) ≤ evOf p := by unfold evOf; omega
  refine ⟨hV, Nat.one_le_pow _ _ hX1, hL, h8, ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [plan_cnt]
    have hn := nodes_le p r
    have hD : (reqD r).length ≤ 2 * m := by
      unfold reqD; rw [frame_length']; unfold OracleCompilationRequest.measure at hmdef; omega
    unfold tokenBound
    rw [← hmdef]
    nlinarith
  · calc clockBits p (requestWidth r) r.fuel + r.ell ≤ xOf p r := hcbX
      _ = xOf p r ^ 1 := (pow_one _).symm
      _ ≤ valueBound p r := Nat.pow_le_pow_right hX1 (by unfold evOf; omega)
  · exact U.okV_of_pow (reqD r) (xOf p r) (kmaxOf p) hX (addrT p) kA 1 _ le_rfl (hsnoc j (by omega)) _ (hVle _ vA)
  · exact U.okV_of_pow (reqD r) (xOf p r) (kmaxOf p) hX (Ti p) kTi 1 _ le_rfl (hsnoc j (by omega)) _ (hVle _ vTi)
  · exact U.okV_of_pow (reqD r) (xOf p r) (kmaxOf p) hX (Tt p) kTt 1 _ le_rfl (hsnoc j (by omega)) _ (hVle _ vTt)
  · exact U.okV_of_pow (reqD r) (xOf p r) (kmaxOf p) hX (verdU p) kV 1 _ le_rfl (fun j => by rw [pow_one]; exact henv j)
      _ (hVle _ vV)

/-! ## The register width -/

section Width

variable (p : OrdinaryOracleProgram)

/-- Everything the run must fit into the register width. -/
def bigOf (r : OracleCompilationRequest) : ℕ :=
  2 * valueBound p r + 2 * tokenBound p r + 2 * parseX p r ^ 20 + 2 * r.measure + r.ell +
    (requestStream p r).1.length + 20

/-- The width exponent. -/
def progC : ℕ := evOf p + 20

/-- The coefficient of `bigOf`. -/
def bigCoef : ℕ :=
  2 * (kcOf p + kmaxOf p + 3) ^ evOf p +
    2 * (2 * circuitCoefficient p.base.tapeCount p.base.stateCount + kcOf p + 8) +
    2 * (2 * p.base.tapeCount + p.base.stateCount + 16) ^ 20 + circuitCoefficient p.base.tapeCount p.base.stateCount + 23

/-- The width coefficient. -/
def progA : ℕ := bigCoef p + 1

theorem big_le (r : OracleCompilationRequest) : bigOf p r ≤ bigCoef p * r.measure ^ progC p := by
  set m := r.measure with hmdef
  have hm : 1 ≤ m := measure_one r
  set c := progC p
  set cc := circuitCoefficient p.base.tapeCount p.base.stateCount
  have hm5 : m ≤ m ^ 5 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 5 := Nat.pow_le_pow_right hm (by omega)
  have hpc : ∀ d, d ≤ c → m ^ d ≤ m ^ c := fun d hd => Nat.pow_le_pow_right hm hd
  have h1c : 1 ≤ m ^ c := Nat.one_le_pow _ _ hm
  -- the value bound
  have hx : xOf p r ≤ (kcOf p + kmaxOf p + 3) * m := by unfold xOf; rw [← hmdef]; nlinarith
  have hV : valueBound p r ≤ (kcOf p + kmaxOf p + 3) ^ evOf p * m ^ c := by
    unfold valueBound
    calc xOf p r ^ evOf p ≤ ((kcOf p + kmaxOf p + 3) * m) ^ evOf p := Nat.pow_le_pow_left hx _
      _ = (kcOf p + kmaxOf p + 3) ^ evOf p * m ^ evOf p := mul_pow _ _ _
      _ ≤ (kcOf p + kmaxOf p + 3) ^ evOf p * m ^ c := Nat.mul_le_mul_left _ (hpc _ (by unfold c progC; omega))
  -- the token bound
  have hL : tokenBound p r ≤ (2 * cc + kcOf p + 8) * m ^ c := by
    have e : tokenBound p r ≤ (2 * cc + kcOf p + 8) * m ^ 5 := by
      unfold tokenBound; rw [← hmdef]
      have : (kcOf p + 3) * m ≤ (kcOf p + 3) * m ^ 5 := Nat.mul_le_mul_left _ hm5
      nlinarith
    exact e.trans (Nat.mul_le_mul_left _ (hpc 5 (by unfold c progC; omega)))
  -- the parse scale
  have hP : parseX p r ^ 20 ≤ (2 * p.base.tapeCount + p.base.stateCount + 16) ^ 20 * m ^ c := by
    have e : parseX p r ≤ (2 * p.base.tapeCount + p.base.stateCount + 16) * m := by
      unfold parseX; rw [← hmdef]; nlinarith
    calc parseX p r ^ 20 ≤ ((2 * p.base.tapeCount + p.base.stateCount + 16) * m) ^ 20 := Nat.pow_le_pow_left e _
      _ = (2 * p.base.tapeCount + p.base.stateCount + 16) ^ 20 * m ^ 20 := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (hpc 20 (by unfold c progC; omega))
  -- the rest
  have hR : 2 * m + r.ell + (requestStream p r).1.length + 20 ≤ (cc + 23) * m ^ c := by
    have hn := nodes_le p r
    have hell := ell_le r
    have e : 2 * m + r.ell + (requestStream p r).1.length + 20 ≤ (cc + 23) * m ^ 5 := by
      rw [← hmdef] at hn hell; nlinarith
    exact e.trans (Nat.mul_le_mul_left _ (hpc 5 (by unfold c progC; omega)))
  unfold bigOf bigCoef
  nlinarith

/-- The register width of the printing context exceeds `bigOf`. -/
theorem width_big (r : OracleCompilationRequest) :
    bigOf p r ≤ (ctxOf noCallee (oracleSz (progA p) (progC p)) (entryWord r)).Wd := by
  have hw := entryWidth_ge (progA p) (progC p) r
  have hl : r.word.length + 1 = 2 * r.measure + 2 := by rw [requestWord_length]
  rw [hl] at hw
  have hm : r.measure ^ progC p ≤ (2 * r.measure + 2) ^ progC p := Nat.pow_le_pow_left (by omega) _
  have := big_le p r
  have : bigCoef p * r.measure ^ progC p ≤ (2 * r.measure + 2) ^ progC p * progA p := by
    unfold progA; rw [Nat.mul_comm (bigCoef p)]
    exact Nat.mul_le_mul hm (by omega)
  omega

end Width

/-! ## The step count -/

section Cost

variable (p : OrdinaryOracleProgram)

theorem flatMap_nodeRec_le {n k : ℕ} (l : List (OracleNode n k)) : (l.flatMap nodeRec).length ≤ (k + 3) * l.length := by
  induction l with
  | nil => simp
  | cons nd l ih =>
      have := nodeArgs_length_le nd
      simp only [List.flatMap_cons, List.length_append, nodeRec, List.length_cons, List.length_nil] at ih ⊢
      nlinarith

/-- The scale of the step count. -/
def yCoef : ℕ :=
  3 * circuitCoefficient p.base.tapeCount p.base.stateCount + kcOf p + p.base.tapeCount + p.base.stateCount +
    (Ti p).ucost + (Tt p).ucost + (addrT p).ucost + (verdU p).ucost + 1000

/-- The coefficient of the step count. -/
def costCoef : ℕ := 2000 * yCoef p ^ 3

theorem mul_le_YY {x y A B Y : ℕ} (hx : x ≤ A * Y) (hy : y ≤ B * Y) : x * y ≤ (A * B) * (Y * Y) :=
  (Nat.mul_le_mul hx hy).trans (le_of_eq (by ring))

theorem mul_le_YYY {x y A B Y : ℕ} (hx : x ≤ A * Y) (hy : y ≤ B * (Y * Y)) : x * y ≤ (A * B) * (Y * Y * Y) :=
  (Nat.mul_le_mul hx hy).trans (le_of_eq (by ring))

/-- **The printing run takes at most `costCoef p · measure^15` steps.** -/
theorem runCost_le (r : OracleCompilationRequest) :
    runCost p (templatesOf p) r (tokenBound p r) ≤ costCoef p * r.measure ^ 15 := by
  set m := r.measure with hmdef
  have hm : 1 ≤ m := measure_one r
  set Y := yCoef p * m ^ 5 with hYdef
  set L := tokenBound p r
  have hm5 : m ≤ m ^ 5 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 5 := Nat.pow_le_pow_right hm (by omega)
  have h15 : 1 ≤ m ^ 5 := Nat.one_le_pow _ _ hm
  have hYc : ∀ x, x ≤ yCoef p → x ≤ Y := fun x hx => hx.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hY1000 : 1000 ≤ Y := hYc _ (by unfold yCoef; omega)
  have hn := nodes_le p r
  have hell := ell_le r
  have hf : r.fuel ≤ m := by rw [hmdef]; unfold OracleCompilationRequest.measure; omega
  have hYm : ∀ k, k ≤ yCoef p → k * m ^ 5 ≤ Y := fun k hk => Nat.mul_le_mul_right _ hk
  have hmY : m ≤ Y := hm5.trans (by have := hYm 1 (by unfold yCoef; omega); omega)
  have hLY : L ≤ Y := by
    have : tokenBound p r ≤ (2 * circuitCoefficient p.base.tapeCount p.base.stateCount + kcOf p + 8) * m ^ 5 := by
      unfold tokenBound; rw [← hmdef]
      have : (kcOf p + 3) * m ≤ (kcOf p + 3) * m ^ 5 := Nat.mul_le_mul_left _ hm5
      nlinarith
    exact this.trans (hYm _ (by unfold yCoef; omega))
  have hNY : (requestStream p r).1.length + r.ell + 6 ≤ Y := by
    have : (requestStream p r).1.length + r.ell + 6 ≤ (circuitCoefficient p.base.tapeCount p.base.stateCount + 7) * m ^ 5 := by
      rw [← hmdef] at hn hell; nlinarith
    exact this.trans (hYm _ (by unfold yCoef; omega))
  have hts : p.base.tapeCount + p.base.stateCount ≤ Y := hYc _ (by unfold yCoef; omega)
  have huI : (Ti p).ucost ≤ Y := hYc _ (by unfold yCoef; omega)
  have huT : (Tt p).ucost ≤ Y := hYc _ (by unfold yCoef; omega)
  have huA : (addrT p).ucost ≤ Y := hYc _ (by unfold yCoef; omega)
  have huV : (verdU p).ucost ≤ Y := hYc _ (by unfold yCoef; omega)
  have hYY : Y ≤ Y * Y := Nat.le_mul_of_pos_right _ (by omega)
  have hYYY : Y * Y ≤ Y * Y * Y := Nat.le_mul_of_pos_right _ (by omega)
  have hQ : Qc L ≤ 160 * Y := by unfold Qc; omega
  -- the vectors
  have a1 : ((Ti p).ucost + Qc L) * L ≤ (161 * 1) * (Y * Y) := mul_le_YY (by omega) (by omega)
  have a2 : (12 * L + 40) * L ≤ (52 * 1) * (Y * Y) := mul_le_YY (by omega) (by omega)
  have a3 : ((Tt p).ucost + Qc L) * L ≤ (161 * 1) * (Y * Y) := mul_le_YY (by omega) (by omega)
  have a4 : ((addrT p).ucost + Qc L) * L ≤ (161 * 1) * (Y * Y) := mul_le_YY (by omega) (by omega)
  have a5 : ((verdU p).ucost + Qc L) * L ≤ (161 * 1) * (Y * Y) := mul_le_YY (by omega) (by omega)
  have hrc : roundCost (addrT p).ucost (Tt p).ucost L + 4 ≤ 580 * (Y * Y) := by unfold roundCost; omega
  have a6 : r.fuel * (roundCost (addrT p).ucost (Tt p).ucost L + 4) ≤ (1 * 580) * (Y * Y * Y) :=
    mul_le_YYY (by omega) hrc
  -- the printing
  have hB : (natBitLength (r.ell + (requestStream p r).1.length + 5)) ≤ Y := by have := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le (r.ell + (requestStream p r).1.length + 5); omega
  have hnc : nodeCost r.ell (natBitLength (r.ell + (requestStream p r).1.length + 5)) + 12 ≤ 102 * (Y * Y) := by
    unfold nodeCost
    have : (r.ell + 3) * (40 * (natBitLength (r.ell + (requestStream p r).1.length + 5)) + 50) ≤ (1 * 90) * (Y * Y) := mul_le_YY (by omega) (by omega)
    omega
  have a7 : (requestStream p r).1.length * (nodeCost r.ell (natBitLength (r.ell + (requestStream p r).1.length + 5)) + 12) ≤ (1 * 102) * (Y * Y * Y) := mul_le_YYY (by omega) hnc
  have a8 : ((requestStream p r).1.flatMap nodeRec).length ≤ (1 * 1) * (Y * Y) :=
    (flatMap_nodeRec_le _).trans (mul_le_YY (by omega) (by omega))
  have hfin : runCost p (templatesOf p) r L ≤ 2000 * (Y * Y * Y) := by
    unfold runCost printCost parseCost
    have e1 : (templatesOf p).init = Ti p := rfl
    have e2 : (templatesOf p).trans = Tt p := rfl
    rw [e1, e2]
    omega
  calc runCost p (templatesOf p) r L ≤ 2000 * (Y * Y * Y) := hfin
    _ = costCoef p * m ^ 15 := by rw [hYdef]; unfold costCoef; ring

end Cost

/-! ## The printing program runs; the join -/

theorem programRuns (p : OrdinaryOracleProgram) :
    OracleProgramRuns (requestCircuit p) (mainP p (templatesOf p)) (progA p) (progC p)
      (fun r => runCost p (templatesOf p) r (tokenBound p r)) := by
  intro r
  set C := ctxOf noCallee (oracleSz (progA p) (progC p)) (entryWord r) with hC
  have hbig := width_big p r
  rw [← hC] at hbig
  have hWlt : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hb : bigOf p r ≤ C.Wd := hbig
  unfold bigOf at hb
  have hnb : natBitLength r.word.length + 2 ≤ C.Wd := by
    have := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le r.word.length
    rw [requestWord_length] at this ⊢; omega
  have hE : natBitLength (r.ell + (requestStream p r).1.length + 5) + 2 < 2 ^ C.Wd := by
    have := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le (r.ell + (requestStream p r).1.length + 5)
    omega
  have h8 : 8 ≤ 2 ^ C.Wd := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by omega) (by omega)
  have cf := cfg_ok C p r (by omega) (by omega) h8
  exact mainP_spec (C := C) p (templatesOf p) r rfl cf (parseX p r ^ 20) (by omega) le_rfl hnb (by omega) hE

/-- **X5(a), the join** (proof of `thm:short-pcp-ours`; proof of `cor:short-pcp-clock`): for every fixed short oracle program, one
ordinary polynomial-time generator writes the exact MW20 oracle circuit of every bounded request. -/
theorem computationToCircuit : ComputationToCircuit :=
  computationToCircuit_of_programs fun p =>
    ⟨requestCircuit p, circuitCoefficient p.base.tapeCount p.base.stateCount, 5, mainP p (templatesOf p), progA p,
      progC p, costCoef p, 15, fun r => runCost p (templatesOf p) r (tokenBound p r), requestCircuit_false_iff p,
      requestCircuit_size_polynomial p, by unfold progA; omega, programRuns p, runCost_le p⟩

end NearCubicGates.Adapters.Compile.OraclePrint

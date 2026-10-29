import SourceAdapters.Joins.ComputationToCircuit
import SourceAdapters.Compile.OraclePrintBounds
import SourceAdapters.Proximity.PrefixSizes
import SourceAdapters.Code.Composition
import Proof.Gates.CounterMachine.PrefixFinal

/-!
# X5(a): the written oracle circuit from one printing program

Paper context: proof of `thm:short-pcp-ours`, Step 4. The algorithm computes `T`, the affine instance
`I_x`, the small-bias set `S`, and the oracle circuit `C^O_x` in polynomial time in `n` and `log T`.
`cor:short-pcp-clock` gives the same construction with the clock integer supplied as input.

The written object is the RAW native word `OracleOutput.word ⟨r.ell, circuit r⟩` (`Statement.lean:1500`), with no
outer frame: `WordFunction` frames only the input. For a GENERIC circuit family, the ordinary word function on the
actual compiler input `OracleCompilationRequest.word` is assembled from three existing actual programs, exactly as
`CNFAssembly` does for X5(b):
* `Proximity.LengthPrefix.polynomialWordFunction` prints `frame (natWord |w| ++ w)` (paid size header);
* `Cells.wordFunction_of_lang` runs a cell-language program whose register width is polynomial in `|w|`;
* `Code.composeFramed` composes the two, paying both rewinds.

The physical program contract is `OracleProgramRuns`: one fixed cell program prints exactly
`OracleOutput.word ⟨r.ell, circuit r⟩` in `N r ≤ K₀·measure^e` language steps. Its type names the paper quantity
(the written circuit `C^O_x`); nothing weaker typechecks. It is a premise of this assembly theorem; `computationToCircuit` in `OraclePrintMain.lean` supplies the concrete
request-to-node-stream program and proves the complete interface.

-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.SourceInterfaces
open NearCubicWires.Bindings.MW20
open NearCubicGates.Adapters.Compile (OracleCompilationRequest fixedArityOracle ComputationToCircuit)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

set_option autoImplicit false

/-! ## The request word -/

theorem frame_length (l : List Bool) : (RepairOrdinary.frame l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [RepairOrdinary.frame, ih]; ring

/-- The fixed request word has exactly `2·measure + 1` bits. -/
theorem requestWord_length (r : OracleCompilationRequest) : r.word.length = 2 * r.measure + 1 := by
  simp only [OracleCompilationRequest.word, OracleCompilationRequest.measure, List.length_append, frame_length,
    List.length_replicate]
  ring

theorem measure_positive (r : OracleCompilationRequest) : 1 ≤ r.measure := by
  unfold OracleCompilationRequest.measure; omega

/-- The request word is linear in the request measure. -/
theorem requestWord_succ_le (r : OracleCompilationRequest) : r.word.length + 1 ≤ 4 * r.measure := by
  have h := requestWord_length r
  have hm := measure_positive r
  omega

/-! ## The physical program contract -/

/-- The entry word of the printing program: the paid size header, then the request word. -/
def entryWord (r : OracleCompilationRequest) : List Bool :=
  Proximity.LengthPrefix.wrapped r.word

/-- The written circuit: the raw native output word (proof of `thm:short-pcp-ours`, `Statement.lean:1500`). -/
def circuitWord (circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell)
    (r : OracleCompilationRequest) : List Bool :=
  OracleOutput.word ⟨r.ell, circuit r⟩

/-- Cell size constants: register width `2^(c·L)·a` where `L` is the bit length of `|word r|`. -/
def oracleSz (a c : ℕ) : Sz := ⟨a, c, 0, 0, 0, 0⟩

/-- **The physical program contract** (proof of `thm:short-pcp-ours`; proof of `cor:short-pcp-clock`): the fixed cell program `main`, run on the
entry word, prints exactly the native word of the request's oracle circuit within `N r` language steps. -/
def OracleProgramRuns (circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell)
    (main : St VV MM) (a c : ℕ) (N : OracleCompilationRequest → ℕ) : Prop :=
  ∀ r, ∃ b n, Ex (ctxOf noCallee ⟨a, c, 0, 0, 0, 0⟩ (Proximity.LengthPrefix.wrapped r.word)) main a0 b n ∧
    b.out = OracleOutput.word ⟨r.ell, circuit r⟩ ∧ n ≤ N r

/-! ## The three-piece ordinary word function -/

/-- The paid size header, as a word function of the request. -/
noncomputable def prefixWordFunction : WordFunction OracleCompilationRequest OracleCompilationRequest.word
    (fun r => RepairOrdinary.frame (entryWord r)) (fun r => 10000 * (r.word.length + 1) ^ 2) where
  program := Proximity.LengthPrefix.polynomialWordFunction.program
  realizes r := Proximity.LengthPrefix.polynomialWordFunction.realizes r.word

/-- The printing program, as a word function of the request. -/
noncomputable def cellsWordFunction (circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell)
    (main : St VV MM) (a c : ℕ) (N : OracleCompilationRequest → ℕ) (ha : 1 ≤ a)
    (hrun : OracleProgramRuns circuit main a c N) :
    WordFunction OracleCompilationRequest entryWord (circuitWord circuit)
      (fun r => langBudget noCallee (oracleSz a c) VV MM (entryWord r) (N r)) :=
  wordFunction_of_lang entryWord (circuitWord circuit) noCallee (oracleSz a c) main N hrun (fun r => by
    change 1 ≤ 2 ^ (c * leadOnes (entryWord r)) * a
    have := Nat.one_le_two_pow (n := c * leadOnes (entryWord r))
    nlinarith)

/-- The composed actual word function on the fixed request word, printing the raw circuit word. -/
noncomputable def composedWordFunction (circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell)
    (main : St VV MM) (a c : ℕ) (N : OracleCompilationRequest → ℕ) (ha : 1 ≤ a)
    (hrun : OracleProgramRuns circuit main a c N) :
    WordFunction OracleCompilationRequest OracleCompilationRequest.word (circuitWord circuit)
      (fun r => (2 * (10000 * (r.word.length + 1) ^ 2) + 2) + 1 +
        (2 * langBudget noCallee (oracleSz a c) VV MM (entryWord r) (N r) + 2)) :=
  Code.composeFramed prefixWordFunction (cellsWordFunction circuit main a c N ha hrun)

/-! ## The budget is a fixed polynomial in the measure -/

/-- The coefficient of the composed budget; it depends only on the program constants `a c K₀`. -/
noncomputable def budgetCoefficient (a c K₀ : ℕ) : ℕ :=
  720005 + 2 * 10 ^ 6 * (K₀ + 1) * (a * 12 ^ c + a + c + TSK noCallee + 25) ^ 2

/-- proof of `cor:short-pcp-clock`: the composed budget is a fixed polynomial in the measure, with coefficient and degree depending
only on the program constants `a c K₀ e`, not on the request. -/
theorem composedBudget_le (a c K₀ e : ℕ) (N : OracleCompilationRequest → ℕ)
    (hN : ∀ r, N r ≤ K₀ * r.measure ^ e) (r : OracleCompilationRequest) :
    (2 * (10000 * (r.word.length + 1) ^ 2) + 2) + 1 +
        (2 * langBudget noCallee (oracleSz a c) VV MM (entryWord r) (N r) + 2) ≤
      budgetCoefficient a c K₀ * r.measure ^ (e + 2 * c + 2) := by
  unfold budgetCoefficient
  set m := r.measure with hmdef
  set T := TSK noCallee
  have hm : 1 ≤ m := measure_positive r
  have hw : r.word.length + 1 ≤ 6 * m := by have := requestWord_succ_le r; omega
  have hlang := NearCubicGates.Close.CounterMachine.PrefixProg.lang_le noCallee a c (entryWord r) (N r)
  have halloc := Proximity.LengthPrefix.allocation_bound a c r.word
  have hL : leadOnes (entryWord r) ≤ r.word.length + 1 := by
    change leadOnes (Proximity.LengthPrefix.wrapped r.word) ≤ _
    rw [Proximity.LengthPrefix.wrapped_leadOnes]
    exact NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le _
  have hI : (entryWord r).length ≤ 3 * (r.word.length + 1) :=
    Proximity.LengthPrefix.wrapped_length_bound r.word
  have hpc : (r.word.length + 1) ^ c ≤ 6 ^ c * m ^ c := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hw c
  have hmc : m ^ c ≤ m ^ (c + 1) := Nat.pow_le_pow_right hm (by omega)
  have hm1 : m ≤ m ^ (c + 1) := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ (c + 1) := Nat.pow_le_pow_right hm (by omega)
  have h1 : 1 ≤ m ^ (c + 1) := Nat.one_le_pow _ _ hm
  have h12 : a * 2 ^ c * 6 ^ c = a * 12 ^ c := by
    rw [mul_assoc, ← mul_pow]; norm_num
  have hW : 2 ^ (c * leadOnes (entryWord r)) * a ≤ a * 12 ^ c * m ^ (c + 1) := by
    calc 2 ^ (c * leadOnes (entryWord r)) * a ≤ (a * 2 ^ c) * (r.word.length + 1) ^ c := halloc
      _ ≤ (a * 2 ^ c) * (6 ^ c * m ^ c) := Nat.mul_le_mul_left _ hpc
      _ = a * 12 ^ c * m ^ c := by rw [← h12]; ring
      _ ≤ a * 12 ^ c * m ^ (c + 1) := Nat.mul_le_mul_left _ hmc
  set X := 2 ^ (c * leadOnes (entryWord r)) * a + leadOnes (entryWord r) +
    (entryWord r).length + a + c + T + 1 with hX
  set Cx := a * 12 ^ c + a + c + T + 25 with hCx
  have hXle : X ≤ Cx * m ^ (c + 1) := by
    have hlin : leadOnes (entryWord r) + (entryWord r).length ≤ 24 * m ^ (c + 1) := by
      omega
    have hc1 : a + c + T + 1 ≤ (a + c + T + 1) * m ^ (c + 1) := Nat.le_mul_of_pos_right _ h1
    rw [hCx, hX]
    nlinarith
  have hN1 : N r + 1 ≤ (K₀ + 1) * m ^ e := by
    have := hN r
    have he : 1 ≤ m ^ e := Nat.one_le_pow _ _ hm
    nlinarith
  have hlang' : langBudget noCallee (oracleSz a c) VV MM (entryWord r) (N r) ≤
      10 ^ 6 * (K₀ + 1) * Cx ^ 2 * m ^ (e + 2 * c + 2) := by
    refine hlang.trans ?_
    have hsq : X ^ 2 ≤ (Cx * m ^ (c + 1)) ^ 2 := Nat.pow_le_pow_left hXle 2
    have hpow : m ^ (e + 2 * c + 2) = m ^ e * (m ^ (c + 1)) ^ 2 := by
      rw [← pow_mul, ← pow_add]; ring_nf
    calc 10 ^ 6 * ((N r + 1) * X ^ 2) ≤ 10 ^ 6 * (((K₀ + 1) * m ^ e) * (Cx * m ^ (c + 1)) ^ 2) := by
          gcongr
      _ = 10 ^ 6 * (K₀ + 1) * Cx ^ 2 * m ^ (e + 2 * c + 2) := by rw [hpow]; ring
  have hpre : 2 * (10000 * (r.word.length + 1) ^ 2) + 2 ≤ 720002 * m ^ (e + 2 * c + 2) := by
    have hsq : (r.word.length + 1) ^ 2 ≤ 36 * m ^ 2 := by
      calc (r.word.length + 1) ^ 2 ≤ (6 * m) ^ 2 := Nat.pow_le_pow_left hw 2
        _ = 36 * m ^ 2 := by ring
    have hm2 : m ^ 2 ≤ m ^ (e + 2 * c + 2) := Nat.pow_le_pow_right hm (by omega)
    have h1' : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
    nlinarith
  have hD : 1 ≤ m ^ (e + 2 * c + 2) := Nat.one_le_pow _ _ hm
  nlinarith

/-- A bound with exponent `p ≤ d` and coefficient `A ≤ K` is a bound with `K` and `d` (measure `≥ 1`). -/
theorem measure_bound_mono {x A K p d : ℕ} (r : OracleCompilationRequest) (hx : x ≤ A * r.measure ^ p)
    (hA : A ≤ K) (hp : p ≤ d) : x ≤ K * r.measure ^ d := by
  have hm := measure_positive r
  calc x ≤ A * r.measure ^ p := hx
    _ ≤ K * r.measure ^ d := Nat.mul_le_mul hA (Nat.pow_le_pow_right hm hp)

/-- **The written circuit as one ordinary word function** on the fixed request word, with the join's budget
shape `K·measure^d` for every `K ≥ budgetCoefficient a c K₀` and `d ≥ e + 2c + 2`. -/
noncomputable def circuitWordFunction (circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell)
    (main : St VV MM) (a c K₀ e : ℕ) (N : OracleCompilationRequest → ℕ) (ha : 1 ≤ a)
    (hrun : OracleProgramRuns circuit main a c N) (hN : ∀ r, N r ≤ K₀ * r.measure ^ e) (K d : ℕ)
    (hK : budgetCoefficient a c K₀ ≤ K) (hd : e + 2 * c + 2 ≤ d) :
    WordFunction OracleCompilationRequest OracleCompilationRequest.word
      (fun r => OracleOutput.word ⟨r.ell, circuit r⟩) (fun r => K * r.measure ^ d) :=
  (composedWordFunction circuit main a c N ha hrun).enlargeBudget (fun r =>
    measure_bound_mono r (composedBudget_le a c K₀ e N hN r) hK hd)

/-! ## The width preconditions of the emitters hold in the printing context -/

/-- The register width of the printing context: `2^(c·natBitLength |word|)·a`. -/
theorem entryWidth_eq (a c : ℕ) (r : OracleCompilationRequest) :
    (ctxOf noCallee (oracleSz a c) (entryWord r)).Wd = 2 ^ (c * natBitLength r.word.length) * a := by
  show 2 ^ (c * leadOnes (Proximity.LengthPrefix.wrapped r.word)) * a = _
  rw [Proximity.LengthPrefix.wrapped_leadOnes]

theorem entryWidth_ge (a c : ℕ) (r : OracleCompilationRequest) :
    (r.word.length + 1) ^ c * a ≤ (ctxOf noCallee (oracleSz a c) (entryWord r)).Wd := by
  rw [entryWidth_eq, Nat.mul_comm c, pow_mul]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (lt_natBitLength _) c)

/-- **Satisfiability of the emitter width preconditions** (`OraclePrintCells.emitNode_spec`,
`emitHeader_spec`, `emitTrailer_spec`) in the context of `OracleProgramRuns`: for a circuit family of size
`≤ Ks·measure^ds`, the constants `a ≥ Ks + 8`, `c ≥ ds + 1` give width `≥ 3`, room for the arity, and room for
every field of every node. -/
theorem emitterWidth_ok (circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell) (Ks ds a c : ℕ)
    (hsize : ∀ r, (circuit r).size ≤ Ks * r.measure ^ ds) (ha : Ks + 8 ≤ a) (hc : ds + 1 ≤ c)
    (r : OracleCompilationRequest) :
    3 ≤ (ctxOf noCallee (oracleSz a c) (entryWord r)).Wd ∧
      r.ell < 2 ^ (ctxOf noCallee (oracleSz a c) (entryWord r)).Wd ∧
      natBitLength (r.ell + (circuit r).size + 5) + 2 < 2 ^ (ctxOf noCallee (oracleSz a c) (entryWord r)).Wd := by
  set W := (ctxOf noCallee (oracleSz a c) (entryWord r)).Wd with hWdef
  set m := r.measure with hmdef
  have hm : 1 ≤ m := measure_positive r
  have hwl : r.word.length + 1 = 2 * m + 2 := by rw [requestWord_length]
  have hW := entryWidth_ge a c r
  rw [← hWdef, hwl] at hW
  have hp1 : (m + 1) ^ (ds + 1) ≤ (2 * m + 2) ^ c :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hc)
  have hp2 : m ^ ds ≤ (m + 1) ^ (ds + 1) :=
    (Nat.pow_le_pow_left (by omega) ds).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hp3 : m + 1 ≤ (m + 1) ^ (ds + 1) := by
    calc m + 1 = (m + 1) ^ 1 := (pow_one _).symm
      _ ≤ (m + 1) ^ (ds + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hS : (circuit r).size ≤ Ks * m ^ ds := hsize r
  have hell : r.ell ≤ m := by rw [hmdef]; unfold OracleCompilationRequest.measure; omega
  have hKs : Ks * m ^ ds ≤ Ks * (m + 1) ^ (ds + 1) := Nat.mul_le_mul_left _ hp2
  have hx : r.ell + (circuit r).size + 8 ≤ W := by
    have h1 : (Ks + 8) * (m + 1) ^ (ds + 1) ≤ (2 * m + 2) ^ c * a := by
      rw [Nat.mul_comm (Ks + 8)]
      exact Nat.mul_le_mul hp1 ha
    have h2 : (Ks + 8) * (m + 1) ^ (ds + 1) = Ks * (m + 1) ^ (ds + 1) + 8 * (m + 1) ^ (ds + 1) := by ring
    omega
  have hnb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le (r.ell + (circuit r).size + 5)
  have hW2 : W < 2 ^ W := Nat.lt_two_pow_self
  refine ⟨by omega, by omega, by omega⟩

/-! ## The join's body for one program, from its parts -/

/-- **X5(a) for one program `p`, from its parts.** The five conjuncts of the join `ComputationToCircuit`
at `p`: exact negated verdict and size from the semantic producer (premises), the native word length from
`OraclePrintBounds.word_length_le_measure`, and the written circuit from `OracleProgramRuns` (premise). -/
theorem computationToCircuit_at_of_program (p : OrdinaryOracleProgram)
    (circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell) (Ks ds : ℕ)
    (hverdict : ∀ (r : OracleCompilationRequest) (O : BitInput r.ell → Bool) (z : BitInput r.ell),
      (circuit r).eval O z = false ↔
        OrdinaryOracleRuns (fixedArityOracle O) p (r.runInput z) [true] r.fuel)
    (hsize : ∀ r, (circuit r).size ≤ Ks * r.measure ^ ds)
    (main : St VV MM) (a c K₀ e : ℕ) (N : OracleCompilationRequest → ℕ) (ha : 1 ≤ a)
    (hrun : OracleProgramRuns circuit main a c N) (hN : ∀ r, N r ≤ K₀ * r.measure ^ e) :
    ∃ K d : ℕ, ∃ circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell,
      1 ≤ K ∧
      (∀ (r : OracleCompilationRequest) (O : BitInput r.ell → Bool) (z : BitInput r.ell),
        (circuit r).eval O z = false ↔
          OrdinaryOracleRuns (fixedArityOracle O) p (r.runInput z) [true] r.fuel) ∧
      (∀ r, (circuit r).size ≤ K * r.measure ^ d) ∧
      (∀ r, (OracleOutput.word ⟨r.ell, circuit r⟩).length ≤ K * r.measure ^ d) ∧
      Nonempty (WordFunction OracleCompilationRequest OracleCompilationRequest.word
        (fun r => OracleOutput.word ⟨r.ell, circuit r⟩)
        (fun r => K * r.measure ^ d)) := by
  set Kb := budgetCoefficient a c K₀
  set Kl := 64 * (Ks + 2) ^ 3
  refine ⟨Ks + Kl + Kb + 1, ds + 3 * ds + 3 + (e + 2 * c + 2), circuit, by omega, hverdict,
    fun r => measure_bound_mono r (hsize r) (by omega) (by omega), fun r => ?_,
    ⟨circuitWordFunction circuit main a c K₀ e N ha hrun hN _ _ (by omega) (by omega)⟩⟩
  have hell : r.ell ≤ r.measure := by unfold OracleCompilationRequest.measure; omega
  exact measure_bound_mono r
    (word_length_le_measure (circuit r) r.measure Ks ds (measure_positive r) hell (hsize r)) (by omega) (by omega)

/-- **X5(a) from per-program parts.** If every program has a semantic producer (exact negated verdict, polynomial
size) and a printing program for its circuit family, the join holds. -/
theorem computationToCircuit_of_programs
    (h : ∀ p : OrdinaryOracleProgram, ∃ (circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell)
      (Ks ds : ℕ) (main : St VV MM) (a c K₀ e : ℕ) (N : OracleCompilationRequest → ℕ),
      (∀ (r : OracleCompilationRequest) (O : BitInput r.ell → Bool) (z : BitInput r.ell),
        (circuit r).eval O z = false ↔
          OrdinaryOracleRuns (fixedArityOracle O) p (r.runInput z) [true] r.fuel) ∧
      (∀ r, (circuit r).size ≤ Ks * r.measure ^ ds) ∧ 1 ≤ a ∧
      OracleProgramRuns circuit main a c N ∧ (∀ r, N r ≤ K₀ * r.measure ^ e)) :
    ComputationToCircuit := by
  intro p
  obtain ⟨circuit, Ks, ds, main, a, c, K₀, e, N, hverdict, hsize, ha, hrun, hN⟩ := h p
  exact computationToCircuit_at_of_program p circuit Ks ds hverdict hsize main a c K₀ e N ha hrun hN

end NearCubicGates.Adapters.Compile.OraclePrint

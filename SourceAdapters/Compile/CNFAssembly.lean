import SourceAdapters.Compile.BoundedRequestFields
import SourceAdapters.Proximity.PrefixSizes
import SourceAdapters.Code.Composition
import Proof.Gates.CounterMachine.PrefixFinal

/-!
# X5(b): the join from one printing program

Paper context: proof of `lem:multitape-refuter`, Steps 3–4, and `cor:framed-refuter`. Each bounded
question is converted to a satisfiability-equivalent 3-CNF query and written by an ordinary machine.
The running-time polynomial has degree independent of the machine being simulated. The native balanced
encoding and explicit bounds below describe this implementation.

The formula is the semantic producer `requestFormula` (BoundedCNFValues: exact satisfiability; BoundedCNFBounds:
clause count `≤ 512·measure^6`, native bits `≤ 16000·130^6·measure^36`). The ordinary word function is assembled
from three existing actual programs:
* `Proximity.LengthPrefix.polynomialWordFunction` prints `frame (natWord |w| ++ w)` (paid size header);
* `Cells.wordFunction_of_lang` runs a cell-language program whose register width is polynomial in `|w|`;
* `Code.composeFramed` composes the two, paying both rewinds.

The physical program contract is `CNFProgramRuns`: one fixed cell program prints exactly the framed SAT
query `requestQueryWord r` of the actual formula, in `N r ≤ K₀·measure^e` language steps. Its type names the paper
quantity (the written query); nothing weaker typechecks.

-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

set_option autoImplicit false

/-- proof of `lem:multitape-refuter`: the framed native balanced SAT query of the request's formula. -/
def requestQueryWord (r : CNFCompilationRequest) : List Bool :=
  RepairOrdinary.frame (RecoveryOracle.sourceSATCode (requestFormula r)).bits

/-- The entry word of the printing program: the paid size header, then the request word. -/
def requestEntryWord (r : CNFCompilationRequest) : List Bool :=
  Proximity.LengthPrefix.wrapped r.word

/-- Cell size constants: register width `2^(c·L)·a` where `L` is the bit length of `|word r|`. -/
def cnfSz (a c : ℕ) : Sz := ⟨a, c, 0, 0, 0, 0⟩

/-- **The physical program contract** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`): the fixed cell program `main`, run on
the entry word, prints exactly the framed SAT query of the request within `N r` language steps. -/
def CNFProgramRuns (main : St VV MM) (a c : ℕ) (N : CNFCompilationRequest → ℕ) : Prop :=
  ∀ r, ∃ b n, Ex (ctxOf noCallee (cnfSz a c) (requestEntryWord r)) main a0 b n ∧
    b.out = requestQueryWord r ∧ n ≤ N r

/-- The paid size header, as a word function of the request. -/
noncomputable def requestPrefixWordFunction : WordFunction CNFCompilationRequest CNFCompilationRequest.word
    (fun r => RepairOrdinary.frame (requestEntryWord r)) (fun r => 10000 * (r.word.length + 1) ^ 2) where
  program := Proximity.LengthPrefix.polynomialWordFunction.program
  realizes r := Proximity.LengthPrefix.polynomialWordFunction.realizes r.word

/-- The printing program, as a word function of the request. -/
noncomputable def requestCellsWordFunction (main : St VV MM) (a c : ℕ) (N : CNFCompilationRequest → ℕ)
    (ha : 1 ≤ a) (hrun : CNFProgramRuns main a c N) :
    WordFunction CNFCompilationRequest requestEntryWord requestQueryWord
      (fun r => langBudget noCallee (cnfSz a c) VV MM (requestEntryWord r) (N r)) :=
  wordFunction_of_lang requestEntryWord requestQueryWord noCallee (cnfSz a c) main N hrun (fun r => by
    change 1 ≤ 2 ^ (c * leadOnes (requestEntryWord r)) * a
    have := Nat.one_le_two_pow (n := c * leadOnes (requestEntryWord r))
    nlinarith)

/-- The composed actual word function. -/
noncomputable def requestQueryWordFunction (main : St VV MM) (a c : ℕ) (N : CNFCompilationRequest → ℕ)
    (ha : 1 ≤ a) (hrun : CNFProgramRuns main a c N) :
    WordFunction CNFCompilationRequest CNFCompilationRequest.word requestQueryWord
      (fun r => (2 * (10000 * (r.word.length + 1) ^ 2) + 2) + 1 +
        (2 * langBudget noCallee (cnfSz a c) VV MM (requestEntryWord r) (N r) + 2)) :=
  Code.composeFramed requestPrefixWordFunction (requestCellsWordFunction main a c N ha hrun)

/-- The request word is linear in the request measure. -/
theorem requestWord_succ_le (r : CNFCompilationRequest) : r.word.length + 1 ≤ 6 * r.measure := by
  have h := requestWord_length r
  have hm := request_measure_positive r
  omega

/-- proof of `cor:framed-refuter`: the composed budget is a fixed polynomial in the measure, with coefficient and degree
depending only on the program constants `a c K₀ e`, not on the verifier. -/
theorem requestQueryBudget_le (a c K₀ e : ℕ) (N : CNFCompilationRequest → ℕ)
    (hN : ∀ r, N r ≤ K₀ * r.measure ^ e) (r : CNFCompilationRequest) :
    (2 * (10000 * (r.word.length + 1) ^ 2) + 2) + 1 +
        (2 * langBudget noCallee (cnfSz a c) VV MM (requestEntryWord r) (N r) + 2) ≤
      (720005 + 2 * 10 ^ 6 * (K₀ + 1) * (a * 12 ^ c + a + c + TSK noCallee + 25) ^ 2) *
        r.measure ^ (e + 2 * c + 2) := by
  set m := r.measure with hmdef
  set T := TSK noCallee
  have hm : 1 ≤ m := request_measure_positive r
  have hw : r.word.length + 1 ≤ 6 * m := requestWord_succ_le r
  have hlang := NearCubicGates.Close.CounterMachine.PrefixProg.lang_le noCallee a c (requestEntryWord r) (N r)
  have halloc := Proximity.LengthPrefix.allocation_bound a c r.word
  have hL : leadOnes (requestEntryWord r) ≤ r.word.length + 1 := by
    change leadOnes (Proximity.LengthPrefix.wrapped r.word) ≤ _
    rw [Proximity.LengthPrefix.wrapped_leadOnes]
    exact NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le _
  have hI : (requestEntryWord r).length ≤ 3 * (r.word.length + 1) :=
    Proximity.LengthPrefix.wrapped_length_bound r.word
  -- powers of the measure
  have hpc : (r.word.length + 1) ^ c ≤ 6 ^ c * m ^ c := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hw c
  have hmc : m ^ c ≤ m ^ (c + 1) := Nat.pow_le_pow_right hm (by omega)
  have hm1 : m ≤ m ^ (c + 1) := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ (c + 1) := Nat.pow_le_pow_right hm (by omega)
  have h1 : 1 ≤ m ^ (c + 1) := Nat.one_le_pow _ _ hm
  have h12 : a * 2 ^ c * 6 ^ c = a * 12 ^ c := by
    rw [mul_assoc, ← mul_pow]; norm_num
  -- the width term
  have hW : 2 ^ (c * leadOnes (requestEntryWord r)) * a ≤ a * 12 ^ c * m ^ (c + 1) := by
    calc 2 ^ (c * leadOnes (requestEntryWord r)) * a ≤ (a * 2 ^ c) * (r.word.length + 1) ^ c := halloc
      _ ≤ (a * 2 ^ c) * (6 ^ c * m ^ c) := Nat.mul_le_mul_left _ hpc
      _ = a * 12 ^ c * m ^ c := by rw [← h12]; ring
      _ ≤ a * 12 ^ c * m ^ (c + 1) := Nat.mul_le_mul_left _ hmc
  set X := 2 ^ (c * leadOnes (requestEntryWord r)) * a + leadOnes (requestEntryWord r) +
    (requestEntryWord r).length + a + c + T + 1 with hX
  set Cx := a * 12 ^ c + a + c + T + 25 with hCx
  have hXle : X ≤ Cx * m ^ (c + 1) := by
    have hlin : leadOnes (requestEntryWord r) + (requestEntryWord r).length ≤ 24 * m ^ (c + 1) := by
      omega
    have hc1 : a + c + T + 1 ≤ (a + c + T + 1) * m ^ (c + 1) := Nat.le_mul_of_pos_right _ h1
    rw [hCx, hX]
    nlinarith
  have hN1 : N r + 1 ≤ (K₀ + 1) * m ^ e := by
    have := hN r
    have he : 1 ≤ m ^ e := Nat.one_le_pow _ _ hm
    nlinarith
  have hlang' : langBudget noCallee (cnfSz a c) VV MM (requestEntryWord r) (N r) ≤
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
theorem measure_bound_mono {x A K p d : ℕ} (r : CNFCompilationRequest) (hx : x ≤ A * r.measure ^ p)
    (hA : A ≤ K) (hp : p ≤ d) : x ≤ K * r.measure ^ d := by
  have hm := request_measure_positive r
  calc x ≤ A * r.measure ^ p := hx
    _ ≤ K * r.measure ^ d := Nat.mul_le_mul hA (Nat.pow_le_pow_right hm hp)

/-- **X5(b) from the printing program.** The eight conjuncts of the join: the seven semantic/size ones
from the producer `requestFormula`, and the written query from `CNFProgramRuns`. -/
theorem computationToCNF_of_program (main : St VV MM) (a c K₀ e : ℕ) (N : CNFCompilationRequest → ℕ)
    (ha : 1 ≤ a) (hrun : CNFProgramRuns main a c N) (hN : ∀ r, N r ≤ K₀ * r.measure ^ e) :
    ComputationToCNF := by
  set Kw := 720005 + 2 * 10 ^ 6 * (K₀ + 1) * (a * 12 ^ c + a + c + TSK noCallee + 25) ^ 2
  refine ⟨16000 * 130 ^ 6 + 512 + Kw, 36 + e + 2 * c + 2, requestFormula, by omega,
    requestFormula_three, requestFormula_correct, requestFormula_decode, requestFormula_sourceSAT,
    fun r => measure_bound_mono r (requestFormula_length r) (by omega) (by omega),
    fun r => measure_bound_mono r (requestFormula_bits r) (by omega) (by omega), ?_⟩
  exact ⟨(requestQueryWordFunction main a c N ha hrun).enlargeBudget (fun r =>
    measure_bound_mono r (requestQueryBudget_le a c K₀ e N hN r) (by omega) (by omega))⟩

end NearCubicGates.Adapters.Compile

import Bindings.Williams14_Corollary4_4_PrefixLookup
import Proof.Foundations.RepresentationSourceContracts
import StatementSupport

/-!
# Binding: Williams, JACM 2014, Corollary 4.4 (= Corollary C.2) → `RepairRepresentation.WilliamsSource`

Source PDF: `WilACC14_Williams_Nonuniform_ACC_Circuit_Lower_Bounds_JACM.pdf`
(J. ACM 61(1), Article 2, 2014). Every quotation below was checked against the rendered page image.
The text layer drops superscripts: "N.1" is `N^{.1}` and "N2" is `N²`.

* PDF page 17 (printed 2:17), verbatim:
  "COROLLARY 4.4. For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and
  N^{.1} × N can be multiplied over the integers in O(N² · poly(log N)) time."
* PDF page 29 (printed 2:29), Appendix C, verbatim (the same statement):
  "COROLLARY C.2. For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and
  N^{.1} × N can be multiplied over the integers in O(N² · poly(log N)) time."
* PDF page 26 (printed 2:26), Appendix C, on the machine model, verbatim: "Prima facie, it could
  be that Coppersmith's algorithm is nonuniform, making it difficult to apply. For the sake of
  completeness, here we verify using standard ideas that Coppersmith's algorithm can indeed be
  implemented to run (even on a multitape TM) in O(N² · poly(log N)) time, on matrices over any
  field of poly(N) elements."

## Transcription choices

* **One algorithm, hidden constants existential.** The paper's point on p.26 is that the
  algorithm is uniform, so the literal asserts ONE machine. "For all sufficiently large N" is an
  onset `N₀`; `O(N² · poly(log N))` is `C · N² · (log₂ N)^e`. `N₀`, `C` and `e` are existential and
  chosen with the machine (the weakest reading: they may depend on everything the sentence lets them
  depend on). Below `N₀` the literal says NOTHING, neither about correctness nor about time.
  The log base and the polynomial's shape are absorbed by `C` and `e` once `N ≥ 2`.
* **`N^{.1}` on exact tenth powers.** `N^{.1}` is a whole number exactly when `N = k^10`, and then
  it is `k`. For other `N` the paper fixes no rounding. The instances `N = k^10` are the ones on
  which every rounding convention (floor, ceiling, nearest) agrees, so every reading of the printed
  statement implies this one. The literal therefore quantifies over `k` with `N = k^10`.
* **"multiplied over the integers".** `product A B i j = Σ_l [A i l] · [B l j]`, the ordinary
  integer product of the 0-1 matrices (not Boolean, not mod 2). Its entries are nonnegative, so it
  is stated in `ℕ`; `product_cast` checks it is the `ℤ` product.
* **Tier 1 machine model, and why it is not an `OrdinaryWordFunction`.** The algorithmic clause is
  the separable structure `MultitapeMultiplier`, stated in the repo's multitape machine
  (`Proof/Foundations/LocalBitMultitapeCore.lean`: finite control, one scanned Boolean per tape,
  local writes, unit head moves, one step per transition, deterministic), which is Williams's own
  "(even on a multitape TM)" (p.26). The input convention is the import's own: tape 0 holds `N`
  (self-delimiting binary, `natWord`) followed by the entries of the `N × N^{.1}` matrix row by
  row; tape 1 holds the entries of the `N^{.1} × N` matrix row by row; all other tapes are blank.
  The output, on a separate, initially blank tape, is the `N × N` product row by row, each entry
  in `⌊log₂ N⌋ + 1` binary digits (entries are at most `N^{.1} ≤ N`, so nothing is lost). The
  imported `WilliamsSource` (`Proof/Foundations/RepresentationSourceContracts.lean`) is not a
  `WordFunction`. Its tapes are unframed and carry no end marker, so a framed single-word literal
  would force the adapter to include a framer that computes `N · N^{.1}` to find where tape 0
  ends. The paper never mentions such machinery. A two-input-tape layout is a standard multitape
  convention. Tier 2 replaces only `MultitapeMultiplier`.

## The adapter and the finite prefix

The import asks for ONE machine that is correct, within `coefficient · U² · logScale(U)^e`, for
EVERY `U = k^10` with `k ≥ 1`, while the paper speaks only of `N ≥ N₀`. `williams14_to_import`
closes the gap with the gate of `Bindings.Williams14_Corollary4_4_PrefixLookup`, placed in front of the literal machine:
it reads the first `B = 2(N₀ + 1) + 1 + N₀²` cells of tapes 0 and 1 into finite control. When they
are the input of one of the finitely many requests with `U < N₀` (`table`), it writes that
request's product directly, within a constant number of steps. Otherwise it rewinds and starts the
literal machine exactly in its initial configuration. `table_small` and `table_large` show the
lookup is exact. The key fact is `natWord_prefix_inj` (the self-delimiting header of `N` is
prefix-free), so a small request is determined by its first `B` cells, and a large request never
looks like a small one. The small-case cost is absorbed in the coefficient, and
`log₂ U ≤ logScale U` (`Nat.log ≤ Nat.clog`).
-/

namespace NearCubicWires.Bindings.Williams14

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.WilliamsLoaderForms
open NearCubicWires.WilliamsProductCertificate
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## The literal -/

/-! ## Sanity checks on the literal's vocabulary -/

/-- `product` is the product over `ℤ`. -/
theorem product_cast {n m p : ℕ} (A : BitMatrix n m) (B : BitMatrix m p) (i : Fin n) (j : Fin p) :
    ((product A B i j : ℕ) : ℤ) = ∑ l, ((bit (A i l) : ℤ) * (bit (B l j) : ℤ)) := by
  simp [product]

/-- The output width suffices: every entry is at most `N^{.1} = k ≤ N`, below `2^(⌊log₂ N⌋+1)`. -/
theorem product_lt {k : ℕ} (A : BitMatrix (k ^ 10) k) (B : BitMatrix k (k ^ 10))
    (i j : Fin (k ^ 10)) : product A B i j < 2 ^ natBitLength (k ^ 10) := by
  have hle : product A B i j ≤ k := by
    calc product A B i j = ∑ l, bit (A i l) * bit (B l j) := rfl
      _ ≤ ∑ _l : Fin k, 1 := Finset.sum_le_sum fun l _ => by
          unfold bit; split <;> split <;> simp
      _ = k := by simp
  have hkN : k ≤ k ^ 10 := Nat.le_self_pow (by norm_num) k
  exact lt_of_le_of_lt (hle.trans hkN) (Nat.lt_pow_succ_log_self (by norm_num) _)

/-! ## Bridges to the import's vocabulary -/

theorem product_eq {n m p : ℕ} (A : BitMatrix n m) (B : BitMatrix m p) :
    product A B = integerMatrixProduct A B := by
  funext i j
  unfold product integerMatrixProduct
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold bit
  cases A i l <;> cases B l j <;> rfl

/-- The import's tapes of a request. -/
def importTapes (t : ℕ) (r : ExactPowerRequest) : Fin t → List Bool :=
  fun tape => if tape.val = 0 then natWord r.dimension ++ rowMajorBitMatrix r.left
    else if tape.val = 1 then rowMajorBitMatrix r.right else []

theorem inputTapes_eq (t : ℕ) (r : ExactPowerRequest) :
    (inputTapes r.dimension r.left r.right : Fin t → List Bool) = importTapes t r := rfl

theorem output_eq (r : ExactPowerRequest) :
    outputWord r.dimension (product r.left r.right) = r.output := by
  rw [product_eq]
  rfl

/-! ## The self-delimiting header is prefix-free -/

theorem replicate_false_cancel : ∀ (p q : ℕ) (X Y : List Bool),
    List.replicate p true ++ false :: X = List.replicate q true ++ false :: Y → p = q ∧ X = Y
  | 0, 0, X, Y, h => by simpa using h
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | p + 1, q + 1, X, Y, h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hpq, hXY⟩ := replicate_false_cancel p q X Y h
      exact ⟨by omega, hXY⟩

/-- Inlined from `RepairCloseoutFinalC10RoundCursor.fixedWidthNatBits_inj`
(`Proof/CaseAnalysis/FinalRoundCursor.lean`). -/
theorem fixedWidth_inj {width a b : ℕ} (ha : a < 2 ^ width) (hb : b < 2 ^ width)
    (h : WilliamsPublishedForm.fixedWidthNatBits width a =
      WilliamsPublishedForm.fixedWidthNatBits width b) : a = b := by
  unfold WilliamsPublishedForm.fixedWidthNatBits at h
  have hfun : (fun bit : Fin width => a.testBit bit.val) = fun bit : Fin width => b.testBit bit.val :=
    List.ofFn_inj.mp h
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  by_cases hi : i < width
  · simpa using congrFun hfun ⟨i, hi⟩
  · have hp : (2 : ℕ) ^ width ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hp)]

theorem natWord_length (n : ℕ) : (natWord n).length = 2 * natBitLength n + 1 := by
  simp [natWord, WilliamsPublishedForm.framedNatBits,
    WilliamsPublishedForm.fixedWidthNatBits]
  omega

/-- The header `natWord` is prefix-free: a header that begins another header is that header. -/
theorem natWord_prefix_inj {a b : ℕ} (h : natWord a <+: natWord b) : a = b := by
  obtain ⟨s, hs⟩ := h
  simp only [natWord, WilliamsPublishedForm.framedNatBits, List.append_assoc,
    List.cons_append] at hs
  obtain ⟨hpq, hXY⟩ := replicate_false_cancel _ _ _ _ hs
  have hlen := congrArg List.length hXY
  simp only [WilliamsPublishedForm.fixedWidthNatBits, List.length_append,
    List.length_ofFn, hpq] at hlen
  have hs0 : s = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hs0
  rw [List.append_nil, hpq] at hXY
  have ha : a < 2 ^ natBitLength b := by
    rw [← hpq]; exact Nat.lt_pow_succ_log_self (by norm_num) a
  have hb : b < 2 ^ natBitLength b := Nat.lt_pow_succ_log_self (by norm_num) b
  exact fixedWidth_inj ha hb hXY

/-- Two headers that begin a common word are equal. -/
theorem natWord_eq_of_prefix {a b : ℕ} {L : List Bool} (ha : natWord a <+: L)
    (hb : natWord b <+: L) : a = b := by
  rcases List.prefix_or_prefix_of_prefix ha hb with h | h
  · exact natWord_prefix_inj h
  · exact (natWord_prefix_inj h).symm

theorem rowMajor_length {n m : ℕ} (M : BitMatrix n m) :
    (rowMajorBitMatrix M).length = n * m := by
  simp [rowMajorBitMatrix, List.length_flatten, List.sum_ofFn]

theorem rowMajor_inj : ∀ {n m : ℕ} {M M' : BitMatrix n m},
    rowMajorBitMatrix M = rowMajorBitMatrix M' → M = M'
  | 0, _, _, _, _ => funext fun i => i.elim0
  | n + 1, m, M, M', h => by
      unfold rowMajorBitMatrix at h
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons] at h
      obtain ⟨h0, htail⟩ := List.append_inj h (by simp)
      have hrow : M 0 = M' 0 := List.ofFn_inj.mp h0
      have hrest : (fun i : Fin n => M i.succ) = fun i => M' i.succ :=
        rowMajor_inj (M := fun i : Fin n => M i.succ) (M' := fun i : Fin n => M' i.succ) htail
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hrow
      · exact congrFun hrest i

/-! ## The finite table of small requests -/

/-- Tape 0 of a request. -/
def tapeA (r : ExactPowerRequest) : List Bool := natWord r.dimension ++ rowMajorBitMatrix r.left

/-- Tape 1 of a request. -/
def tapeB (r : ExactPowerRequest) : List Bool := rowMajorBitMatrix r.right

/-- The number of cells the gate reads: every small request fits. -/
def smallBound (N₀ : ℕ) : ℕ := 2 * (N₀ + 1) + 1 + N₀ * N₀

/-- A bound on the output length of every small request. -/
def outBound (N₀ : ℕ) : ℕ := N₀ * N₀ * (N₀ + 1)

open Gate in
/-- The table: the product of the small request (`U < N₀`) whose first `B` cells these are. -/
noncomputable def table (N₀ : ℕ) (a b : Fin (smallBound N₀) → Bool) : Option (List Bool) := by
  classical
  exact if h : ∃ r : ExactPowerRequest, r.dimension < N₀ ∧
      window (smallBound N₀) (tapeA r) = a ∧ window (smallBound N₀) (tapeB r) = b
    then some (Classical.choose h).output else none

theorem padded_eq_take (B : ℕ) (T : List Bool) :
    List.ofFn (Gate.window B T) = (T ++ List.replicate B false).take B := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_ofFn, Gate.window, readTapeBit, List.getElem_take]
  by_cases hj : j < T.length
  · rw [List.getD_eq_getElem _ _ hj, List.getElem_append_left hj]
  · rw [List.getD_eq_default _ _ (by omega), List.getElem_append_right (by omega)]
    simp

theorem padded_of_le {B : ℕ} {T : List Bool} (h : T.length ≤ B) :
    List.ofFn (Gate.window B T) = T ++ List.replicate (B - T.length) false := by
  refine List.ext_getElem (by simp; omega) fun j h1 h2 => ?_
  simp only [List.getElem_ofFn, Gate.window, readTapeBit]
  by_cases hj : j < T.length
  · rw [List.getD_eq_getElem _ _ hj, List.getElem_append_left hj]
  · rw [List.getD_eq_default _ _ (by omega), List.getElem_append_right (by omega)]
    simp

theorem encodedNatCellTape_length (width : ℕ) (cells : List ℕ) :
    (encodedNatCellTape width cells).length = cells.length * width := by
  induction cells with
  | nil => simp [encodedNatCellTape]
  | cons c cells ih =>
      simp only [encodedNatCellTape, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      rw [ih]
      simp [WilliamsLoaderForms.fixedWidthNatBits]
      ring

theorem small_lengths {N₀ : ℕ} (r : ExactPowerRequest) (hr : r.dimension < N₀) :
    (tapeA r).length ≤ smallBound N₀ ∧ (tapeB r).length ≤ smallBound N₀ ∧
      r.output.length ≤ outBound N₀ := by
  have hk : r.inner ≤ r.dimension := Nat.le_self_pow (by norm_num) r.inner
  have hbit : natBitLength r.dimension ≤ r.dimension + 1 := by
    unfold natBitLength; have := Nat.log_le_self 2 r.dimension; omega
  have hU : r.dimension ≤ N₀ := hr.le
  have hUk : r.dimension * r.inner ≤ N₀ * N₀ := Nat.mul_le_mul hU (hk.trans hU)
  have hkU : r.inner * r.dimension ≤ N₀ * N₀ := Nat.mul_le_mul (hk.trans hU) hU
  refine ⟨?_, ?_, ?_⟩
  · simp only [tapeA, List.length_append, natWord_length, rowMajor_length]
    unfold smallBound
    change 2 * natBitLength r.dimension + 1 + r.dimension * r.inner ≤ _
    omega
  · simp only [tapeB, rowMajor_length]
    unfold smallBound
    change r.inner * r.dimension ≤ _
    omega
  · rw [ExactPowerRequest.output, encodedNatCellTape_length, rowMajorNatMatrix_length]
    unfold outBound
    exact Nat.mul_le_mul (Nat.mul_le_mul hU hU) (hbit.trans (by omega))

/-- A small request's header is recognized from the first `B` cells of ANY request's tape 0. -/
theorem dimension_eq_of_window {N₀ : ℕ} (r r' : ExactPowerRequest) (hr' : r'.dimension < N₀)
    (h : Gate.window (smallBound N₀) (tapeA r') = Gate.window (smallBound N₀) (tapeA r)) :
    r'.dimension = r.dimension := by
  have hl := (small_lengths r' hr').1
  have hlist := congrArg List.ofFn h
  rw [padded_of_le hl, padded_eq_take] at hlist
  have hA' : natWord r'.dimension <+: tapeA r' := List.prefix_append _ _
  have hpad : tapeA r' <+: tapeA r' ++ List.replicate (smallBound N₀ - (tapeA r').length) false :=
    List.prefix_append _ _
  rw [hlist] at hpad
  have h1 : natWord r'.dimension <+: tapeA r ++ List.replicate (smallBound N₀) false :=
    (hA'.trans hpad).trans (List.take_prefix _ _)
  have h2 : natWord r.dimension <+: tapeA r ++ List.replicate (smallBound N₀) false :=
    List.IsPrefix.trans (List.prefix_append _ _) (List.prefix_append _ _)
  exact natWord_eq_of_prefix h1 h2

/-- Two small requests with the same first `B` cells on both tapes are equal. -/
theorem small_unique {N₀ : ℕ} (r r' : ExactPowerRequest) (hr : r.dimension < N₀)
    (hr' : r'.dimension < N₀)
    (ha : Gate.window (smallBound N₀) (tapeA r') = Gate.window (smallBound N₀) (tapeA r))
    (hb : Gate.window (smallBound N₀) (tapeB r') = Gate.window (smallBound N₀) (tapeB r)) :
    r' = r := by
  have hdim := dimension_eq_of_window r r' hr' ha
  obtain ⟨la, lb, _⟩ := small_lengths r hr
  obtain ⟨la', lb', _⟩ := small_lengths r' hr'
  have hA := congrArg List.ofFn ha
  have hB := congrArg List.ofFn hb
  rw [padded_of_le la, padded_of_le la'] at hA
  rw [padded_of_le lb, padded_of_le lb'] at hB
  obtain ⟨k, _, A, B⟩ := r
  obtain ⟨k', _, A', B'⟩ := r'
  have hkk : k' = k := Nat.pow_left_injective (by norm_num : 10 ≠ 0) hdim
  subst hkk
  have hA' := List.append_inj hA (by simp [tapeA, ExactPowerRequest.dimension])
  have hB' := List.append_inj hB (by simp [tapeB])
  have hAA : A' = A := rowMajor_inj (List.append_cancel_left hA'.1)
  have hBB : B' = B := rowMajor_inj hB'.1
  subst hAA
  subst hBB
  rfl

theorem table_small {N₀ : ℕ} (r : ExactPowerRequest) (hr : r.dimension < N₀) :
    table N₀ (Gate.window (smallBound N₀) (tapeA r)) (Gate.window (smallBound N₀) (tapeB r)) =
      some r.output := by
  have h : ∃ r' : ExactPowerRequest, r'.dimension < N₀ ∧
      Gate.window (smallBound N₀) (tapeA r') = Gate.window (smallBound N₀) (tapeA r) ∧
      Gate.window (smallBound N₀) (tapeB r') = Gate.window (smallBound N₀) (tapeB r) :=
    ⟨r, hr, rfl, rfl⟩
  unfold table
  rw [dif_pos h]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
  rw [small_unique r _ hr h1 h2 h3]

theorem table_large {N₀ : ℕ} (r : ExactPowerRequest) (hr : N₀ ≤ r.dimension) :
    table N₀ (Gate.window (smallBound N₀) (tapeA r)) (Gate.window (smallBound N₀) (tapeB r)) =
      none := by
  unfold table
  rw [dif_neg]
  rintro ⟨r', hr', ha, _⟩
  have := dimension_eq_of_window r r' hr' ha
  omega

/-! ## The adapter -/

section Adapter

variable {N₀ C e : ℕ} (M : MultitapeMultiplier N₀ C e)

theorem two_le_tapes : 2 ≤ M.tapeCount := by
  have := M.threeTapes
  omega

/-- The gate followed by the literal machine. -/
noncomputable def fullMachine :=
  Gate.combined (W := outBound N₀) (two_le_tapes M) M.outputTape (table N₀) M.machine

/-- The import's coefficient. -/
def coefficientOf (N₀ C : ℕ) : ℕ := C + 3 * smallBound N₀ + outBound N₀ + 10

theorem window_tape0 (r : ExactPowerRequest) :
    importTapes M.tapeCount r (Gate.tape0 (two_le_tapes M)) = tapeA r := rfl

theorem window_tape1 (r : ExactPowerRequest) :
    importTapes M.tapeCount r (Gate.tape1 (two_le_tapes M)) = tapeB r := rfl

theorem scale_pos (r : ExactPowerRequest) :
    1 ≤ r.dimension ^ 2 * logScale r.dimension ^ e := by
  have hU : 0 < r.dimension := Nat.pow_pos r.positive
  have hL : 0 < logScale r.dimension := by
    unfold logScale
    exact Nat.clog_pos (by norm_num) (by omega)
  exact Nat.mul_pos (Nat.pow_pos hU) (Nat.pow_pos hL)

theorem log_le_logScale (U : ℕ) : Nat.log 2 U ≤ logScale U :=
  (Nat.log_le_clog 2 U).trans (Nat.clog_mono_right 2 (by omega))

/-- The combined machine meets the import on every request. -/
theorem fullMachine_runs (r : ExactPowerRequest) :
    ∃ receipt, run (fullMachine M)
        (coefficientOf N₀ C * r.dimension ^ 2 * logScale r.dimension ^ e)
        (importTapes M.tapeCount r) = some receipt ∧
      receipt.final.tapes M.outputTape = r.output := by
  have hX := scale_pos (e := e) r
  have hscale : coefficientOf N₀ C * r.dimension ^ 2 * logScale r.dimension ^ e =
      coefficientOf N₀ C * (r.dimension ^ 2 * logScale r.dimension ^ e) := by ring
  by_cases hsmall : r.dimension < N₀
  · obtain ⟨_, _, hout⟩ := small_lengths r hsmall
    have hT : importTapes M.tapeCount r M.outputTape = [] := by
      simp [importTapes, M.outputFreshLeft, M.outputFreshRight]
    have hw := table_small r hsmall
    rw [← window_tape0 M, ← window_tape1 M] at hw
    obtain ⟨receipt, hrun, hfin⟩ := Gate.combined_small_run (W := outBound N₀) (two_le_tapes M)
      M.outputTape (table N₀) M.machine (importTapes M.tapeCount r) M.outputFreshLeft
      M.outputFreshRight hT hw hout
    have hbound : smallBound N₀ + outBound N₀ + 3 ≤
        coefficientOf N₀ C * r.dimension ^ 2 * logScale r.dimension ^ e := by
      rw [hscale]
      calc smallBound N₀ + outBound N₀ + 3 ≤ coefficientOf N₀ C * 1 := by
            unfold coefficientOf; omega
        _ ≤ _ := Nat.mul_le_mul_left _ hX
    have hm := run_moreFuel (fullMachine M) (smallBound N₀ + outBound N₀ + 3)
      (coefficientOf N₀ C * r.dimension ^ 2 * logScale r.dimension ^ e -
        (smallBound N₀ + outBound N₀ + 3)) (importTapes M.tapeCount r) receipt hrun
    rw [Nat.add_sub_of_le hbound] at hm
    exact ⟨receipt, hm, hfin⟩
  · have hlarge : N₀ ≤ r.dimension := by omega
    have hw := table_large r hlarge
    rw [← window_tape0 M, ← window_tape1 M] at hw
    obtain ⟨rL, hL0, hLout⟩ := M.multiplies r.inner r.left r.right hlarge
    have hL : run M.machine (C * r.dimension ^ 2 * Nat.log 2 r.dimension ^ e)
        (importTapes M.tapeCount r) = some rL := hL0
    obtain ⟨receipt, hrun, hfin⟩ := Gate.combined_large_run (W := outBound N₀) (two_le_tapes M)
      M.outputTape (table N₀) M.machine (importTapes M.tapeCount r) hw _ rL hL
    have hlog : Nat.log 2 r.dimension ^ e ≤ logScale r.dimension ^ e :=
      Nat.pow_le_pow_left (log_le_logScale _) e
    have hbound : C * r.dimension ^ 2 * Nat.log 2 r.dimension ^ e + 2 * smallBound N₀ + 4 ≤
        coefficientOf N₀ C * r.dimension ^ 2 * logScale r.dimension ^ e := by
      rw [hscale]
      have h1 : C * r.dimension ^ 2 * Nat.log 2 r.dimension ^ e ≤
          C * (r.dimension ^ 2 * logScale r.dimension ^ e) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlog)
      have h2 : 2 * smallBound N₀ + 4 ≤
          (3 * smallBound N₀ + outBound N₀ + 10) * (r.dimension ^ 2 * logScale r.dimension ^ e) :=
        le_trans (by omega) (Nat.mul_le_mul_left _ hX)
      unfold coefficientOf
      nlinarith
    have hm := run_moreFuel (fullMachine M)
      (C * r.dimension ^ 2 * Nat.log 2 r.dimension ^ e + 2 * smallBound N₀ + 4)
      (coefficientOf N₀ C * r.dimension ^ 2 * logScale r.dimension ^ e -
        (C * r.dimension ^ 2 * Nat.log 2 r.dimension ^ e + 2 * smallBound N₀ + 4))
      (importTapes M.tapeCount r) receipt hrun
    rw [Nat.add_sub_of_le hbound] at hm
    refine ⟨receipt, hm, ?_⟩
    rw [hfin, hLout]
    exact output_eq r

end Adapter

/-- **Adapter.** The literal Williams Corollary 4.4 (Tier 1) implies the imported
`RepairRepresentation.WilliamsSource`: the finitely many requests below the onset are served by
the prefix-lookup gate, every other request by the literal machine. -/
theorem williams14_to_import : Williams14_Corollary4_4 → WilliamsSource := by
  rintro ⟨N₀, C, e, ⟨M⟩⟩
  exact ⟨{
    tapeCount := M.tapeCount
    stateCount := _
    threeTapes := M.threeTapes
    machine := fullMachine M
    outputTape := M.outputTape
    outputFreshLeft := M.outputFreshLeft
    outputFreshRight := M.outputFreshRight
    coefficient := coefficientOf N₀ C
    logExponent := e
    coefficientPositive := by unfold coefficientOf; omega
    runs := fun r => fullMachine_runs M r }⟩

end NearCubicWires.Bindings.Williams14

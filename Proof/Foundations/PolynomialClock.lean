import Proof.Foundations.ExecutableInterfaces

/-!
# Executable polynomial-dominating refuter clocks

The fixed refuter must dominate the *declared* polynomial budget of its weak
machine for every multiplier.  Iterating the machine's primitive pairing
instruction gives a canonical clock of degree `2^depth`, together with the
program that computes exactly that same value.
-/

namespace NearCubicWires.PolynomialClock

open NearCubicWires
open NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces

theorem natBitLength_le_succ (value : ℕ) :
    natBitLength value ≤ value + 1 := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_le_self 2 value) 1

/-- Repeated self-pairing.  `Nat.pair x x` is at least `x²`, so `depth`
iterations dominate degree `2^depth`. -/
def pairIter : ℕ → ℕ → ℕ
  | 0, value => value
  | depth + 1, value => pairIter depth (Nat.pair value value)

@[simp] theorem pairIter_zero (value : ℕ) : pairIter 0 value = value := rfl

@[simp] theorem pairIter_succ (depth value : ℕ) :
    pairIter (depth + 1) value = pairIter depth (Nat.pair value value) := rfl

theorem value_le_pairIter (depth value : ℕ) :
    value ≤ pairIter depth value := by
  induction depth generalizing value with
  | zero => simp
  | succ depth ih =>
      exact (Nat.left_le_pair value value).trans (ih (Nat.pair value value))

theorem pairIter_mono_value (depth : ℕ) :
    Monotone (pairIter depth) := by
  intro left right hle
  induction depth generalizing left right with
  | zero => exact hle
  | succ depth ih =>
      apply ih
      calc
        Nat.pair left left ≤ Nat.pair right left := by
          rcases hle.eq_or_lt with h | h
          · simp [h]
          · exact (Nat.pair_lt_pair_left left h).le
        _ ≤ Nat.pair right right := by
          rcases hle.eq_or_lt with h | h
          · simp [h]
          · exact (Nat.pair_lt_pair_right right h).le

theorem pow_twoPow_le_pairIter (depth value : ℕ) :
    value ^ (2 ^ depth) ≤ pairIter depth value := by
  induction depth generalizing value with
  | zero => simp
  | succ depth ih =>
      calc
        value ^ (2 ^ (depth + 1)) =
            value ^ (2 * (2 ^ depth)) := by
          congr 1
          rw [Nat.pow_succ]
          omega
        _ = (value ^ 2) ^ (2 ^ depth) := by
          rw [pow_mul]
        _ ≤ (Nat.pair value value) ^ (2 ^ depth) := by
          gcongr
          exact (Nat.le_add_right (value ^ 2) value).trans
            (by simpa using Nat.max_sq_add_min_le_pair value value)
        _ ≤ pairIter depth (Nat.pair value value) := ih _
        _ = pairIter (depth + 1) value := rfl

theorem pairIter_add_one_le_pow (depth value : ℕ) :
    pairIter depth value + 1 ≤ (value + 1) ^ (2 ^ depth) := by
  induction depth generalizing value with
  | zero => simp
  | succ depth ih =>
      have hpair :
          Nat.pair value value + 1 ≤ (value + 1) ^ 2 := by
        exact Nat.succ_le_iff.mpr <| by
          simpa using Nat.pair_lt_max_add_one_sq value value
      calc
        pairIter (depth + 1) value + 1 =
            pairIter depth (Nat.pair value value) + 1 := rfl
        _ ≤ (Nat.pair value value + 1) ^ (2 ^ depth) := ih _
        _ ≤ ((value + 1) ^ 2) ^ (2 ^ depth) :=
          Nat.pow_le_pow_left hpair (2 ^ depth)
        _ = (value + 1) ^ (2 ^ (depth + 1)) := by
          rw [← pow_mul]
          congr 1
          rw [Nat.pow_succ]
          omega

/-- The canonical refuter clock at source length `n`. -/
def pairClock (depth n : ℕ) : ℕ :=
  pairIter depth n

theorem pow_twoPow_le_pairClock (depth n : ℕ) :
    n ^ (2 ^ depth) ≤ pairClock depth n :=
  pow_twoPow_le_pairIter depth n

theorem pairClock_positive (depth n : ℕ) (hn : 0 < n) :
    0 < pairClock depth n :=
  lt_of_lt_of_le hn (value_le_pairIter depth n)

theorem pairClock_polynomiallyBounded (depth : ℕ) :
    PolynomiallyBounded (pairClock depth) := by
  refine ⟨1, 2 ^ depth, by omega, ?_⟩
  intro n
  simpa [pairClock] using
    (Nat.le_add_right (pairIter depth n) 1).trans
      (pairIter_add_one_le_pow depth n)

def pairTail : ℕ → ℕ → NPOracleProgram
  | _pc, 0 => [.halt 0]
  | pc, depth + 1 =>
      .pair 0 0 0 (pc + 1) :: pairTail (pc + 1) depth

@[simp] theorem pairTail_length (pc depth : ℕ) :
    (pairTail pc depth).length = depth + 1 := by
  induction depth generalizing pc with
  | zero => simp [pairTail]
  | succ depth ih => simp [pairTail, ih]

theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right hle) 1

/-- Execute a self-pairing suffix after an arbitrary already-executed prefix.
This prefix-general statement is what makes absolute program counters explicit
and prevents an unverified "run the remaining list" shortcut. -/
theorem run_pairTail (prelude : NPOracleProgram) (depth maximumBits extra : ℕ)
    (state : NPOracleState) (value : ℕ)
    (hpc : state.pc = prelude.length)
    (hvalue : state.registers 0 = value)
    (hbits : natBitLength (pairIter depth value) ≤ maximumBits) :
    runNPOracleProgram (prelude ++ pairTail prelude.length depth)
        maximumBits (extra + depth + 1) state =
      some (pairIter depth value) := by
  induction depth generalizing prelude state value with
  | zero =>
      have hvalueBits : natBitLength value ≤ maximumBits := by
        simpa [pairIter] using hbits
      simp [pairTail, runNPOracleProgram, hpc, hvalue, hvalueBits]
  | succ depth ih =>
      have hnext :
          Nat.pair value value ≤
            pairIter depth (Nat.pair value value) :=
        value_le_pairIter depth (Nat.pair value value)
      have hpairBits :
          natBitLength (Nat.pair value value) ≤ maximumBits :=
        (natBitLength_mono hnext).trans hbits
      let instruction : NPOracleInstruction :=
        .pair 0 0 0 (prelude.length + 1)
      let nextState :=
        (state.write 0 (Nat.pair value value)).jump (prelude.length + 1)
      have hstep :
          runNPOracleProgram
              (prelude ++ pairTail prelude.length (depth + 1))
              maximumBits (extra + (depth + 1) + 1) state =
            runNPOracleProgram
              ((prelude ++ [instruction]) ++
                pairTail (prelude.length + 1) depth)
              maximumBits (extra + depth + 1) nextState := by
        simp only [pairTail, runNPOracleProgram]
        simp [hpc, hvalue, instruction, nextState, NPOracleState.boundedWrite,
          hpairBits, List.append_assoc]
      rw [hstep]
      have hrun := ih (prelude ++ [instruction]) nextState
        (Nat.pair value value)
        (by
          simp [nextState, NPOracleState.jump])
        (by
          simp [nextState, NPOracleState.jump, NPOracleState.write])
        hbits
      simpa [pairIter] using hrun

theorem pairTail_oracleFree (pc depth : ℕ) :
    OracleFree (pairTail pc depth) := by
  induction depth generalizing pc with
  | zero => simp [OracleFree, pairTail]
  | succ depth ih =>
      simp only [pairTail, OracleFree, List.all_cons, Bool.true_and]
      simpa only [OracleFree] using ih (pc + 1)

def pairClockTimeConstructible (depth : ℕ) :
    TimeConstructible (pairClock depth) where
  program := pairTail 0 depth
  coefficient := depth + 1
  coefficientPositive := by omega
  oracleFree := pairTail_oracleFree 0 depth
  computesBound := by
    intro n
    let clock := pairClock depth n
    let budget := (depth + 1) * (clock + 1)
    have hminimum : depth + 1 ≤ budget := by
      dsimp [budget]
      nlinarith
    obtain ⟨extra, hbudget⟩ := Nat.exists_eq_add_of_le hminimum
    have hbits : natBitLength clock ≤ budget := by
      calc
        natBitLength clock ≤ clock + 1 := natBitLength_le_succ clock
        _ ≤ budget := by
          dsimp [budget]
          nlinarith
    have hrun := run_pairTail ([] : NPOracleProgram) depth budget extra
      (initialNPOracleState n n) n
      (by simp [initialNPOracleState])
      (by simp [initialNPOracleState])
      (by simpa [clock, pairClock] using hbits)
    have hfuel : budget = extra + depth + 1 := by
      omega
    change
      runNPOracleProgram (pairTail 0 depth) budget budget
        (initialNPOracleState n n) =
          some clock
    rw [hfuel] at hrun
    rw [hfuel]
    simpa [clock, pairClock] using hrun

def pairClockAdmissible (depth : ℕ) :
    RefuterClockAdmissible (pairClock depth) where
  constructible := pairClockTimeConstructible depth
  atLeastInput := value_le_pairIter depth
  polynomiallyBounded := pairClock_polynomiallyBounded depth

/-- A degree-`degree` polynomial whose measure is at most `2n` is little-o of
any pairing clock with strictly larger degree.  The proof exposes a concrete
onset for each multiplier, matching the source contract's exact quantifiers. -/
theorem polynomialBudget_runsInLittleO_pairClock
    (coefficient degree depth : ℕ) (hdegree : degree < 2 ^ depth)
    (measure : ℕ → ℕ) (hmeasure : ∀ n, measure n ≤ 2 * n) :
    ∀ multiplier : ℕ, 0 < multiplier →
      ∃ onset, ∀ n, onset ≤ n →
        multiplier * polynomialBudget coefficient degree (measure n) ≤
          pairClock depth n := by
  intro multiplier hmultiplier
  let scale := multiplier * coefficient * 3 ^ degree
  refine ⟨max 1 scale, ?_⟩
  intro n hn
  have hnPositive : 0 < n := lt_of_lt_of_le (by omega)
    (le_trans (le_max_left 1 scale) hn)
  have hscale : scale ≤ n :=
    le_trans (le_max_right 1 scale) hn
  have hmeasureThree : measure n + 1 ≤ 3 * n := by
    have := hmeasure n
    omega
  have hmeasurePower :
      (measure n + 1) ^ degree ≤ (3 * n) ^ degree :=
    Nat.pow_le_pow_left hmeasureThree degree
  have hscaled :
      multiplier * polynomialBudget coefficient degree (measure n) ≤
        scale * n ^ degree := by
    unfold polynomialBudget
    calc
      multiplier * (coefficient * (measure n + 1) ^ degree) ≤
          multiplier * (coefficient * (3 * n) ^ degree) := by
        gcongr
      _ = scale * n ^ degree := by
        simp only [mul_pow, scale]
        ring
  have hmonomial : scale * n ^ degree ≤ n ^ (degree + 1) := by
    calc
      scale * n ^ degree ≤ n * n ^ degree :=
        Nat.mul_le_mul_right (n ^ degree) hscale
      _ = n ^ (degree + 1) := by
        simp [Nat.pow_succ, Nat.mul_comm]
  have hexponent : degree + 1 ≤ 2 ^ depth :=
    Nat.succ_le_iff.mpr hdegree
  exact hscaled.trans <| hmonomial.trans <|
    (Nat.pow_le_pow_right hnPositive hexponent).trans
      (pow_twoPow_le_pairClock depth n)

/-- Direct resource certificate for the executable weak-machine wrapper.
The machine's declared budget is the QUOTIENT budget, which sits
under the pure power (`quotientBudget_le_pure`), so the strict-drop form
remains true and discharges through the pure-power lemma. -/
theorem executableMachine_runsInLittleO_pairClock
    (machine : ExecutableWeakNondeterministicMachine) (depth : ℕ)
    (hdegree : machine.verifier.degree < 2 ^ depth)
    (hwitness : ∀ n, machine.witnessBits n ≤ n) :
    RunsInLittleO machine.toSemantic (pairClock depth) := by
  intro multiplier hmultiplier
  obtain ⟨onset, hbound⟩ :=
    polynomialBudget_runsInLittleO_pairClock
      machine.verifier.coefficient machine.verifier.degree depth hdegree
      (fun n => n + machine.witnessBits n)
      (fun n => by
        have := hwitness n
        omega)
      multiplier hmultiplier
  refine ⟨onset, ?_⟩
  intro n hn input witness
  have hle : machine.toSemantic.steps n input witness ≤
      polynomialBudget machine.verifier.coefficient machine.verifier.degree
        (n + machine.witnessBits n) := by
    simpa [ExecutableWeakNondeterministicMachine.toSemantic,
      ExecutableWeakNondeterministicMachine.verifierBudget,
      QuotientNatProgram.budget, WeakVerifierRequest.measure,
      polynomialBudget] using
        quotientBudget_le_pure machine.verifier.coefficient
          machine.verifier.degree machine.verifier.logPower
          (n + machine.witnessBits n)
  exact (Nat.mul_le_mul_left multiplier hle).trans (hbound n hn)

/-- **The quotient budget is little-o of the pair clock at the boundary
degree**.  Where the pure-power form demands
`degree + 1 ≤ 2^depth` (a strict drop), the quotient form admits
`degree ≤ 2^depth` with one saving power: the `logScale` divisor supplies
the multiplier headroom, with an explicit onset. -/
theorem quotientBudget_runsInLittleO_pairClock
    (coefficient degree saving depth : ℕ)
    (hdegree : degree ≤ 2 ^ depth) (hsaving : 1 ≤ saving)
    (measureOf : ℕ → ℕ)
    (hlower : ∀ n, n ≤ measureOf n)
    (hupper : ∀ n, measureOf n ≤ 2 * n)
    (multiplier : ℕ) :
    ∃ onset, ∀ n, onset ≤ n →
      multiplier * quotientBudget coefficient degree saving (measureOf n) ≤
        pairClock depth n := by
  refine ⟨max 1 (2 ^ (multiplier * coefficient * 3 ^ degree)), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have honset : 2 ^ (multiplier * coefficient * 3 ^ degree) ≤ n :=
    le_trans (le_max_right _ _) hn
  set m := measureOf n with hm
  have hLn : multiplier * coefficient * 3 ^ degree ≤ logScale n :=
    le_logScale_of_two_pow_le honset
  have hLmono : logScale n ≤ logScale m := by
    have := hlower n
    exact Nat.clog_mono_right _ (by omega)
  have hL : multiplier * coefficient * 3 ^ degree ≤ logScale m :=
    hLn.trans hLmono
  have hLpos : 0 < logScale m := Nat.clog_pos (by norm_num) (by omega)
  have hdivPow :
      quotientBudget coefficient degree saving m ≤
        coefficient * (m + 1) ^ degree / logScale m := by
    rw [quotientBudget]
    exact Nat.div_le_div_left
      (Nat.le_self_pow (by omega) _) hLpos
  have hpoly : coefficient * (m + 1) ^ degree ≤
      coefficient * 3 ^ degree * n ^ degree := by
    have hm3 : m + 1 ≤ 3 * n := by
      have := hupper n
      omega
    calc coefficient * (m + 1) ^ degree
        ≤ coefficient * (3 * n) ^ degree :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm3 _)
      _ = coefficient * 3 ^ degree * n ^ degree := by
          rw [mul_pow]; ring
  have hclock : n ^ degree ≤ pairClock depth n :=
    (Nat.pow_le_pow_right hn1 hdegree).trans (pow_twoPow_le_pairClock depth n)
  have hcore : multiplier * (coefficient * (m + 1) ^ degree / logScale m) *
      logScale m ≤ pairClock depth n * logScale m := by
    have h1 : coefficient * (m + 1) ^ degree / logScale m * logScale m ≤
        coefficient * (m + 1) ^ degree := Nat.div_mul_le_self _ _
    calc multiplier * (coefficient * (m + 1) ^ degree / logScale m) *
          logScale m
        = multiplier * (coefficient * (m + 1) ^ degree / logScale m *
            logScale m) := by ring
      _ ≤ multiplier * (coefficient * (m + 1) ^ degree) :=
          Nat.mul_le_mul_left _ h1
      _ ≤ multiplier * (coefficient * 3 ^ degree * n ^ degree) :=
          Nat.mul_le_mul_left _ hpoly
      _ = multiplier * coefficient * 3 ^ degree * n ^ degree := by ring
      _ ≤ logScale m * n ^ degree := Nat.mul_le_mul_right _ hL
      _ ≤ logScale m * pairClock depth n := Nat.mul_le_mul_left _ hclock
      _ = pairClock depth n * logScale m := Nat.mul_comm _ _
  have hstep : multiplier * (coefficient * (m + 1) ^ degree / logScale m) ≤
      pairClock depth n :=
    Nat.le_of_mul_le_mul_right hcore hLpos
  calc multiplier * quotientBudget coefficient degree saving m
      ≤ multiplier * (coefficient * (m + 1) ^ degree / logScale m) :=
        Nat.mul_le_mul_left _ hdivPow
    _ ≤ pairClock depth n := hstep

/-- The machine-level little-o certificate AT the boundary degree — the
form the refuter closure consumes: degree may equal
`2 ^ depth` provided one saving power is declared. -/
theorem executableMachine_quotient_runsInLittleO_pairClock
    (machine : ExecutableWeakNondeterministicMachine) (depth : ℕ)
    (hdegree : machine.verifier.degree ≤ 2 ^ depth)
    (hsaving : 1 ≤ machine.verifier.logPower)
    (hwitness : ∀ n, machine.witnessBits n ≤ n) :
    RunsInLittleO machine.toSemantic (pairClock depth) := by
  intro multiplier _hmultiplier
  obtain ⟨onset, hbound⟩ :=
    quotientBudget_runsInLittleO_pairClock
      machine.verifier.coefficient machine.verifier.degree
      machine.verifier.logPower depth hdegree hsaving
      (fun n => n + machine.witnessBits n)
      (fun n => Nat.le_add_right n _)
      (fun n => by
        have := hwitness n
        omega)
      multiplier
  refine ⟨onset, ?_⟩
  intro n hn input witness
  simpa [ExecutableWeakNondeterministicMachine.toSemantic,
    ExecutableWeakNondeterministicMachine.verifierBudget,
    QuotientNatProgram.budget, WeakVerifierRequest.measure] using
      hbound n hn

end NearCubicWires.PolynomialClock

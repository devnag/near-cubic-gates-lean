import Proof.Gates.Main.Statement
import Proof.CaseAnalysis.PairClockExact
import Proof.Circuits.PolynomialOrdinaryClock

/-!
# Input 8 with the multitape clock gives the amplifier source

`NineInputs.amplification` is CLW20 Lemma 3.9 with the ordinary multitape `TimeConstructible` of input 7
(`CLW20_Lemma3_9_Multitape`). The proof needs the lemma at the size schedule `oracleSizeBound d = pairClock D`,
`S(n) = (n+1)^K − 1` with `K = 2^D`, `D = oracleDepth d ≥ 1` (`pairClock_succ_exact`). The lemma is applied where
the paper applies it (paper v2, `imp:ae-amplification`: "with S(q) = q^G"), at `S'(n) = n^K`, whose multitape clock is
`PolynomialClock.ordinaryClock (K − 2)`. `transfer` then moves the conclusion from `S'` to `S` with the constant
doubled: `S' ≤ S` carries the hardness hypothesis down, and `S ≤ S'^2` for `n ≥ 2` carries the inapproximability
up; `n = 0` is the same statement, and `n = 1` is vacuous (every one-bit function has a circuit with two nodes, while
`S(1) ≥ 3`). `g`, the arity and the construction are unchanged.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Amplifier

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.Bindings.CLW20Lemma39

/-! ## Monotonicity of the two circuit notions -/

theorem hasCircuitOfSize_mono {n : ℕ} {f : BoolFunction n} {s t : ℕ} (h : HasCircuitOfSize f s)
    (hst : s ≤ t) : HasCircuitOfSize f t := by
  obtain ⟨circuit, hsize, hf⟩ := h
  exact ⟨circuit, hsize.trans hst, hf⟩

/-- Non-approximability survives a larger advantage `ε` and a smaller size bound `s`. -/
theorem cannotBeApproximated_mono {m : ℕ} {g : BoolFunction m} {ε ε' s s' : ℝ}
    (h : CannotBeApproximated g ε s) (hε : ε ≤ ε') (hs : s' ≤ s) : CannotBeApproximated g ε' s' := by
  intro circuit hsize
  calc _ < (1 / 2 + ε) * 2 ^ m := h circuit (hsize.trans hs)
    _ ≤ (1 / 2 + ε') * 2 ^ m := by gcongr

/-! ## One-bit functions have two-node circuits -/

theorem eq_of_two_points (f e : BoolFunction 1) (h0 : e (fun _ => false) = f (fun _ => false))
    (h1 : e (fun _ => true) = f (fun _ => true)) (x : BitInput 1) : e x = f x := by
  have hx : x = fun _ => x 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [hx]
  generalize x 0 = b
  cases b
  · exact h0
  · exact h1

theorem hasCircuitOfSize_one (f : BoolFunction 1) : HasCircuitOfSize f 2 := by
  cases h0 : f (fun _ => false) <;> cases h1 : f (fun _ => true)
  · refine ⟨⟨[.const false], ⟨0, by simp⟩, fun ⟨i, hi⟩ => ?_⟩, by simp [BooleanCircuit.size], ?_⟩
    · simp at hi; subst hi; trivial
    · exact eq_of_two_points f _ (by simp [BooleanCircuit.eval, BooleanCircuit.values, BooleanNode.eval, h0])
        (by simp [BooleanCircuit.eval, BooleanCircuit.values, BooleanNode.eval, h1])
  · refine ⟨⟨[.input 0], ⟨0, by simp⟩, fun ⟨i, hi⟩ => ?_⟩, by simp [BooleanCircuit.size], ?_⟩
    · simp at hi; subst hi; trivial
    · exact eq_of_two_points f _ (by simp [BooleanCircuit.eval, BooleanCircuit.values, BooleanNode.eval, h0])
        (by simp [BooleanCircuit.eval, BooleanCircuit.values, BooleanNode.eval, h1])
  · refine ⟨⟨[.input 0, .not 0], ⟨1, by simp⟩, fun ⟨i, hi⟩ => ?_⟩, by simp [BooleanCircuit.size], ?_⟩
    · simp at hi
      interval_cases i <;> simp [BooleanNode.WellFormedAt]
    · exact eq_of_two_points f _ (by simp [BooleanCircuit.eval, BooleanCircuit.values, BooleanNode.eval, h0])
        (by simp [BooleanCircuit.eval, BooleanCircuit.values, BooleanNode.eval, h1])
  · refine ⟨⟨[.const true], ⟨0, by simp⟩, fun ⟨i, hi⟩ => ?_⟩, by simp [BooleanCircuit.size], ?_⟩
    · simp at hi; subst hi; trivial
    · exact eq_of_two_points f _ (by simp [BooleanCircuit.eval, BooleanCircuit.values, BooleanNode.eval, h0])
        (by simp [BooleanCircuit.eval, BooleanCircuit.values, BooleanNode.eval, h1])

/-! ## The two size functions -/

/-- Where the lemma is applied: `S'(n) = n^K`, `K = 2^(oracleDepth d)` (paper v2's `S(q) = q^G`). -/
def powSize (d n : ℕ) : ℕ := n ^ (2 ^ oracleDepth d)

theorem two_le_degree (d : ℕ) : 2 ≤ 2 ^ oracleDepth d := by
  have h : 1 ≤ oracleDepth d := RecoveryPipeline.coefficientExponent_positive d
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ oracleDepth d := Nat.pow_le_pow_right (by norm_num) h

theorem powSize_le (d n : ℕ) : powSize d n ≤ oracleSizeBound d n :=
  PolynomialClock.pow_twoPow_le_pairClock _ _

theorem oracleSizeBound_succ (d n : ℕ) : oracleSizeBound d n + 1 = (n + 1) ^ (2 ^ oracleDepth d) :=
  CloseoutPairClock.pairClock_succ_exact _ _

theorem oracleSizeBound_zero (d : ℕ) : oracleSizeBound d 0 = 0 := by
  have := oracleSizeBound_succ d 0
  simp at this
  omega

theorem three_le_oracleSizeBound_one (d : ℕ) : 3 ≤ oracleSizeBound d 1 := by
  have h := oracleSizeBound_succ d 1
  have h4 : 2 ^ 2 ≤ 2 ^ (2 ^ oracleDepth d) := Nat.pow_le_pow_right (by norm_num) (two_le_degree d)
  norm_num at h h4
  omega

/-- `S ≤ S'^2` from `n = 2` on: `(n+1)^K ≤ (n^2)^K`. -/
theorem oracleSizeBound_le_sq (d n : ℕ) (hn : 2 ≤ n) : oracleSizeBound d n ≤ powSize d n ^ 2 := by
  have h := oracleSizeBound_succ d n
  have hle : (n + 1) ^ (2 ^ oracleDepth d) ≤ (n ^ 2) ^ (2 ^ oracleDepth d) :=
    Nat.pow_le_pow_left (by nlinarith) _
  have heq : (n ^ 2) ^ (2 ^ oracleDepth d) = powSize d n ^ 2 := by
    unfold powSize
    rw [← pow_mul, ← pow_mul, mul_comm]
  omega

/-- The real-power comparison behind the transfer, for sizes `1 ≤ a ≤ b^2`, `1 ≤ b`. -/
theorem rpow_transfer {a b c : ℝ} (hc : 1 ≤ c) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≤ b ^ 2) :
    a ^ ((1 : ℝ) / (2 * c)) ≤ b ^ ((1 : ℝ) / c) ∧ b ^ (-(1 : ℝ) / c) ≤ a ^ (-(1 : ℝ) / (2 * c)) := by
  have hc0 : 0 < c := by linarith
  have h1 : a ^ ((1 : ℝ) / (2 * c)) ≤ b ^ ((1 : ℝ) / c) := by
    calc a ^ ((1 : ℝ) / (2 * c)) ≤ (b ^ 2) ^ ((1 : ℝ) / (2 * c)) :=
          Real.rpow_le_rpow (by linarith) hab (by positivity)
      _ = b ^ ((1 : ℝ) / c) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          congr 1
          field_simp
          norm_num
  refine ⟨h1, ?_⟩
  rw [neg_div, neg_div, Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
  exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) h1

/-! ## The transfer -/

/-- **The transfer.** The lemma at `n^K` gives the lemma at `oracleSizeBound d`, with the constant doubled. -/
noncomputable def transfer {c : ℝ} (hc : 1 ≤ c) (d : ℕ) (W : Lemma3_9At c (powSize d)) :
    Lemma3_9At (2 * c) (oracleSizeBound d) where
  g := W.g
  arityFactor := W.arityFactor
  arityOnset := W.arityOnset
  amplifies := fun n f hf => by
    have hf' : ¬ HasCircuitOfSize f (powSize d n) := fun h => hf (hasCircuitOfSize_mono h (powSize_le d n))
    obtain ⟨harity, happrox⟩ := W.amplifies n f hf'
    refine ⟨harity, cannotBeApproximated_mono happrox ?_ ?_⟩
    · rcases n with _ | _ | n
      · have hc0 : (0 : ℝ) < c := by linarith
        simp [powSize, oracleSizeBound_zero, Real.zero_rpow, hc0.ne']
      · exact (hf (hasCircuitOfSize_mono (hasCircuitOfSize_one f)
          ((by norm_num : 2 ≤ 3).trans (three_le_oracleSizeBound_one d)))).elim
      · have hb : (1 : ℝ) ≤ (powSize d (n + 2) : ℝ) := by
          exact_mod_cast Nat.one_le_pow _ _ (by omega)
        have ha : (1 : ℝ) ≤ (oracleSizeBound d (n + 2) : ℝ) := hb.trans (by exact_mod_cast powSize_le d _)
        have hab : (oracleSizeBound d (n + 2) : ℝ) ≤ (powSize d (n + 2) : ℝ) ^ 2 := by
          exact_mod_cast oracleSizeBound_le_sq d (n + 2) (by omega)
        exact (rpow_transfer hc ha hb hab).2
    · rcases n with _ | _ | n
      · have hc0 : (0 : ℝ) < c := by linarith
        simp [powSize, oracleSizeBound_zero, Real.zero_rpow, hc0.ne']
      · exact (hf (hasCircuitOfSize_mono (hasCircuitOfSize_one f)
          ((by norm_num : 2 ≤ 3).trans (three_le_oracleSizeBound_one d)))).elim
      · have hb : (1 : ℝ) ≤ (powSize d (n + 2) : ℝ) := by
          exact_mod_cast Nat.one_le_pow _ _ (by omega)
        have ha : (1 : ℝ) ≤ (oracleSizeBound d (n + 2) : ℝ) := hb.trans (by exact_mod_cast powSize_le d _)
        have hab : (oracleSizeBound d (n + 2) : ℝ) ≤ (powSize d (n + 2) : ℝ) ^ 2 := by
          exact_mod_cast oracleSizeBound_le_sq d (n + 2) (by omega)
        exact (rpow_transfer hc ha hb hab).1
  construction := W.construction

/-! ## The multitape clock and the adapter -/

/-- The multitape clock of `n^K`: the `n^(k+2)` clock `PolynomialClock.ordinaryClock` at `k = K − 2`. -/
noncomputable def powClock (d : ℕ) : OrdinaryClock (powSize d) := by
  have h : (fun n => n ^ ((2 ^ oracleDepth d - 2) + 2)) = powSize d := by
    funext n
    unfold powSize
    have := two_le_degree d
    congr 1
    omega
  exact h ▸ RepairOrdinary.PolynomialClock.ordinaryClock (2 ^ oracleDepth d - 2)

/-- **Input 8 → the amplifier source.** As `clw20_lemma3_9_to_import` (`Bindings/CLW20_Lemma3_9.lean`), with the
lemma taken at `n^K` through the multitape clock and moved to `oracleSizeBound d` by `transfer`. -/
theorem amplifier_of_multitape : CLW20_Lemma3_9_Multitape → Nonempty SourceAmplifierFactory := by
  rintro ⟨c, hc, hlit⟩
  have hc2 : 1 ≤ 2 * c := by linarith
  exact ⟨{ stvExponent := ⌈2 * c⌉₊
           stvExponentPositive := Nat.ceil_pos.mpr (by linarith)
           forSchedule := fun d =>
             (hlit (powSize d) (NearCubicWires.Bindings.CLW20Theorem113.clock_timeConstructible (powClock d))).map
               fun W => scheduleAmplifierOfLiteral hc2 d (transfer hc d W.toTier1) }⟩

end NearCubicGates.Close.Amplifier

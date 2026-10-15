import Proof.Wire_3_5.RecoveryAssembly

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)
open Filter

/-- The length schedule at the gate constants. -/
noncomputable def recSched (l : Literals) (G : Split.Gate) (kclk : ℕ) : LengthSchedule :=
  recSchedule (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l)

/-- The width `q(2^{a(n)})` of the slice `n`. -/
noncomputable def recWidth (l : Literals) (G : Split.Gate) (kclk n : ℕ) : ℕ :=
  nativeWidth kclk G.Apad (2 ^ (recSched l G kclk).sourceIdx n)

theorem tendsto_two_pow_sourceIdx (T : LengthSchedule) : Tendsto (fun n => 2 ^ T.sourceIdx n) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => by
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 T.tendsto_sourceIdx b
    exact ⟨N, fun n hn => (hN n hn).trans (Nat.lt_two_pow_self).le⟩

theorem tendsto_recWidth (l : Literals) (G : Split.Gate) (kclk : ℕ) : Tendsto (recWidth l G kclk) atTop atTop :=
  (tendsto_nativeWidth kclk G.Apad).comp (tendsto_two_pow_sourceIdx (recSched l G kclk))

/-- The slice length is at most `(q+1)⁴` once `K₀ ≤ q`. -/
theorem n_succ_le (K₀ q n : ℕ) (hK : K₀ ≤ q) (hn : n ≤ K₀ * q * (Nat.log 2 (Lq q) + 1)) : n + 1 ≤ (q + 1) ^ 4 := by
  have hl : Nat.log 2 (Lq q) + 1 ≤ q + 2 := by
    have h1 := (Nat.log_le_clog 2 (Lq q)).trans (clog_le_self' (Lq q))
    have h2 := Lq_le q
    omega
  have h1 : K₀ * q * (Nat.log 2 (Lq q) + 1) ≤ q * q * (q + 2) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hK) hl
  have h2 : q * q * (q + 2) + 1 ≤ (q + 1) ^ 4 := by nlinarith
  omega

section Leaf
variable (l : Literals) (G : Split.Gate) (hG : GateRel l G) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
  (U : Split.UnionLeafAt (G.inputs kclk coef A a ha) (unionSetupS1 l G kclk coef A a ha))
  (P : FusedPrimitive (G.inputs kclk coef A a ha))

include hG in
/-- **Every large slice is hard in both classes** within the integer per-atom caps. -/
theorem eventually_slice :
    ∀ᶠ n : ℕ in atTop,
      (∀ circuit : SymmetricThresholdCircuit n,
        circuit.wireCount ≤ ⌊wireCap G.row.cap .sym (recWidth l G kclk n)⌋₊ →
        agreement circuit.eval (recLanguage l G (gateZeta_pos l) (gateZeta_lt l) (recDG l) kclk coef A a ha
          (recMachine l G U P) n) <
          1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n))) ∧
      (∀ circuit : ThresholdThresholdCircuit n,
        circuit.wireCount ≤ ⌊wireCap G.row.cap .thr (recWidth l G kclk n)⌋₊ →
        agreement circuit.eval (recLanguage l G (gateZeta_pos l) (gateZeta_lt l) (recDG l) kclk coef A a ha
          (recMachine l G U P) n) <
          1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n))) := by
  have hN := tendsto_two_pow_sourceIdx (recSched l G kclk)
  have hq := tendsto_recWidth l G kclk
  obtain ⟨onR, hR⟩ := rejected_yes_eventually l G U P
  obtain ⟨onC, hC⟩ := U.complete P (recL l kclk) (recL_inNTIME l kclk)
  obtain ⟨cB, dB, _, hB⟩ := recBudget_poly l kclk
  have hNev : ∀ᶠ N : ℕ in atTop,
      ((recSetup l G kclk coef A a ha).pcp.nativeWidth N = nativeWidth kclk G.Apad N ∧
        ∀ (z : BitInput N) (oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N)),
          ((recSetup l G kclk coef A a ha).request z oracle).arity = nativeWidth kclk G.Apad N) ∧
      onR ≤ N ∧ onC ≤ N ∧ (G.budget kclk coef A a ha).onset ≤ N ∧
      cB * (nativeWidth kclk G.Apad N + 1) ^ dB ≤ N / 16 := by
    filter_upwards [eventually_request_arity l G kclk coef A a ha hG.apad, eventually_ge_atTop onR,
      eventually_ge_atTop onC, eventually_ge_atTop (G.budget kclk coef A a ha).onset,
      eventually_poly_le_div16 kclk G.Apad cB dB] with N h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hK : ∀ᶠ q : ℕ in atTop, (gatePCPP l).coefficient * recKs l kclk ^ (gatePCPP l).degree ≤ q + 2 ∧
      6 * ((recSched l G kclk).J + 1) + 2 ≤ q := by
    filter_upwards [eventually_ge_atTop ((gatePCPP l).coefficient * recKs l kclk ^ (gatePCPP l).degree +
      (6 * ((recSched l G kclk).J + 1) + 2))] with q hq
    exact ⟨by omega, by omega⟩
  filter_upwards [hN.eventually hNev, hq.eventually (eventually_recQ l G hG), hq.eventually hK,
    (recSched l G kclk).eventually_lengths] with n hNn hQn hKn hlen
  obtain ⟨⟨hw, harity⟩, hRn, hCn, hBn, hbud⟩ := hNn
  obtain ⟨-, hlen2, -, hnq⟩ := hlen
  rw [recLanguage_slice]
  exact core_hard_at l G hG U P _ (recWidth l G kclk n) n hw (harity _) (hR _ hRn).1 (hR _ hRn).2
    (fun g hg => hC _ hCn _ g hg) ((G.budget kclk coef A a ha).fits _ hBn) ((hB _).trans hbud) hQn hKn.1
    (hlen2.trans (Nat.div_le_self _ _)) (n_succ_le _ _ n hKn.2 hnq)

/-- **The recovered language**: the canonical language, `false` while `2^{a(n)}` is below the cutoff. -/
noncomputable def recLanguageCut (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (M : OrdinaryWeakMachine) (cutoff : ℕ) : Language :=
  fun n => if cutoff ≤ 2 ^ (recSched l G kclk).sourceIdx n then
    recLanguage l G (gateZeta_pos l) (gateZeta_lt l) (recDG l) kclk coef A a ha M n else fun _ => false

include hG in
/-- **The recovered language is hard in both classes** at row B's exponents, at every positive multiplier. -/
theorem recLanguageCut_hard (cutoff : ℕ) :
    (∀ AT : ℝ, 0 < AT →
      ThrHardAt (1 / 8) (11 / 2) (recLanguageCut l G kclk coef A a ha (recMachine l G U P) cutoff) AT) ∧
    (∀ AS : ℝ, 0 < AS →
      SymHardAt (1 / 8) (9 / 2) (recLanguageCut l G kclk coef A a ha (recMachine l G U P) cutoff) AS) := by
  have hq := tendsto_recWidth l G kclk
  have hrange : ∀ᶠ n : ℕ in atTop, recWidth l G kclk n ≤ n ∧
      n ≤ (6 * ((recSched l G kclk).J + 1) + 2) * recWidth l G kclk n *
        (Nat.log 2 (Lq (recWidth l G kclk n)) + 1) := by
    filter_upwards [(recSched l G kclk).eventually_lengths] with n h
    exact ⟨h.2.2.1, h.2.2.2⟩
  have hlang : ∀ᶠ n : ℕ in atTop, recLanguageCut l G kclk coef A a ha (recMachine l G U P) cutoff n =
      recLanguage l G (gateZeta_pos l) (gateZeta_lt l) (recDG l) kclk coef A a ha (recMachine l G U P) n := by
    filter_upwards [(tendsto_two_pow_sourceIdx (recSched l G kclk)).eventually (eventually_ge_atTop cutoff)]
      with n h
    unfold recLanguageCut
    rw [if_pos h]
  have hsl := eventually_slice l G hG U P
  refine ⟨?_, ?_⟩
  · exact rowB_thrHardAt G.row.cap hG.aT (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) _ _
      (recWidth l G kclk) hq hrange
      (fun n => xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n)))
      (by
        filter_upwards [hsl, hlang] with n h hl
        intro circuit hwire
        rw [hl]
        exact h.2 circuit (Nat.le_floor hwire))
      (Eventually.of_forall fun _ => le_rfl)
  · exact rowB_symHardAt G.row.cap hG.aS (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) _ _
      (recWidth l G kclk) hq hrange
      (fun n => xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n)))
      (by
        filter_upwards [hsl, hlang] with n h hl
        intro circuit hwire
        rw [hl]
        exact h.1 circuit (Nat.le_floor hwire))
      (Eventually.of_forall fun _ => le_rfl)

end Leaf

noncomputable def recoveryLeaf (l : Literals) (G : Split.Gate) (hG : GateRel l G)
    (cert : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
      (U : Split.UnionLeafAt (G.inputs kclk coef A a ha) (unionSetupS1 l G kclk coef A a ha))
      (P : FusedPrimitive (G.inputs kclk coef A a ha)),
      ∃ cutoff : ℕ, Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat
        (recLanguageCut l G kclk coef A a ha (recMachine l G U P) cutoff))) :
    Split.RecoveryLeaf G (unionSetupS1 l G) := fun kclk coef A a ha U P =>
  { language := fun _ =>
      recLanguageCut l G kclk coef A a ha (recMachine l G U P) (Classical.choose (cert kclk coef A a ha U P))
    certificate := fun _ => Classical.choice (Classical.choose_spec (cert kclk coef A a ha U P))
    thr := fun _ _ _ => (recLanguageCut_hard l G hG U P _).1
    sym := fun _ _ _ => (recLanguageCut_hard l G hG U P _).2 }

end NearCubicWires.WireExponent3_5.Transfer

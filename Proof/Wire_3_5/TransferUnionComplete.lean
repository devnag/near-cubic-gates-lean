import Proof.Wire_3_5.TransferUnionSound
import Proof.Wire_3_5.FilterGap

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open Filter Topology
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR uMean_mono)
open NearCubicWires.ComponentwiseBranchExtraction (systematicConstraint)

/-- `tr:completeness`'s acceptance with real estimates: within `ε₀` of the tests of a completeness witness whose
masks miss at most `β + ξ`, the estimates pass the thresholds. -/
theorem completeness_accepts_real {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {cp sp : ℝ}
    {params : MaskedSoundnessParameters cp sp} (cparams : MaskedCompletenessParameters params)
    {Seed : Type} [Fintype Seed] [Nonempty Seed] (aux : BitInput q → BitInput pcpp.auxiliaryBits)
    (T S : PcppVar pcpp → BitInput q → ℝ) (w : CompletenessWitness pcpp aux T S cparams.ζ cparams.δ)
    (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (hacc : cp ≤ uMean (fun x : BitInput q => pcpp.satisfiedFraction x (aux x)))
    (hmissing : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
        1 - bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2)) ≤ (cparams.β : ℝ) + cparams.ξ)
    (Vh Qh μh : ℝ) (hV : |Vh - testV pcpp S G| ≤ params.eps0) (hQ : |Qh - testQ pcpp S G| ≤ params.eps0)
    (hμ : |μh - testMu pcpp S G| ≤ params.eps0) :
    Vh ≤ 2 * (params.v0 : ℝ) ∧ Qh ≤ 1 + (params.v0 : ℝ) ∧ (params.threshold : ℝ) ≤ μh := by
  have hζ1 : Real.sqrt (cparams.ζ : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact_mod_cast cparams.ζ_le_one
  have hδ1 : (cparams.δ : ℝ) ≤ 1 := by exact_mod_cast cparams.δ_le_one
  have hu : Real.sqrt (cparams.ζ : ℝ) + cparams.δ ≤ 2 := by linarith
  have hVb := completeness_testV w G
  have hQb := completeness_testQ w G
  have hmiss := (missingClause_le G).trans (mul_le_mul_of_nonneg_left hmissing zero_le_two)
  have hμb := completeness_testMu w G hacc hmiss hu
  have hVs := cparams.V_slack
  have hQs := cparams.Q_slack
  have hμs := cparams.μ_slack
  refine ⟨?_, ?_, ?_⟩
  · linarith [(abs_le.mp hV).2]
  · linarith [(abs_le.mp hQ).2]
  · linarith [(abs_le.mp hμ).1]

section Union
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

theorem honest_acceptance (S : UnionSetup I) {N : ℕ} (z : BitInput N) (oracle : BooleanCircuit (S.pcp.nativeWidth N))
    (htaut : ∀ x, (S.request z oracle).circuit.eval x = true) :
    S.pcppAlg.completeness ≤ uMean (fun x : BitInput (S.request z oracle).arity =>
      (S.pcppOf z oracle).satisfiedFraction x ((S.pcppOf z oracle).honestAuxiliary x)) := by
  have h := uMean_mono (Ω := BitInput (S.request z oracle).arity) (f := fun _ => S.pcppAlg.completeness)
    (g := fun x => (S.pcppOf z oracle).satisfiedFraction x ((S.pcppOf z oracle).honestAuxiliary x))
    (fun x => S.pcppAlg.complete (S.request z oracle) x (htaut x))
  rwa [uMean_const] at h

namespace UnionGuess
variable {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z)

/-- The guess's grid sum is `(Λ̄/s)Σ_a σ_{X,a} C_{X,a}(x)`. -/
theorem forms_guess (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) (X : PcppVar g.pcpp) (x : BitInput g.q) :
    (g.forms hsign).guess X x =
      (S.gridMass g.q : ℝ) / g.s * ∑ a : Fin g.s, (g.sign X a : ℝ) * bitR (g.mode.eval (g.atom X a) x) := by
  show linForm g.atoms (g.wS X) x = _
  unfold linForm
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : ∑ u : Unit, g.wS X (Sum.inl u) * bitR (g.atoms (Sum.inl u) x) = 0 :=
    Finset.sum_eq_zero fun u _ => by simp [wS]
  have h3 : ∑ Y : PcppVar g.pcpp, g.wS X (Sum.inr (Sum.inr Y)) * bitR (g.atoms (Sum.inr (Sum.inr Y)) x) = 0 :=
    Finset.sum_eq_zero fun Y _ => by simp [wS]
  have h2 : ∑ Y : PcppVar g.pcpp, ∑ a : Fin g.s,
      g.wS X (Sum.inr (Sum.inl (Y, a))) * bitR (g.atoms (Sum.inr (Sum.inl (Y, a))) x) =
      ∑ a : Fin g.s, (S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ) * bitR (g.mode.eval (g.atom X a) x) := by
    rw [Finset.sum_eq_single X]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [show g.wS X (Sum.inr (Sum.inl (X, a))) = (S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ) from if_pos rfl]
      rfl
    · intro Y _ hY; exact Finset.sum_eq_zero fun a _ => by simp [wS, hY]
    · simp
  rw [h1, h2, h3, zero_add, add_zero, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem unionAccepts_of_parts (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params)
    (hsize : g.oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N))
    (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) (hword : g.word.length ≤ N / 16)
    (hVcall : ∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t))
    (hQcall : ∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t))
    (hμcall : ∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t))
    (htaut : ∀ x, (S.request z g.oracle).circuit.eval x = true)
    (T : PcppVar g.pcpp → BitInput g.q → ℝ)
    (w : CompletenessWitness g.pcpp g.pcpp.honestAuxiliary T (g.forms hsign).guess cparams.ζ cparams.δ)
    (hmissing : uMean (fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 × (I.Seed g.mode g.q × BitInput g.q) =>
        1 - bitR (carrierFilter I g.mode g.pcpp g.carrier g.translation (posVar g.pcpp p.1 p.2.1) p.2.2.1 p.2.2.2)) ≤
      (cparams.β : ℝ) + cparams.ξ)
    (hD : (1 + (S.gridMass g.q : ℝ)) ^ 4 * (g.q : ℝ) ^ (-(I.D : ℝ)) ≤ (S.params.eps0 : ℝ)) :
    UnionAccepts S P z g := by
  have hL : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) := by exact_mod_cast S.gridMass_nonneg _
  have hVacc := seed_propagated_V I P hL (g.forms hsign) g.carrier g.translation hVcall
  have hQacc := seed_propagated_Q I P hL (g.forms hsign) g.carrier g.translation hQcall
  have hμacc := seed_propagated_Mu I P hL (g.forms hsign) g.carrier g.translation hμcall
  obtain ⟨hV, hQ, hμ⟩ := completeness_accepts_real g.pcpp cparams g.pcpp.honestAuxiliary T (g.forms hsign).guess w
    (carrierFilter I g.mode g.pcpp g.carrier g.translation) (honest_acceptance S z g.oracle htaut) hmissing
    (g.Vhat P) (g.Qhat P) (g.μhat P) (hVacc.trans hD) (hQacc.trans hD) (hμacc.trans hD)
  exact ⟨hsize, hsign, hword, hVcall, hQcall, hμcall, hV, hQ, hμ⟩

/-! ## Admissible calls: the tuple of a nonzero coefficient lies in the named carriers -/

theorem wS_support {X : PcppVar g.pcpp} {a : g.AtomIx} (h : g.wS X a ≠ 0) :
    ∃ b, a = Sum.inr (Sum.inl (X, b)) := by
  rcases a with u | (⟨Y, b⟩ | Y)
  · exact absurd rfl h
  · by_cases hY : Y = X
    · exact ⟨b, by rw [hY]⟩
    · exact absurd (if_neg hY) h
  · exact absurd rfl h

theorem wOne_support {a : g.AtomIx} (h : g.wOne a ≠ 0) : ∃ u, a = Sum.inl u := by
  rcases a with u | (p | Y)
  · exact ⟨u, rfl⟩
  · exact absurd rfl h
  · exact absurd rfl h

theorem wE_support {X : PcppVar g.pcpp} {a : g.AtomIx} (h : g.wE X a ≠ 0) : a = Sum.inr (Sum.inr X) := by
  rcases a with u | (p | Y)
  · exact absurd rfl h
  · exact absurd rfl h
  · by_cases hY : Y = X
    · rw [hY]
    · exact absurd (if_neg hY) h

theorem gates_const (u : Unit) : g.mode.gates (g.circ (Sum.inl u)) = [] := S.constAtom_gates _ _

theorem gates_atom_sublist (X : PcppVar g.pcpp) (b : Fin g.s) :
    (g.mode.gates (g.atom X b)).Sublist (g.carrier X) := by
  unfold carrier
  exact (List.sublist_flatten_of_mem (L := List.ofFn fun a => g.mode.gates (g.atom X a))
    (List.mem_ofFn.mpr ⟨b, rfl⟩)).trans (List.sublist_append_left _ _)

theorem gates_parity_sublist (X : PcppVar g.pcpp) (h : g.sysBit X = true) :
    (g.mode.gates (g.parity X)).Sublist (g.carrier X) := by
  unfold carrier
  rw [if_pos h]
  exact List.sublist_append_right _ _

theorem coeff_factor_ne {α : Type} {P : Poly4 α} {j : Fin 4} {t : Fin 4 → α} (h : P.coeff j t ≠ 0) (k : Fin 4) :
    P.F j k (t k) ≠ 0 := by
  unfold Poly4.coeff at h
  have h2 : ∏ k, P.F j k (t k) ≠ 0 := right_ne_zero_of_mul h
  exact (Finset.prod_ne_zero_iff.mp h2) k (Finset.mem_univ _)

theorem polyV_factor {α : Type} (sys : Bool) (wS wOne wE : α → ℝ) (j k : Fin 4) :
    (polyV sys wS wOne wE).F j k = wS ∨ (polyV sys wS wOne wE).F j k = wOne ∨
      (sys = true ∧ (polyV sys wS wOne wE).F j k = wE) := by
  cases sys <;> fin_cases j <;> fin_cases k <;> simp [polyV, Poly4.mk4, fac4]

theorem polyQ_factor {α : Type} (wS wOne : α → ℝ) (j k : Fin 4) :
    (polyQ wS wOne).F j k = wS ∨ (polyQ wS wOne).F j k = wOne := by
  fin_cases j <;> fin_cases k <;> simp [polyQ, Poly4.mk4, fac4]

theorem polyMu_factor {α : Type} (n₀ n₁ : Bool) (wX wY wOne : α → ℝ) (j k : Fin 4) :
    (polyMu n₀ n₁ wX wY wOne).F j k = wX ∨ (polyMu n₀ n₁ wX wY wOne).F j k = wY ∨
      (polyMu n₀ n₁ wX wY wOne).F j k = wOne := by
  fin_cases j <;> fin_cases k <;> simp [polyMu, Poly4.mk4, fac4]

/-- A tuple entry allowed for a `V`/`Q` call of `X` has its gates in `X`'s carrier. -/
theorem gates_sublist_of_allowed (X : PcppVar g.pcpp) (a : g.AtomIx)
    (ha : (∃ u, a = Sum.inl u) ∨ (∃ b, a = Sum.inr (Sum.inl (X, b))) ∨
      (g.sysBit X = true ∧ a = Sum.inr (Sum.inr X))) :
    (g.mode.gates (g.circ a)).Sublist (g.carrier X) := by
  rcases ha with ⟨u, rfl⟩ | ⟨b, rfl⟩ | ⟨hs, rfl⟩
  · rw [gates_const]; exact List.nil_sublist _
  · exact g.gates_atom_sublist X b
  · exact g.gates_parity_sublist X hs

open Classical in

theorem translationOk (hStar : I.StarAt g.q) (req : PrimRequest) (hn : req.n = g.q)
    (ht : req.translation = g.translation) : B.TranslationOk req := by
  have htr : g.translation = (I.starParams g.q hStar).selectCodes g.pops := by
    unfold translation; rw [dif_pos hStar]
  refine ⟨?_, ?_⟩
  · rw [ht, htr, Shared.StarParams.selectCodes_length, hn]; rfl
  · intro t hti
    rw [ht, htr] at hti
    rw [hn]
    exact Shared.StarParams.selectCodes_lt _ _ t hti

/-- **Every nonzero-coefficient `V` call is admissible**, given the star and fit conditions at `q`, the name count,
the carriers' and circuits' envelopes. -/
theorem vCall_call (hStar : I.StarAt g.q) (hFit : B.FitsAt g.q) (hname : 2 ≤ I.nameCount)
    (henv : ∀ X, (g.carrier X).WithinEnvelope I.carrierDeg)
    (hdesc : ∀ a : g.AtomIx, g.mode.descriptionBits (g.circ a) ≤ (g.q + 1) ^ I.descDeg)
    (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (t : Fin 4 → g.AtomIx)
    (hallow : ∀ k, (g.mode.gates (g.circ (t k))).Sublist (g.carrier (posVar g.pcpp pos.1 pos.2))) :
    I.Call (g.vCall pos t) := by
  refine ⟨fun k => ((hallow k).subperm).trans ?_, ?_, fun k => hdesc (t k), ?_, ?_, hStar, hFit⟩
  · simp only [vCall, tupleRequest, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact List.Subperm.refl _
  · intro Y hY
    have hY' : Y = g.carrier (posVar g.pcpp pos.1 pos.2) := List.mem_singleton.mp hY
    rw [hY']; exact henv _
  · show 1 ≤ I.nameCount
    omega
  · exact g.translationOk hStar _ rfl rfl

/-- **Every nonzero-coefficient `μ` call is admissible.** -/
theorem muCall_call (hStar : I.StarAt g.q) (hFit : B.FitsAt g.q) (hname : 2 ≤ I.nameCount)
    (henv : ∀ X, (g.carrier X).WithinEnvelope I.carrierDeg)
    (hdesc : ∀ a : g.AtomIx, g.mode.descriptionBits (g.circ a) ≤ (g.q + 1) ^ I.descDeg)
    (i : Fin (2 ^ g.pcpp.clauseBits)) (t : Fin 4 → g.AtomIx)
    (hallow : ∀ k, (g.mode.gates (g.circ (t k))).Sublist (g.carrier (posVar g.pcpp i 0)) ∨
      (g.mode.gates (g.circ (t k))).Sublist (g.carrier (posVar g.pcpp i 1))) :
    I.Call (g.muCall i t) := by
  refine ⟨fun k => ?_, ?_, fun k => hdesc (t k), ?_, ?_, hStar, hFit⟩
  · simp only [muCall, tupleRequest, List.flatten_cons, List.flatten_nil, List.append_nil]
    rcases hallow k with h | h
    · exact (h.trans (List.sublist_append_left _ _)).subperm
    · exact (h.trans (List.sublist_append_right _ _)).subperm
  · intro Y hY
    have hY0 : Y ∈ [g.carrier (posVar g.pcpp i 0), g.carrier (posVar g.pcpp i 1)] := hY
    rcases List.mem_cons.mp hY0 with h | h
    · rw [h]; exact henv _
    · rw [List.mem_singleton.mp h]; exact henv _
  · show 2 ≤ I.nameCount
    exact hname
  · exact g.translationOk hStar _ rfl rfl

/-- The `V`, `Q` and `μ` calls of every nonzero coefficient are admissible. -/
theorem calls_admissible (hStar : I.StarAt g.q) (hFit : B.FitsAt g.q) (hname : 2 ≤ I.nameCount)
    (henv : ∀ X, (g.carrier X).WithinEnvelope I.carrierDeg)
    (hdesc : ∀ a : g.AtomIx, g.mode.descriptionBits (g.circ a) ≤ (g.q + 1) ^ I.descDeg) :
    (∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
    (∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
    (∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t)) := by
  refine ⟨fun pos j t hc => ?_, fun pos j t hc => ?_, fun i j t hc => ?_⟩
  · refine g.vCall_call hStar hFit hname henv hdesc pos t fun k => ?_
    have hk := coeff_factor_ne hc k
    refine g.gates_sublist_of_allowed _ _ ?_
    rcases polyV_factor (g.sysBit (posVar g.pcpp pos.1 pos.2)) _ _ _ j k with h | h | ⟨hs, h⟩ <;>
      unfold polyVAt at hk <;> rw [h] at hk
    · exact Or.inr (Or.inl (g.wS_support hk))
    · exact Or.inl (g.wOne_support hk)
    · exact Or.inr (Or.inr ⟨hs, g.wE_support hk⟩)
  · refine g.vCall_call hStar hFit hname henv hdesc pos t fun k => ?_
    have hk := coeff_factor_ne hc k
    refine g.gates_sublist_of_allowed _ _ ?_
    rcases polyQ_factor _ _ j k with h | h <;> unfold polyQAt at hk <;> rw [h] at hk
    · exact Or.inr (Or.inl (g.wS_support hk))
    · exact Or.inl (g.wOne_support hk)
  · refine g.muCall_call hStar hFit hname henv hdesc i t fun k => ?_
    have hk := coeff_factor_ne hc k
    rcases polyMu_factor (posNeg g.pcpp i 0) (posNeg g.pcpp i 1) _ _ _ j k with h | h | h <;>
      unfold polyMuAt at hk <;> rw [h] at hk
    · obtain ⟨b, hb⟩ := g.wS_support hk
      exact Or.inl (g.gates_sublist_of_allowed _ _ (Or.inr (Or.inl ⟨b, hb⟩)))
    · obtain ⟨b, hb⟩ := g.wS_support hk
      exact Or.inr (g.gates_sublist_of_allowed _ _ (Or.inr (Or.inl ⟨b, hb⟩)))
    · obtain ⟨u, hu⟩ := g.wOne_support hk
      exact Or.inl (g.gates_sublist_of_allowed _ _ (Or.inl ⟨u, hu⟩))

/-- The residual bits of a carrier have twice its length. -/
theorem length_residualBits {n : ℕ} (X : Stars.Carrier n) (c u v : BitInput n) :
    (Stars.Carrier.residualBits X c u v).length = 2 * X.length := by
  unfold Stars.Carrier.residualBits
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate, smul_eq_mul]
  ring

/-- `star:selection`'s objective of a list indexed by `Fin k`. -/
theorem objective_finRange (P : Shared.StarParams) (σ : P.Translation) {k : ℕ} (F : Fin k → ℚ × Stars.Carrier P.n) :
    (P.objective σ ((List.finRange k).map F) : ℝ) =
      (∑ i : Fin k, ((F i).1 : ℝ) * ∑ x : BitInput P.n, (Stars.inputPopulation P σ (F i).2 x : ℝ)) / 2 ^ P.n := by
  unfold Shared.StarParams.objective
  rw [List.map_map, ← Fin.sum_univ_def]
  simp only [Function.comp_apply]
  push_cast
  rfl

/-- Grouping a position sum by the variable named there. -/
theorem sum_pos_eq_sum_var (G : PcppVar g.pcpp → ℝ) :
    ∑ pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2, G (posVar g.pcpp pos.1 pos.2) =
      ∑ X : PcppVar g.pcpp, ((Finset.univ.filter fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 =>
        posVar g.pcpp p.1 p.2 = X).card : ℝ) * G X := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 => posVar g.pcpp pos.1 pos.2)
    (fun pos => G (posVar g.pcpp pos.1 pos.2))]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.sum_congr rfl fun pos hpos => by rw [(Finset.mem_filter.mp hpos).2], Finset.sum_const, nsmul_eq_mul]

theorem objective_eq_uMean (hStar : I.StarAt g.q) (σ : (I.starParams g.q hStar).Translation) :
    ((I.starParams g.q hStar).objective σ g.pops : ℝ) =
      uMean (fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 × BitInput g.q =>
        (Stars.inputPopulation (I.starParams g.q hStar) σ (g.carrier (posVar g.pcpp p.1 p.2.1)) p.2.2 : ℝ)) := by
  classical
  obtain ⟨Rf, hRf⟩ : ∃ Rf : PcppVar g.pcpp → BitInput g.q → ℝ,
      Rf = fun X x => (Stars.inputPopulation (I.starParams g.q hStar) σ (g.carrier X) x : ℝ) := ⟨_, rfl⟩
  have hL : ((I.starParams g.q hStar).objective σ g.pops : ℝ) =
      (∑ X : PcppVar g.pcpp, (g.weight X : ℝ) * ∑ x : BitInput g.q, Rf X x) / 2 ^ g.q := by
    have h := objective_finRange (I.starParams g.q hStar) σ (fun X : PcppVar g.pcpp => (g.weight X, g.carrier X))
    rw [hRf]
    exact h
  have hRside : uMean (fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 × BitInput g.q =>
      (Stars.inputPopulation (I.starParams g.q hStar) σ (g.carrier (posVar g.pcpp p.1 p.2.1)) p.2.2 : ℝ)) =
      uMean (fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 × BitInput g.q => Rf (posVar g.pcpp p.1 p.2.1) p.2.2) := by
    rw [hRf]
  rw [hL, hRside]
  have hsum : ∑ p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 × BitInput g.q, Rf (posVar g.pcpp p.1 p.2.1) p.2.2 =
      ∑ pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2, (fun X => ∑ x : BitInput g.q, Rf X x) (posVar g.pcpp pos.1 pos.2) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  have hcard : (Fintype.card (BitInput g.q) : ℝ) = 2 ^ g.q := by simp [BitInput, Fintype.card_pi]
  unfold uMean
  rw [hsum, g.sum_pos_eq_sum_var (fun X => ∑ x : BitInput g.q, Rf X x), Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [hcard]
  unfold weight
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun X _ => ?_
  field_simp

/-- The incidence weights are nonnegative and sum to one. -/
theorem weight_nonneg (X : PcppVar g.pcpp) : 0 ≤ g.weight X := by
  unfold weight; positivity

theorem sum_weight : ∑ X : PcppVar g.pcpp, (g.weight X : ℝ) = 1 := by
  classical
  unfold weight
  push_cast
  rw [← Finset.sum_div]
  have hcount : (∑ X : PcppVar g.pcpp, ((Finset.univ.filter fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 =>
      posVar g.pcpp p.1 p.2 = X).card : ℝ)) = 2 * 2 ^ g.pcpp.clauseBits := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (2 ^ g.pcpp.clauseBits) × Fin 2)))
      (t := (Finset.univ : Finset (PcppVar g.pcpp))) (f := fun p => posVar g.pcpp p.1 p.2)
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
    have h' : ((2 ^ g.pcpp.clauseBits * 2 : ℕ) : ℝ) =
        ∑ X : PcppVar g.pcpp, ((Finset.univ.filter fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 =>
          posVar g.pcpp p.1 p.2 = X).card : ℝ) := by
      rw [h]; push_cast; rfl
    rw [← h']; push_cast; ring
  rw [hcount]
  field_simp

theorem missing_at_guess (hStar : I.StarAt g.q) (spectrum : ExpanderSpectrumContract) (β ξ w Cpar : ℝ)
    (hξ0 : 0 ≤ ξ) (hξ : 1 / (2 : ℝ) ^ (I.filterParams g.mode g.q).errExp ≤ ξ)
    (henv : ∀ X, (g.carrier X).WithinEnvelope I.carrierDeg)
    (hwires : ∀ X, ((g.carrier X).wires : ℝ) ≤ g.s * w + Cpar * (g.q : ℝ) ^ 2)
    (hcap : (I.starParams g.q hStar).popRate * (g.s * w + Cpar * (g.q : ℝ) ^ 2) ≤ β * (B.capOf g.mode g.q : ℝ)) :
    uMean (fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 × (I.Seed g.mode g.q × BitInput g.q) =>
        1 - bitR (carrierFilter I g.mode g.pcpp g.carrier g.translation (posVar g.pcpp p.1 p.2.1) p.2.2.1 p.2.2.2)) ≤
      β + ξ := by
  classical
  set Pst := I.starParams g.q hStar
  set σ := Pst.translationOfCodes g.translation
  have htr : g.translation = Pst.selectCodes g.pops := by unfold translation; rw [dif_pos hStar]
  have hcap1 : (1 : ℝ) ≤ (B.capOf g.mode g.q : ℝ) := by exact_mod_cast B.capOf_pos g.mode g.q
  -- the filter's rejection below the cap
  have hfilt : ∀ X x, (Stars.inputPopulation Pst σ (g.carrier X) x : ℝ) ≤ (B.capOf g.mode g.q : ℝ) →
      uMean (fun e : I.Seed g.mode g.q => 1 - bitR (carrierFilter I g.mode g.pcpp g.carrier g.translation X e x)) ≤
        ξ := by
    intro X x hR
    set Z := Stars.inputResidualBits Pst σ (g.carrier X) x
    have hG : ∀ e : I.Seed g.mode g.q, carrierFilter I g.mode g.pcpp g.carrier g.translation X e x =
        Filters.gapFilter (I.filterParams g.mode g.q) e Z := by
      intro e
      show I.mask (maskRequest g.mode g.q [g.carrier X] g.translation) e x = _
      unfold PrimitiveInputs.mask maskRequest
      rw [dif_pos hStar]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      rfl
    have hlen : Z.length ≤ (I.filterParams g.mode g.q).len := by
      show (Stars.Carrier.residualBits _ _ _ _).length ≤ 2 * (g.q + 1) ^ I.carrierDeg
      rw [length_residualBits]
      exact Nat.mul_le_mul_left 2 (henv X).1
    have hcount : Z.count true ≤ (I.filterParams g.mode g.q).cap := by
      show (Stars.Carrier.residualBits _ _ _ _).count true ≤ B.capOf g.mode g.q
      rw [Stars.Carrier.count_residualBits]
      exact_mod_cast hR
    have hspec := (Filters.gapFilter_spec spectrum (I.filterParams g.mode g.q) (B.capOf_pos g.mode g.q) Z hlen).1
      hcount
    calc uMean (fun e : I.Seed g.mode g.q => 1 - bitR (carrierFilter I g.mode g.pcpp g.carrier g.translation X e x))
        = SupplierPipeline.booleanMean (fun e : Filters.GapSeed (I.filterParams g.mode g.q) =>
            !Filters.gapFilter (I.filterParams g.mode g.q) e Z) := by
          rw [Shared.booleanMean_eq_uMean]
          refine congrArg uMean (funext fun e => ?_)
          rw [hG e]
          cases Filters.gapFilter (I.filterParams g.mode g.q) e Z <;> simp [bitR]
      _ ≤ 1 / 2 ^ (I.filterParams g.mode g.q).errExp := hspec
      _ ≤ ξ := by exact_mod_cast hξ
  -- the population bound at the chosen translation
  have hpop : uMean (fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 × BitInput g.q =>
      (Stars.inputPopulation Pst σ (g.carrier (posVar g.pcpp p.1 p.2.1)) p.2.2 : ℝ)) ≤
      β * (B.capOf g.mode g.q : ℝ) := by
    rw [← g.objective_eq_uMean hStar σ]
    have hsel := Pst.selectCodes_population_le g.pops (fun p hp => by
      obtain ⟨X, -, rfl⟩ := List.mem_map.mp hp
      exact g.weight_nonneg X)
    rw [← htr] at hsel
    refine hsel.trans ?_
    have hsum : (g.pops.map fun p => (p.1 : ℝ) * (Stars.Carrier.wires p.2 : ℝ)).sum ≤
        g.s * w + Cpar * (g.q : ℝ) ^ 2 := by
      unfold pops
      rw [List.map_map, ← Fin.sum_univ_def]
      calc ∑ X : PcppVar g.pcpp, (g.weight X : ℝ) * ((g.carrier X).wires : ℝ)
          ≤ ∑ X : PcppVar g.pcpp, (g.weight X : ℝ) * (g.s * w + Cpar * (g.q : ℝ) ^ 2) :=
            Finset.sum_le_sum fun X _ => mul_le_mul_of_nonneg_left (hwires X) (by exact_mod_cast g.weight_nonneg X)
        _ = g.s * w + Cpar * (g.q : ℝ) ^ 2 := by rw [← Finset.sum_mul, g.sum_weight, one_mul]
    calc Pst.popRate * (g.pops.map fun p => (p.1 : ℝ) * (Stars.Carrier.wires p.2 : ℝ)).sum
        ≤ Pst.popRate * (g.s * w + Cpar * (g.q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (Stars.popRate_nonneg _)
      _ ≤ _ := hcap
  exact missing_le (Seed := I.Seed g.mode g.q) (carrierFilter I g.mode g.pcpp g.carrier g.translation)
    (fun X x => (Stars.inputPopulation Pst σ (g.carrier X) x : ℝ)) (B.capOf g.mode g.q : ℝ) β ξ
    (by linarith) hξ0 (fun X x => Nat.cast_nonneg _) hfilt hpop

/-! ## The guess word, the carriers' envelope and wires -/

theorem length_flatten_ofFn {β : Type} {k : ℕ} (F : Fin k → List β) :
    (List.ofFn F).flatten.length = ∑ a, (F a).length := by
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]; rfl

theorem word_length_le (Ko Ks Kc : ℕ)
    (hO : (natWord (ExecutableInterfaces.encodeBooleanCircuit g.oracle)).length ≤ Ko)
    (hS : ∀ X a, (intWord (g.sign X a)).length ≤ Ks) (hC : ∀ X a, (natWord (g.mode.code (g.atom X a))).length ≤ Kc) :
    g.word.length ≤ 1 + Ko + (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * (g.s * (Ks + Kc)) := by
  unfold word
  rw [List.length_append, List.length_append, List.length_singleton, length_flatten_ofFn]
  simp only [length_flatten_ofFn, List.length_append]
  have hinner : ∀ X : PcppVar g.pcpp,
      (∑ a : Fin g.s, ((intWord (g.sign X a)).length + (natWord (g.mode.code (g.atom X a))).length)) ≤
        g.s * (Ks + Kc) := by
    intro X
    calc _ ≤ ∑ _a : Fin g.s, (Ks + Kc) := Finset.sum_le_sum fun a _ => Nat.add_le_add (hS X a) (hC X a)
      _ = g.s * (Ks + Kc) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have houter : (∑ X : PcppVar g.pcpp, ∑ a : Fin g.s,
      ((intWord (g.sign X a)).length + (natWord (g.mode.code (g.atom X a))).length)) ≤
      (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * (g.s * (Ks + Kc)) := by
    calc _ ≤ ∑ _X : PcppVar g.pcpp, g.s * (Ks + Kc) := Finset.sum_le_sum fun X _ => hinner X
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.add_le_add (Nat.add_le_add_left hO 1) houter

theorem wires_append {n : ℕ} (X Y : Stars.Carrier n) :
    Stars.Carrier.wires (X ++ Y) = Stars.Carrier.wires X + Stars.Carrier.wires Y := by
  unfold Stars.Carrier.wires; rw [List.map_append, List.sum_append]

theorem wires_flatten_ofFn {n k : ℕ} (F : Fin k → Stars.Carrier n) :
    Stars.Carrier.wires (List.ofFn F).flatten = ∑ a, Stars.Carrier.wires (F a) := by
  unfold Stars.Carrier.wires
  rw [List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

theorem carrier_wires_le (w Cpar : ℝ)
    (hwA : ∀ X a, ((g.mode.gates (g.atom X a)).wires : ℝ) ≤ w)
    (hwP : ∀ X, ((g.mode.gates (g.parity X)).wires : ℝ) ≤ Cpar * (g.q : ℝ) ^ 2) (hCpar : 0 ≤ Cpar) (X : PcppVar g.pcpp) :
    ((g.carrier X).wires : ℝ) ≤ g.s * w + Cpar * (g.q : ℝ) ^ 2 := by
  unfold carrier
  rw [wires_append, wires_flatten_ofFn]
  push_cast
  have h1 : (∑ a : Fin g.s, ((g.mode.gates (g.atom X a)).wires : ℝ)) ≤ g.s * w := by
    calc _ ≤ ∑ _a : Fin g.s, w := Finset.sum_le_sum fun a _ => hwA X a
      _ = g.s * w := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ((Stars.Carrier.wires (if g.sysBit X then g.mode.gates (g.parity X) else [])) : ℝ) ≤
      Cpar * (g.q : ℝ) ^ 2 := by
    split
    · exact hwP X
    · simp [Stars.Carrier.wires]; positivity
  linarith

/-- The carrier's envelope: at most `(s+1)·K` gates, each within the gate envelope. -/
theorem carrier_envelope (K : ℕ) (hKA : ∀ X a, (g.mode.gates (g.atom X a)).length ≤ K)
    (hKP : ∀ X, (g.mode.gates (g.parity X)).length ≤ K) (hlen : (g.s + 1) * K ≤ (g.q + 1) ^ I.carrierDeg)
    (hbA : ∀ X a, ∀ gt ∈ g.mode.gates (g.atom X a), gt.encodingBits ≤ (g.q + 1) ^ I.carrierDeg)
    (hbP : ∀ X, ∀ gt ∈ g.mode.gates (g.parity X), gt.encodingBits ≤ (g.q + 1) ^ I.carrierDeg) (X : PcppVar g.pcpp) :
    (g.carrier X).WithinEnvelope I.carrierDeg := by
  refine ⟨?_, fun gt hgt => ?_⟩
  · unfold carrier
    rw [List.length_append, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    have h1 : (∑ a : Fin g.s, (Function.comp List.length (fun a => g.mode.gates (g.atom X a))) a) ≤ g.s * K := by
      calc _ ≤ ∑ _a : Fin g.s, K := Finset.sum_le_sum fun a _ => hKA X a
        _ = g.s * K := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h2 : (if g.sysBit X then g.mode.gates (g.parity X) else []).length ≤ K := by
      split
      · exact hKP X
      · simp
    calc _ ≤ g.s * K + K := Nat.add_le_add h1 h2
      _ = (g.s + 1) * K := by ring
      _ ≤ _ := hlen
  · unfold carrier at hgt
    rcases List.mem_append.mp hgt with h | h
    · obtain ⟨l, hl, hgl⟩ := List.mem_flatten.mp h
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hl
      exact hbA X a gt hgl
    · split at h
      · exact hbP X gt h
      · simp at h

end UnionGuess

/-! ## The guess of a sparse witness, and the accepting guess -/

section Build
variable (S : UnionSetup I) {N : ℕ} (z : BitInput N) (oracle : BooleanCircuit (S.pcp.nativeWidth N)) (m : Mode)
variable {J : PcppVar (S.pcppOf z oracle) → Type}

/-- The sign of a grid entry: the witness's sign on a drawn atom, zero on the zero atom. -/
def witnessSign (σ : PcppVar (S.pcppOf z oracle) → Fin (S.gridSize (S.request z oracle).arity) → ℤ)
    (atom : ∀ X, Fin (S.gridSize (S.request z oracle).arity) → Option (J X))
    (X : PcppVar (S.pcppOf z oracle)) (a : Fin (S.gridSize (S.request z oracle).arity)) : ℤ :=
  match atom X a with
  | some _ => σ X a
  | none => 0

/-- The circuit of a grid entry: the drawn atom, or the constant for the zero atom. -/
def witnessAtom (C : ∀ X, J X → m.Circuit (S.request z oracle).arity)
    (atom : ∀ X, Fin (S.gridSize (S.request z oracle).arity) → Option (J X))
    (X : PcppVar (S.pcppOf z oracle)) (a : Fin (S.gridSize (S.request z oracle).arity)) :
    m.Circuit (S.request z oracle).arity :=
  match atom X a with
  | some j => C X j
  | none => S.constAtom m _

def guessOfWitness (C : ∀ X, J X → m.Circuit (S.request z oracle).arity)
    (σ : PcppVar (S.pcppOf z oracle) → Fin (S.gridSize (S.request z oracle).arity) → ℤ)
    (atom : ∀ X, Fin (S.gridSize (S.request z oracle).arity) → Option (J X)) : UnionGuess S z :=
  ⟨oracle, m, witnessSign S z oracle σ atom, witnessAtom S z oracle m C atom⟩

theorem exists_unionAccepts (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params)
    (hsize : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N))
    (htaut : ∀ x, (S.request z oracle).circuit.eval x = true)
    [∀ X, Fintype (J X)] (C : ∀ X, J X → m.Circuit (S.request z oracle).arity) (α : ∀ X, J X → ℝ)
    (hT : ∀ X x, 0 ≤ ∑ j, α X j * bitR (m.eval (C X j) x) ∧ ∑ j, α X j * bitR (m.eval (C X j) x) ≤ 1)
    (happrox : uMean (fun p : Fin (2 ^ (S.pcppOf z oracle).clauseBits) × Fin 2 × BitInput (S.request z oracle).arity =>
      |∑ j, α (posVar (S.pcppOf z oracle) p.1 p.2.1) j *
          bitR (m.eval (C (posVar (S.pcppOf z oracle) p.1 p.2.1) j) p.2.2) -
        honestBit (S.pcppOf z oracle) (S.pcppOf z oracle).honestAuxiliary
          (posVar (S.pcppOf z oracle) p.1 p.2.1) p.2.2|) ≤ (cparams.ζ : ℝ))
    (hmass : ∀ X, ∑ j, |α X j| ≤ (S.gridMass (S.request z oracle).arity : ℝ))
    (hΛ : 1 ≤ (S.gridMass (S.request z oracle).arity : ℝ)) (hs : 1 ≤ S.gridSize (S.request z oracle).arity)
    (hsδ : 19 * (S.gridMass (S.request z oracle).arity : ℝ) ^ 4 ≤
      (S.gridSize (S.request z oracle).arity : ℝ) ^ 2 * (cparams.δ : ℝ) ^ 4)
    (hStar : I.StarAt (S.request z oracle).arity) (hFit : B.FitsAt (S.request z oracle).arity)
    (hname : 2 ≤ I.nameCount)
    (hdescC : ∀ X j, m.descriptionBits (C X j) ≤ ((S.request z oracle).arity + 1) ^ I.descDeg)
    (hdescK : m.descriptionBits (S.constAtom m (S.request z oracle).arity) ≤
      ((S.request z oracle).arity + 1) ^ I.descDeg)
    (hdescP : ∀ Sp, m.descriptionBits (S.parityAtom m (S.request z oracle).arity Sp) ≤
      ((S.request z oracle).arity + 1) ^ I.descDeg)
    (K : ℕ) (hKC : ∀ X j, (m.gates (C X j)).length ≤ K)
    (hKP : ∀ Sp, (m.gates (S.parityAtom m (S.request z oracle).arity Sp)).length ≤ K)
    (hlen : (S.gridSize (S.request z oracle).arity + 1) * K ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg)
    (hbC : ∀ X j, ∀ gt ∈ m.gates (C X j), gt.encodingBits ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg)
    (hbP : ∀ Sp, ∀ gt ∈ m.gates (S.parityAtom m (S.request z oracle).arity Sp),
      gt.encodingBits ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg)
    (w Cpar : ℝ) (hw0 : 0 ≤ w) (hCpar : 0 ≤ Cpar) (hwC : ∀ X j, ((m.gates (C X j)).wires : ℝ) ≤ w)
    (hwP : ∀ Sp, ((m.gates (S.parityAtom m (S.request z oracle).arity Sp)).wires : ℝ) ≤
      Cpar * ((S.request z oracle).arity : ℝ) ^ 2)
    (hcap : (I.starParams (S.request z oracle).arity hStar).popRate *
        ((S.gridSize (S.request z oracle).arity : ℝ) * w + Cpar * ((S.request z oracle).arity : ℝ) ^ 2) ≤
      (cparams.β : ℝ) * (B.capOf m (S.request z oracle).arity : ℝ))
    (spectrum : ExpanderSpectrumContract)
    (hξ : 1 / (2 : ℝ) ^ (I.filterParams m (S.request z oracle).arity).errExp ≤ (cparams.ξ : ℝ))
    (hD : (1 + (S.gridMass (S.request z oracle).arity : ℝ)) ^ 4 *
        ((S.request z oracle).arity : ℝ) ^ (-(I.D : ℝ)) ≤ (S.params.eps0 : ℝ))
    (Ko Ks Kc : ℕ) (hO : (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤ Ko)
    (hKs : ∀ σ ∈ ({-1, 0, 1} : Finset ℤ), (intWord σ).length ≤ Ks)
    (hcodeC : ∀ X j, (natWord (m.code (C X j))).length ≤ Kc)
    (hcodeK : (natWord (m.code (S.constAtom m (S.request z oracle).arity))).length ≤ Kc)
    (hbudget : 1 + Ko + ((S.pcppOf z oracle).systematicBits + (S.pcppOf z oracle).auxiliaryBits) *
      (S.gridSize (S.request z oracle).arity * (Ks + Kc)) ≤ N / 16) :
    ∃ g : UnionGuess S z, UnionAccepts S P z g := by
  have hδ0 : (0 : ℝ) ≤ cparams.δ := by exact_mod_cast cparams.δ_nonneg
  -- the sparse witness of every named variable, at one `s` and grid
  obtain ⟨σ, atom, hσ, -, hL4⟩ := sparseGuess_exists (fun X j x => m.eval (C X j) x) α
    (S.gridMass (S.request z oracle).arity : ℝ) (S.gridSize (S.request z oracle).arity) hs hΛ hmass
    (cparams.δ : ℝ) hsδ
  set g := guessOfWitness S z oracle m C σ atom with hg
  have hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ) := by
    intro X a
    show witnessSign S z oracle σ atom X a ∈ _
    unfold witnessSign
    split
    · exact hσ X a
    · simp
  -- the completeness witness: the guess's grid sums are the sparse witnesses
  have wit : CompletenessWitness g.pcpp g.pcpp.honestAuxiliary (fun X x => ∑ j, α X j * bitR (m.eval (C X j) x))
      (g.forms hsign).guess cparams.ζ cparams.δ := by
    refine ⟨hT, happrox, fun X => ?_, by exact_mod_cast cparams.ζ_nonneg, hδ0⟩
    refine le_of_eq_of_le ?_ (hL4 X)
    refine congrArg uMean (funext fun x => ?_)
    congr 2
    rw [g.forms_guess hsign X x]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    show (witnessSign S z oracle σ atom X a : ℝ) * bitR (m.eval (witnessAtom S z oracle m C atom X a) x) = _
    unfold witnessSign witnessAtom
    cases atom X a
    · simp
    · rfl
  -- the calls, the missing mass, the word
  have hdesc : ∀ a : g.AtomIx, g.mode.descriptionBits (g.circ a) ≤ (g.q + 1) ^ I.descDeg := by
    rintro (u | ⟨X, b⟩ | X)
    · exact hdescK
    · show m.descriptionBits (witnessAtom S z oracle m C atom X b) ≤ _
      unfold witnessAtom
      split
      · exact hdescC X _
      · exact hdescK
    · exact hdescP _
  have hKA : ∀ X a, (g.mode.gates (g.atom X a)).length ≤ K := by
    intro X a
    show (m.gates (witnessAtom S z oracle m C atom X a)).length ≤ K
    unfold witnessAtom
    split
    · exact hKC X _
    · rw [S.constAtom_gates]; exact Nat.zero_le _
  have hbA : ∀ X a, ∀ gt ∈ g.mode.gates (g.atom X a), gt.encodingBits ≤ (g.q + 1) ^ I.carrierDeg := by
    intro X a gt hgt
    change gt ∈ m.gates (witnessAtom S z oracle m C atom X a) at hgt
    unfold witnessAtom at hgt
    split at hgt
    · exact hbC X _ gt hgt
    · rw [S.constAtom_gates] at hgt; cases hgt
  have henv : ∀ X, (g.carrier X).WithinEnvelope I.carrierDeg :=
    g.carrier_envelope K hKA (fun X => hKP _) hlen hbA (fun X => hbP _)
  have hwA : ∀ X a, ((g.mode.gates (g.atom X a)).wires : ℝ) ≤ w := by
    intro X a
    show ((m.gates (witnessAtom S z oracle m C atom X a)).wires : ℝ) ≤ w
    unfold witnessAtom
    split
    · exact hwC X _
    · rw [S.constAtom_gates]
      show ((0 : ℕ) : ℝ) ≤ w
      simpa using hw0
  obtain ⟨hVcall, hQcall, hμcall⟩ := g.calls_admissible hStar hFit hname henv hdesc
  have hmissing := g.missing_at_guess hStar spectrum cparams.β cparams.ξ w Cpar (by exact_mod_cast cparams.ξ_nonneg)
    hξ henv (g.carrier_wires_le w Cpar hwA (fun X => hwP _) hCpar) hcap
  have hword : g.word.length ≤ N / 16 := by
    refine (g.word_length_le Ko Ks Kc hO (fun X a => hKs _ (hsign X a)) fun X a => ?_).trans hbudget
    show (natWord (m.code (witnessAtom S z oracle m C atom X a))).length ≤ Kc
    unfold witnessAtom
    split
    · exact hcodeC X _
    · exact hcodeK
  exact ⟨g, g.unionAccepts_of_parts P cparams hsize hsign hword hVcall hQcall hμcall htaut _ wit hmissing hD⟩

end Build

end Union

end NearCubicWires.WireExponent3_5.Transfer

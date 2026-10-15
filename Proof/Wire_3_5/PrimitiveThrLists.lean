import Proof.Wire_3_5.PrimitiveThr
import Proof.Wire_3_5.FilterSoftHash

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Rows

/-! ## Occurrences are the charged gates -/

/-- Theorem 2.5's retained occurrences of a `THR∘THR` circuit are its charged gates, up to order. -/
theorem thrOccurrences_perm {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) :
    ((thresholdCircuitOccurrences C).map (·.gate)).Perm (thrGates C) := by
  unfold thresholdCircuitOccurrences thrGates
  have h1 : (List.ofFn fun k : Fin C.top.support.card => C.bottom (retainedTopIndex C k)).map (·.gate) =
      (List.ofFn (retainedTopIndex C)).map (fun i => (C.bottom i).gate) := by
    rw [List.map_ofFn, List.map_ofFn]; rfl
  rw [h1]
  refine List.Perm.map _ ?_
  rw [List.perm_ext_iff_of_nodup]
  · intro i
    rw [List.mem_ofFn', List.mem_filter]
    simp only [List.mem_finRange, true_and, decide_eq_true_eq]
    unfold retainedTopIndex
    rw [Finset.range_orderEmbOfFin]
    rfl
  · exact List.nodup_ofFn.mpr (retainedTopIndex C).injective
  · exact (List.nodup_finRange _).filter _

section Lists
variable (P : StarParams) (σ : P.Translation) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Carrier P.n)) (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)

theorem sum_occ_residual_eq (c u v : BitInput P.n) :
    ∑ i : Fin (thrOccs P Cs).length, ((occPlus (thrOccs P Cs) c u v i).toNat + (occMinus (thrOccs P Cs) c u v i).toNat) =
      Carrier.population ((thrOccs P Cs).map (·.gate)) c u v := by
  have hL : (thrOccs P Cs).map (·.gate) = List.ofFn (fun i => ((thrOccs P Cs).get i).gate) := by
    conv_lhs => rw [← List.ofFn_get (thrOccs P Cs)]
    rw [List.map_ofFn]; rfl
  rw [hL]
  unfold Carrier.population
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- The occurrences' residual population is at most `a·Σ_XR_X` when the circuits' gates lie in the named carriers. -/
theorem occ_population_le (hgates : GatesIn (fun i => thrGates (Cs i)) carriers) (c u v : BitInput P.n) :
    Carrier.population ((thrOccs P Cs).map (·.gate)) c u v ≤
      a * (carriers.map fun X => Carrier.population X c u v).sum := by
  have hflat : (thrOccs P Cs).map (·.gate) =
      ((List.ofFn Cs).map fun C => (thresholdCircuitOccurrences C).map (·.gate)).flatten := by
    simp [thrOccs, thresholdFourfoldOccurrences, List.flatMap_def]
    rfl
  rw [hflat, Carrier.population_flatten, List.map_map, List.map_ofFn, List.sum_ofFn]
  calc ∑ i : Fin a, (Function.comp (fun X => Carrier.population X c u v)
        (fun C => (thresholdCircuitOccurrences C).map (·.gate))) (Cs i)
      ≤ ∑ _i : Fin a, (carriers.map fun X => Carrier.population X c u v).sum := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Function.comp_apply]
        rw [← Carrier.population_flatten]
        exact Carrier.population_le_of_subperm ((thrOccurrences_perm (Cs i)).subperm.trans (hgates i)) c u v
    _ = a * (carriers.map fun X => Carrier.population X c u v).sum := by simp

/-- Every digit population is at most `a·Σ_XR_X` (binary digits: each residual has at most one copy). -/
theorem digitPop_count_le (hgates : GatesIn (fun i => thrGates (Cs i)) carriers) (g : ThrEq P Cs algorithm)
    (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (d : Fin (thrDigits P Cs algorithm den)) (sgn : Bool)
    (c : BitInput P.n) (u v : P.Errors) :
    (thrDigitPop P Cs algorithm den g pr d sgn c u v).count true ≤
      a * (carriers.map fun X => Carrier.population X c (P.errorVector P.leftBlock u)
        (P.errorVector P.rightBlock v)).sum := by
  unfold thrDigitPop
  rw [count_digitPop]
  refine le_trans ?_ ((sum_occ_residual_eq P Cs c _ _).le.trans (occ_population_le P Cs carriers hgates c _ _))
  refine Finset.sum_le_sum fun i _ => ?_
  have hv : digitOf (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val 2 (thrDigits P Cs algorithm den) i d ≤ 1 := by
    unfold digitOf; have := Nat.mod_lt (redCoeff (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val i / 2 ^ (d : ℕ))
      (by norm_num : 0 < 2); omega
  cases sgn
  · simp only [Bool.false_eq_true, if_false]
    cases occMinus (thrOccs P Cs) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) i
    · simp
    · simp only [Bool.toNat_true, mul_one]; omega
  · simp only [if_true]
    cases occPlus (thrOccs P Cs) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) i
    · simp
    · simp only [Bool.toNat_true, mul_one]; omega

/-! ## The fixed hash of `filt:soft` -/

/-- The named carriers' residual vector read by the auxiliary filter (weight `Σ_XR_X`). -/
def thrZres (c : BitInput P.n) (u v : P.Errors) : List Bool :=
  carriers.flatMap fun X => Carrier.residualBits X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)

theorem count_thrZres (c : BitInput P.n) (u v : P.Errors) :
    (thrZres P carriers c u v).count true =
      (carriers.map fun X => Carrier.population X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)).sum := by
  unfold thrZres
  rw [List.count_flatMap]
  congr 1
  exact List.map_congr_left fun X _ => Carrier.count_residualBits X _ _ _

theorem length_thrZres (c : BitInput P.n) (u v : P.Errors) :
    (thrZres P carriers c u v).length = 2 * (carriers.map List.length).sum := by
  unfold thrZres
  rw [List.length_flatMap]
  induction carriers with
  | nil => simp
  | cons X rest ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, length_residualBits, ih]; ring

def thrAux (e : ℕ) : GapParams := ⟨2 * (carriers.map List.length).sum, (carriers.length + 1) * (4096 * FP.cap), e⟩

/-- The majorant parameters of the fixed hash (`filt:majorant`): `M` occurrences per population, `A` populations,
`B_* = a·4096·cap_aux`, `t`, `J`. -/
def thrMajorant (e t J : ℕ) : MajorantParams :=
  ⟨(thrOccs P Cs).length,
    Fintype.card (ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den) × Fin (thrDigits P Cs algorithm den) ×
      Bool),
    a * (4096 * (thrAux P carriers FP e).cap), t, J⟩

noncomputable def thrHash (e t J : ℕ) : (thrMajorant P Cs carriers FP algorithm den e t J).Seed :=
  (thrMajorant P Cs carriers FP algorithm den e t J).seedCode
    (greedy (2 * (thrMajorant P Cs carriers FP algorithm den e t J).t * (thrMajorant P Cs carriers FP algorithm den e t J).ell0)
      fun s => softObjective
        (fun e' (pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) =>
          gapFilter (thrAux P carriers FP e) e' (thrZres P carriers pt.1.1 pt.2.1 pt.2.2))
        (fun h (pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) =>
          (thrMajorant P Cs carriers FP algorithm den e t J).H (thrPops P Cs algorithm den pt.1.1 pt.2.1 pt.2.2) h)
        ((thrMajorant P Cs carriers FP algorithm den e t J).seedCode s))

/-- The digit lists' reports under the fixed hash (the repaired lists of `list:repair`). -/
noncomputable def thrReport (e t J : ℕ) : List Bool → ℕ :=
  ((thrMajorant P Cs carriers FP algorithm den e t J).data (thrHash P σ Cs carriers FP algorithm den e t J)).listReport

/-- `filt:soft`'s failure bound at these parameters. -/
noncomputable def thrListBound (e t J : ℕ) : ℝ :=
  ((thrMajorant P Cs carriers FP algorithm den e t J).A *
      ((thrMajorant P Cs carriers FP algorithm den e t J).Bstar * (1 / 2 ^ J) + J * (1 / 64) ^ t) +
    (1 / 2 ^ e) * ((thrMajorant P Cs carriers FP algorithm den e t J).A *
      ((thrMajorant P Cs carriers FP algorithm den e t J).M +
        J * ((thrMajorant P Cs carriers FP algorithm den e t J).M : ℝ) ^ (2 * t)))) / (1 - 1 / 2 ^ e)

theorem card_active_le (MP : MajorantParams) (Z : List Bool) : (MP.active Z).card ≤ Z.count true := by
  rw [← card_activeSet]
  refine Finset.card_le_card_of_injOn (fun i => (i : ℕ)) (fun i hi => ?_) (fun i _ j _ h => Fin.ext h)
  simp only [MajorantParams.active, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
  simp only [activeSet, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
  refine ⟨?_, hi⟩
  by_contra hlt
  rw [List.getD_eq_default _ _ (by omega)] at hi
  exact Bool.false_ne_true hi

theorem thr_list_failure (spectrum : ExpanderSpectrumContract) (hgates : GatesIn (fun i => thrGates (Cs i)) carriers)
    (hcap1 : 1 ≤ FP.cap) (e t J : ℕ) (ht : 1 ≤ t) (he : 1 ≤ e) :
    uMean (fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) =>
      bitR (thrFail P Cs algorithm den (thrReport P σ Cs carriers FP algorithm den e t J) pt.1.1 pt.2.1 pt.2.2 &&
        !symOver P carriers FP pt.1.1 pt.2.1 pt.2.2)) ≤ thrListBound P Cs carriers FP algorithm den e t J := by
  haveI : Nonempty {c // P.IsCenter σ c} := Fintype.card_pos_iff.mp (by rw [P.card_centers σ]; positivity)
  have hauxU : 1 ≤ (thrAux P carriers FP e).cap := by
    show 1 ≤ (carriers.length + 1) * (4096 * FP.cap)
    have : 1 ≤ carriers.length + 1 := by omega
    nlinarith
  have hzlen : ∀ pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors),
      (thrZres P carriers pt.1.1 pt.2.1 pt.2.2).length ≤ (thrAux P carriers FP e).len := fun pt => (length_thrZres P carriers _ _ _).le
  have hA : ∀ pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors),
      (thrPops P Cs algorithm den pt.1.1 pt.2.1 pt.2.2).length ≤ (thrMajorant P Cs carriers FP algorithm den e t J).A := by
    intro pt
    simp [thrPops, thrMajorant]
  have hmem : ∀ (c : BitInput P.n) (u v : P.Errors) (Z : List Bool), Z ∈ thrPops P Cs algorithm den c u v →
      ∃ g pr d sgn, Z = thrDigitPop P Cs algorithm den g pr d sgn c u v := by
    intro c u v Z hZ
    simp only [thrPops, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hZ
    obtain ⟨⟨g, pr, d, sgn⟩, hk⟩ := hZ
    exact ⟨g, pr, d, sgn, hk.symm⟩
  have hM : ∀ pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors),
      ∀ Z ∈ thrPops P Cs algorithm den pt.1.1 pt.2.1 pt.2.2, Z.length ≤ (thrMajorant P Cs carriers FP algorithm den e t J).M := by
    intro pt Z hZ
    obtain ⟨g, pr, d, sgn, rfl⟩ := hmem _ _ _ Z hZ
    have := length_digitPop_le (thrOccs P Cs)
      (fun i => digitOf (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val 2 (thrDigits P Cs algorithm den) i d)
      (if sgn then occPlus (thrOccs P Cs) pt.1.1 (P.errorVector P.leftBlock pt.2.1) (P.errorVector P.rightBlock pt.2.2)
        else occMinus (thrOccs P Cs) pt.1.1 (P.errorVector P.leftBlock pt.2.1) (P.errorVector P.rightBlock pt.2.2)) 1
      (fun i => by
        unfold digitOf
        have := Nat.mod_lt (redCoeff (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val i / 2 ^ (d : ℕ))
          (by norm_num : 0 < 2)
        omega)
    simpa [thrMajorant, thrDigitPop] using this
  have hlow : ∀ pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors),
      (thrZres P carriers pt.1.1 pt.2.1 pt.2.2).count true ≤ 4096 * (thrAux P carriers FP e).cap →
        ∀ Z ∈ thrPops P Cs algorithm den pt.1.1 pt.2.1 pt.2.2, ((thrMajorant P Cs carriers FP algorithm den e t J).active Z).card ≤ (thrMajorant P Cs carriers FP algorithm den e t J).Bstar := by
    intro pt hw Z hZ
    obtain ⟨g, pr, d, sgn, rfl⟩ := hmem _ _ _ Z hZ
    refine (card_active_le (thrMajorant P Cs carriers FP algorithm den e t J) _).trans ?_
    have h1 := digitPop_count_le P Cs carriers algorithm den hgates g pr d sgn pt.1.1 pt.2.1 pt.2.2
    rw [← count_thrZres] at h1
    show _ ≤ a * (4096 * (thrAux P carriers FP e).cap)
    calc _ ≤ a * (thrZres P carriers pt.1.1 pt.2.1 pt.2.2).count true := h1
      _ ≤ a * (4096 * (thrAux P carriers FP e).cap) := Nat.mul_le_mul_left a hw
  have hsoft := (thrMajorant P Cs carriers FP algorithm den e t J).soft_hash spectrum (thrAux P carriers FP e) hauxU he
    (fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) => thrZres P carriers pt.1.1 pt.2.1 pt.2.2) hzlen
    (fun pt => thrPops P Cs algorithm den pt.1.1 pt.2.1 pt.2.2) ht hA hM hlow
  refine le_trans (uMean_mono fun pt => ?_) hsoft
  obtain ⟨⟨c, hc⟩, u, v⟩ := pt
  cases hfail : thrFail P Cs algorithm den (thrReport P σ Cs carriers FP algorithm den e t J) c u v
  · simp only [Bool.false_and, bitR, Bool.false_eq_true, if_false]
    split_ifs <;> norm_num
  cases hov : symOver P carriers FP c u v
  · -- below the enlarged cap: the auxiliary filter's cap covers the named populations
    have hpop : ∀ X ∈ carriers, Carrier.population X c (P.errorVector P.leftBlock u)
        (P.errorVector P.rightBlock v) ≤ 4096 * FP.cap := by
      intro X hX
      simp only [symOver, List.any_eq_false, decide_eq_true_eq, not_le] at hov
      exact (hov X hX).le
    have hw : (thrZres P carriers c u v).count true ≤ (thrAux P carriers FP e).cap := by
      rw [count_thrZres]
      refine (list_sum_map_le carriers _ _ hpop).trans ?_
      show carriers.length * (4096 * FP.cap) ≤ (carriers.length + 1) * (4096 * FP.cap)
      exact Nat.mul_le_mul_right _ (Nat.le_succ _)
    have hex : ∃ Z ∈ thrPops P Cs algorithm den c u v,
        ((thrMajorant P Cs carriers FP algorithm den e t J).data (thrHash P σ Cs carriers FP algorithm den e t J)).listReport Z ≠ Z.count true := by
      unfold thrFail at hfail
      exact of_decide_eq_true hfail
    simp only [Bool.not_false, Bool.and_true, bitR, if_true]
    rw [if_pos]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hw, hex⟩
  · simp only [Bool.not_true, Bool.and_false, bitR, Bool.false_eq_true, if_false]
    split_ifs <;> norm_num

end Lists

end NearCubicWires.WireExponent3_5.Primitive

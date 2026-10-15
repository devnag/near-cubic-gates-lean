import Proof.Wire_3_5.PrimitiveThrRow
import Proof.Wire_3_5.PrimitiveSym
import Proof.Supplier.SupplierEstimator
import Proof.Supplier.RowThresholdSelections

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Rows
open scoped Matrix.Norms.L2Operator

instance instNeZeroPrimeIndex {c : ℕ} (pr : PrimeIndex c) : NeZero pr.val :=
  ⟨(Nat.Prime.pos ((mem_primesUpTo.mp pr.2).1)).ne'⟩

theorem prime_error_at {G Pr Ω : Type} [Fintype G] [Fintype Pr] (cert : PrimeSurrogateCertificate G Pr Ω) (x : Ω)
    (C : Bool) (hsum : bitR C = ∑ g, bitR (cert.exact g x)) :
    bitR C ≤ ∑ g, uMean (fun p => bitR (cert.modular g p x)) ∧
      ∑ g, uMean (fun p => bitR (cert.modular g p x)) ≤ bitR C + Fintype.card G * cert.error := by
  have hPr : (0 : ℝ) < Fintype.card Pr := Nat.cast_pos.mpr cert.cardPositive
  have hper : ∀ g, bitR (cert.exact g x) ≤ uMean (fun p => bitR (cert.modular g p x)) ∧
      uMean (fun p => bitR (cert.modular g p x)) ≤ bitR (cert.exact g x) + cert.error := by
    intro g
    cases hex : cert.exact g x
    · have hs := cert.sound g x (by simp [hex])
      refine ⟨?_, ?_⟩
      · simp only [bitR, Bool.false_eq_true, if_false]
        exact div_nonneg (Finset.sum_nonneg fun p _ => bitR_nonneg _) hPr.le
      · simp only [bitR, Bool.false_eq_true, if_false, zero_add]
        exact hs
    · have hall : ∀ p, cert.modular g p x = true := cert.complete g x hex
      have hone : uMean (fun p => bitR (cert.modular g p x)) = 1 := by
        unfold uMean
        simp only [hall, bitR, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact div_self hPr.ne'
      rw [hone]
      exact ⟨le_of_eq (by simp [bitR]), by simp [bitR, cert.errorNonnegative]⟩
  rw [hsum]
  refine ⟨Finset.sum_le_sum fun g _ => (hper g).1, ?_⟩
  calc ∑ g, uMean (fun p => bitR (cert.modular g p x)) ≤ ∑ g, (bitR (cert.exact g x) + cert.error) :=
        Finset.sum_le_sum fun g _ => (hper g).2
    _ = ∑ g, bitR (cert.exact g x) + Fintype.card G * cert.error := by
        rw [Finset.sum_add_distrib]; simp

section Thr
variable (P : StarParams) (σ : P.Translation) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Carrier P.n)) (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm)

/-- The Theorem 2.5 request of the tuple. -/
abbrev thrRequest : FourfoldRequest NormalizedThresholdThresholdCircuit := ⟨P.n, List.ofFn Cs⟩

/-- The flattened bottom occurrences of the tuple (one shared occurrence universe for every row). -/
abbrev thrOccs : List (SupportedNormalizedGate P.n) := thresholdFourfoldOccurrences (thrRequest P Cs)

abbrev ThrEq : Type := RepairOrdinary.ThresholdRows.Selection algorithm (thrRequest P Cs)

/-- The equation of selection `g`. -/
def thrRealize (g : ThrEq P Cs algorithm) : LabelledEquation (Fin (thrOccs P Cs).length) :=
  RepairOrdinary.ThresholdRows.equation algorithm (thrRequest P Cs) g

theorem thr_conj_sum (x : BitInput P.n) :
    bitR (decide (∀ i, (Cs i).eval x = true)) =
      ∑ g : ThrEq P Cs algorithm, bitR (decide ((thrRealize P Cs algorithm g).Holds (occVals (thrOccs P Cs) x))) := by
  have h := RepairOrdinary.ThresholdRows.selection_sum algorithm (thrRequest P Cs) x
  have hcast := congrArg (fun k : ℕ => (k : ℝ)) h
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcast
  have hb : ∀ b : Bool, ((b.toNat : ℕ) : ℝ) = bitR b := fun b => by cases b <;> simp [bitR]
  simp only [hb] at hcast
  have hconj : conjunctionBit NormalizedThresholdThresholdCircuit.eval (thrRequest P Cs).circuits x =
      decide (∀ i, (Cs i).eval x = true) := by
    simp only [conjunctionBit, thrRequest]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_ofFn, decide_eq_true_eq]
    constructor
    · intro hall i; exact hall _ ⟨i, rfl⟩
    · rintro hall _ ⟨i, rfl⟩; exact hall i
  rw [hconj] at hcast
  rw [← hcast]
  apply Finset.sum_congr rfl
  intro g _
  simp only [bitR, decide_eq_true_eq]
  rfl

variable (theta : PrimeThetaBoundContract) (den : ℕ)

/-- The prime cutoff of the tuned surrogate. -/
def thrCutoff : ℕ :=
  canonicalPrimeCutoff (familyMagnitudeExponent (thrRealize P Cs algorithm)) den

noncomputable def thrCert : PrimeSurrogateCertificate (ThrEq P Cs algorithm) (PrimeIndex (thrCutoff P Cs algorithm den))
    (Fin (thrOccs P Cs).length → Bool) :=
  tunedFiniteFamilyPrimeSurrogateCertificate theta (thrRealize P Cs algorithm) den

def thrDigits : ℕ := Nat.clog 2 (thrCutoff P Cs algorithm den)

theorem prime_le_two_pow (pr : PrimeIndex (thrCutoff P Cs algorithm den)) :
    pr.val ≤ 2 ^ thrDigits P Cs algorithm den :=
  ((mem_primesUpTo.mp pr.2).2).trans (Nat.le_pow_clog (by norm_num) _)

def thrDigitPop (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (d : Fin (thrDigits P Cs algorithm den)) (sgn : Bool) (c : BitInput P.n) (u v : P.Errors) : List Bool :=
  digitPop (thrOccs P Cs) (fun i => digitOf (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val 2
      (thrDigits P Cs algorithm den) i d)
    (if sgn then occPlus (thrOccs P Cs) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)
      else occMinus (thrOccs P Cs) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v))

noncomputable def thrPops (c : BitInput P.n) (u v : P.Errors) : List (List Bool) :=
  (Finset.univ : Finset (ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den) ×
      Fin (thrDigits P Cs algorithm den) × Bool)).toList.map
    fun k => thrDigitPop P Cs algorithm den k.1 k.2.1 k.2.2.1 k.2.2.2 c u v

theorem mem_thrPops (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (d : Fin (thrDigits P Cs algorithm den)) (sgn : Bool) (c : BitInput P.n) (u v : P.Errors) :
    thrDigitPop P Cs algorithm den g pr d sgn c u v ∈ thrPops P Cs algorithm den c u v := by
  unfold thrPops
  exact List.mem_map.mpr ⟨(g, pr, d, sgn), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

variable (report : List Bool → ℕ)

def thrResHat (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (c : BitInput P.n)
    (u v : P.Errors) : ZMod pr.val :=
  tupleResidue pr.val 2 (fun d => report (thrDigitPop P Cs algorithm den g pr d true c u v))
    (fun d => report (thrDigitPop P Cs algorithm den g pr d false c u v))

def thrRhat (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (c : BitInput P.n)
    (u v : P.Errors) : Bool :=
  thrReported (thrLeft (thrOccs P Cs) (thrRealize P Cs algorithm g) c (P.errorVector P.leftBlock u))
    (thrRight (thrOccs P Cs) (thrRealize P Cs algorithm g) c (P.errorVector P.rightBlock v))
    (thrResHat P Cs algorithm den report g pr c u v)

/-- Some digit list reports a wrong count at the point. -/
noncomputable def thrFail (c : BitInput P.n) (u v : P.Errors) : Bool :=
  decide (∃ Z ∈ thrPops P Cs algorithm den c u v, report Z ≠ Z.count true)

theorem thrRhat_eq_of_correct (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (c : BitInput P.n) (u v : P.Errors) (hok : thrFail P Cs algorithm den report c u v = false) :
    thrRhat P Cs algorithm den report g pr c u v =
      (thrCert P Cs algorithm theta den).modular g pr (occVals (thrOccs P Cs) (P.point c u v)) := by
  have hcorr : ∀ Z ∈ thrPops P Cs algorithm den c u v, report Z = Z.count true := by
    intro Z hZ
    by_contra hne
    have : thrFail P Cs algorithm den report c u v = true := by
      unfold thrFail; exact decide_eq_true ⟨Z, hZ, hne⟩
    rw [hok] at this; exact Bool.false_ne_true this
  have hmod := thr_modular_point (thrOccs P Cs) (thrRealize P Cs algorithm g) pr 2 (thrDigits P Cs algorithm den)
    le_rfl (prime_le_two_pow P Cs algorithm den pr) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)
    (errorVector_disjoint P u v)
  show _ = modularEquationHolds (thrRealize P Cs algorithm g) pr _
  unfold StarParams.point
  rw [hmod]
  unfold thrRhat thrResHat
  congr 2
  · funext d
    exact hcorr _ (mem_thrPops P Cs algorithm den g pr d true c u v)
  · funext d
    exact hcorr _ (mem_thrPops P Cs algorithm den g pr d false c u v)

/-- The masked truth `E_{(c,u,v)}E_e[M·ΠC_i]` over cells and filter seeds. -/
noncomputable def thrTruthMean : ℝ :=
  uMean fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) => uMean fun e : GapSeed FP =>
    bitR (symMask P σ carriers FP e (P.point pt.1.1 pt.2.1 pt.2.2)) *
      bitR (decide (∀ i, (Cs i).eval (P.point pt.1.1 pt.2.1 pt.2.2) = true))

noncomputable def thrReportedMean : ℝ :=
  ∑ g : ThrEq P Cs algorithm, uMean fun pr : PrimeIndex (thrCutoff P Cs algorithm den) =>
    uMean fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) => uMean fun e : GapSeed FP =>
      bitR (symMask P σ carriers FP e (P.point pt.1.1 pt.2.1 pt.2.2)) *
        bitR (thrRhat P Cs algorithm den report g pr pt.1.1 pt.2.1 pt.2.2)

theorem thr_first_error (spectrum : ExpanderSpectrumContract) (hFlen : ∀ X ∈ carriers, 2 * X.length ≤ FP.len)
    (hcap1 : 1 ≤ FP.cap) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : uMean (fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) =>
      bitR (thrFail P Cs algorithm den report pt.1.1 pt.2.1 pt.2.2 && !symOver P carriers FP pt.1.1 pt.2.1 pt.2.2)) ≤ δ) :
    |thrTruthMean P σ Cs carriers FP - thrReportedMean P σ Cs carriers FP algorithm den report| ≤
      Fintype.card (ThrEq P Cs algorithm) * (thrCert P Cs algorithm theta den).error +
        Fintype.card (ThrEq P Cs algorithm) * (δ + 1 / 2 ^ FP.errExp) := by
  set Ω := ({c // P.IsCenter σ c} × (P.Errors × P.Errors)) × GapSeed FP
  set cert := thrCert P Cs algorithm theta den
  set M : Ω → Bool := fun ω => symMask P σ carriers FP ω.2 (P.point ω.1.1.1 ω.1.2.1 ω.1.2.2)
  set C : Ω → Bool := fun ω => decide (∀ i, (Cs i).eval (P.point ω.1.1.1 ω.1.2.1 ω.1.2.2) = true)
  set R : ThrEq P Cs algorithm → PrimeIndex (thrCutoff P Cs algorithm den) → Ω → Bool := fun g pr ω =>
    cert.modular g pr (occVals (thrOccs P Cs) (P.point ω.1.1.1 ω.1.2.1 ω.1.2.2))
  set Rh : ThrEq P Cs algorithm → PrimeIndex (thrCutoff P Cs algorithm den) → Ω → Bool := fun g pr ω =>
    thrRhat P Cs algorithm den report g pr ω.1.1.1 ω.1.2.1 ω.1.2.2
  have hξ0 : (0 : ℝ) ≤ 1 / 2 ^ FP.errExp := by positivity
  have hprime : ∀ ω, bitR (C ω) ≤ ∑ g, uMean (fun p => bitR (R g p ω)) ∧
      ∑ g, uMean (fun p => bitR (R g p ω)) ≤ bitR (C ω) + Fintype.card (ThrEq P Cs algorithm) * cert.error :=
    fun ω => prime_error_at cert _ (C ω) (thr_conj_sum P Cs algorithm _)
  have hrow : ∀ g p, uMean (fun ω => bitR (M ω) * |bitR (Rh g p ω) - bitR (R g p ω)|) ≤ δ + 1 / 2 ^ FP.errExp := by
    intro g p
    refine maskedRowError_holds M (Rh g p) (R g p)
      (fun ω => thrFail P Cs algorithm den report ω.1.1.1 ω.1.2.1 ω.1.2.2)
      (fun ω => symOver P carriers FP ω.1.1.1 ω.1.2.1 ω.1.2.2) δ (1 / 2 ^ FP.errExp) ?_ ?_ ?_
    · intro ω _ hfail
      exact thrRhat_eq_of_correct P Cs algorithm theta den report g p _ _ _ hfail
    · rw [uMean_prod_eq]
      simp only [uMean_const]
      exact hδ
    · rw [uMean_prod_eq]
      refine uMean_le_const _ _ hξ0 fun pt => ?_
      obtain ⟨⟨c, hc⟩, u, v⟩ := pt
      cases hov : symOver P carriers FP c u v
      · simp only [M, hov, Bool.and_false, uMean_const, bitR, Bool.false_eq_true, if_false]
        exact hξ0
      · simp only [symOver, List.any_eq_true, decide_eq_true_eq] at hov
        obtain ⟨X, hX, hXpop⟩ := hov
        have hov' : symOver P carriers FP c u v = true := by
          simp only [symOver, List.any_eq_true, decide_eq_true_eq]; exact ⟨X, hX, hXpop⟩
        simp only [M, hov', Bool.and_true]
        have hsound := (gapFilter_guarantee spectrum FP hcap1).sound
          (Carrier.residualBits X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v))
          (by rw [length_residualBits]; exact hFlen X hX) (by rw [Carrier.count_residualBits]; exact hXpop)
        refine le_trans (booleanMean_mono _ _ fun e he => ?_) hsound
        rw [symMask_point P σ carriers FP hc, List.all_eq_true] at he
        exact he X hX
  have hfull := thr_full_error M C R Rh (Fintype.card (ThrEq P Cs algorithm) * cert.error) (δ + 1 / 2 ^ FP.errExp)
    (mul_nonneg (Nat.cast_nonneg _) cert.errorNonnegative) (by positivity) hprime hrow
  have hT : Shared.maskedMean M (fun ω => bitR (C ω)) = thrTruthMean P σ Cs carriers FP := by
    unfold Shared.maskedMean thrTruthMean
    rw [uMean_prod_eq]
  have hR : ∑ g, uMean (fun p => Shared.maskedMean M (fun ω => bitR (Rh g p ω))) =
      thrReportedMean P σ Cs carriers FP algorithm den report := by
    unfold Shared.maskedMean thrReportedMean
    refine Finset.sum_congr rfl fun g _ => congrArg uMean (funext fun p => ?_)
    rw [uMean_prod_eq]
  rw [hT, hR] at hfull
  exact hfull

/-! ## The second error: the sampled estimate -/

theorem sum_uMean_eq_sum_prod {G Pr : Type} [Fintype G] [Fintype Pr] (Y : G → Pr → ℝ) :
    ∑ g, uMean (fun pr => Y g pr) = ∑ gp : G × Pr, (1 / (Fintype.card Pr : ℝ)) * Y gp.1 gp.2 := by
  unfold uMean
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun pr _ => by ring

theorem mean_reorder {G Pr Zc Es U : Type} [Fintype G] [Fintype Pr] [Fintype Zc] [Fintype Es] [Fintype U]
    (F : G → Pr → Zc → Es → U → ℝ) :
    ∑ g, uMean (fun pr => uMean (fun c => uMean (fun e => uMean (fun uv => F g pr c e uv)))) =
      uMean (fun c => uMean (fun e => ∑ g, uMean (fun pr => uMean (fun uv => F g pr c e uv)))) := by
  symm
  calc uMean (fun c => uMean (fun e => ∑ g, uMean (fun pr => uMean (fun uv => F g pr c e uv))))
      = uMean (fun c => ∑ g, uMean (fun e => uMean (fun pr => uMean (fun uv => F g pr c e uv)))) :=
        congrArg uMean (funext fun c => uMean_finsum _)
    _ = ∑ g, uMean (fun c => uMean (fun e => uMean (fun pr => uMean (fun uv => F g pr c e uv)))) := uMean_finsum _
    _ = ∑ g, uMean (fun pr => uMean (fun c => uMean (fun e => uMean (fun uv => F g pr c e uv)))) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        calc uMean (fun c => uMean (fun e => uMean (fun pr => uMean (fun uv => F g pr c e uv))))
            = uMean (fun c => uMean (fun pr => uMean (fun e => uMean (fun uv => F g pr c e uv)))) :=
              congrArg uMean (funext fun c => uMean_prod_swap (fun e pr => uMean (fun uv => F g pr c e uv)))
          _ = _ := uMean_prod_swap (fun c pr => uMean (fun e => uMean (fun uv => F g pr c e uv)))

variable {N Q : ℕ} (eqv : P.Errors ≃ Fin N) (S : Fin Q → Fin N × Fin N)

def thrStates (c : {c // P.IsCenter σ c}) (g : ThrEq P Cs algorithm)
    (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val) (i j : Fin N) : Bool :=
  decide (thrResHat P Cs algorithm den report g pr c.1 (eqv.symm i) (eqv.symm j) = s)

noncomputable def thrCellObs (c : {c // P.IsCenter σ c}) (e : GapSeed FP) : Fin N → Fin N → ℝ :=
  thrObservable (fun pr : PrimeIndex (thrCutoff P Cs algorithm den) => pr.val)
    (fun i j => symMask P σ carriers FP e (P.point c.1 (eqv.symm i) (eqv.symm j)))
    (thrStates P σ Cs algorithm den report eqv c)
    (fun g _ i => thrLeft (thrOccs P Cs) (thrRealize P Cs algorithm g) c.1 (P.errorVector P.leftBlock (eqv.symm i)))
    (fun g _ j => thrRight (thrOccs P Cs) (thrRealize P Cs algorithm g) c.1 (P.errorVector P.rightBlock (eqv.symm j)))

/-- **The THR state matrices** `D_{(g,p),s} = G·H_{g,p,s}` of the call (row:matrix). -/
noncomputable def thrStateAt (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (g : ThrEq P Cs algorithm)
    (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val) : Fin N → Fin N → ℂ :=
  thrStateMatrix (fun pr : PrimeIndex (thrCutoff P Cs algorithm den) => pr.val)
    (fun i j => symMask P σ carriers FP e (P.point c.1 (eqv.symm i) (eqv.symm j)))
    (thrStates P σ Cs algorithm den report eqv c) g pr s

/-- **The THR estimate** `E_zE_e(1/Q)Σ_ℓ G·Σ_{g,p}(1/|𝒫|)R̂_{g,p}` at the sampled pairs. -/
noncomputable def thrEstimate : ℝ :=
  uMean fun c : {c // P.IsCenter σ c} => uMean fun e : GapSeed FP =>
    sampleMean S (thrCellObs P σ Cs carriers FP algorithm den report eqv c e)

theorem thrRow_cell (c : {c // P.IsCenter σ c}) (g : ThrEq P Cs algorithm)
    (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (i j : Fin N) :
    thrRow (fun pr : PrimeIndex (thrCutoff P Cs algorithm den) => pr.val) (thrStates P σ Cs algorithm den report eqv c)
        (fun g _ i => thrLeft (thrOccs P Cs) (thrRealize P Cs algorithm g) c.1 (P.errorVector P.leftBlock (eqv.symm i)))
        (fun g _ j => thrRight (thrOccs P Cs) (thrRealize P Cs algorithm g) c.1
          (P.errorVector P.rightBlock (eqv.symm j))) g pr i j =
      bitR (thrRhat P Cs algorithm den report g pr c.1 (eqv.symm i) (eqv.symm j)) := by
  unfold thrRow thrStates thrRhat
  rw [Finset.sum_eq_single (thrResHat P Cs algorithm den report g pr c.1 (eqv.symm i) (eqv.symm j))]
  · simp [bitR]
  · intro s _ hs
    simp [bitR, Ne.symm hs]
  · simp

/-- The live-pair average of a column's observable. -/
theorem thrCell_live (c : {c // P.IsCenter σ c}) (e : GapSeed FP) :
    liveMean (thrCellObs P σ Cs carriers FP algorithm den report eqv c e) =
      ∑ g : ThrEq P Cs algorithm, uMean fun pr : PrimeIndex (thrCutoff P Cs algorithm den) =>
        uMean fun uv : P.Errors × P.Errors => bitR (symMask P σ carriers FP e (P.point c.1 uv.1 uv.2)) *
          bitR (thrRhat P Cs algorithm den report g pr c.1 uv.1 uv.2) := by
  unfold thrCellObs thrObservable
  rw [liveMean_sum, sum_uMean_eq_sum_prod]
  refine Finset.sum_congr rfl fun gp _ => ?_
  congr 1
  simp only [thrRow_cell]
  rw [liveMean_eq_uMean, uMean_prod_eq, ← uMean_equiv eqv.symm]
  refine congrArg uMean (funext fun i => ?_)
  rw [← uMean_equiv eqv.symm]

theorem thr_second_error (hN : 0 < N) (hQ : 0 < Q) (ηz : {c // P.IsCenter σ c} → ℝ) (η : ℝ)
    (hηz : ∀ c e g pr s, ‖sampleError (thrStateAt P σ Cs carriers FP algorithm den report eqv c e g pr s) S‖ /
      (Q * N) ≤ ηz c)
    (hη : uMean ηz ≤ η) :
    |thrReportedMean P σ Cs carriers FP algorithm den report -
        thrEstimate P σ Cs carriers FP algorithm den report eqv S| ≤
      Fintype.card (ThrEq P Cs algorithm) * (thrCutoff P Cs algorithm den : ℝ) * η := by
  have hrep : thrReportedMean P σ Cs carriers FP algorithm den report =
      uMean (fun c : {c // P.IsCenter σ c} => uMean (fun e : GapSeed FP =>
        liveMean (thrCellObs P σ Cs carriers FP algorithm den report eqv c e))) := by
    have hR : (fun c : {c // P.IsCenter σ c} => uMean (fun e : GapSeed FP =>
        liveMean (thrCellObs P σ Cs carriers FP algorithm den report eqv c e))) =
        fun c => uMean (fun e : GapSeed FP => ∑ g : ThrEq P Cs algorithm,
          uMean fun pr : PrimeIndex (thrCutoff P Cs algorithm den) =>
            uMean fun uv : P.Errors × P.Errors => bitR (symMask P σ carriers FP e (P.point c.1 uv.1 uv.2)) *
              bitR (thrRhat P Cs algorithm den report g pr c.1 uv.1 uv.2)) :=
      funext fun c => congrArg uMean (funext fun e => thrCell_live P σ Cs carriers FP algorithm den report eqv c e)
    rw [hR]
    unfold thrReportedMean
    have hin : ∀ (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)),
        (uMean fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) => uMean fun e : GapSeed FP =>
          bitR (symMask P σ carriers FP e (P.point pt.1.1 pt.2.1 pt.2.2)) *
            bitR (thrRhat P Cs algorithm den report g pr pt.1.1 pt.2.1 pt.2.2)) =
        uMean (fun c : {c // P.IsCenter σ c} => uMean (fun e : GapSeed FP =>
          uMean fun uv : P.Errors × P.Errors => bitR (symMask P σ carriers FP e (P.point c.1 uv.1 uv.2)) *
            bitR (thrRhat P Cs algorithm den report g pr c.1 uv.1 uv.2))) := by
      intro g pr
      rw [uMean_prod_eq]
      exact congrArg uMean (funext fun c => uMean_prod_swap (fun (uv : P.Errors × P.Errors) (e : GapSeed FP) =>
        bitR (symMask P σ carriers FP e (P.point c.1 uv.1 uv.2)) * bitR (thrRhat P Cs algorithm den report g pr c.1 uv.1 uv.2)))
    simp only [hin]
    exact mean_reorder (fun (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
      (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (uv : P.Errors × P.Errors) =>
      bitR (symMask P σ carriers FP e (P.point c.1 uv.1 uv.2)) * bitR (thrRhat P Cs algorithm den report g pr c.1 uv.1 uv.2))
  rw [hrep]
  have hM0 : (0 : ℝ) ≤ Fintype.card (ThrEq P Cs algorithm) * (thrCutoff P Cs algorithm den : ℝ) := by positivity
  refine averaged_sample_error _ _ _ ηz η hM0 (fun c e => ?_) hη
  rcases isEmpty_or_nonempty (ThrEq P Cs algorithm) with hE | hne
  · -- no exact equations: the observable vanishes and so does the bound
    haveI : IsEmpty (ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den)) := inferInstance
    have h0 : thrCellObs P σ Cs carriers FP algorithm den report eqv c e = fun _ _ => 0 := by
      funext i j
      unfold thrCellObs thrObservable
      exact Fintype.sum_empty _
    rw [h0, Fintype.card_eq_zero]
    simp [liveMean, sampleMean]
  · obtain ⟨g⟩ := hne
    have h563 := canonicalPrimeCutoff_ge_563 (familyMagnitudeExponent (thrRealize P Cs algorithm)) den
    have pr : PrimeIndex (thrCutoff P Cs algorithm den) :=
      ⟨2, mem_primesUpTo.mpr ⟨Nat.prime_two, by unfold thrCutoff; omega⟩⟩
    have hη0 : 0 ≤ ηz c := le_trans (by positivity) (hηz c e g pr 0)
    exact thr_sampler_interface (fun pr : PrimeIndex (thrCutoff P Cs algorithm den) => pr.val) hN hQ
      (fun i j => symMask P σ carriers FP e (P.point c.1 (eqv.symm i) (eqv.symm j)))
      (thrStates P σ Cs algorithm den report eqv c)
      (fun g _ i => thrLeft (thrOccs P Cs) (thrRealize P Cs algorithm g) c.1 (P.errorVector P.leftBlock (eqv.symm i)))
      (fun g _ j => thrRight (thrOccs P Cs) (thrRealize P Cs algorithm g) c.1
        (P.errorVector P.rightBlock (eqv.symm j))) S (ηz c) (thrCutoff P Cs algorithm den) hη0 (Nat.cast_nonneg _)
      (fun pr => by exact_mod_cast (mem_primesUpTo.mp pr.2).2) (fun g pr s => hηz c e g pr s)

theorem thr_primitive_error (spectrum : ExpanderSpectrumContract) (hFlen : ∀ X ∈ carriers, 2 * X.length ≤ FP.len)
    (hcap1 : 1 ≤ FP.cap) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : uMean (fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) =>
      bitR (thrFail P Cs algorithm den report pt.1.1 pt.2.1 pt.2.2 && !symOver P carriers FP pt.1.1 pt.2.1 pt.2.2)) ≤ δ)
    (hN : 0 < N) (hQ : 0 < Q) (ηz : {c // P.IsCenter σ c} → ℝ) (η : ℝ)
    (hηz : ∀ c e g pr s, ‖sampleError (thrStateAt P σ Cs carriers FP algorithm den report eqv c e g pr s) S‖ /
      (Q * N) ≤ ηz c)
    (hη : uMean ηz ≤ η) :
    |thrEstimate P σ Cs carriers FP algorithm den report eqv S -
        WireExponent3_5.maskedMean (symMask P σ carriers FP) (fun i => (Cs i).eval)| ≤
      Fintype.card (ThrEq P Cs algorithm) * (thrCert P Cs algorithm theta den).error +
        Fintype.card (ThrEq P Cs algorithm) * (δ + 1 / 2 ^ FP.errExp) +
        Fintype.card (ThrEq P Cs algorithm) * (thrCutoff P Cs algorithm den : ℝ) * η := by
  have htruth : WireExponent3_5.maskedMean (symMask P σ carriers FP) (fun i => (Cs i).eval) =
      thrTruthMean P σ Cs carriers FP := by
    rw [seedMaskedMean_eq]
    have hx : ∀ e : GapSeed FP, uMean (fun x => bitR (symMask P σ carriers FP e x) *
        bitR (decide (∀ i, (Cs i).eval x = true))) =
        uMean (fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) =>
          bitR (symMask P σ carriers FP e (P.point pt.1.1 pt.2.1 pt.2.2)) *
            bitR (decide (∀ i, (Cs i).eval (P.point pt.1.1 pt.2.1 pt.2.2) = true))) := by
      intro e
      rw [← uMean_equiv (P.decomposition σ).symm]
      rfl
    simp only [hx]
    unfold thrTruthMean
    exact uMean_prod_swap _
  rw [htruth]
  have h1 := thr_first_error P σ Cs carriers FP algorithm theta den report spectrum hFlen hcap1 δ hδ0 hδ
  have h2 := thr_second_error P σ Cs carriers FP algorithm den report eqv S hN hQ ηz η hηz hη
  calc _ = |(thrTruthMean P σ Cs carriers FP - thrReportedMean P σ Cs carriers FP algorithm den report) +
          (thrReportedMean P σ Cs carriers FP algorithm den report -
            thrEstimate P σ Cs carriers FP algorithm den report eqv S)| := by
        rw [abs_sub_comm]; ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

end Thr

end NearCubicWires.WireExponent3_5.Primitive

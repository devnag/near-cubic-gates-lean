import Proof.Wire_3_5.PrimitiveMeans
import Proof.Wire_3_5.PrimitiveSymRow
import Proof.Wire_3_5.StarPartition
import Proof.Wire_3_5.FilterGap
import Proof.Wire_3_5.StarCarrierConsumer

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Rows
open scoped Matrix.Norms.L2Operator

theorem list_sum_map_le {α : Type} (l : List α) (f : α → ℕ) (K : ℕ) (h : ∀ x ∈ l, f x ≤ K) :
    (l.map f).sum ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    nlinarith

section Sym
variable (P : StarParams) (σ : P.Translation) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n)
  (carriers : List (Carrier P.n)) (FP : GapParams) (Pl : FlatListParams)

noncomputable def symMask (e : GapSeed FP) (x : BitInput P.n) : Bool :=
  carriers.all fun X => gapFilter FP e (inputResidualBits P σ X x)

/-- The output alphabets `{0,…,m_j}`. -/
def symM (i : Fin a) : ℕ := (Cs i).bottomCount

/-- The extended lookups `g_j`. -/
def symG (i : Fin a) : ℤ → Bool := symLookupFn (Cs i)

/-- The one-sided score `A_{j,c}(u) + B_{j,c}(v)`. -/
def symScore (c : BitInput P.n) (u v : P.Errors) (i : Fin a) : ℤ :=
  symLeftScore (Cs i) c (P.errorVector P.leftBlock u) + symRightScore (Cs i) c (P.errorVector P.rightBlock v)

/-- The residual vector `(Z_{j,i}^+)_i` of circuit `j`. -/
def symZp (c : BitInput P.n) (u v : P.Errors) (i : Fin a) : List Bool :=
  plusBits (symGates (Cs i)) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)

/-- The residual vector `(Z_{j,i}^−)_i` of circuit `j`. -/
def symZm (c : BitInput P.n) (u v : P.Errors) (i : Fin a) : List Bool :=
  minusBits (symGates (Cs i)) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)

/-- The lists' reports `(t_j^+, t_j^−)` at list seed `e'`. -/
def symRep (el : Pl.FlatSeed) (c : BitInput P.n) (u v : P.Errors) : Fin a → ℕ × ℕ :=
  Pl.jointState (symZp P Cs c u v) (symZm P Cs c u v) el

def symRhat (el : Pl.FlatSeed) (c : BitInput P.n) (u v : P.Errors) : Bool :=
  symReported (symM P Cs) (symG P Cs) (symScore P Cs c u v) (symRep P Cs Pl el c u v)

/-- The true lookup `Π_j g_j(A_j + B_j + s_j^+ − s_j^−)`. -/
def symTrue (c : BitInput P.n) (u v : P.Errors) : Bool :=
  FlatListParams.trueSym (symG P Cs) (symScore P Cs c u v) (symZp P Cs c u v) (symZm P Cs c u v)

/-- Some named population is at least the enlarged cap `4096·B` (the region the regular filter suppresses). -/
def symOver (c : BitInput P.n) (u v : P.Errors) : Bool :=
  carriers.any fun X => decide (4096 * FP.cap ≤
    Carrier.population X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v))

theorem symConj_point (c : BitInput P.n) (u v : P.Errors) :
    decide (∀ i, (Cs i).eval (P.point c u v) = true) = symTrue P Cs c u v := by
  unfold symTrue FlatListParams.trueSym
  congr 1
  apply propext
  have h : ∀ i, (Cs i).eval (P.point c u v) =
      symG P Cs i (symScore P Cs c u v i + ((symZp P Cs c u v i).count true : ℤ) - (symZm P Cs c u v i).count true) := by
    intro i
    unfold StarParams.point symG symScore symZp symZm
    rw [sym_eval_point (Cs i) c _ _ (errorVector_disjoint P u v), add_sub_assoc]
  simp only [h]

/-- The mask at `c+u+v` reads the residual vectors at `(c,u,v)` when `c` is a cell center. -/
theorem symMask_point {c : BitInput P.n} (hc : P.IsCenter σ c) (e : GapSeed FP) (u v : P.Errors) :
    symMask P σ carriers FP e (P.point c u v) = carriers.all fun X => gapFilter FP e
      (Carrier.residualBits X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)) := by
  unfold symMask inputResidualBits
  rw [P.center_point hc, P.leftErrors_point hc, P.rightErrors_point hc]

/-- The masked truth `E_{(c,u,v)}E_{(e,e')}[M·ΠC]` over cells and seeds. -/
noncomputable def symTruthMean : ℝ :=
  uMean fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) => uMean fun s : GapSeed FP × Pl.FlatSeed =>
    bitR (symMask P σ carriers FP s.1 (P.point pt.1.1 pt.2.1 pt.2.2)) * bitR (symTrue P Cs pt.1.1 pt.2.1 pt.2.2)

noncomputable def symReportedMean : ℝ :=
  uMean fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) => uMean fun s : GapSeed FP × Pl.FlatSeed =>
    bitR (symMask P σ carriers FP s.1 (P.point pt.1.1 pt.2.1 pt.2.2)) * bitR (symRhat P Cs Pl s.2 pt.1.1 pt.2.1 pt.2.2)

theorem sym_first_error (spectrum : ExpanderSpectrumContract) (hgates : GatesIn (fun i => symGates (Cs i)) carriers)
    (hFlen : ∀ X ∈ carriers, 2 * X.length ≤ FP.len) (hcap1 : 1 ≤ FP.cap)
    (hM : ∀ i, (Cs i).bottomCount ≤ Pl.M) (hB : carriers.length * (4096 * FP.cap) ≤ Pl.B) :
    |symTruthMean P σ Cs carriers FP Pl - symReportedMean P σ Cs carriers FP Pl| ≤
      (2 * a : ℕ) * (1 / 2 ^ Pl.errExp) + 1 / 2 ^ FP.errExp := by
  set Ω := ({c // P.IsCenter σ c} × (P.Errors × P.Errors)) × (GapSeed FP × Pl.FlatSeed)
  set G : Ω → Bool := fun ω => symMask P σ carriers FP ω.2.1 (P.point ω.1.1.1 ω.1.2.1 ω.1.2.2)
  set Rh : Ω → Bool := fun ω => symRhat P Cs Pl ω.2.2 ω.1.1.1 ω.1.2.1 ω.1.2.2
  set Tr : Ω → Bool := fun ω => symTrue P Cs ω.1.1.1 ω.1.2.1 ω.1.2.2
  set Ov : Ω → Bool := fun ω => symOver P carriers FP ω.1.1.1 ω.1.2.1 ω.1.2.2
  have hδ0 : (0 : ℝ) ≤ (2 * a : ℕ) * (1 / 2 ^ Pl.errExp) := by positivity
  have hξ0 : (0 : ℝ) ≤ 1 / 2 ^ FP.errExp := by positivity
  -- the list failure off the over-cap region
  have hδ : uMean (fun ω : Ω => bitR (decide (Rh ω ≠ Tr ω) && !Ov ω)) ≤ (2 * a : ℕ) * (1 / 2 ^ Pl.errExp) := by
    rw [uMean_prod_eq]
    refine uMean_le_const _ _ hδ0 fun pt => ?_
    obtain ⟨⟨c, hc⟩, u, v⟩ := pt
    cases hov : symOver P carriers FP c u v
    · -- all named populations are below the enlarged cap
      have hpop : ∀ X ∈ carriers, Carrier.population X c (P.errorVector P.leftBlock u)
          (P.errorVector P.rightBlock v) ≤ 4096 * FP.cap := by
        intro X hX
        have := hov
        simp only [symOver, List.any_eq_false, decide_eq_true_eq, not_le] at this
        exact (this X hX).le
      have hcap : ∀ i, (symZp P Cs c u v i).count true ≤ Pl.B ∧ (symZm P Cs c u v i).count true ≤ Pl.B := by
        intro i
        have hsum := count_plus_add_minus (symGates (Cs i)) c (P.errorVector P.leftBlock u)
          (P.errorVector P.rightBlock v)
        have hle := GatesIn.population_le hgates i c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)
        have hK := list_sum_map_le carriers _ _ hpop
        unfold symZp symZm
        constructor <;> omega
      have hlen : ∀ i, (symZp P Cs c u v i).length ≤ symM P Cs i ∧ (symZm P Cs c u v i).length ≤ symM P Cs i := by
        intro i
        simp [symZp, symZm, length_plusBits, length_minusBits, length_symGates, symM]
      have hlenM : ∀ i, (symZp P Cs c u v i).length ≤ Pl.M ∧ (symZm P Cs c u v i).length ≤ Pl.M := by
        intro i
        exact ⟨(hlen i).1.trans (hM i), (hlen i).2.trans (hM i)⟩
      have hfail := symReported_fail_le spectrum Pl (symM P Cs) (symG P Cs) (symScore P Cs c u v)
        (symZp P Cs c u v) (symZm P Cs c u v) hlen hlenM hcap
      rw [uMean_prod_eq]
      simp only [Ov, Rh, Tr, hov, Bool.not_false, Bool.and_true]
      rw [uMean_const (A := GapSeed FP)
        (uMean fun el : Pl.FlatSeed => bitR (decide (symRhat P Cs Pl el c u v ≠ symTrue P Cs c u v)))]
      exact hfail
    · simp only [Ov, hov, Bool.not_true, Bool.and_false, uMean_const, bitR, Bool.false_eq_true, if_false]
      exact hδ0
  -- the regular filter above the enlarged cap
  have hξ : uMean (fun ω : Ω => bitR (G ω && Ov ω)) ≤ 1 / 2 ^ FP.errExp := by
    rw [uMean_prod_eq]
    refine uMean_le_const _ _ hξ0 fun pt => ?_
    obtain ⟨⟨c, hc⟩, u, v⟩ := pt
    cases hov : symOver P carriers FP c u v
    · simp only [Ov, hov, Bool.and_false, uMean_const, bitR, Bool.false_eq_true, if_false]
      exact hξ0
    · simp only [symOver, List.any_eq_true, decide_eq_true_eq] at hov
      obtain ⟨X, hX, hXpop⟩ := hov
      have hov' : symOver P carriers FP c u v = true := by
        simp only [symOver, List.any_eq_true, decide_eq_true_eq]; exact ⟨X, hX, hXpop⟩
      simp only [G, Ov, hov', Bool.and_true]
      rw [uMean_prod_eq, uMean_prod_swap]
      simp only [uMean_const]
      have hsound := (gapFilter_guarantee spectrum FP hcap1).sound
        (Carrier.residualBits X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v))
        (by rw [length_residualBits]; exact hFlen X hX) (by rw [Carrier.count_residualBits]; exact hXpop)
      refine le_trans (booleanMean_mono _ _ fun e he => ?_) hsound
      rw [symMask_point P σ carriers FP hc, List.all_eq_true] at he
      exact he X hX
  -- S7's masked row error
  have hmask := maskedRowError_holds G Rh Tr (fun ω => decide (Rh ω ≠ Tr ω)) Ov
    ((2 * a : ℕ) * (1 / 2 ^ Pl.errExp)) (1 / 2 ^ FP.errExp)
    (fun ω _ hf => by simpa using hf) hδ hξ
  have hT : symTruthMean P σ Cs carriers FP Pl = uMean (fun ω : Ω => bitR (G ω) * bitR (Tr ω)) := by
    rw [uMean_prod_eq]; rfl
  have hR : symReportedMean P σ Cs carriers FP Pl = uMean (fun ω : Ω => bitR (G ω) * bitR (Rh ω)) := by
    rw [uMean_prod_eq]; rfl
  rw [hT, hR, ← uMean_sub']
  refine (abs_uMean_le _).trans (le_trans (uMean_mono fun ω => ?_) hmask)
  rw [← mul_sub, abs_mul, abs_of_nonneg (bitR_nonneg _), abs_sub_comm]

/-! ## The masked truth of the call -/

/-- **The seed's `prim:truth` at a symmetric-top call** is the masked truth over cells and seeds (the list seed is a
dummy coordinate of the truth). -/
theorem symTruth_eq :
    WireExponent3_5.maskedMean (symMask P σ carriers FP) (fun i => (Cs i).eval) =
      symTruthMean P σ Cs carriers FP Pl := by
  rw [seedMaskedMean_eq]
  have hx : ∀ e : GapSeed FP, uMean (fun x => bitR (symMask P σ carriers FP e x) *
      bitR (decide (∀ i, (Cs i).eval x = true))) =
      uMean (fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) =>
        bitR (symMask P σ carriers FP e (P.point pt.1.1 pt.2.1 pt.2.2)) * bitR (symTrue P Cs pt.1.1 pt.2.1 pt.2.2)) := by
    intro e
    rw [← uMean_equiv (P.decomposition σ).symm]
    refine congrArg uMean (funext fun pt => ?_)
    show bitR (symMask P σ carriers FP e (P.point pt.1.1 pt.2.1 pt.2.2)) *
      bitR (decide (∀ i, (Cs i).eval (P.point pt.1.1 pt.2.1 pt.2.2) = true)) = _
    rw [symConj_point]
  simp only [hx]
  rw [uMean_prod_swap]
  unfold symTruthMean
  refine congrArg uMean (funext fun pt => ?_)
  rw [uMean_prod_eq]
  refine congrArg uMean (funext fun e => ?_)
  simp only [uMean_const]

/-! ## The second error: the sampled estimate -/

variable {N Q : ℕ} (eqv : P.Errors ≃ Fin N) (S : Fin Q → Fin N × Fin N)

noncomputable def symCell (c : {c // P.IsCenter σ c}) (s : GapSeed FP × Pl.FlatSeed) (i j : Fin N) : ℝ :=
  bitR (symMask P σ carriers FP s.1 (P.point c.1 (eqv.symm i) (eqv.symm j))) *
    bitR (symRhat P Cs Pl s.2 c.1 (eqv.symm i) (eqv.symm j))

noncomputable def symStateAt (c : {c // P.IsCenter σ c}) (s : GapSeed FP × Pl.FlatSeed) (τ : SymState (symM P Cs)) :
    Fin N → Fin N → ℂ :=
  symStateMatrix (symM P Cs) (fun i j => symMask P σ carriers FP s.1 (P.point c.1 (eqv.symm i) (eqv.symm j)))
    (fun τ i j => symIndicator (symM P Cs) (symRep P Cs Pl s.2 c.1 (eqv.symm i) (eqv.symm j)) τ) τ

noncomputable def symEstimate : ℝ :=
  uMean fun c : {c // P.IsCenter σ c} => uMean fun s : GapSeed FP × Pl.FlatSeed =>
    sampleMean S (symCell P σ Cs carriers FP Pl eqv c s)

noncomputable def symMass : ℝ := ((∏ j, ((symM P Cs j + 1) ^ 2 : ℕ) : ℝ) * ∏ j, (symModulus (symM P Cs j) : ℝ))

theorem symMass_nonneg : 0 ≤ symMass P Cs := by unfold symMass; positivity

/-- The live-pair average of a cell is its uniform average over the live halves. -/
theorem symCell_live (c : {c // P.IsCenter σ c}) (s : GapSeed FP × Pl.FlatSeed) :
    liveMean (symCell P σ Cs carriers FP Pl eqv c s) =
      uMean (fun uv : P.Errors × P.Errors => bitR (symMask P σ carriers FP s.1 (P.point c.1 uv.1 uv.2)) *
        bitR (symRhat P Cs Pl s.2 c.1 uv.1 uv.2)) := by
  rw [liveMean_eq_uMean, uMean_prod_eq]
  rw [← uMean_equiv eqv.symm]
  refine congrArg uMean (funext fun i => ?_)
  rw [← uMean_equiv eqv.symm]
  rfl

theorem sym_second_error (hN : 0 < N) (hQ : 0 < Q) (ηz : {c // P.IsCenter σ c} → ℝ) (η : ℝ)
    (hηz : ∀ c s τ, ‖sampleError (symStateAt P σ Cs carriers FP Pl eqv c s τ) S‖ / (Q * N) ≤ ηz c)
    (hη : uMean ηz ≤ η) :
    |symReportedMean P σ Cs carriers FP Pl - symEstimate P σ Cs carriers FP Pl eqv S| ≤ symMass P Cs * η := by
  have hrep : symReportedMean P σ Cs carriers FP Pl =
      uMean (fun c : {c // P.IsCenter σ c} => uMean (fun s : GapSeed FP × Pl.FlatSeed =>
        liveMean (symCell P σ Cs carriers FP Pl eqv c s))) := by
    unfold symReportedMean
    rw [uMean_prod_eq]
    refine congrArg uMean (funext fun c => ?_)
    rw [uMean_prod_swap]
    refine congrArg uMean (funext fun s => ?_)
    rw [symCell_live]
  rw [hrep]
  refine averaged_sample_error _ _ (symMass P Cs) ηz η (symMass_nonneg P Cs) (fun c s => ?_) hη
  have hη0 : 0 ≤ ηz c := le_trans (by positivity) (hηz c s (fun j => (0, 0)))
  have hrow := sym_sampler_interface hN hQ (symM P Cs) (symG P Cs)
    (fun i j => symMask P σ carriers FP s.1 (P.point c.1 (eqv.symm i) (eqv.symm j)))
    (fun τ i j => symIndicator (symM P Cs) (symRep P Cs Pl s.2 c.1 (eqv.symm i) (eqv.symm j)) τ)
    (fun k i => symLeftScore (Cs k) c.1 (P.errorVector P.leftBlock (eqv.symm i)))
    (fun k j => symRightScore (Cs k) c.1 (P.errorVector P.rightBlock (eqv.symm j)))
    (fun k i => symLeftScore_range (Cs k) c.1 _) (fun k j => symRightScore_range (Cs k) c.1 _) S (ηz c) hη0
    (fun τ => hηz c s τ)
  have hcell : symRow (symM P Cs) (symG P Cs)
      (fun i j => symMask P σ carriers FP s.1 (P.point c.1 (eqv.symm i) (eqv.symm j)))
      (fun τ i j => symIndicator (symM P Cs) (symRep P Cs Pl s.2 c.1 (eqv.symm i) (eqv.symm j)) τ)
      (fun k i => symLeftScore (Cs k) c.1 (P.errorVector P.leftBlock (eqv.symm i)))
      (fun k j => symRightScore (Cs k) c.1 (P.errorVector P.rightBlock (eqv.symm j))) =
      symCell P σ Cs carriers FP Pl eqv c s := by
    funext i j
    unfold symRow symCell
    rw [symStateSum_eq]
    rfl
  rw [hcell] at hrow
  unfold symMass
  exact hrow

theorem sym_primitive_error (spectrum : ExpanderSpectrumContract)
    (hgates : GatesIn (fun i => symGates (Cs i)) carriers) (hFlen : ∀ X ∈ carriers, 2 * X.length ≤ FP.len)
    (hcap1 : 1 ≤ FP.cap) (hM : ∀ i, (Cs i).bottomCount ≤ Pl.M) (hB : carriers.length * (4096 * FP.cap) ≤ Pl.B)
    (hN : 0 < N) (hQ : 0 < Q) (ηz : {c // P.IsCenter σ c} → ℝ) (η : ℝ)
    (hηz : ∀ c s τ, ‖sampleError (symStateAt P σ Cs carriers FP Pl eqv c s τ) S‖ / (Q * N) ≤ ηz c)
    (hη : uMean ηz ≤ η) :
    |symEstimate P σ Cs carriers FP Pl eqv S -
        WireExponent3_5.maskedMean (symMask P σ carriers FP) (fun i => (Cs i).eval)| ≤
      (2 * a : ℕ) * (1 / 2 ^ Pl.errExp) + 1 / 2 ^ FP.errExp + symMass P Cs * η := by
  rw [symTruth_eq P σ Cs carriers FP Pl]
  have h1 := sym_first_error P σ Cs carriers FP Pl spectrum hgates hFlen hcap1 hM hB
  have h2 := sym_second_error P σ Cs carriers FP Pl eqv S hN hQ ηz η hηz hη
  calc _ = |(symTruthMean P σ Cs carriers FP Pl - symReportedMean P σ Cs carriers FP Pl) +
          (symReportedMean P σ Cs carriers FP Pl - symEstimate P σ Cs carriers FP Pl eqv S)| := by
        rw [abs_sub_comm]; ring_nf
    _ ≤ |symTruthMean P σ Cs carriers FP Pl - symReportedMean P σ Cs carriers FP Pl| +
          |symReportedMean P σ Cs carriers FP Pl - symEstimate P σ Cs carriers FP Pl eqv S| := abs_add_le _ _
    _ ≤ ((2 * a : ℕ) * (1 / 2 ^ Pl.errExp) + 1 / 2 ^ FP.errExp) + symMass P Cs * η := add_le_add h1 h2

end Sym

end NearCubicWires.WireExponent3_5.Primitive

import Proof.Wire_3_5.PrimitiveThrLists
import Proof.Wire_3_5.PrimitiveSymCall

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Rows NearCubicWires.WireExponent3_5.Cost
open scoped Matrix.Norms.L2Operator

/-! ## The parameter arithmetic of the fixed hash -/

theorem lt_two_pow_clog (X : ℕ) : (X : ℝ) < 2 ^ Nat.clog 2 (X + 1) := by
  have := Nat.le_pow_clog (b := 2) (by norm_num) (X + 1)
  have h : (X : ℝ) + 1 ≤ 2 ^ Nat.clog 2 (X + 1) := by exact_mod_cast this
  linarith

/-- The list parameters as functions of `A`, `B_*`, `M` and the target `K`. -/
def listJ (A Bs K : ℕ) : ℕ := Nat.clog 2 (8 * K * A * Bs + 1)

def listT (A Bs K : ℕ) : ℕ := Nat.clog 2 (8 * K * A * listJ A Bs K + 1) + 1

def listE (A Bs M K : ℕ) : ℕ :=
  Nat.clog 2 (8 * K * A * (M + listJ A Bs K * M ^ (2 * listT A Bs K)) + 1) + 1

/-- **The fixed hash's failure at the chosen parameters** is at most `3/(4K)`. -/
theorem list_params_bound (A Bs M K : ℕ) (hK : 1 ≤ K) :
    ((A : ℝ) * (Bs * (1 / 2 ^ listJ A Bs K) + listJ A Bs K * (1 / 64) ^ listT A Bs K) +
        (1 / 2 ^ listE A Bs M K) * (A * (M + listJ A Bs K * (M : ℝ) ^ (2 * listT A Bs K)))) /
      (1 - 1 / 2 ^ listE A Bs M K) ≤ 3 / (4 * K) := by
  set J := listJ A Bs K
  set t := listT A Bs K
  set e := listE A Bs M K
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have h8K : (0 : ℝ) < 8 * K := by positivity
  -- the three terms
  have h1 : (A : ℝ) * (Bs * (1 / 2 ^ J)) ≤ 1 / (8 * K) := by
    have hX := lt_two_pow_clog (8 * K * A * Bs)
    have hJ : (2 : ℝ) ^ J = 2 ^ Nat.clog 2 (8 * K * A * Bs + 1) := rfl
    have hpos : (0 : ℝ) < 2 ^ J := by positivity
    rw [← hJ] at hX
    push_cast at hX
    rw [mul_one_div, ← mul_div_assoc, div_le_div_iff₀ hpos h8K]
    nlinarith
  have h2 : (A : ℝ) * (J * (1 / 64) ^ t) ≤ 1 / (8 * K) := by
    have hX := lt_two_pow_clog (8 * K * A * J)
    have ht : (2 : ℝ) ^ t = 2 * 2 ^ Nat.clog 2 (8 * K * A * J + 1) := by
      show (2 : ℝ) ^ (Nat.clog 2 (8 * K * A * listJ A Bs K + 1) + 1) = _
      rw [pow_succ]; ring
    have h64 : (1 / 64 : ℝ) ^ t ≤ 1 / 2 ^ t := by
      rw [one_div_pow]
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) t
    have hpos : (0 : ℝ) < 2 ^ t := by positivity
    calc (A : ℝ) * (J * (1 / 64) ^ t) ≤ A * (J * (1 / 2 ^ t)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left h64 (Nat.cast_nonneg _)
      _ ≤ 1 / (8 * K) := by
          rw [mul_one_div, ← mul_div_assoc, div_le_div_iff₀ hpos h8K, ht]
          push_cast at hX
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (Nat.clog 2 (8 * K * A * J + 1))]
  have h3 : (1 / 2 ^ e : ℝ) * (A * (M + J * (M : ℝ) ^ (2 * t))) ≤ 1 / (8 * K) := by
    have hX := lt_two_pow_clog (8 * K * A * (M + J * M ^ (2 * t)))
    have he : (2 : ℝ) ^ e = 2 * 2 ^ Nat.clog 2 (8 * K * A * (M + J * M ^ (2 * t)) + 1) := by
      show (2 : ℝ) ^ (Nat.clog 2 (8 * K * A * (M + listJ A Bs K * M ^ (2 * listT A Bs K)) + 1) + 1) = _
      rw [pow_succ]; ring
    have hpos : (0 : ℝ) < 2 ^ e := by positivity
    rw [one_div_mul_eq_div, div_le_div_iff₀ hpos h8K, he]
    push_cast at hX
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (Nat.clog 2 (8 * K * A * (M + J * M ^ (2 * t)) + 1))]
  have he1 : (1 : ℝ) / 2 ^ e ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : 1 ≤ e := by show 1 ≤ Nat.clog 2 _ + 1; omega
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) this
  have hden : (1 : ℝ) / 2 ≤ 1 - 1 / 2 ^ e := by linarith
  have hnum : (A : ℝ) * (Bs * (1 / 2 ^ J) + J * (1 / 64) ^ t) + (1 / 2 ^ e) * (A * (M + J * (M : ℝ) ^ (2 * t))) ≤
      3 / (8 * K) := by
    have : (A : ℝ) * (Bs * (1 / 2 ^ J) + J * (1 / 64) ^ t) = A * (Bs * (1 / 2 ^ J)) + A * (J * (1 / 64) ^ t) := by
      ring
    rw [this]
    have h3' : (3 : ℝ) / (8 * K) = 1 / (8 * K) + 1 / (8 * K) + 1 / (8 * K) := by ring
    rw [h3']
    linarith
  have hnum0 : 0 ≤ (A : ℝ) * (Bs * (1 / 2 ^ J) + J * (1 / 64) ^ t) +
      (1 / 2 ^ e) * (A * (M + J * (M : ℝ) ^ (2 * t))) := by positivity
  calc _ ≤ (3 / (8 * (K : ℝ))) / (1 / 2) := div_le_div₀ (by positivity) hnum (by norm_num) hden
    _ = 3 / (4 * (K : ℝ)) := by field_simp; ring

theorem listBound_nonneg (A Bs M J t e : ℕ) (he : 1 ≤ e) :
    0 ≤ ((A : ℝ) * (Bs * (1 / 2 ^ J) + J * (1 / 64) ^ t) + (1 / 2 ^ e) * (A * (M + J * (M : ℝ) ^ (2 * t)))) /
      (1 - 1 / 2 ^ e) := by
  have he2 : (1 : ℝ) / 2 ^ e < 1 := by
    rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
  apply div_nonneg (by positivity)
  linarith

theorem budget_le (G err δ ξ cη nD K : ℝ) (hG : 0 ≤ G) (hnD : 0 < nD) (hK : K = 8 * (G + 1) * nD)
    (herr : err ≤ 1 / (K + 1)) (hδ : δ ≤ 3 / (4 * K)) (hξ : G * ξ ≤ 1 / nD / 8) (hη : 2 * G * cη ≤ 1 / nD) :
    G * err + G * (δ + ξ) + G * cη ≤ 1 / nD := by
  have hKpos : 0 < K := by rw [hK]; positivity
  have h1 : G * err ≤ 1 / nD / 8 := by
    refine (mul_le_mul_of_nonneg_left herr hG).trans ?_
    rw [hK, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : G * δ ≤ 1 / nD / 8 := by
    refine (mul_le_mul_of_nonneg_left hδ hG).trans ?_
    rw [hK, mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h3 : G * cη ≤ 1 / nD / 2 := by linarith
  have h4 : 1 / nD / 8 + (1 / nD / 8 + 1 / nD / 8) + 1 / nD / 2 ≤ 1 / nD := by
    have : 0 < 1 / nD := by positivity
    linarith
  nlinarith

/-! ## The call -/

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- A threshold-top call. -/
abbrev thrReq (n a : ℕ) (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) : PrimRequest :=
  ⟨n, .thr, a, ha, Cs, carriers, translation⟩

section Call
variable (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- The prime surrogate's denominator and the lists' target, `K = 8(|𝒢|+1)n^D`. -/
def thrCallDen : ℕ := 8 * (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) + 1) * n ^ I.D

/-- `A`: the number of digit populations. -/
def thrCallA : ℕ :=
  Fintype.card (ThrEq (I.starParams n hs) Cs algorithm ×
    PrimeIndex (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs)) ×
    Fin (thrDigits (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs)) × Bool)

/-- `B_* = a·4096·cap_aux`. -/
def thrCallBs : ℕ := a * (4096 * ((carriers.length + 1) * (4096 * B.capOf .thr n)))

/-- `M`: the number of occurrences. -/
def thrCallM : ℕ := (thrOccs (I.starParams n hs) Cs).length

def thrCallJ : ℕ :=
  listJ (thrCallA algorithm I hs Cs) (thrCallBs (B := B) carriers (n := n) (a := a)) (thrCallDen algorithm I hs Cs)

def thrCallT : ℕ :=
  listT (thrCallA algorithm I hs Cs) (thrCallBs (B := B) carriers (n := n) (a := a)) (thrCallDen algorithm I hs Cs)

def thrCallE : ℕ :=
  listE (thrCallA algorithm I hs Cs) (thrCallBs (B := B) carriers (n := n) (a := a)) (thrCallM I hs Cs)
    (thrCallDen algorithm I hs Cs)

/-- The call's digit-list reporter (the greedy fixed hash of `filt:soft` at the chosen parameters). -/
noncomputable def thrCallReport : List Bool → ℕ :=
  thrReport (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
    (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs) (thrCallE algorithm I hs Cs carriers)
    (thrCallT algorithm I hs Cs carriers) (thrCallJ algorithm I hs Cs carriers)

/-- **The printed estimate at a `THR` call**. -/
noncomputable def thrCallEstimate (smp : CallSample (I.starParams n hs)) : ℝ :=
  thrEstimate (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
    (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs) (thrCallReport algorithm I hs Cs carriers translation)
    smp.eqv smp.S

/-- The call's THR state matrices (row:matrix), the family the sampler must control. -/
noncomputable def thrCallStates (smp : CallSample (I.starParams n hs))
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (e : GapSeed (I.filterParams .thr n)) (g : ThrEq (I.starParams n hs) Cs algorithm)
    (pr : PrimeIndex (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs))) (s : ZMod pr.val) :
    Fin smp.N → Fin smp.N → ℂ :=
  thrStateAt (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
    (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs) (thrCallReport algorithm I hs Cs carriers translation)
    smp.eqv c e g pr s

end Call

theorem thr_call_error (spectrum : ExpanderSpectrumContract) (theta : PrimeThetaBoundContract)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (h : I.Call (thrReq n a ha Cs carriers translation)) (hs : I.StarAt n)
    (smp : CallSample (I.starParams n hs)) (hQ : 0 < smp.Q)
    (hfeG : (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) * (1 / 2 ^ (I.filterParams .thr n).errExp) ≤
      (n : ℝ) ^ (-(I.D : ℝ)) / 8)
    (ηz : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} → ℝ)
    (hηz : ∀ c e g pr s, ‖sampleError (thrCallStates algorithm I hs Cs carriers translation smp c e g pr s) smp.S‖ /
      (smp.Q * smp.N) ≤ ηz c)
    (hη : 2 * (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
      (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) : ℝ) * uMean ηz ≤
        (n : ℝ) ^ (-(I.D : ℝ))) :
    |thrCallEstimate algorithm I hs Cs carriers translation smp - I.truth (thrReq n a ha Cs carriers translation)| ≤
      (n : ℝ) ^ (-(I.D : ℝ)) := by
  have hn : 0 < n := by
    have h2 : 4 * B.rOf n ≤ n := hs.2.2.1
    have h1 : 2 ≤ B.rOf n := hs.2.1
    omega
  have hN : 0 < smp.N := by
    rw [← Fintype.card_fin smp.N, ← Fintype.card_congr smp.eqv]
    exact Fintype.card_pos_iff.mpr ⟨fun _ => none⟩
  have hmask : I.mask (thrReq n a ha Cs carriers translation) =
      symMask (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) carriers
        (I.filterParams .thr n) := by
    funext e x
    exact mask_of_call I hs e x
  have htruth : I.truth (thrReq n a ha Cs carriers translation) =
      WireExponent3_5.maskedMean (symMask (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        carriers (I.filterParams .thr n)) (fun i => (Cs i).eval) := by
    unfold PrimitiveInputs.truth
    rw [hmask]
    rfl
  have hgates : GatesIn (fun i => thrGates (Cs i)) carriers := h.1
  have hFlen : ∀ X ∈ carriers, 2 * X.length ≤ (I.filterParams .thr n).len :=
    fun X hX => Nat.mul_le_mul_left 2 (h.2.1 X hX).1
  have hcap1 := B.capOf_pos .thr n
  have ht : 1 ≤ thrCallT algorithm I hs Cs carriers := by unfold thrCallT listT; omega
  have he : 1 ≤ thrCallE algorithm I hs Cs carriers := by unfold thrCallE listE; omega
  have hlist := thr_list_failure (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
    (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs) spectrum hgates hcap1
    (thrCallE algorithm I hs Cs carriers) (thrCallT algorithm I hs Cs carriers) (thrCallJ algorithm I hs Cs carriers)
    ht he
  have hδ0 : 0 ≤ thrListBound (I.starParams n hs) Cs carriers (I.filterParams .thr n) algorithm
      (thrCallDen algorithm I hs Cs) (thrCallE algorithm I hs Cs carriers) (thrCallT algorithm I hs Cs carriers)
      (thrCallJ algorithm I hs Cs carriers) :=
    listBound_nonneg (thrCallA algorithm I hs Cs) (thrCallBs (B := B) carriers (n := n) (a := a)) (thrCallM I hs Cs)
      (thrCallJ algorithm I hs Cs carriers) (thrCallT algorithm I hs Cs carriers) (thrCallE algorithm I hs Cs carriers) he
  have hmain := thr_primitive_error (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
    (I.filterParams .thr n) algorithm theta (thrCallDen algorithm I hs Cs)
    (thrCallReport algorithm I hs Cs carriers translation) smp.eqv smp.S spectrum hFlen hcap1 _ hδ0 hlist hN hQ ηz
    (uMean ηz) hηz le_rfl
  rw [htruth]
  refine (hmain.trans ?_)
  -- the error budget
  have hrp := rpow_neg_eq n I.D
  rw [hrp] at hfeG hη ⊢
  have hK1 : 1 ≤ thrCallDen algorithm I hs Cs := by
    unfold thrCallDen
    have : 1 ≤ n ^ I.D := Nat.one_le_pow _ _ hn
    nlinarith
  have hKreal : ((thrCallDen algorithm I hs Cs : ℕ) : ℝ) =
      8 * ((Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) + 1) * (n : ℝ) ^ I.D := by
    unfold thrCallDen; push_cast; ring
  have herr := tunedFiniteFamilyPrimeSurrogateCertificate_error_le theta
    (thrRealize (I.starParams n hs) Cs algorithm) (thrCallDen algorithm I hs Cs)
  have herr' : (thrCert (I.starParams n hs) Cs algorithm theta (thrCallDen algorithm I hs Cs)).error ≤
      1 / ((thrCallDen algorithm I hs Cs : ℝ) + 1) := by
    refine herr.trans (le_of_eq ?_)
    push_cast; ring
  have hl := list_params_bound (thrCallA algorithm I hs Cs) (thrCallBs (B := B) carriers (n := n) (a := a))
    (thrCallM I hs Cs) (thrCallDen algorithm I hs Cs) hK1
  have hb := budget_le (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm))
    (thrCert (I.starParams n hs) Cs algorithm theta (thrCallDen algorithm I hs Cs)).error
    (thrListBound (I.starParams n hs) Cs carriers (I.filterParams .thr n) algorithm
      (thrCallDen algorithm I hs Cs) (thrCallE algorithm I hs Cs carriers) (thrCallT algorithm I hs Cs carriers)
      (thrCallJ algorithm I hs Cs carriers))
    (1 / 2 ^ (I.filterParams .thr n).errExp)
    ((thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) : ℝ) * uMean ηz)
    ((n : ℝ) ^ I.D) (thrCallDen algorithm I hs Cs) (Nat.cast_nonneg _) (by positivity) hKreal herr' hl hfeG
    (by linarith)
  calc _ = (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
          (thrCert (I.starParams n hs) Cs algorithm theta (thrCallDen algorithm I hs Cs)).error +
        (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
          (thrListBound (I.starParams n hs) Cs carriers (I.filterParams .thr n) algorithm
            (thrCallDen algorithm I hs Cs) (thrCallE algorithm I hs Cs carriers) (thrCallT algorithm I hs Cs carriers)
            (thrCallJ algorithm I hs Cs carriers) + 1 / 2 ^ (I.filterParams .thr n).errExp) +
        (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
          ((thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) : ℝ) * uMean ηz) := by ring
    _ ≤ _ := hb

end NearCubicWires.WireExponent3_5.Primitive

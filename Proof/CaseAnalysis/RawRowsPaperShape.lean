import Proof.CaseAnalysis.RawRowsLoad

/-! The paper's summed graded windows and logarithmic mode factors, before
choosing the positive wire-cap coefficient and the common arity onset. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierTouching
open RepairOrdinary.CloseoutRowsRawLogShape
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem touchingCost_le_occurrenceLength
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) :
    touchingCost (occurrenceSupport occurrences) selected ≤
      occurrences.length := by
  unfold touchingCost SupplierTouching.touchIndicator
  calc
    (∑ gate : Fin occurrences.length,
      if Disjoint selected (occurrenceSupport occurrences gate) then 0
      else 1) ≤
        ∑ _gate : Fin occurrences.length, 1 := by
      apply Finset.sum_le_sum
      intro gate _
      split <;> omega
    _ = occurrences.length := by simp

theorem source_le_two_pow_logScale (q : ℕ) :
    q ≤ 2 ^ logScale q := by
  exact (Nat.le_add_right q 2).trans
    (Nat.le_pow_clog (by omega) (q + 2))

theorem canonicalGradedDepth_le_logScale_of_activeBound
    (q activeBound : ℕ) (hactive : activeBound ≤ 4 * q ^ 3) :
    canonicalGradedDepth activeBound ≤ 10 * (logScale q + 1) := by
  have hqPower := Nat.pow_le_pow_left (source_le_two_pow_logScale q) 3
  have hinput : 256 * activeBound ≤ 2 ^ (3 * logScale q + 10) := by
    calc
      256 * activeBound ≤ 256 * (4 * q ^ 3) :=
        Nat.mul_le_mul_left 256 hactive
      _ = 1024 * q ^ 3 := by ring
      _ ≤ 1024 * (2 ^ logScale q) ^ 3 :=
        Nat.mul_le_mul_left 1024 hqPower
      _ = 2 ^ (3 * logScale q + 10) := by
        rw [show 1024 = 2 ^ 10 by norm_num, ← pow_mul, ← pow_add]
        congr 1
        omega
  unfold canonicalGradedDepth
  have hdepth := Nat.clog_le_of_le_pow hinput
  omega

theorem window_sum_real {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L : ℕ) :
    (windowSum gs L : ℝ) ≤ 384*Real.sqrt
      (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L))+65*(rowDepth gs L) := by
  have h := sum_gradedWindow_cast_le
    (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L)) (rowDepth gs L)
  unfold windowSum
  push_cast
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [executableGradedWindow_eq_gradedWindow]

theorem window_depth_shape {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L : ℕ)
    (hpop : gs.length ≤ 4*q^3) :
    ((windowSum gs L+rowDepth gs L+1 : ℕ) : ℝ) ≤
      1400*(Real.sqrt (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L))+
        (logScale q : ℝ)) := by
  have hw := window_sum_real gs L
  have hd := canonicalGradedDepth_le_logScale_of_activeBound q _
    ((touchingCost_le_occurrenceLength gs (normalizedLiveSet gs L)).trans hpop)
  change rowDepth gs L ≤ 10*(logScale q+1) at hd
  have hl : (1 : ℝ) ≤ logScale q := by exact_mod_cast logScale_pos q
  have hd' : (rowDepth gs L : ℝ) ≤ 10*((logScale q : ℝ)+1) := by exact_mod_cast hd
  push_cast
  nlinarith [Real.sqrt_nonneg (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L))]

def shapeCoefficient (cz ct ce kappa : ℕ) := 200000*(cz+1)*(ct+1)*(ce+1)*(kappa+2)

theorem load_shape (z t W h ell a K ell0 cz ct ce kappa u v : ℕ) (root : ℝ)
    (hroot : 0 ≤ root) (hlog : 1 ≤ ell0) (ha : a ≤ ell)
    (hz : z+1 ≤ (cz+1)*ell0^u) (ht : t+1 ≤ (ct+1)*ell0^v)
    (he : ell+1 ≤ (ce+1)*ell0) (hK : K ≤ kappa*ell0)
    (hW : ((W+h+1 : ℕ) : ℝ) ≤ 1400*(root+ell0)) :
    ((K+rowWidth z t W h ell a*(K+2) : ℕ) : ℝ) ≤
      (shapeCoefficient cz ct ce kappa : ℝ)*(root+ell0)*(ell0 : ℝ)^(u+v+2) := by
  let ellR : ℝ := ell0
  let F : ℝ := (cz+1)*(ct+1)*(ce+1)*(kappa+2)
  have hL : 1 ≤ ellR := by dsimp only [ellR]; exact_mod_cast hlog
  have hL0 : 0 ≤ ellR := by positivity
  have hZ : (z : ℝ)+1 ≤ (cz+1)*ellR^u := by dsimp only [ellR]; exact_mod_cast hz
  have hT : (t : ℝ)+1 ≤ (ct+1)*ellR^v := by dsimp only [ellR]; exact_mod_cast ht
  have hE : (ell : ℝ)+1 ≤ (ce+1)*ellR := by dsimp only [ellR]; exact_mod_cast he
  have hK' : (K : ℝ) ≤ kappa*ellR := by dsimp only [ellR]; exact_mod_cast hK
  have hW' : (W : ℝ)+h+1 ≤ 1400*(root+ellR) := by exact_mod_cast hW
  have hK2 : (K : ℝ)+2 ≤ (kappa+2)*ellR := by nlinarith
  have hpower : 1 ≤ ellR^(u+v+2) := one_le_pow₀ hL
  have hF : (kappa : ℝ)+2 ≤ F := by
    dsimp only [F]
    calc
      _ = 1*1*1*((kappa : ℝ)+2) := by ring
      _ ≤ _ := by gcongr <;> linarith [Nat.cast_nonneg (α := ℝ) cz, Nat.cast_nonneg (α := ℝ) ct, Nat.cast_nonneg (α := ℝ) ce]
  have hF0 : 0 ≤ F := by positivity
  have hsmall : (K : ℝ) ≤ F*(root+ellR)*ellR^(u+v+2) := by
    calc
      _ ≤ (kappa+2)*ellR := by nlinarith
      _ ≤ F*(root+ellR) := by gcongr; linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpower
  have hraw := digit_load K z t W h ell a ha
  have hrawR : ((K+rowWidth z t W h ell a*(K+2) : ℕ) : ℝ) ≤
      K+128*((z : ℝ)+1)*((t : ℝ)+1)*(W+h+1)*((ell : ℝ)+1)*(K+2) := by
    exact_mod_cast hraw
  have hmain : 128*((z : ℝ)+1)*((t : ℝ)+1)*(W+h+1)*((ell : ℝ)+1)*(K+2) ≤
      179200*F*(root+ellR)*ellR^(u+v+2) := by
    calc
      _ ≤ 128*((cz+1)*ellR^u)*((ct+1)*ellR^v)*(1400*(root+ellR))*
          ((ce+1)*ellR)*((kappa+2)*ellR) := by gcongr
      _ = _ := by dsimp only [F]; rw [pow_add,pow_add,pow_two]; ring
  have htotal := hrawR.trans (add_le_add le_rfl hmain)
  unfold shapeCoefficient
  push_cast
  have hcoef : 200000*((cz : ℝ)+1)*(ct+1)*(ce+1)*(kappa+2)=200000*F := by dsimp only [F]; ring
  rw [hcoef]
  change _ ≤ (200000*F)*(root+ellR)*ellR^(u+v+2)
  push_cast at htotal
  have hnonneg : 0 ≤ F*(root+ellR)*ellR^(u+v+2) := by positivity
  nlinarith only [hsmall,htotal,hnonneg]

end
end NearCubicWires.RepairSource.CloseoutRawRows

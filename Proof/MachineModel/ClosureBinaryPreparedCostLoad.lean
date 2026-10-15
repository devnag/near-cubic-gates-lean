import Proof.MachineModel.ClosureBinaryPreparedCost
import Proof.MachineModel.ClosureCompactSourceCost
import Proof.MachineModel.ClosureCompactModeCost

/-! Additive preparation has one residual exponential after the existing
load gate is applied. The internal-syntax preparation ledger is unchanged.
The source radix, original degree and selected digit-load instantiations
remain explicitly separated from this arithmetic consequence. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryPreparedCost
open RepairOrdinary RepairRepresentation ExtIncidence
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput

theorem envelope_bound (q C D K w : Nat) :
    envelope q C D K w+1 ≤ 32*(q+C+D+K+w+2)^4*2^(K+w) := by
  let T := q+C+D+K+w+2
  let Y := 2^K
  let Z := 2^w
  have ht : 1 ≤ T := by dsimp [T]; omega
  have hy : 1 ≤ Y := Nat.one_le_two_pow
  have hz : 1 ≤ Z := Nat.one_le_two_pow
  have hq : q+1 ≤ T := by dsimp [T]; omega
  have hc : C+1 ≤ T := by dsimp [T]; omega
  have hd : D ≤ T := by dsimp [T]; omega
  have hk : K+1 ≤ T := by dsimp [T]; omega
  have hprod : Y*C+2 ≤ 2*Y*T := by nlinarith [Nat.mul_le_mul_left Y hc]
  have cache : 4*(Y*C+2)*(q+1)*(C+1) ≤ 8*Y*T^3 := by
    calc
      _ ≤ 4*(2*Y*T)*T*T := Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 hprod) hq) hc
      _ = _ := by ring
  have width : C*(D*(K+1))+(K+1) ≤ T^3+T := by
    calc
      _ ≤ T*(T*T)+T := Nat.add_le_add (Nat.mul_le_mul (by omega) (Nat.mul_le_mul hd hk)) hk
      _ = _ := by ring
  have raw : rawBound C D K w ≤ 2*Y*Z*T^2+2*Z+1 := by
    calc
      _ ≤ Z*(T*(2*Y*T)+2)+1 := Nat.add_le_add_right
        (Nat.mul_le_mul_left Z (Nat.add_le_add_right (Nat.mul_le_mul hd hprod) 2)) 1
      _ = _ := by ring
  let H := T^4*(Y*Z)
  have ht1 : T ≤ T^4 := by simpa only [pow_one] using Nat.pow_le_pow_right ht (by decide : 1 ≤ 4)
  have ht2 : T^2 ≤ T^4 := Nat.pow_le_pow_right ht (by decide)
  have ht3 : T^3 ≤ T^4 := Nat.pow_le_pow_right ht (by decide)
  have ht4 : 1 ≤ T^4 := Nat.one_le_pow _ _ ht
  have hyz : 1 ≤ Y*Z := by simpa only [one_mul] using Nat.mul_le_mul hy hz
  have hT : T ≤ H := ht1.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hYZ : Y ≤ Y*Z := Nat.le_mul_of_pos_right _ (by omega)
  have hZY : Z ≤ Y*Z := Nat.le_mul_of_pos_left _ (by omega)
  have hY : Y ≤ H := hYZ.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hZ : Z ≤ H := hZY.trans (Nat.le_mul_of_pos_left _ (by omega))
  have h3 : Y*T^3 ≤ H := by
    calc
      _ ≤ (Y*Z)*T^4 := Nat.mul_le_mul hYZ ht3
      _ = _ := by dsimp only [H]; ac_rfl
  have h2 : Y*Z*T^2 ≤ H := by
    calc
      _ ≤ (Y*Z)*T^4 := Nat.mul_le_mul_left _ ht2
      _ = _ := by dsimp only [H]; ac_rfl
  have hW : T^3 ≤ H := ht3.trans (Nat.le_mul_of_pos_right _ (by omega))
  have h1 : 1 ≤ H := ht.trans hT
  have cacheH : 4*(Y*C+2)*(q+1)*(C+1) ≤ 8*H := cache.trans (by
    simpa only [mul_assoc] using Nat.mul_le_mul_left 8 h3)
  have widthH : C*(D*(K+1))+(K+1) ≤ 2*H := by omega
  have rawH : rawBound C D K w ≤ 5*H := by
    have htwice : 2*Y*Z*T^2 ≤ 2*H := by
      simpa only [mul_assoc] using Nat.mul_le_mul_left 2 h2
    omega
  have total : envelope q C D K w+1 ≤ 32*H := by
    unfold envelope
    change q+C+D+K+w+Y+4*(Y*C+2)*(q+1)*(C+1)+
      (C*(D*(K+1))+(K+1))+rawBound C D K w+1+1 ≤ _
    have hsum : q+C+D+K+w+2=T := rfl
    omega
  simpa only [H,T,Y,Z,pow_add,mul_assoc] using total

theorem loaded_exponent (K w s : Nat) (hload : 200*(K+w*(K+2)) ≤ s) :
    22*(K+w)+w*(K+2) ≤ s := by nlinarith

/-- Eightfold exponent slack survives; polynomial/onset accounting must not
erase it by replacing this prematurely with the full residual table budget. -/
theorem loaded_exponent_slack (K w s : Nat) (hload : 200*(K+w*(K+2)) ≤ s) :
    8*(22*(K+w)+w*(K+2)) ≤ s := by nlinarith

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) (C D w : Nat)

theorem budget_exponent (hcache : CompactBounds.radix a live occ ≤ C)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost D P)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w) :
    BinaryPreparedWriter.budget a live occ s harity P w D (rawBound C D live.card w) ≤
      2^230*(q+C+D+live.card+w+2)^88*2^(22*(live.card+w)+w*(live.card+2)) := by
  calc
    _ ≤ 2^120*(envelope q C D live.card w+1)^22*2^(w*(live.card+2)) :=
      budget_bound a live occ s harity P C D w hcache hdegree hmon
    _ ≤ 2^120*(32*(q+C+D+live.card+w+2)^4*2^(live.card+w))^22*2^(w*(live.card+2)) := by
      gcongr
      exact envelope_bound _ _ _ _ _
    _ = _ := by
      rw [mul_pow,mul_pow,←pow_mul,←pow_mul]
      rw [show (32 : Nat)^22=2^110 by norm_num]
      rw [show (230 : Nat)=120+110 by decide,pow_add,
        show 22*(live.card+w)=(live.card+w)*22 by omega,pow_add]
      norm_num only [Nat.reduceMul]
      have reorder (A B C D E : Nat) : A*(B*C*D)*E=(A*B)*C*(D*E) := by ac_rfl
      exact reorder _ _ _ _ _

theorem budget_residual (hcache : CompactBounds.radix a live occ ≤ C)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost D P)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hload : 200*(live.card+w*(live.card+2)) ≤ s) :
    BinaryPreparedWriter.budget a live occ s harity P w D (rawBound C D live.card w) ≤
      2^230*(q+C+D+live.card+w+2)^88*2^s := by
  exact (budget_exponent a live occ s harity P C D w hcache hdegree hmon).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (loaded_exponent _ _ _ hload)))

theorem budget_residual_slack (hcache : CompactBounds.radix a live occ ≤ C)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost D P)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hload : 200*(live.card+w*(live.card+2)) ≤ s) :
    BinaryPreparedWriter.budget a live occ s harity P w D (rawBound C D live.card w) ≤
      2^230*(q+C+D+live.card+w+2)^88*2^(s/8) := by
  have he := loaded_exponent_slack live.card w s hload
  exact (budget_exponent a live occ s harity P C D w hcache hdegree hmon).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))

theorem budget_polynomial (c e : Nat)
    (hcache : CompactBounds.radix a live occ ≤ c*(q+1)^e)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost D P) (hD : D ≤ q+1)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hload : 200*(live.card+w*(live.card+2)) ≤ s) :
    BinaryPreparedWriter.budget a live occ s harity P w D (rawBound (c*(q+1)^e) D live.card w) ≤
      (2^230*(c+5)^88)*(q+1)^((e+1)*88)*2^(s/8) := by
  have hK : live.card ≤ q := (Finset.card_le_univ _).trans_eq (Fintype.card_fin q)
  have hs : s ≤ q := by
    have hc : liveᶜ.card ≤ q := (Finset.card_le_univ _).trans_eq (Fintype.card_fin q)
    omega
  have hw : w ≤ q := by nlinarith
  have hp : q+1 ≤ (q+1)^(e+1) := Nat.le_self_pow (by omega) _
  have hc : c*(q+1)^e ≤ c*(q+1)^(e+1) :=
    Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega) (by omega))
  have hbase : q+c*(q+1)^e+D+live.card+w+2 ≤ (c+5)*(q+1)^(e+1) := by nlinarith
  calc
    _ ≤ 2^230*(q+c*(q+1)^e+D+live.card+w+2)^88*2^(s/8) :=
      budget_residual_slack a live occ s harity P (c*(q+1)^e) D w hcache hdegree hmon hload
    _ ≤ 2^230*((c+5)*(q+1)^(e+1))^88*2^(s/8) := by gcongr
    _ = _ := by rw [mul_pow,←pow_mul,←mul_assoc]

end NearCubicWires.P1Closure.BinaryPreparedCost

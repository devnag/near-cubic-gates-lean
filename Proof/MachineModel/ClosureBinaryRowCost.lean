import Proof.MachineModel.ClosureBinaryReusableRow
import Proof.MachineModel.ClosureCompactModeCost

/-! Actual binary-row driver accounting: header support stays linear and
additive, cut scanning retains load slack, and the signed table appears once.
The source radix and original degree, not the replicated pool, price p. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryRowCost
open RepairRepresentation RepairOrdinary ExtIncidence
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput CloseoutRowsEstimator

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

variable {q : Nat} (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) (w degree : Nat)
  (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
  (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
  (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)

local notation "row" => BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree

include harity in
theorem arity_eq : s+live.card=q := by
  have h := Finset.card_add_card_compl live
  rw [Fintype.card_fin] at h
  omega

theorem width_bound : (row).p ≤ CompactBounds.radix a live occ*(degree*(live.card+1))+(live.card+1) := by
  change CompactBounds.radix a live occ*(min degree (BinaryPool.pool a live occ s harity).length*
    (live.card+1))+(live.card+1) ≤ _
  gcongr
  exact Nat.min_le_left _ _

theorem cuts_bound : (row).cuts.length ≤ 2^(2*(live.card+w*(live.card+2))) := by
  letI := BinaryRequest.radix a live occ s harity degree
  have hw := bank_rows_le a live occ s harity P w hmon
  have hc := P1CompactCloseoutRowsSharedDigits.batch_perm (BinaryPool.pool a live occ s harity)
    (live.card+1) w (bank a live occ s harity P) hw
  have ho := CloseoutRowsSharedDigits.batch_perm (BinaryPool.pool a live occ s harity)
    (live.card+1) w (bank a live occ s harity P) hw
  have hcl := hc.length_eq
  have hol := ho.length_eq
  rw [RowPowerBinLift.batch_length] at hcl hol
  have he : (row).cuts.length=
      ((bank a live occ s harity P).flatMap
        (CloseoutRowsSharedDigits.cuts (BinaryPool.pool a live occ s harity) (live.card+1) w)).length :=
    hcl.trans hol.symm
  rw [he]
  exact CloseoutRawRows.raw_cuts_bound (BinaryPool.pool a live occ s harity) live.card w
    (bank a live occ s harity P) (le_of_eq (bank_length a live occ s harity P)) hw hpos

theorem width_polynomial (c e : Nat)
    (hcache : CompactBounds.radix a live occ ≤ c*(q+1)^e) (hdeg : degree ≤ q+1) :
    (row).p ≤ (c+1)*(q+1)^(e+2) := by
  have hK : live.card+1 ≤ q+1 := by have h := arity_eq live s harity; omega
  have hp : q+1 ≤ (q+1)^(e+2) := Nat.le_self_pow (by omega) _
  calc
    _ ≤ CompactBounds.radix a live occ*(degree*(live.card+1))+(live.card+1) :=
      width_bound a live occ s harity P w degree hs hmon hpos hload hdegree
    _ ≤ (c*(q+1)^e)*((q+1)*(q+1))+(q+1) := by gcongr
    _ = c*(q+1)^(e+2)+(q+1) := by rw [pow_add,pow_two]; ring
    _ ≤ _ := by nlinarith

theorem table_bound (c e : Nat)
    (hcache : CompactBounds.radix a live occ ≤ c*(q+1)^e) (hdeg : degree ≤ q+1) :
    Driver.tableValue printer (row).d (row).p ≤ CompactCost.tableCoefficient printer c*
      (2^s*(q+1)^((e+2)*CompetitorCrossScheduler.exponent printer)) := by
  have h := CompactCost.table_polynomial printer q live.card s
    (CompactBounds.radix a live occ) degree c e (arity_eq live s harity) hcache hdeg
  have hs' : q-live.card=s := by have h := arity_eq live s harity; omega
  rw [hs'] at h
  apply le_trans ?_ h
  change Driver.tableValue printer ((s+1)/2) (row).p ≤ _
  unfold Driver.tableValue
  gcongr
  exact width_bound a live occ s harity P w degree hs hmon hpos hload hdegree

theorem driver_bound (C c e : Nat)
    (hcache : CompactBounds.radix a live occ ≤ c*(q+1)^e) (hdeg : degree ≤ q+1) :
    Driver.value printer (row).d (row).p (row).cuts.length C ≤
      64*(C+1)+2^21*(c+4)^3*(q+1)^((e+2)*3)*2^(s/32)+
        CompactCost.tableCoefficient printer c*(2^s*(q+1)^((e+2)*CompetitorCrossScheduler.exponent printer)) := by
  let T := (q+1)^(e+2)
  let E := 2^(2*(live.card+w*(live.card+2)))
  have ht : q+1 ≤ T := Nat.le_self_pow (by omega) _
  have ht1 : 1 ≤ T := by omega
  have he : 1 ≤ E := Nat.one_le_two_pow
  have hd : (row).d ≤ T := by
    change (s+1)/2 ≤ T
    have h := arity_eq live s harity
    omega
  have hp : (row).p ≤ (c+1)*T := width_polynomial a live occ s harity P w degree
    hs hmon hpos hload hdegree c e hcache hdeg
  have hg : (row).cuts.length ≤ E := cuts_bound a live occ s harity P w degree
    hs hmon hpos hload hdegree
  have hm : (row).d+(row).p+(row).cuts.length+1 ≤ ((c+4)*T)*E := by
    have hpE := Nat.le_mul_of_pos_right ((c+4)*T) (by omega : 0 < E)
    nlinarith only [hd,hp,hg,ht1,he,hpE,Nat.mul_le_mul_right E ht1]
  have hexp : (2*(live.card+w*(live.card+2)))*3 ≤ s/32 := by omega
  have hcube : E^3 ≤ 2^(s/32) := by
    dsimp only [E]
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) hexp
  have prep : 2000000*((row).d+(row).p+(row).cuts.length+1)^3 ≤
      2^21*(c+4)^3*(q+1)^((e+2)*3)*2^(s/32) := by
    calc
      _ ≤ 2^21*(((c+4)*T)*E)^3 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hm 3)
      _ = (2^21*(c+4)^3*T^3)*E^3 := by rw [mul_pow,mul_pow]; ring
      _ ≤ (2^21*(c+4)^3*T^3)*2^(s/32) := Nat.mul_le_mul_left _ hcube
      _ = _ := by dsimp only [T]; rw [←pow_mul]
  have table := table_bound a printer live occ s harity P w degree hs hmon hpos hload hdegree c e hcache hdeg
  exact Nat.add_le_add (Nat.add_le_add_left prep _) table

end NearCubicWires.P1Closure.BinaryRowCost

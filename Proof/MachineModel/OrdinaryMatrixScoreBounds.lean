import Proof.MachineModel.OrdinaryMatrixScoreWeightLoad

/-! Numeric invariants for the actual sign/assignment-selected accumulator.
The two branch predicates match ScoreWeightSelect's physical flags. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBatch
open LocalBitMultitape SupplierPrinter SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def term (negative : Bool) (assignment : ℕ) (wi : ℤ×ℕ) : ℕ :=
  if assignment.testBit wi.2 && (decide (wi.1<0)==negative) then wi.1.natAbs else 0
def part (negative : Bool) (weights : List ℤ) (assignment : ℕ) : ℕ :=
  (weights.zipIdx.map (term negative assignment)).sum

theorem term_identity (assignment : ℕ) (wi : ℤ×ℕ) :
    (if assignment.testBit wi.2 then wi.1 else 0)=
      (term false assignment wi : ℤ)-(term true assignment wi : ℤ) := by
  obtain ⟨w,i⟩ := wi
  cases hb : assignment.testBit i <;> cases w <;> simp [term,hb]
  omega

theorem parts_identity (assignment : ℕ) (xs : List (ℤ×ℕ)) :
    (xs.map (fun wi => if assignment.testBit wi.2 then wi.1 else 0)).sum=
      ((xs.map (term false assignment)).sum : ℤ)-((xs.map (term true assignment)).sum : ℤ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]
    rw [term_identity]
    ring

theorem linearForm_parts (weights : List ℤ) (assignment : ℕ) :
    linearForm weights assignment=(part false weights assignment : ℤ)-(part true weights assignment : ℤ) :=
  parts_identity assignment weights.zipIdx

theorem sum_bounded (xs : List ℕ) (B : ℕ) (hb : ∀ x ∈ xs,x≤B) : xs.sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (by intro y hy; exact hb y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem part_bound (weights : List ℤ) (assignment p : ℕ) (negative : Bool)
    (hf : ∀ w ∈ weights,w.natAbs<2^p) : part negative weights assignment≤weights.length*2^p := by
  have h := sum_bounded (weights.zipIdx.map (term negative assignment)) (2^p) (by
    intro x hx
    obtain ⟨wi,hw,rfl⟩ := List.mem_map.mp hx
    have hb := hf wi.1 (List.fst_mem_of_mem_zipIdx hw)
    unfold term
    split <;> omega)
  simpa [part] using h

theorem linearForm_bounds (weights : List ℤ) (assignment p : ℕ)
    (hf : ∀ w ∈ weights,w.natAbs<2^p) :
    -(weights.length*2^p : ℕ)≤linearForm weights assignment ∧
      linearForm weights assignment≤(weights.length*2^p : ℕ) := by
  have hp : (part false weights assignment : ℤ)≤(weights.length*2^p : ℕ) := by
    exact_mod_cast part_bound weights assignment p false hf
  have hn : (part true weights assignment : ℤ)≤(weights.length*2^p : ℕ) := by
    exact_mod_cast part_bound weights assignment p true hf
  rw [linearForm_parts]
  omega

theorem score_bound (r : Request) : (r.width+1)*2^r.p<2^r.S := by
  have hd : r.d+1≤2^natBitLength r.d := Nat.lt_pow_succ_log_self (by decide) r.d
  have hw := r.widthLe
  have hp : 0<2^r.p := Nat.pow_pos (by decide)
  calc
    _ ≤ (2*r.d+1)*2^r.p := Nat.mul_le_mul_right _ (by omega)
    _ < (4*2^natBitLength r.d)*2^r.p := Nat.mul_lt_mul_of_pos_right (by omega) hp
    _ = 2^r.S := by unfold Request.S; rw [Nat.pow_add,Nat.pow_add]; ring

theorem score_bounds (r : Request) (gate : Fin r.Gates) :
    (∀ row,-(2^r.S : ℕ)≤leftScore r row gate ∧ leftScore r row gate<(2^r.S : ℕ)) ∧
    (∀ col,-(2^r.S : ℕ)≤rightScore r gate col ∧ rightScore r gate col<(2^r.S : ℕ)) := by
  have hc : r.cuts.get gate∈r.cuts := List.get_mem _ _
  obtain ⟨hl,hr⟩ := r.lengths _ hc
  obtain ⟨hw,ht,_⟩ := r.fits _ hc
  have hL : ∀ w ∈ (r.cuts.get gate).leftWeights,w.natAbs<2^r.p := by
    intro w hm; exact hw w (List.mem_append_left _ hm)
  have hR : ∀ w ∈ (r.cuts.get gate).rightWeights,w.natAbs<2^r.p := by
    intro w hm; exact hw w (List.mem_append_right _ hm)
  have hb : (((r.width+1)*2^r.p : ℕ) : ℤ)<(2^r.S : ℕ) := by exact_mod_cast score_bound r
  have hθ : ((r.cuts.get gate).threshold.natAbs : ℤ)<(2^r.p : ℕ) := by exact_mod_cast ht
  have hθl : -((r.cuts.get gate).threshold.natAbs : ℤ) ≤ (r.cuts.get gate).threshold := by
    simpa only [Int.natCast_natAbs] using neg_abs_le (r.cuts.get gate).threshold
  have hθu : (r.cuts.get gate).threshold ≤ ((r.cuts.get gate).threshold.natAbs : ℤ) := Int.le_natAbs
  push_cast at hθ hθl hθu
  constructor
  · intro row
    have hs := linearForm_bounds (r.cuts.get gate).leftWeights (r.phi row.val) r.p hL
    rw [hl] at hs
    change -(2^r.S : ℕ)≤(r.cuts.get gate).threshold-linearForm _ _ ∧
      (r.cuts.get gate).threshold-linearForm _ _<(2^r.S : ℕ)
    push_cast at hb hs ⊢
    constructor <;> nlinarith only [hb,hs.1,hs.2,hθ,hθl,hθu]
  · intro col
    have hs := linearForm_bounds (r.cuts.get gate).rightWeights (r.phi col.val) r.p hR
    rw [hr] at hs
    change -(2^r.S : ℕ)≤linearForm _ _ ∧ linearForm _ _<(2^r.S : ℕ)
    push_cast at hb hs ⊢
    have hp : (0 : ℤ)≤2^r.p := by positivity
    constructor <;> nlinarith only [hb,hs.1,hs.2,hp]

theorem score_lo (r : Request) : ∀ gate copy,
    -(2^r.S : ℕ)≤ stableDominanceCopyScore (leftScore r) (rightScore r) gate copy := by
  intro gate copy
  cases copy with
  | inl row => exact ((score_bounds r gate).1 row).1
  | inr col => exact ((score_bounds r gate).2 col).1

theorem score_hi (r : Request) : ∀ gate copy,
    stableDominanceCopyScore (leftScore r) (rightScore r) gate copy<(2^r.S : ℕ) := by
  intro gate copy
  cases copy with
  | inl row => exact ((score_bounds r gate).1 row).2
  | inr col => exact ((score_bounds r gate).2 col).2

theorem common_width (r : Request) : r.M=r.d+3 := by
  have hu : r.U+r.U=2^(r.d+1) := by unfold Request.U; rw [Nat.pow_succ]; omega
  unfold Request.M natBitLength
  rw [hu,Nat.log_pow (by decide)]

end NearCubicWires.RepairOrdinary.MatrixScoreBatch

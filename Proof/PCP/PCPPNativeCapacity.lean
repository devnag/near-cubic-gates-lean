import Proof.PCP.PCPPNativeCapacityBank
import Proof.PCP.PCPSerializerCapacityPower

/-! Physically evaluate one common C/F/G bank from the retained measured W.
The fixed native caller chooses D/K once; all three actual unary results
share that same input counter and are charged before entering either loop. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCapacityCold
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def degree (D : ℕ) (j : Fin 3) := if j=2 then D+1 else D
def coefficient (K : ℕ) (j : Fin 3) := if j=0 then K else if j=1 then 32*K else 4096*K
def width (D : ℕ) := DimensionPolynomial.tapes (D+1)
def tapes (D : ℕ) := 1+3*width D
def slots (D : ℕ) (j : Fin 3) (i : Fin (DimensionPolynomial.tapes (degree D j))) : Fin (tapes D) :=
  ⟨if i.val=0 then 0 else 1+j.val*width D+i.val,by
    have hi := i.isLt
    have hj := j.isLt
    have hd : degree D j ≤ D+1 := by unfold degree; split_ifs <;> omega
    have hw : i.val < width D := by dsimp [width,DimensionPolynomial.tapes]; dsimp [DimensionPolynomial.tapes] at hi; omega
    have hjw : j.val*width D ≤ 2*width D := Nat.mul_le_mul_right _ (by omega)
    dsimp [tapes]
    split_ifs <;> omega⟩
theorem slots_injective (D : ℕ) (j : Fin 3) : Function.Injective (slots D j) := by
  intro a b h
  have hv := congrArg Fin.val h
  dsimp only [slots] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem slots_disjoint (D : ℕ) (j k : Fin 3) (hjk : j≠k)
    (i : Fin (DimensionPolynomial.tapes (degree D j)))
    (l : Fin (DimensionPolynomial.tapes (degree D k))) (hl : l.val≠0) : slots D j i≠slots D k l := by
  have hd (a : Fin 3) : degree D a ≤ D+1 := by unfold degree; split_ifs <;> omega
  have hi : i.val < width D := by have h := i.isLt; dsimp [width,DimensionPolynomial.tapes] at *; have hdj := hd j; omega
  have hli : l.val < width D := by have h := l.isLt; dsimp [width,DimensionPolynomial.tapes] at *; have hdk := hd k; omega
  intro he
  have hv := congrArg Fin.val he
  simp only [slots,if_neg hl] at hv
  split_ifs at hv with hz
  · omega
  · have hval : j.val≠k.val := fun h => hjk (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hm := Nat.mul_le_mul_right (width D) (show j.val+1 ≤ k.val by omega)
      nlinarith
    · have hm := Nat.mul_le_mul_right (width D) (show k.val+1 ≤ j.val by omega)
      nlinarith

def input (D W : ℕ) : Fin (tapes D) → List Bool := fun i => if i.val=0 then List.replicate W true else []
noncomputable def program (D K : ℕ) (j : Fin 3) :=
  RecoveryFocus.machine (slots D j) (PCPSerializerCapacity.Power.machine (degree D j) (coefficient K j))
noncomputable def machine (D K : ℕ) :=
  Composition.machine (Composition.machine (program D K 0) (program D K 1)) (program D K 2)
def value (D K W : ℕ) (j : Fin 3) := coefficient K j*(W+1)^degree D j
def outputSlot (D : ℕ) (j : Fin 3) := slots D j (PCPSerializerCapacity.Power.outputSlot (degree D j))
def budget (D K W : ℕ) :=
  PCPSerializerCapacity.Power.budget D K W+1+PCPSerializerCapacity.Power.budget D (32*K) W+1+
    PCPSerializerCapacity.Power.budget (D+1) (4096*K) W

theorem initial (D W : ℕ) (j : Fin 3) (i : Fin (DimensionPolynomial.tapes (degree D j))) :
    input D W (slots D j i)=DimensionPolynomial.input (degree D j) W i := by
  by_cases hi : i.val=0 <;> simp [input,slots,DimensionPolynomial.input,hi]

theorem next_input (D W : ℕ) (j k : Fin 3) (hjk : j≠k)
    (old : Fin (tapes D) → List Bool)
    (out : Fin (DimensionPolynomial.tapes (degree D j)) → List Bool)
    (hsource : out ⟨0,by simp [DimensionPolynomial.tapes]⟩=List.replicate W true)
    (hnext : ∀ i,old (slots D k i)=DimensionPolynomial.input (degree D k) W i)
    (i : Fin (DimensionPolynomial.tapes (degree D k))) :
    install (slots D j) old out (slots D k i)=DimensionPolynomial.input (degree D k) W i := by
  by_cases hi : i.val=0
  · have he : slots D k i=slots D j ⟨0,by simp [DimensionPolynomial.tapes]⟩ := by
      apply Fin.ext; simp [slots,hi]
    rw [he,install_slot _ (slots_injective D j),hsource]
    simp [DimensionPolynomial.input,hi]
  · rw [install_other _ _ _ _ (fun l => slots_disjoint D j k hjk l i hi)]
    exact hnext i

theorem retained (D : ℕ) (j k : Fin 3) (hjk : j≠k)
    (old : Fin (tapes D) → List Bool)
    (out : Fin (DimensionPolynomial.tapes (degree D j)) → List Bool) :
    install (slots D j) old out (outputSlot D k)=old (outputSlot D k) := by
  exact install_other _ _ _ _ (fun l => slots_disjoint D j k hjk l _ (by
    simp [PCPSerializerCapacity.Power.outputSlot,DimensionPolynomial.binarySlots]))

theorem capacity_run (D K W : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine D K) (budget D K W) (input D W) out ∧
    out ⟨0,by simp [tapes]⟩=List.replicate W true ∧
    ∀ j : Fin 3,out (outputSlot D j)=List.replicate (value D K W j) true := by
  obtain ⟨a,ha,as,av⟩ := PCPSerializerCapacity.Power.capacity_run (degree D 0) (coefficient K 0) W
  obtain ⟨b,hb,bs,bv⟩ := PCPSerializerCapacity.Power.capacity_run (degree D 1) (coefficient K 1) W
  obtain ⟨c,hc,cs,cv⟩ := PCPSerializerCapacity.Power.capacity_run (degree D 2) (coefficient K 2) W
  have first := ha.focus (slots D 0) (slots_injective D 0) (input D W) (initial D W 0)
  have second := hb.focus (slots D 1) (slots_injective D 1) _
    (next_input D W 0 1 (by decide) (input D W) a as (initial D W 1))
  have third := hc.focus (slots D 2) (slots_injective D 2) _
    (next_input D W 1 2 (by decide) _ b bs
      (next_input D W 0 2 (by decide) (input D W) a as (initial D W 2)))
  have joined := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ first second) third
  refine ⟨_,joined,?_,?_⟩
  · change install (slots D 2) _ c (slots D 2 ⟨0,by simp [DimensionPolynomial.tapes]⟩)=_
    rw [install_slot _ (slots_injective D 2)]
    exact cs
  · intro j
    fin_cases j
    · exact (retained D 2 0 (by decide) _ _).trans
        ((retained D 1 0 (by decide) _ _).trans
          ((install_slot _ (slots_injective D 0) _ _ _).trans av))
    · exact (retained D 2 1 (by decide) _ _).trans
        ((install_slot _ (slots_injective D 1) _ _ _).trans bv)
    · exact (install_slot _ (slots_injective D 2) _ _ _).trans cv

end NearCubicWires.RepairOrdinary.PCPPNativeCapacityCold

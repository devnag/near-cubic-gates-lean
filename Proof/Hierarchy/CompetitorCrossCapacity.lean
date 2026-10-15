import Proof.Hierarchy.CompetitorCrossAffineDimensions
import Proof.Hierarchy.CompetitorPlaneTable

/-! The complete native cross-table workspace is physically produced from
raw W and raw cell count n. Only one multiplication contains n, preserving
the required U² dependence when n=U². -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossCapacity
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slope (w : ℕ) := CompetitorCrossAffineDimensions.value 18000 6 w
def intercept (w : ℕ) := CompetitorCrossAffineDimensions.value 16384 25 w
def input (w n : ℕ) : Fin 53 → List Bool := fun i =>
  if i.val=0 then List.replicate w true else if i.val=1 then List.replicate n true else []
def slopeSlots (i : Fin 24) : Fin 53 := if i.val=0 then 0 else ⟨i.val+1,by omega⟩
def interceptSlots (i : Fin 24) : Fin 53 := if i.val=0 then 0 else ⟨i.val+24,by omega⟩
def productSlots : Fin 4 → Fin 53 := ![1,23,49,50]
def sumSlots : Fin 4 → Fin 53 := ![49,44,51,52]
noncomputable def first := RecoveryFocus.machine slopeSlots (CompetitorCrossAffineDimensions.machine 18000 6)
noncomputable def second := RecoveryFocus.machine interceptSlots (CompetitorCrossAffineDimensions.machine 16384 25)
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def machine := Composition.machine first (Composition.machine second (Composition.machine product sum))
def budget (w n : ℕ) := CompetitorCrossAffineDimensions.budget 18000 6 w+1+
  (CompetitorCrossAffineDimensions.budget 16384 25 w+1+
    (WilliamsUnaryProduct.budget n (slope w)+1+(2*(n*slope w+intercept w)+6)))

theorem slope_injective : Function.Injective slopeSlots := by decide
theorem intercept_injective : Function.Injective interceptSlots := by decide
theorem slope_value (i : Fin 24) : (slopeSlots i).val=if i.val=0 then 0 else i.val+1 := by
  unfold slopeSlots
  split_ifs <;> rfl
theorem intercept_value (i : Fin 24) : (interceptSlots i).val=if i.val=0 then 0 else i.val+24 := by
  unfold interceptSlots
  split_ifs <;> rfl

theorem capacity_formula (w n : ℕ) :
    CompetitorPlanePacketPass.capacity w n=n*slope w+intercept w := by
  unfold CompetitorPlanePacketPass.capacity CompetitorPlaneReusable.capacity
    CompetitorPlanePaddedEntry.capacity CompetitorPlaneSign.budget CompetitorPlaneEntry.readyBudget
    CompetitorPlaneEntry.budget CompetitorPlaneStream.planeBudget CompetitorPlaneStream.bodyBudget
    slope intercept CompetitorCrossAffineDimensions.value CompetitorPlane.capacity
  ring

theorem capacity_run (w n : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget w n) (input w n) out ∧
      out 0=List.replicate w true ∧ out 1=List.replicate n true ∧
      out 51=List.replicate (CompetitorPlanePacketPass.capacity w n) true := by
  obtain ⟨a,ha,ha0,_,ha22⟩ := CompetitorCrossAffineDimensions.affine_run 18000 6 w
  have hfirst := bounded_focus slopeSlots slope_injective _ _ _ ha (input w n) (by
    intro i
    by_cases hi : i.val=0
    · simp [slopeSlots,hi,input,CompetitorCrossAffineDimensions.input]
    · simp [slopeSlots,hi,input,CompetitorCrossAffineDimensions.input])
  let atapes := install slopeSlots (input w n) a
  have first_keep (i : Fin 53) (hi : i.val=1 ∨ 25 ≤ i.val) : atapes i=input w n i := by
    apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    rw [slope_value] at hv
    split_ifs at hv <;> omega
  have first_zero : atapes 0=List.replicate w true :=
    (install_slot slopeSlots slope_injective _ a 0).trans ha0
  obtain ⟨b,hb,hb0,hb20,_⟩ := CompetitorCrossAffineDimensions.affine_run 16384 25 w
  have hsecond := bounded_focus interceptSlots intercept_injective _ _ _ hb atapes (by
    intro i
    by_cases hi : i.val=0
    · have he : i=0 := Fin.ext hi
      subst i
      exact first_zero
    · rw [first_keep _ (Or.inr (by rw [intercept_value,if_neg hi]; omega))]
      simp [input,interceptSlots,hi,CompetitorCrossAffineDimensions.input])
  let btapes := install interceptSlots atapes b
  have second_keep (i : Fin 53) (hi : (0 < i.val ∧ i.val < 25) ∨ 48 ≤ i.val) : btapes i=atapes i := by
    apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    rw [intercept_value] at hv
    split_ifs at hv <;> omega
  have hproduct := bounded_focus productSlots (by decide) _ _ _
    (CompetitorDimensions.unary_ready n (slope w)) btapes (by
      intro i
      fin_cases i
      · exact (second_keep 1 (Or.inl (by decide))).trans (first_keep 1 (Or.inl rfl))
      · exact (second_keep 23 (Or.inl (by decide))).trans
          ((install_slot slopeSlots slope_injective _ a 22).trans ha22)
      · exact (second_keep 49 (Or.inr (by decide))).trans (first_keep 49 (Or.inr (by decide)))
      · exact (second_keep 50 (Or.inr (by decide))).trans (first_keep 50 (Or.inr (by decide))))
  let ctapes := install productSlots btapes (WilliamsUnaryProduct.output n (slope w))
  have hsum := bounded_focus sumSlots (by decide) _ _ _
    (CompetitorSameBucketGroupColdDimensions.sum_ready (n*slope w) (intercept w)) ctapes (by
      intro i
      fin_cases i
      · exact install_slot productSlots (by decide) _ _ 2
      · exact (install_other productSlots _ _ _ (by decide)).trans
          ((install_slot interceptSlots intercept_injective _ b 20).trans hb20)
      · exact (install_other productSlots _ _ _ (by decide)).trans
          ((second_keep 51 (Or.inr (by decide))).trans (first_keep 51 (Or.inr (by decide))))
      · exact (install_other productSlots _ _ _ (by decide)).trans
          ((second_keep 52 (Or.inr (by decide))).trans (first_keep 52 (Or.inr (by decide)))))
  let out := install sumSlots ctapes (CompetitorSameBucketGroupColdDimensions.sumOutput (n*slope w) (intercept w))
  have htail := ClockJoin.join _ _ _ _ _ _ _ hproduct hsum
  have hrest := ClockJoin.join _ _ _ _ _ _ _ hsecond htail
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hfirst hrest,?_,?_,?_⟩
  · exact (install_other sumSlots _ _ _ (by decide)).trans
      ((install_other productSlots _ _ _ (by decide)).trans
        ((install_slot interceptSlots intercept_injective _ b 0).trans hb0))
  · exact (install_other sumSlots _ _ _ (by decide)).trans (install_slot productSlots (by decide) _ _ 0)
  · rw [capacity_formula]
    exact install_slot sumSlots (by decide) _ _ 2

end NearCubicWires.RepairOrdinary.CompetitorCrossCapacity

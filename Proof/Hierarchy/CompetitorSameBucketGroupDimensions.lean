import Proof.Hierarchy.CompetitorSameBucketGroupDense
import Proof.MachineModel.ClockUnarySum
import Proof.Hierarchy.CompetitorDimensions

/-! Cold production of the grouping capacity from actual raw W,p,M tapes.
The accepted polynomial dimension producer avoids a second scale machine. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdDimensions
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (w p m : ℕ) := CompetitorReusableDecision.capacity (w+p+m)
def input (w p m : ℕ) (source : List Bool) : Fin 46 → List Bool := fun i =>
  if i=0 then source else if i=1 then List.replicate w true else
    if i=2 then List.replicate p true else if i=3 then List.replicate m true else []
def sumOutput (r s : ℕ) : Fin 4 → List Bool :=
  ![List.replicate r true,List.replicate s true,List.replicate (r+s) true,List.replicate (r+s+2) false]
def slots1 : Fin 4 → Fin 46 := ![1,2,24,25]
def slots2 : Fin 4 → Fin 46 := ![24,3,26,27]
def dimsSlots (j : Fin 19) : Fin 46 := if j=0 then 26 else if j=17 then 22 else ⟨27+j.val,by omega⟩
theorem dims_injective : Function.Injective dimsSlots := by decide
noncomputable def first := RecoveryFocus.machine slots1 ClockUnarySum.machine
noncomputable def second := RecoveryFocus.machine slots2 ClockUnarySum.machine
noncomputable def last := RecoveryFocus.machine dimsSlots CompetitorDimensions.machine
noncomputable def machine := Composition.machine first (Composition.machine second last)
def budget (w p m : ℕ) := (2*(w+p)+6)+1+((2*(w+p+m)+6)+1+CompetitorDimensions.budget (w+p+m))
noncomputable def data1 (w p m : ℕ) (source : List Bool) := install slots1 (input w p m source) (sumOutput w p)
noncomputable def data2 (w p m : ℕ) (source : List Bool) := install slots2 (data1 w p m source) (sumOutput (w+p) m)

theorem sum_ready (r s : ℕ) : ClockJoin.ReadyRun ClockUnarySum.machine (2*(r+s)+6)
    ![List.replicate r true,List.replicate s true,[],[]] (sumOutput r s) := by
  obtain ⟨a,hr,ht,hh,hs⟩ := ClockUnarySum.sum_ready r s
  exact ⟨a,hr,ht,hh,hs⟩

theorem dimensions_run (w p m : ℕ) (source : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget w p m) (input w p m source) out ∧
    out 22=List.replicate (capacity w p m) true ∧
    (∀ i : Fin 24,i≠22 → out (i.castAdd 22)=input w p m source (i.castAdd 22)) := by
  have hfirst := bounded_focus slots1 (by decide) _ _ _ (sum_ready w p) (input w p m source)
    (by intro j;fin_cases j <;> rfl)
  have hsecond := bounded_focus slots2 (by decide) _ _ _ (sum_ready (w+p) m) (data1 w p m source)
    (by
      intro j
      fin_cases j
      · exact install_slot slots1 (by decide) _ _ 2
      all_goals exact install_other slots1 _ _ _ (by decide))
  obtain ⟨dims,hd,h0,_,h17⟩ := CompetitorDimensions.dimensions_run (w+p+m)
  have hdInput : ∀ j,data2 w p m source (dimsSlots j)=CompetitorDimensions.input (w+p+m) j := by
    intro j
    fin_cases j
    · exact install_slot slots2 (by decide) _ _ 2
    all_goals
      apply (install_other slots2 _ _ _ (by decide)).trans
      exact install_other slots1 _ _ _ (by decide)
  have hlast := bounded_focus dimsSlots dims_injective _ _ _ hd (data2 w p m source) hdInput
  let out := install dimsSlots (data2 w p m source) dims
  have htail := ClockJoin.join second last _ _ _ _ _ hsecond hlast
  have hwhole := ClockJoin.join first (Composition.machine second last) _ _ _ _ _ hfirst htail
  refine ⟨out,hwhole,?_,?_⟩
  · exact (install_slot dimsSlots dims_injective _ dims 17).trans h17
  · intro i hi
    have hdim : ∀ j,dimsSlots j≠i.castAdd 22 := by
      intro j hj
      have hv := congrArg Fin.val hj
      by_cases h0 : j=0
      · subst j;simp only [dimsSlots,↓reduceIte] at hv;change 26=i.val at hv;omega
      by_cases h17 : j=17
      · subst j;exact hi (Fin.ext (by simpa [dimsSlots] using hv.symm))
      simp only [dimsSlots,h0,h17,↓reduceIte] at hv
      change 27+j.val=i.val at hv
      omega
    change install dimsSlots _ _ _=_
    rw [install_other dimsSlots _ _ _ hdim]
    fin_cases i <;> first
      | exact False.elim (hi rfl)
      | exact (install_other slots2 _ _ _ (by decide)).trans (install_slot slots1 (by decide) _ _ 0)
      | exact (install_other slots2 _ _ _ (by decide)).trans (install_slot slots1 (by decide) _ _ 1)
      | exact install_slot slots2 (by decide) _ _ 1
      | exact (install_other slots2 _ _ _ (by decide)).trans (install_other slots1 _ _ _ (by decide))

theorem capacity_bounds (w p m : ℕ) : 8*m+3≤capacity w p m ∧ 4*w+3≤capacity w p m ∧ 1≤capacity w p m := by
  unfold capacity CompetitorReusableDecision.capacity
  have hsq : w+p+m+1≤(w+p+m+1)^2 := Nat.le_self_pow (by decide) _
  constructor
  · omega
  · constructor <;> omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdDimensions

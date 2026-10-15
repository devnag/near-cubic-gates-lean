import Proof.PCP.PCPSerializerCapacityPower
import Proof.Hierarchy.CompetitorSameBucketGroupDimensions

/-! Actual short-field producer for the two coefficients in the cross-table
workspace formula. The constant term and every unary byte are written by the
finite program. Its reusable template feeds the U²-linear product. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossAffineDimensions
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def value (c k w : ℕ) := c*(w+1)^2+k
def input (w : ℕ) : Fin 24 → List Bool := fun i => if i.val=0 then List.replicate w true else []
def powerSlots (i : Fin 18) : Fin 24 := i.castAdd 6
def constantSlots : Fin 2 → Fin 24 := ![18,19]
def sumSlots : Fin 4 → Fin 24 := ![7,18,20,21]
def templateSlots : Fin 3 → Fin 24 := ![20,22,23]
noncomputable def power (c : ℕ) := RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 2 c)
noncomputable def constant (k : ℕ) := RecoveryFocus.machine constantSlots (HierarchyFixedWord.machine (List.replicate k true))
noncomputable def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def template := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
noncomputable def machine (c k : ℕ) := Composition.machine (power c)
  (Composition.machine (constant k) (Composition.machine sum template))
def budget (c k w : ℕ) := PCPSerializerCapacity.Power.budget 2 c w+1+
  ((2*k+2)+1+((2*value c k w+6)+1+(2*value c k w+8)))

theorem power_injective : Function.Injective powerSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 24 => a.val) h)

theorem constant_ready (k : ℕ) : ClockJoin.ReadyRun
    (HierarchyFixedWord.machine (List.replicate k true)) (2*k+2) (fun _ => [])
    ![List.replicate k true,List.replicate k false] := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (List.replicate k true)
  simpa only [List.length_replicate] using
    (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩)

theorem affine_run (c k w : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine c k) (budget c k w) (input w) out ∧
      out 0=List.replicate w true ∧ out 20=List.replicate (value c k w) true ∧
      out 22=UnaryTemplate.tape (value c k w) := by
  obtain ⟨p,hp,hp0,hpv⟩ := PCPSerializerCapacity.Power.capacity_run 2 c w
  have hpower := bounded_focus powerSlots power_injective _ _ _ hp (input w)
    (by intro i; rfl)
  let a := install powerSlots (input w) p
  have fresh (i : Fin 24) (hi : 18 ≤ i.val) : a i=[] := by
    rw [show a i=install powerSlots (input w) p i from rfl]
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv := congrArg Fin.val hj
      change j.val=i.val at hv
      omega)]
    simp [input,show i.val≠0 by omega]
  have ha0 : a 0=List.replicate w true :=
    (install_slot powerSlots power_injective _ p 0).trans hp0
  have ha7 : a 7=List.replicate (c*(w+1)^2) true :=
    (install_slot powerSlots power_injective _ p 7).trans hpv
  have hconstant := bounded_focus constantSlots (by decide) _ _ _ (constant_ready k) a
    (by intro i; fin_cases i <;> exact fresh _ (by decide))
  let b := install constantSlots a (![List.replicate k true,List.replicate k false])
  have hsum := bounded_focus sumSlots (by decide) _ _ _
    (CompetitorSameBucketGroupColdDimensions.sum_ready (c*(w+1)^2) k) b (by
      intro i
      fin_cases i
      · exact (install_other constantSlots _ _ _ (by decide)).trans ha7
      · exact install_slot constantSlots (by decide) _ _ 0
      all_goals exact (install_other constantSlots _ _ _ (by decide)).trans (fresh _ (by decide)))
  let d := install sumSlots b (CompetitorSameBucketGroupColdDimensions.sumOutput (c*(w+1)^2) k)
  have htemplate := bounded_focus templateSlots (by decide) _ _ _
    (DimensionTemplate.ready false (value c k w)) d (by
      intro i
      fin_cases i
      · exact install_slot sumSlots (by decide) _ _ 2
      · exact (install_other sumSlots _ _ _ (by decide)).trans
          ((install_other constantSlots _ _ _ (by decide)).trans (fresh _ (by decide)))
      · exact (install_other sumSlots _ _ _ (by decide)).trans
          ((install_other constantSlots _ _ _ (by decide)).trans (fresh _ (by decide))))
  let out := install templateSlots d (DimensionTemplate.output false (value c k w))
  have htail := ClockJoin.join _ _ _ _ _ _ _ hsum htemplate
  have hrest := ClockJoin.join _ _ _ _ _ _ _ hconstant htail
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hpower hrest,?_,?_,?_⟩
  · exact (install_other templateSlots _ _ _ (by decide)).trans
      ((install_other sumSlots _ _ _ (by decide)).trans
        ((install_other constantSlots _ _ _ (by decide)).trans ha0))
  · exact install_slot templateSlots (by decide) _ _ 0
  · exact install_slot templateSlots (by decide) _ _ 1

end NearCubicWires.RepairOrdinary.CompetitorCrossAffineDimensions

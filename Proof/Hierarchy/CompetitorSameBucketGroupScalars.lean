import Proof.Hierarchy.CompetitorSameBucketGroupAllocate

/-! Produce the three padded zero scalar fields in the allocated bank.
Existing normalization and reusable copying execute all writes and resets. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdScalars
open LocalBitMultitape RecoveryRootRound SignedSortKey RadixSemantics CompetitorRationalProducts
open CompetitorSameBucketGroupColdDimensions (capacity)
open CompetitorSameBucketGroupArithmetic (field scalar zeros normalInput normalOutput copyInput copyOutput)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def normalSlots : Fin 5 → Fin 47 := ![1,7,13,46,16]
def copySlots1 : Fin 4 → Fin 47 := ![13,14,16,17]
def copySlots2 : Fin 4 → Fin 47 := ![13,15,16,17]
noncomputable def normal := RecoveryFocus.machine normalSlots ClockNormalize.machine
noncomputable def copy1 := RecoveryFocus.machine copySlots1 copyMachine
noncomputable def copy2 := RecoveryFocus.machine copySlots2 copyMachine
noncomputable def tail := Composition.machine normal (Composition.machine copy1 copy2)
noncomputable def machine := Composition.machine CompetitorSameBucketGroupColdAllocate.machine tail
def budget (w p m : ℕ) := CompetitorSameBucketGroupColdAllocate.budget w p m+1+
  ((4*w+4)+1+((8*w+8)+1+(8*w+8)))
def values (cap w p m : ℕ) (source : List Bool) (i : Fin 24) :=
  if i=13 ∨ i=14 ∨ i=15 then scalar cap w 0 else CompetitorSameBucketGroupColdAllocate.values cap w p m source i

theorem empty_field (cap : ℕ) (hc : 1 ≤ cap) : field cap []=zeros cap := by
  change ZeroPadding.pad cap (List.replicate 1 false)=List.replicate cap false
  rw [Rewind.Workspace.pad_zeros,max_eq_left hc]

theorem normal_ready (cap w : ℕ) (hc : 2*w+1 ≤ cap) : ClockJoin.ReadyRun ClockNormalize.machine
    (4*w+4) (normalInput cap w []) (normalOutput cap w []) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := CompetitorSameBucketGroupArithmetic.normal_ready cap w [] (by simp) hc
  exact ⟨r,hr,ht,hh,hs.le⟩
theorem copy_ready (cap w : ℕ) (hc : 4*w+3 ≤ cap) : ClockJoin.ReadyRun copyMachine
    (8*w+8) (copyInput cap (binary w 0) []) (copyOutput cap (binary w 0)) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := CompetitorSameBucketGroupArithmetic.field_copy_ready cap (binary w 0) []
    (by simp) (by simpa using hc)
  simpa only [binary_length] using (show ClockJoin.ReadyRun copyMachine _ _ _ from ⟨r,hr,ht,hh,hs.le⟩)

theorem scalars_run (w p m : ℕ) (source : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget w p m) (CompetitorSameBucketGroupColdAllocate.input w p m source) out ∧
    ∀ i : Fin 24,out (i.castAdd 23)=values (capacity w p m) w p m source i := by
  obtain ⟨a,ha,atapes,h46⟩ := CompetitorSameBucketGroupColdAllocate.allocation_run w p m source
  obtain ⟨_,hcap,hpos⟩ := CompetitorSameBucketGroupColdDimensions.capacity_bounds w p m
  have hempty := empty_field (capacity w p m) hpos
  have hnormal := bounded_focus normalSlots (by decide) _ _ _ (normal_ready (capacity w p m) w (by omega)) a (by
    intro j
    fin_cases j
    · exact atapes 1
    · exact (atapes 7).trans hempty.symm
    · exact atapes 13
    · exact h46
    · exact atapes 16)
  let b := install normalSlots a (normalOutput (capacity w p m) w [])
  have hcopy1 := bounded_focus copySlots1 (by decide) _ _ _ (copy_ready (capacity w p m) w hcap) b (by
    intro j
    fin_cases j
    · exact install_slot normalSlots (by decide) _ _ 2
    · exact (install_other normalSlots _ _ _ (by decide)).trans (atapes 14)
    · exact install_slot normalSlots (by decide) _ _ 4
    · exact (install_other normalSlots _ _ _ (by decide)).trans (atapes 17))
  let c := install copySlots1 b (copyOutput (capacity w p m) (binary w 0))
  have hcopy2 := bounded_focus copySlots2 (by decide) _ _ _ (copy_ready (capacity w p m) w hcap) c (by
    intro j
    fin_cases j
    · exact install_slot copySlots1 (by decide) _ _ 0
    · exact (install_other copySlots1 _ _ _ (by decide)).trans
        ((install_other normalSlots _ _ _ (by decide)).trans (atapes 15))
    · exact install_slot copySlots1 (by decide) _ _ 2
    · exact install_slot copySlots1 (by decide) _ _ 3)
  let out := install copySlots2 c (copyOutput (capacity w p m) (binary w 0))
  have hcopies := ClockJoin.join copy1 copy2 _ _ _ _ _ hcopy1 hcopy2
  have htail := ClockJoin.join normal (Composition.machine copy1 copy2) _ _ _ _ _ hnormal hcopies
  refine ⟨out,ClockJoin.join CompetitorSameBucketGroupColdAllocate.machine tail _ _ _ _ _ ha htail,?_⟩
  intro i
  fin_cases i
  all_goals first
    | exact install_slot copySlots2 (by decide) _ _ 0
    | exact install_slot copySlots2 (by decide) _ _ 1
    | exact install_slot copySlots2 (by decide) _ _ 2
    | exact install_slot copySlots2 (by decide) _ _ 3
    | exact (install_other copySlots2 _ _ _ (by decide)).trans (install_slot copySlots1 (by decide) _ _ 1)
    | exact (install_other copySlots2 _ _ _ (by decide)).trans
        ((install_other copySlots1 _ _ _ (by decide)).trans (install_slot normalSlots (by decide) _ _ 0))
    | exact (install_other copySlots2 _ _ _ (by decide)).trans
        ((install_other copySlots1 _ _ _ (by decide)).trans
          ((install_slot normalSlots (by decide) _ _ 1).trans hempty))
    | skip
  all_goals
    apply (install_other copySlots2 _ _ _ (by decide)).trans
    apply (install_other copySlots1 _ _ _ (by decide)).trans
    apply (install_other normalSlots _ _ _ (by decide)).trans
    first | exact atapes 0 | exact atapes 2 | exact atapes 3 | exact atapes 4 | exact atapes 5 | exact atapes 6 |
      exact atapes 8 | exact atapes 9 | exact atapes 10 | exact atapes 11 | exact atapes 12 | exact atapes 18 |
      exact atapes 19 | exact atapes 20 | exact atapes 21 | exact atapes 22 | exact atapes 23

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdScalars

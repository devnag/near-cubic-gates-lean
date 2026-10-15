import Proof.Hierarchy.CompetitorSameBucketGroupDimensions

/-! Actual simultaneous allocation of the grouping scratch and zero banks.
The retained capacity was produced from W,p,M by the preceding cold phase. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdAllocate
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open CompetitorSameBucketGroupColdDimensions (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 15 → Fin 47 := ![7,8,9,13,14,15,16,17,18,19,20,21,46,22,23]
theorem slots_injective : Function.Injective slots := by decide
def localInput (cap : ℕ) : Fin 15 → List Bool := fun i => if i=13 then List.replicate cap true else []
def localOutput (cap : ℕ) : Fin 15 → List Bool := fun i =>
  if i=13 then List.replicate cap true else if i=14 then List.replicate (cap+1) false else List.replicate cap false
def values (cap w p m : ℕ) (source : List Bool) (i : Fin 24) : List Bool :=
  if i=22 then List.replicate cap true else if i=23 then List.replicate (cap+1) false
  else if (7 ≤ i.val ∧ i.val ≤ 9) ∨ (13 ≤ i.val ∧ i.val ≤ 21) then List.replicate cap false
  else CompetitorSameBucketGroupColdDimensions.input w p m source (i.castAdd 22)
def input (w p m : ℕ) (source : List Bool) : Fin 47 → List Bool :=
  Fin.addCases (m := 46) (n := 1) (motive := fun _ => List Bool) (CompetitorSameBucketGroupColdDimensions.input w p m source) (fun _ : Fin 1 => [])
noncomputable def first := ClockJoin.lifted (e := 1) (Equiv.refl (Fin 47)) CompetitorSameBucketGroupColdDimensions.machine
noncomputable def last := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 13)
noncomputable def machine := Composition.machine first last
def budget (w p m : ℕ) := CompetitorSameBucketGroupColdDimensions.budget w p m+1+(2*capacity w p m+4)

theorem allocate_ready (cap : ℕ) : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 13)
    (2*cap+4) (localInput cap) (localOutput cap) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin 13 => []) (by intro i;simp)
  have hi : (Fin.addCases (m := 14) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        (fun _ => []) (fun _ => List.replicate cap true)) (fun _ => List.replicate 0 false))=localInput cap := by
    funext i;fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs.le⟩
  rw [ht]
  simp only [Nat.zero_max]
  funext i;fin_cases i <;> rfl

theorem allocation_run (w p m : ℕ) (source : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget w p m) (input w p m source) out ∧
    (∀ i : Fin 24,out (i.castAdd 23)=values (capacity w p m) w p m source i) ∧
    out 46=List.replicate (capacity w p m) false := by
  obtain ⟨d,hd,hcap,hkeep⟩ := CompetitorSameBucketGroupColdDimensions.dimensions_run w p m source
  let initial : Fin 47 → List Bool := Fin.addCases (m := 46) (n := 1) (motive := fun _ => List Bool) d (fun _ : Fin 1 => [])
  have hfirst : ClockJoin.ReadyRun first (CompetitorSameBucketGroupColdDimensions.budget w p m)
      (input w p m source) initial := ClockJoin.lift (e := 1) (Equiv.refl (Fin 47)) _ _ _ _ (fun _ : Fin 1 => []) hd
  have kept (i : Fin 24) (hi : i≠22) : initial (i.castAdd 23)=
      CompetitorSameBucketGroupColdDimensions.input w p m source (i.castAdd 22) := by
    change (Fin.addCases (m := 46) (n := 1) (motive := fun _ => List Bool) d
      (fun _ => [])) ((i.castAdd 22).castAdd 1)=_
    rw [Fin.addCases_left]
    exact hkeep i hi
  have hselected : ∀ j,initial (slots j)=localInput (capacity w p m) j := by
    intro j
    fin_cases j
    · exact kept 7 (by decide)
    · exact kept 8 (by decide)
    · exact kept 9 (by decide)
    · exact kept 13 (by decide)
    · exact kept 14 (by decide)
    · exact kept 15 (by decide)
    · exact kept 16 (by decide)
    · exact kept 17 (by decide)
    · exact kept 18 (by decide)
    · exact kept 19 (by decide)
    · exact kept 20 (by decide)
    · exact kept 21 (by decide)
    · rfl
    · exact hcap
    · exact kept 23 (by decide)
  have hlast := bounded_focus slots slots_injective _ _ _ (allocate_ready (capacity w p m)) initial hselected
  let out := install slots initial (localOutput (capacity w p m))
  refine ⟨out,ClockJoin.join first last _ _ _ _ _ hfirst hlast,?_,?_⟩
  · intro i
    fin_cases i
    · exact (install_other slots _ _ _ (by decide)).trans (kept 0 (by decide))
    · exact (install_other slots _ _ _ (by decide)).trans (kept 1 (by decide))
    · exact (install_other slots _ _ _ (by decide)).trans (kept 2 (by decide))
    · exact (install_other slots _ _ _ (by decide)).trans (kept 3 (by decide))
    · exact (install_other slots _ _ _ (by decide)).trans (kept 4 (by decide))
    · exact (install_other slots _ _ _ (by decide)).trans (kept 5 (by decide))
    · exact (install_other slots _ _ _ (by decide)).trans (kept 6 (by decide))
    · exact install_slot slots slots_injective _ _ 0
    · exact install_slot slots slots_injective _ _ 1
    · exact install_slot slots slots_injective _ _ 2
    · exact (install_other slots _ _ _ (by decide)).trans (kept 10 (by decide))
    · exact (install_other slots _ _ _ (by decide)).trans (kept 11 (by decide))
    · exact (install_other slots _ _ _ (by decide)).trans (kept 12 (by decide))
    · exact install_slot slots slots_injective _ _ 3
    · exact install_slot slots slots_injective _ _ 4
    · exact install_slot slots slots_injective _ _ 5
    · exact install_slot slots slots_injective _ _ 6
    · exact install_slot slots slots_injective _ _ 7
    · exact install_slot slots slots_injective _ _ 8
    · exact install_slot slots slots_injective _ _ 9
    · exact install_slot slots slots_injective _ _ 10
    · exact install_slot slots slots_injective _ _ 11
    · exact install_slot slots slots_injective _ _ 13
    · exact install_slot slots slots_injective _ _ 14
  · exact install_slot slots slots_injective _ _ 12

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdAllocate

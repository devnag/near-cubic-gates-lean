import Proof.Hierarchy.CompetitorSameBucketGroupDrivers

/-! The literal final cold-entry transition writes all three flags and
advances the two produced comparison drivers to their required head one. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorSameBucketGroupColdDimensions (capacity)
open CompetitorSameBucketGroupMachine (emptyStore)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flag (i : Fin 52) : Prop := i=10 ∨ i=11 ∨ i=12
instance (i : Fin 52) : Decidable (flag i) := inferInstanceAs (Decidable (i=10 ∨ i=11 ∨ i=12))
def entryHeads (i : Fin 52) := if i=5 ∨ i=6 then 1 else 0
def entryTapes (a : Fin 52 → List Bool) (i : Fin 52) := if flag i then [false] else a i
def entry : Machine 52 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if flag i then some false else none,fun i=>if i=5 ∨ i=6 then .right else .stay⟩ else none

theorem entry_run (a : Fin 52 → List Bool) (ha : ∀ i,flag i → a i=[]) :
    ∃ r,run entry 1 a=some r ∧ r.final.heads=entryHeads ∧ r.final.tapes=entryTapes a ∧ r.steps=1 := by
  let last : Configuration 52 2:=⟨1,entryHeads,entryTapes a⟩
  have hs : step entry (initialConfiguration entry a)=some last := by
    simp only [step,entry,Fin.isValue]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases h : i=5 ∨ i=6 <;> simp [applyAction,initialConfiguration,entryHeads,HeadMove.apply,h,last]
    · funext i
      by_cases h : flag i
      · simp [applyAction,initialConfiguration,entryTapes,h,ha i h,last,writeTapeBit]
      · simp [applyAction,initialConfiguration,entryTapes,h,last]
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

noncomputable def machine := Composition.machine CompetitorSameBucketGroupColdDrivers.machine entry
def budget (w p m : ℕ) := CompetitorSameBucketGroupColdDrivers.budget w p m+1+1

theorem prepare_run (w p m : ℕ) (source : List Bool) : ∃ r,
    run machine (budget w p m) (CompetitorSameBucketGroupColdDrivers.input w p m source)=some r ∧
    r.final.heads=entryHeads ∧
    (∀ i : Fin 24,r.final.tapes (i.castAdd 28)=emptyStore.tapes (capacity w p m) w p m source [] i) ∧
    r.steps ≤ budget w p m := by
  obtain ⟨a,⟨base,hb,hbt,hbh,hbs⟩,ha⟩ := CompetitorSameBucketGroupColdDrivers.drivers_run w p m source
  have hflags : ∀ i,flag i → a i=[] := by
    intro i hi
    rcases hi with rfl|rfl|rfl
    · exact ha 10
    · exact ha 11
    · exact ha 12
  obtain ⟨last,hl,hlh,hlt,hls⟩ := entry_run a hflags
  have he : Composition.restart base.final entry.start=initialConfiguration entry a := by
    apply configuration_ext
    · rfl
    · exact funext hbh
    · exact hbt
  change runFrom entry 1 (initialConfiguration entry a)=some last at hl
  rw [←he] at hl
  have hjoined := Composition.run_join CompetitorSameBucketGroupColdDrivers.machine entry _ _ _ base last hb hl
  refine ⟨Composition.joinedReceipt base last,hjoined,hlh,?_,?_⟩
  · intro i
    change last.final.tapes (i.castAdd 28)=_
    rw [hlt]
    have hempty := CompetitorSameBucketGroupColdScalars.empty_field (capacity w p m)
      (CompetitorSameBucketGroupColdDimensions.capacity_bounds w p m).2.2
    fin_cases i
    all_goals first
      | rfl
      | exact ha 0 | exact ha 1 | exact ha 2 | exact ha 3 | exact ha 4 | exact ha 5 | exact ha 6
      | exact (ha 7).trans hempty.symm | exact (ha 8).trans hempty.symm | exact (ha 9).trans hempty.symm
      | exact ha 13 | exact ha 14 | exact ha 15 | exact ha 16 | exact ha 17 | exact ha 18
      | exact ha 19 | exact ha 20 | exact ha 21 | exact ha 22 | exact ha 23
  · change base.steps+1+last.steps ≤ budget w p m
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdEntry

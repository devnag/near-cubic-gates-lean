import Proof.Hierarchy.CompetitorSameBucketGroupScalars
import Proof.PCP.ProjectionNormalizationDriverAtoms

/-! Physically produce Compare.word p and Compare.word (2*M), preserving
the raw W,p,M fields. The factor two is a literal fixed three-bit word. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdDrivers
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization
open CompetitorSameBucketGroupColdDimensions (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w p m : ℕ) (source : List Bool) : Fin 52 → List Bool :=
  Fin.addCases (m := 47) (n := 5) (motive := fun _ => List Bool)
    (CompetitorSameBucketGroupColdAllocate.input w p m source) (fun _ => [])
def pSlots : Fin 4 → Fin 52 := ![2,47,5,48]
def twoSlots : Fin 2 → Fin 52 := ![49,50]
def mSlots : Fin 4 → Fin 52 := ![3,49,6,51]
noncomputable def first := ClockJoin.lifted (e := 5) (Equiv.refl (Fin 52)) CompetitorSameBucketGroupColdScalars.machine
noncomputable def counter := RecoveryFocus.machine pSlots Counter.machine
noncomputable def constant := RecoveryFocus.machine twoSlots (HierarchyFixedWord.machine [false,true,true])
noncomputable def product := RecoveryFocus.machine mSlots Product.reset
noncomputable def tail := Composition.machine counter (Composition.machine constant product)
noncomputable def machine := Composition.machine first tail
def budget (w p m : ℕ) := CompetitorSameBucketGroupColdScalars.budget w p m+1+
  (Counter.budget p+1+(8+1+DriverAtoms.productBudget m 2))
def values (cap w p m : ℕ) (source : List Bool) (i : Fin 24) :=
  if i=5 then CompareMachine.word p else if i=6 then CompareMachine.word (2*m)
  else CompetitorSameBucketGroupColdScalars.values cap w p m source i

theorem constant_ready : ClockJoin.ReadyRun (HierarchyFixedWord.machine [false,true,true]) 8
    (fun _ => []) (![CompareMachine.word 2,List.replicate 3 false]) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready [false,true,true]
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem drivers_run (w p m : ℕ) (source : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget w p m) (input w p m source) out ∧
    ∀ i : Fin 24,out (i.castAdd 28)=values (capacity w p m) w p m source i := by
  obtain ⟨a,ha,atapes⟩ := CompetitorSameBucketGroupColdScalars.scalars_run w p m source
  let initial : Fin 52 → List Bool := Fin.addCases (m := 47) (n := 5) (motive := fun _ => List Bool) a (fun _ => [])
  have hfirst : ClockJoin.ReadyRun first (CompetitorSameBucketGroupColdScalars.budget w p m)
      (input w p m source) initial := ClockJoin.lift (e := 5) (Equiv.refl (Fin 52)) _ _ _ _ (fun _ : Fin 5 => []) ha
  have kept (i : Fin 24) : initial (i.castAdd 28)=
      CompetitorSameBucketGroupColdScalars.values (capacity w p m) w p m source i := by
    change (Fin.addCases (m := 47) (n := 5) (motive := fun _ => List Bool) a
      (fun _ => [])) ((i.castAdd 23).castAdd 5)=_
    rw [Fin.addCases_left]
    exact atapes i
  obtain ⟨c,hc,hc0,hc2⟩ := DriverAtoms.counter_run p
  have hcounter := bounded_focus pSlots (by decide) _ _ _ hc initial (by
    intro j
    fin_cases j
    · exact kept 2
    · rfl
    · exact kept 5
    · rfl)
  let b := install pSlots initial c
  have hconstant := bounded_focus twoSlots (by decide) _ _ _ constant_ready b (by
    intro j;fin_cases j <;> exact install_other pSlots _ _ _ (by decide))
  let d := install twoSlots b (![CompareMachine.word 2,List.replicate 3 false])
  obtain ⟨mout,hm,hm0,_,hm2⟩ := DriverAtoms.product_run m 2
  have hproduct := bounded_focus mSlots (by decide) _ _ _ hm d (by
    intro j
    fin_cases j
    · exact (install_other twoSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans (kept 3))
    · exact install_slot twoSlots (by decide) _ _ 0
    · exact (install_other twoSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans (kept 6))
    · exact (install_other twoSlots _ _ _ (by decide)).trans (install_other pSlots _ _ _ (by decide)))
  rw [Nat.mul_comm m 2] at hm2
  let out := install mSlots d mout
  have htail2 := ClockJoin.join constant product _ _ _ _ _ hconstant hproduct
  have htail := ClockJoin.join counter (Composition.machine constant product) _ _ _ _ _ hcounter htail2
  refine ⟨out,ClockJoin.join first tail _ _ _ _ _ hfirst htail,?_⟩
  intro i
  fin_cases i
  all_goals first
    | exact (install_slot mSlots (by decide) _ _ 0).trans hm0
    | exact (install_slot mSlots (by decide) _ _ 2).trans hm2
    | exact (install_other mSlots _ _ _ (by decide)).trans
        ((install_other twoSlots _ _ _ (by decide)).trans ((install_slot pSlots (by decide) _ _ 0).trans hc0))
    | exact (install_other mSlots _ _ _ (by decide)).trans
        ((install_other twoSlots _ _ _ (by decide)).trans ((install_slot pSlots (by decide) _ _ 2).trans hc2))
    | skip
  all_goals
    apply (install_other mSlots _ _ _ (by decide)).trans
    apply (install_other twoSlots _ _ _ (by decide)).trans
    apply (install_other pSlots _ _ _ (by decide)).trans
    first | exact kept 0 | exact kept 1 | exact kept 4 | exact kept 7 | exact kept 8 | exact kept 9 |
      exact kept 10 | exact kept 11 | exact kept 12 | exact kept 13 | exact kept 14 | exact kept 15 |
      exact kept 16 | exact kept 17 | exact kept 18 | exact kept 19 | exact kept 20 | exact kept 21 |
      exact kept 22 | exact kept 23

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupColdDrivers

import Proof.Supplier.RowTupleLogs

/-! Write the three initial zero fields from the two paid unary widths.
All normalizer flags and scratch start empty; only width/bound/degree/limit
metadata are supplied to this cold prefix. -/
namespace NearCubicWires.RepairOrdinary.RowTupleColdFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w k M : ℕ) : Fin 29→List Bool := fun i=>
  if i=2 then CompareMachine.word w else
  if i=3 then frame (binary w (M-1)) else
  if i=12 then CompareMachine.word k else
  if i=14 then frame (binary (w*k+1) (2^(w*k)-1)) else
  if i=18 then List.replicate w true else
  if i=25 then List.replicate (w*k+1) true else []
def slots (j : Fin 3) : Fin 5→Fin 29 :=
  ![![18,19,1,20,21],![18,22,6,23,24],![25,26,0,27,28]] j
theorem injective (j : Fin 3) : Function.Injective (slots j) := by fin_cases j <;> decide
noncomputable def part (j : Fin 3) := RecoveryFocus.machine (slots j) ClockNormalize.machine
noncomputable def first := Composition.machine (part 0) (part 1)
noncomputable def machine := Composition.machine first (part 2)
def time (w k : ℕ) := 8*w+4*(w*k)+18

theorem zero_ready (w : ℕ) : ∃ out,
    ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockScalarFields.zeroInput w) out ∧
      out 0=List.replicate w true ∧ out 2=frame (binary w 0) := by
  obtain ⟨r,hr,h0,_,h2,_,_,hh,hs⟩ := ClockScalarFields.zero_run w
  exact ⟨r.final.tapes,⟨r,hr,rfl,hh,hs.le⟩,h0,h2⟩

theorem prepare_run (w k M : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (time w k) (input w k M) out ∧
      out 0=frame (binary (w*k+1) 0) ∧ out 1=frame (binary w 0) ∧
      out 6=frame (binary w 0) ∧
      (∀ i : Fin 18,i≠0 → i≠1 → i≠6 → out (i.castAdd 11)=input w k M (i.castAdd 11)) := by
  obtain ⟨z,hz,z0,z2⟩ := zero_ready w
  obtain ⟨b,hb,_,b2⟩ := zero_ready (w*k+1)
  have hfirst := bounded_focus (slots 0) (injective 0) _ _ _ hz (input w k M)
    (by intro i; fin_cases i <;> simp [slots,input,ClockScalarFields.zeroInput])
  let one := install (slots 0) (input w k M) z
  have hsecond := bounded_focus (slots 1) (injective 1) _ _ _ hz one (by
    intro i; fin_cases i
    · exact (install_slot (slots 0) (injective 0) _ z 0).trans z0
    all_goals
      rw [show one (slots 1 _)=install (slots 0) (input w k M) z (slots 1 _) from rfl]
      rw [install_other _ _ _ _ (by decide)]
      rfl)
  let two := install (slots 1) one z
  have hthird := bounded_focus (slots 2) (injective 2) _ _ _ hb two (by
    intro i; fin_cases i
    all_goals
      rw [show two (slots 2 _)=install (slots 1) one z (slots 2 _) from rfl]
      rw [install_other _ _ _ _ (by decide)]
      rw [show one (slots 2 _)=install (slots 0) (input w k M) z (slots 2 _) from rfl]
      rw [install_other _ _ _ _ (by decide)]
      rfl)
  let out := install (slots 2) two b
  have hwhole := ClockJoin.join first (part 2) _ _ _ _ _
    (ClockJoin.join (part 0) (part 1) _ _ _ _ _ hfirst hsecond) hthird
  have ht : (4*w+4+1+(4*w+4))+1+(4*(w*k+1)+4)=time w k := by unfold time; omega
  rw [ht] at hwhole
  refine ⟨out,hwhole,?_,?_,?_,?_⟩
  · exact (install_slot (slots 2) (injective 2) _ b 2).trans b2
  · rw [show out 1=install (slots 2) two b 1 from rfl,install_other _ _ _ _ (by decide)]
    rw [show two 1=install (slots 1) one z 1 from rfl,install_other _ _ _ _ (by decide)]
    exact (install_slot (slots 0) (injective 0) _ z 2).trans z2
  · rw [show out 6=install (slots 2) two b 6 from rfl,install_other _ _ _ _ (by decide)]
    exact (install_slot (slots 1) (injective 1) _ z 2).trans z2
  · intro i h0 h1 h6
    have notslot (j : Fin 3) : ∀ a,slots j a≠i.castAdd 11 := by
      intro a he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      have ni0 : i.val≠0 := by intro h; exact h0 (Fin.ext h)
      have ni1 : i.val≠1 := by intro h; exact h1 (Fin.ext h)
      have ni6 : i.val≠6 := by intro h; exact h6 (Fin.ext h)
      fin_cases j <;> fin_cases a <;> simp [slots] at hv <;> omega
    exact (install_other _ _ _ _ (notslot 2)).trans
      ((install_other _ _ _ _ (notslot 1)).trans (install_other _ _ _ _ (notslot 0)))

end NearCubicWires.RepairOrdinary.RowTupleColdFields

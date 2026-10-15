import Proof.Hierarchy.CompetitorMonomialEntry

/-! Physical docking of the bulk monomial producer to the cold scalar
SUM/decision entry. The output stream, short width and count word are shared
actual tapes; the scalar consumer's remaining workspace starts blank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorProducedScalar
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorMonomialStream CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 90) : Fin 213 := i.castAdd 123
def decisionSlot (i : Fin 126) : Fin 213 :=
  if h : i.val<84 then ⟨i.val+90,by omega⟩ else if i.val=84 then 83
  else if h : i.val<88 then ⟨i.val+89,by omega⟩ else if i.val=88 then 74
  else if h : i.val<94 then ⟨i.val+88,by omega⟩ else if i.val=94 then 88 else ⟨i.val+87,by omega⟩
def input (b t : ℕ) (xs : List Entry) : Fin 213 → List Bool :=
  Fin.addCases (m := 90) (n := 123) (motive := fun _ => List Bool) (CompetitorMonomialEntry.readyInput b t xs) (fun _ => [])
noncomputable def producerProgram := RecoveryFocus.machine native CompetitorMonomialEntry.machine

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 213 => a.val) h)
theorem native_other (j : Fin 90) (i : Fin 213) (hi : 90 ≤ i.val) : native j≠i := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=i.val at hv
  omega
theorem decision_injective : Function.Injective decisionSlot := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [decisionSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem decision_other (i : Fin 126) (h84 : i≠84) (h88 : i≠88) (h94 : i≠94) :
    90 ≤ (decisionSlot i).val := by
  have hn84 : i.val≠84 := fun h => h84 (Fin.ext h)
  have hn88 : i.val≠88 := fun h => h88 (Fin.ext h)
  have hn94 : i.val≠94 := fun h => h94 (Fin.ext h)
  simp only [decisionSlot]
  split_ifs <;> (try simp only) <;> omega

theorem input_outside (b t : ℕ) (xs : List Entry) (i : Fin 213) (hi : 90 ≤ i.val) : input b t xs i=[] := by
  have he : i=(⟨i.val-90,by omega⟩ : Fin 123).natAdd 90 := Fin.ext (by simp; omega)
  rw [he]
  simp only [input,Fin.addCases_right]

theorem scalar_blank (t : ℕ) (xs : List CompetitorValidity.Estimate) (i : Fin 126)
    (h84 : i≠84) (h88 : i≠88) (h94 : i≠94) : CompetitorDimensionedDecision.input t xs i=[] := by
  fin_cases i <;> first | rfl | exact (h84 rfl).elim | exact (h88 rfl).elim | exact (h94 rfl).elim

theorem producer_run (b t : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (htarget : width b≤t) (hn : xs.length≤t) :
    ∃ out,ClockJoin.ReadyRun producerProgram (CompetitorMonomialEntry.readyBudget t xs.length) (input b t xs) out ∧
      (∀ i,out (decisionSlot i)=CompetitorDimensionedDecision.input t (contributions xs) i) ∧
      (∀ a∈contributions xs,a.Valid (width b)) := by
  obtain ⟨produced,hr,h74,h83,h88,hvalid⟩ := CompetitorMonomialEntry.ready_stream_run b t xs hv htarget hn
  have hin : ∀ i,input b t xs (native i)=CompetitorMonomialEntry.readyInput b t xs i := by simp [input,native]
  have hf := CompetitorRationalProducts.bounded_focus native native_injective _ _ _ hr (input b t xs) hin
  refine ⟨install native (input b t xs) produced,hf,?_,hvalid⟩
  intro i
  by_cases h84 : i=84
  · subst i
    exact (install_slot native native_injective _ produced 83).trans h83
  · by_cases h88' : i=88
    · subst i
      exact (install_slot native native_injective _ produced 74).trans h74
    · by_cases h94 : i=94
      · subst i
        have hl : (contributions xs).length=xs.length := List.length_map _
        change install native (input b t xs) produced (native 88)=RepairSource.VerifierDecoding.CompareMachine.word (contributions xs).length
        rw [hl]
        exact (install_slot native native_injective (input b t xs) produced 88).trans h88
      · rw [scalar_blank t (contributions xs) i h84 h88' h94]
        have hval := decision_other i h84 h88' h94
        exact (install_other native _ _ (decisionSlot i) (fun j => native_other j _ hval)).trans (input_outside b t xs _ hval)

end NearCubicWires.RepairOrdinary.CompetitorProducedScalar

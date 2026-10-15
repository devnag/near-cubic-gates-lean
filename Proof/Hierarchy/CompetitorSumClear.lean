import Proof.Hierarchy.CompetitorSumConstants

/-! The initial scalar workspace is physically zeroed from blank tapes.
Its reset counter also starts blank; no initial capacity padding is assumed. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldSlot (j : Fin 89) : Fin 94 :=
  if j.val<6 then ⟨j.val,by omega⟩
  else if j.val<83 then ⟨j.val+1,by omega⟩
  else if j.val<86 then ⟨j.val+2,by omega⟩
  else if j.val=86 then 89 else if j.val=87 then 92 else 93
def coldInput (b : ℕ) (source : List Bool) : Fin 94 → List Bool := fun i =>
  if i.val=6 then List.replicate (width b) true
  else if i.val=84 then List.replicate b true else if i.val=88 then source
  else if i.val=90 then List.replicate (capacity b) true else []
def zeroed (b : ℕ) (source : List Bool) : Fin 94 → List Bool := fun i =>
  if i.val=6 then List.replicate (width b) true
  else if i.val=84 then List.replicate b true else if i.val=88 then source
  else if i.val=90 then List.replicate (capacity b) true
  else if i.val=91 then List.replicate (capacity b+1) false else List.replicate (capacity b) false
noncomputable def coldClearProgram := clearProgram coldSlot

theorem cold_injective : Function.Injective coldSlot := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [coldSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega
theorem cold_not_driver (j : Fin 89) : coldSlot j≠90 ∧ coldSlot j≠91 := by
  constructor <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp only [coldSlot] at hv
    split_ifs at hv <;> (try simp only at hv) <;> omega
theorem cold_not_retained (j : Fin 91) (i : Fin 94) (hi : i=6 ∨ i=84 ∨ i=88) : extend coldSlot j≠i := by
  intro h
  rw [extend_cases] at h
  simp only [coldSlot] at h
  rcases hi with hi | hi | hi
  all_goals
    have hv' := congrArg Fin.val (h.trans hi)
    split_ifs at hv' <;> (try simp only at hv') <;> omega

theorem cold_image (i : Fin 94) (h6 : i≠6) (h84 : i≠84) (h88 : i≠88) : ∃ j,extend coldSlot j=i := by
  have hv6 : i.val≠6 := fun h => h6 (Fin.ext h)
  have hv84 : i.val≠84 := fun h => h84 (Fin.ext h)
  have hv88 : i.val≠88 := fun h => h88 (Fin.ext h)
  by_cases hlo : i.val<6
  · refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    simp [extend_cases,coldSlot,hlo,show i.val<89 by omega]
  · by_cases hmid : i.val<84
    · refine ⟨⟨i.val-1,by omega⟩,?_⟩
      apply Fin.ext
      simp [extend_cases,coldSlot,show i.val-1<89 by omega,
        show ¬i.val-1<6 by omega,show i.val-1<83 by omega]
      omega
    · by_cases hhi : i.val<88
      · refine ⟨⟨i.val-2,by omega⟩,?_⟩
        apply Fin.ext
        simp [extend_cases,coldSlot,show i.val-2<89 by omega,
          show ¬i.val-2<6 by omega,show ¬i.val-2<83 by omega,show i.val-2<86 by omega]
        omega
      · have hcases : i=89 ∨ i=90 ∨ i=91 ∨ i=92 ∨ i=93 := by
          simp only [Fin.ext_iff]
          omega
        rcases hcases with h | h | h | h | h <;> subst i
        · exact ⟨86,rfl⟩
        · exact ⟨89,rfl⟩
        · exact ⟨90,rfl⟩
        · exact ⟨87,rfl⟩
        · exact ⟨88,rfl⟩

theorem cold_clear_run (b : ℕ) (source : List Bool) :
    ClockJoin.ReadyRun coldClearProgram (2*capacity b+4) (coldInput b source) (zeroed b source) := by
  have hready := RecoveryScratchErase.erase_ready (capacity b) 0 (fun _ : Fin 89 => []) (by intro i; simp)
  obtain ⟨r,hr,ht,hh,hs⟩ := hready
  have hi : Function.Injective (extend coldSlot) := extend_injective coldSlot cold_injective
    (fun j => (cold_not_driver j).1) (fun j => (cold_not_driver j).2)
  have ready : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 89) (2*capacity b+4)
      (Fin.addCases (m := 90) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 89) (n := 1) (motive := fun _ => List Bool)
          (fun _ => []) (fun _ => List.replicate (capacity b) true)) (fun _ => []))
      (eraseInput (capacity b) (fun _ : Fin 89 => List.replicate (capacity b) false)) := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    simpa only [eraseInput,Nat.zero_max,List.replicate_zero] using ht
  have hin : ∀ j,coldInput b source (extend coldSlot j)=
      (Fin.addCases (m := 90) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 89) (n := 1) (motive := fun _ => List Bool)
          (fun _ => []) (fun _ => List.replicate (capacity b) true)) (fun _ => [])) j := by
    intro j
    fin_cases j <;> rfl
  have hf := CompetitorRationalProducts.bounded_focus (extend coldSlot) hi _ _ _ ready (coldInput b source) hin
  have hout : install (extend coldSlot) (coldInput b source)
      (eraseInput (capacity b) (fun _ : Fin 89 => List.replicate (capacity b) false))=zeroed b source := by
    funext i
    by_cases h6 : i=6
    · subst i
      exact install_other (extend coldSlot) _ _ 6 (fun j => cold_not_retained j 6 (Or.inl rfl))
    · by_cases h84 : i=84
      · subst i
        exact install_other (extend coldSlot) _ _ 84 (fun j => cold_not_retained j 84 (Or.inr (Or.inl rfl)))
      · by_cases h88 : i=88
        · subst i
          exact install_other (extend coldSlot) _ _ 88 (fun j => cold_not_retained j 88 (Or.inr (Or.inr rfl)))
        · obtain ⟨j,hj⟩ := cold_image i h6 h84 h88
          subst i
          have he := install_slot (extend coldSlot) hi (coldInput b source)
            (eraseInput (capacity b) (fun _ : Fin 89 => List.replicate (capacity b) false)) j
          apply he.trans
          fin_cases j <;> rfl
  rw [hout] at hf
  exact hf

end NearCubicWires.RepairOrdinary.CompetitorSumFold

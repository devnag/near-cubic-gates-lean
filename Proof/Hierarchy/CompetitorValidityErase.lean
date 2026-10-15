import Proof.Hierarchy.CompetitorReusableDecision

/-! Physical reset before every validity record. The scalar width and the
global source cursor are retained; every other scalar-work cell and the
field-loader counter is overwritten using the paid reusable unary driver. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) : Fin 71 → ℕ := fun i => if i.val=67 then pos else 0
def cfg {s : ℕ} (q : Fin s) (pos : ℕ) (tapes : Fin 71 → List Bool) : Configuration 71 s :=
  ⟨q,heads pos,tapes⟩
def scratchSlot (i : Fin 67) : Fin 71 :=
  if i.val<6 then ⟨i.val,by omega⟩ else if i.val<66 then ⟨i.val+1,by omega⟩ else 68
def eraseSlots (j : Fin 69) : Fin 71 :=
  if h : j.val<67 then scratchSlot ⟨j.val,h⟩ else if j.val=67 then 69 else 70
def data (b : ℕ) (source : List Bool) (backing : Fin 67 → List Bool) : Fin 71 → List Bool := fun i =>
  if h : i.val<6 then backing ⟨i.val,by omega⟩
  else if i.val=6 then List.replicate (width b) true
  else if h : i.val<67 then backing ⟨i.val-1,by omega⟩
  else if i.val=67 then source
  else if i.val=68 then backing 66
  else if i.val=69 then List.replicate (capacity b) true
  else List.replicate (capacity b+1) false
def erased (b : ℕ) (source : List Bool) := data b source (fun _ => List.replicate (capacity b) false)
noncomputable def eraseProgram := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 67)

theorem scratch_injective : Function.Injective scratchSlot := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [scratchSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem erase_injective : Function.Injective eraseSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [eraseSlots,scratchSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem erase_not_width (j : Fin 69) : eraseSlots j≠6 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [eraseSlots,scratchSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega
theorem erase_not_source (j : Fin 69) : eraseSlots j≠67 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [eraseSlots,scratchSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem erase_image (i : Fin 71) (h6 : i≠6) (h67 : i≠67) : ∃ j,eraseSlots j=i := by
  have hi6 : i.val≠6 := fun h => h6 (Fin.ext h)
  have hi67 : i.val≠67 := fun h => h67 (Fin.ext h)
  by_cases hlo : i.val<6
  · refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    simp [eraseSlots,scratchSlot,hlo,show i.val<67 by omega]
  · by_cases hmid : i.val<67
    · refine ⟨⟨i.val-1,by omega⟩,?_⟩
      apply Fin.ext
      simp [eraseSlots,scratchSlot,show i.val-1<67 by omega,
        show ¬i.val-1<6 by omega,show i.val-1<66 by omega]
      omega
    · by_cases h68 : i.val=68
      · exact ⟨66,Fin.ext h68.symm⟩
      · by_cases h69 : i.val=69
        · exact ⟨67,Fin.ext h69.symm⟩
        · refine ⟨68,?_⟩
          change (70 : Fin 71)=i
          apply Fin.ext
          change 70=i.val
          omega

def eraseInput (b : ℕ) (backing : Fin 67 → List Bool) : Fin 69 → List Bool :=
  Fin.addCases (m := 68) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 67) (n := 1) (motive := fun _ => List Bool)
      backing (fun _ : Fin 1 => List.replicate (capacity b) true))
    (fun _ : Fin 1 => List.replicate (capacity b+1) false)
def eraseOutput (b : ℕ) : Fin 69 → List Bool := eraseInput b (fun _ => List.replicate (capacity b) false)

theorem data_erase_slot (b : ℕ) (source : List Bool) (backing : Fin 67 → List Bool) (j : Fin 69) :
    data b source backing (eraseSlots j)=eraseInput b backing j := by
  fin_cases j <;> rfl

theorem erase_run (b : ℕ) (source : List Bool) (pos : ℕ) (backing : Fin 67 → List Bool)
    (hb : ∀ j,(backing j).length≤capacity b) :
    ∃ r : ExecutionReceipt 71 4,
      runFrom eraseProgram (2*capacity b+4) (cfg eraseProgram.start pos (data b source backing))=some r ∧
      r.final.heads=heads pos ∧ r.final.tapes=erased b source ∧ r.steps=2*capacity b+4 := by
  have h : ReadyRun (RecoveryScratchErase.resetMachine 67) (2*capacity b+4)
      (eraseInput b backing) (eraseOutput b) := by
    simpa only [eraseInput,eraseOutput,max_self] using
      RecoveryScratchErase.erase_ready (capacity b) (capacity b+1) backing hb
  have hh : ∀ j,heads pos (eraseSlots j)=0 := by
    intro j
    have hj : (eraseSlots j).val≠67 := fun he => erase_not_source j (Fin.ext he)
    simp [heads,hj]
  obtain ⟨r,hr,hrh,hrt,hrs⟩ := HierarchyBinary.focused_run eraseSlots erase_injective _ _ _ h
    (heads pos) (data b source backing) hh (data_erase_slot b source backing)
  refine ⟨r,hr,hrh,?_,hrs⟩
  rw [hrt]
  funext i
  by_cases h6 : i=6
  · subst i
    exact install_other eraseSlots _ _ _ erase_not_width
  · by_cases h67 : i=67
    · subst i
      exact install_other eraseSlots _ _ _ erase_not_source
    · obtain ⟨j,hj⟩ := erase_image i h6 h67
      subst i
      exact (install_slot eraseSlots erase_injective _ _ j).trans
        (data_erase_slot b source (fun _ => List.replicate (capacity b) false) j).symm

end NearCubicWires.RepairOrdinary.CompetitorValidity

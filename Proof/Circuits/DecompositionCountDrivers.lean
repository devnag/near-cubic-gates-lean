import Proof.Circuits.DecompositionAtom

/-! Paid count copies from the two actual native header outputs. Only counts
are expanded to unary; integer magnitudes remain in their native binary form. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCountDrivers
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem template_source (n : ℕ) : UWalkUnary.source (n+2) n=UnaryTemplate.tape n := by
  have hn : n+2-(CompareMachine.word n).length=1 := by
    simp only [CompareMachine.word,List.length_cons,List.length_replicate]
    omega
  rw [UWalkUnary.source,ZeroPadding.pad,hn]
  rfl

theorem template_ready (sentinel extra : Bool) (n : ℕ) :
    ClockJoin.ReadyRun (UWalkUnary.machine sentinel extra) (2*n+6)
      ![UnaryTemplate.tape n,[],[]]
      ![UnaryTemplate.tape n,UWalkUnary.output sentinel extra n,List.replicate (n+2) false] := by
  simpa only [UWalkUnary.input,UWalkUnary.result,template_source] using
    UWalkUnary.ready sentinel extra (n+2) n

abbrev Store := Fin 14 → List Bool
def input (a m : ℕ) : Store := fun i =>
  if i.val=0 then UnaryTemplate.tape a else if i.val=1 then UnaryTemplate.tape m else []
def data1 (a m : ℕ) : Store := fun i =>
  if i.val=2 then List.replicate (a+1) true else if i.val=3 then List.replicate (a+2) false
  else input a m i
def data2 (a m : ℕ) : Store := fun i =>
  if i.val=4 then CompareMachine.word (a+1) else if i.val=5 then List.replicate (a+2) false
  else data1 a m i
def data3 (a m : ℕ) : Store := fun i =>
  if i.val=6 then CompareMachine.word m else if i.val=7 then List.replicate (m+2) false
  else data2 a m i
def slots1 : Fin 3 → Fin 14 := ![0,2,3]
def slots2 : Fin 3 → Fin 14 := ![0,4,5]
def slots3 : Fin 3 → Fin 14 := ![1,6,7]
noncomputable def phase1 := RecoveryFocus.machine slots1 (UWalkUnary.machine false true)
noncomputable def phase2 := RecoveryFocus.machine slots2 (UWalkUnary.machine true true)
noncomputable def phase3 := RecoveryFocus.machine slots3 (UWalkUnary.machine true false)
noncomputable def first := Composition.machine phase1 phase2
noncomputable def copies := Composition.machine first phase3
def copiesBudget (a m : ℕ) := 4*a+2*m+20

theorem ready1 (a m : ℕ) : ClockJoin.ReadyRun phase1 (2*a+6) (input a m) (data1 a m) := by
  have h := (template_ready false true a).focus slots1 (by decide) (input a m)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots1 (input a m)
      ![UnaryTemplate.tape a,UWalkUnary.output false true a,List.replicate (a+2) false]=data1 a m := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h2 : i.val≠2 := fun he => hi 1 (Fin.ext he.symm)
      have h3 : i.val≠3 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data1,h2,h3,ite_false]
  rw [ho] at h
  exact h

theorem ready2 (a m : ℕ) : ClockJoin.ReadyRun phase2 (2*a+6) (data1 a m) (data2 a m) := by
  have h := (template_ready true true a).focus slots2 (by decide) (data1 a m)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots2 (data1 a m)
      ![UnaryTemplate.tape a,UWalkUnary.output true true a,List.replicate (a+2) false]=data2 a m := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h4 : i.val≠4 := fun he => hi 1 (Fin.ext he.symm)
      have h5 : i.val≠5 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data2,h4,h5,ite_false]
  rw [ho] at h
  exact h

theorem ready3 (a m : ℕ) : ClockJoin.ReadyRun phase3 (2*m+6) (data2 a m) (data3 a m) := by
  have h := (template_ready true false m).focus slots3 (by decide) (data2 a m)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots3 (data2 a m)
      ![UnaryTemplate.tape m,UWalkUnary.output true false m,List.replicate (m+2) false]=data3 a m := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h6 : i.val≠6 := fun he => hi 1 (Fin.ext he.symm)
      have h7 : i.val≠7 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data3,h6,h7,ite_false]
  rw [ho] at h
  exact h

theorem copies_ready (a m : ℕ) :
    ClockJoin.ReadyRun copies (copiesBudget a m) (input a m) (data3 a m) := by
  have h := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ready1 a m) (ready2 a m)) (ready3 a m)
  have he : copiesBudget a m=((2*a+6)+1+(2*a+6))+1+(2*m+6) := by
    unfold copiesBudget
    omega
  rw [he]
  exact h

end NearCubicWires.RepairOrdinary.DecompositionCountDrivers

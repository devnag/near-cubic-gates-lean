import Proof.Supplier.EquationCountTools
import Proof.Hierarchy.CompetitorRationalProducts

/-! The actual parsed d/p/G/odd bank supplies all cut-loop counts and the
first two output-header values. Every copy and physical rewind is paid. -/
namespace NearCubicWires.RepairOrdinary.EquationCountCopies
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 16 → List Bool
def input (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=0 then UnaryTemplate.tape d else if i.val=1 then UnaryTemplate.tape p
  else if i.val=2 then UnaryTemplate.tape g else if i.val=3 then [odd] else []
def data1 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=4 then CompareMachine.word (2*d-odd.toNat) else if i.val=5 then List.replicate (EquationWeightCount.ticks d odd) false
  else input d p g odd i
def slots1 : Fin 4 → Fin 16 := ![0,3,4,5]
noncomputable def phase1 := RecoveryFocus.machine slots1 (EquationWeightCount.machine)
def data2 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=6 then CompareMachine.word (p+1) else if i.val=7 then List.replicate (p+2) false
  else data1 d p g odd i
def slots2 : Fin 3 → Fin 16 := ![1,6,7]
noncomputable def phase2 := RecoveryFocus.machine slots2 (UWalkUnary.machine true true)
def data3 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=8 then CompareMachine.word (p+2) else if i.val=9 then List.replicate (p+3) false
  else data2 d p g odd i
def slots3 : Fin 3 → Fin 16 := ![6,8,9]
noncomputable def phase3 := RecoveryFocus.machine slots3 (UWalkUnary.machine true true)
def data4 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=10 then CompareMachine.word g else if i.val=11 then List.replicate (g+2) false
  else data3 d p g odd i
def slots4 : Fin 3 → Fin 16 := ![2,10,11]
noncomputable def phase4 := RecoveryFocus.machine slots4 (UWalkUnary.machine true false)
def data5 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=12 then List.replicate d true else if i.val=13 then List.replicate (d+2) false
  else data4 d p g odd i
def slots5 : Fin 3 → Fin 16 := ![0,12,13]
noncomputable def phase5 := RecoveryFocus.machine slots5 (UWalkUnary.machine false false)
def data6 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=14 then List.replicate (p+1) true else if i.val=15 then List.replicate (p+2) false
  else data5 d p g odd i
def slots6 : Fin 3 → Fin 16 := ![1,14,15]
noncomputable def phase6 := RecoveryFocus.machine slots6 (UWalkUnary.machine false true)

theorem ready1 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase1 (4*d+6) (input d p g odd) (data1 d p g odd) := by
  have h := bounded_focus slots1 (by decide) _ _ _ (EquationWeightCount.ready d odd) (input d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots1 (input d p g odd) (EquationWeightCount.result d odd)=data1 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h4 : i.val≠4 := fun he => hi 2 (Fin.ext he.symm)
      have h5 : i.val≠5 := fun he => hi 3 (Fin.ext he.symm)
      simp only [data1,h4,h5,ite_false]
  rw [ho] at h
  exact h

theorem ready2 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase2 (2*p+6) (data1 d p g odd) (data2 d p g odd) := by
  have h := bounded_focus slots2 (by decide) _ _ _ (EquationCountTools.template_ready true true p) (data1 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots2 (data1 d p g odd) (![UnaryTemplate.tape p,UWalkUnary.output true true p,List.replicate (p+2) false])=data2 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h6 : i.val≠6 := fun he => hi 1 (Fin.ext he.symm)
      have h7 : i.val≠7 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data2,h6,h7,ite_false]
  rw [ho] at h
  exact h

theorem ready3 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase3 (2*(p+1)+6) (data2 d p g odd) (data3 d p g odd) := by
  have h := bounded_focus slots3 (by decide) _ _ _ (EquationCountTools.word_ready true true (p+1)) (data2 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots3 (data2 d p g odd) (![CompareMachine.word (p+1),UWalkUnary.output true true (p+1),List.replicate (p+1+2) false])=data3 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h8 : i.val≠8 := fun he => hi 1 (Fin.ext he.symm)
      have h9 : i.val≠9 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data3,h8,h9,ite_false]
  rw [ho] at h
  exact h

theorem ready4 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase4 (2*g+6) (data3 d p g odd) (data4 d p g odd) := by
  have h := bounded_focus slots4 (by decide) _ _ _ (EquationCountTools.template_ready true false g) (data3 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots4 (data3 d p g odd) (![UnaryTemplate.tape g,UWalkUnary.output true false g,List.replicate (g+2) false])=data4 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h10 : i.val≠10 := fun he => hi 1 (Fin.ext he.symm)
      have h11 : i.val≠11 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data4,h10,h11,ite_false]
  rw [ho] at h
  exact h

theorem ready5 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase5 (2*d+6) (data4 d p g odd) (data5 d p g odd) := by
  have h := bounded_focus slots5 (by decide) _ _ _ (EquationCountTools.template_ready false false d) (data4 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots5 (data4 d p g odd) (![UnaryTemplate.tape d,UWalkUnary.output false false d,List.replicate (d+2) false])=data5 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h12 : i.val≠12 := fun he => hi 1 (Fin.ext he.symm)
      have h13 : i.val≠13 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data5,h12,h13,ite_false]
  rw [ho] at h
  exact h

theorem ready6 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase6 (2*p+6) (data5 d p g odd) (data6 d p g odd) := by
  have h := bounded_focus slots6 (by decide) _ _ _ (EquationCountTools.template_ready false true p) (data5 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots6 (data5 d p g odd) (![UnaryTemplate.tape p,UWalkUnary.output false true p,List.replicate (p+2) false])=data6 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h14 : i.val≠14 := fun he => hi 1 (Fin.ext he.symm)
      have h15 : i.val≠15 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data6,h14,h15,ite_false]
  rw [ho] at h
  exact h

noncomputable def first2 := Composition.machine phase1 phase2
noncomputable def first3 := Composition.machine first2 phase3
noncomputable def first4 := Composition.machine first3 phase4
noncomputable def first5 := Composition.machine first4 phase5
noncomputable def machine := Composition.machine first5 phase6
def budget (d p g : ℕ) := 6*d+6*p+2*g+43

theorem copies_ready (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun machine (budget d p g) (input d p g odd) (data6 d p g odd) := by
  have h2 := ClockJoin.join _ _ _ _ _ _ _ (ready1 d p g odd) (ready2 d p g odd)
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 (ready3 d p g odd)
  have h4 := ClockJoin.join _ _ _ _ _ _ _ h3 (ready4 d p g odd)
  have h5 := ClockJoin.join _ _ _ _ _ _ _ h4 (ready5 d p g odd)
  have h6 := ClockJoin.join _ _ _ _ _ _ _ h5 (ready6 d p g odd)
  have he : (((((4*d+6)+1+(2*p+6))+1+(2*(p+1)+6))+1+(2*g+6))+1+(2*d+6))+1+(2*p+6)=budget d p g := by
    unfold budget
    omega
  rw [he] at h6
  exact h6

end NearCubicWires.RepairOrdinary.EquationCountCopies

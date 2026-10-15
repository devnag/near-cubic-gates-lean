import Proof.Supplier.EquationCountCopies

/-! The paid row-capacity caller: actual parsed counts produce the doubled
gate header value and C=128*(2d+1)*(p+1), retaining all earlier cut drivers. -/
namespace NearCubicWires.RepairOrdinary.EquationCountCapacity
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 32 → List Bool
def input (d p g : ℕ) (odd : Bool) : Store :=
  fun i => Fin.addCases (m := 16) (n := 16) (motive := fun _ => List Bool)
    (EquationCountCopies.data6 d p g odd) (fun _ => []) i

theorem fixed_ready (bits : List Bool) :
    ClockJoin.ReadyRun (HierarchyFixedWord.machine bits) (2*bits.length+2)
      ![[],[]] ![bits,List.replicate bits.length false] := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready bits
  have hi : (![[],[]] : Fin 2 → List Bool)=(fun _ => []) := by
    funext i; fin_cases i <;> rfl
  rw [hi]
  exact ⟨r,hr,ht,hh,hs.le⟩

def data1 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=16 then [false] else if i.val=17 then List.replicate 1 false
  else input d p g odd i
def slots1 : Fin 2 → Fin 32 := ![16,17]
noncomputable def phase1 := RecoveryFocus.machine slots1 (HierarchyFixedWord.machine [false])
def data2 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=18 then CompareMachine.word (2*g) else if i.val=19 then List.replicate (EquationWeightCount.ticks g false) false
  else data1 d p g odd i
def slots2 : Fin 4 → Fin 32 := ![2,16,18,19]
noncomputable def phase2 := RecoveryFocus.machine slots2 (EquationWeightCount.machine)
def data3 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=20 then List.replicate (2*g) true else if i.val=21 then List.replicate (2*g+2) false
  else data2 d p g odd i
def slots3 : Fin 3 → Fin 32 := ![18,20,21]
noncomputable def phase3 := RecoveryFocus.machine slots3 (UWalkUnary.machine false false)
def data4 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=22 then CompareMachine.word (2*d) else if i.val=23 then List.replicate (EquationWeightCount.ticks d false) false
  else data3 d p g odd i
def slots4 : Fin 4 → Fin 32 := ![0,16,22,23]
noncomputable def phase4 := RecoveryFocus.machine slots4 (EquationWeightCount.machine)
def data5 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=24 then List.replicate (2*d+1) true else if i.val=25 then List.replicate (2*d+2) false
  else data4 d p g odd i
def slots5 : Fin 3 → Fin 32 := ![22,24,25]
noncomputable def phase5 := RecoveryFocus.machine slots5 (UWalkUnary.machine false true)
def data6 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=26 then List.replicate ((2*d+1)*(p+1)) true else if i.val=27 then List.replicate ((2*d+1)*(2*(p+1)+3)+2) false
  else data5 d p g odd i
def slots6 : Fin 4 → Fin 32 := ![24,6,26,27]
noncomputable def phase6 := RecoveryFocus.machine slots6 (ClockUnaryProduct.machine)
def data7 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=28 then CompareMachine.word 128 else if i.val=29 then List.replicate 129 false
  else data6 d p g odd i
def slots7 : Fin 2 → Fin 32 := ![28,29]
noncomputable def phase7 := RecoveryFocus.machine slots7 (HierarchyFixedWord.machine (CompareMachine.word 128))
def data8 (d p g : ℕ) (odd : Bool) : Store := fun i =>
  if i.val=30 then List.replicate ((2*d+1)*(p+1)*128) true else if i.val=31 then List.replicate ((2*d+1)*(p+1)*(2*128+3)+2) false
  else data7 d p g odd i
def slots8 : Fin 4 → Fin 32 := ![26,28,30,31]
noncomputable def phase8 := RecoveryFocus.machine slots8 (ClockUnaryProduct.machine)

theorem ready1 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase1 (4) (input d p g odd) (data1 d p g odd) := by
  have h := bounded_focus slots1 (by decide) _ _ _ (fixed_ready [false]) (input d p g odd)
    (by intro j; fin_cases j <;> rfl)
  change ClockJoin.ReadyRun phase1 4 (input d p g odd)
    (install slots1 (input d p g odd) ![[false],List.replicate 1 false]) at h
  have ho : install slots1 (input d p g odd) (![[false],List.replicate 1 false])=data1 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h16 : i.val≠16 := fun he => hi 0 (Fin.ext he.symm)
      have h17 : i.val≠17 := fun he => hi 1 (Fin.ext he.symm)
      simp only [data1,h16,h17,ite_false]
  rw [ho] at h
  exact h

theorem ready2 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase2 (4*g+6) (data1 d p g odd) (data2 d p g odd) := by
  have h := bounded_focus slots2 (by decide) _ _ _ (EquationWeightCount.ready g false) (data1 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots2 (data1 d p g odd) (EquationWeightCount.result g false)=data2 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h18 : i.val≠18 := fun he => hi 2 (Fin.ext he.symm)
      have h19 : i.val≠19 := fun he => hi 3 (Fin.ext he.symm)
      simp only [data2,h18,h19,ite_false]
  rw [ho] at h
  exact h

theorem ready3 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase3 (4*g+6) (data2 d p g odd) (data3 d p g odd) := by
  have h := bounded_focus slots3 (by decide) _ _ _ (EquationCountTools.word_ready false false (2*g)) (data2 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots3 (data2 d p g odd) (![CompareMachine.word (2*g),UWalkUnary.output false false (2*g),List.replicate (2*g+2) false])=data3 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h20 : i.val≠20 := fun he => hi 1 (Fin.ext he.symm)
      have h21 : i.val≠21 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data3,h20,h21,ite_false]
  rw [ho] at h
  have hb : 2*(2*g)+6=4*g+6 := by omega
  rw [hb] at h
  exact h

theorem ready4 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase4 (4*d+6) (data3 d p g odd) (data4 d p g odd) := by
  have h := bounded_focus slots4 (by decide) _ _ _ (EquationWeightCount.ready d false) (data3 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots4 (data3 d p g odd) (EquationWeightCount.result d false)=data4 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h22 : i.val≠22 := fun he => hi 2 (Fin.ext he.symm)
      have h23 : i.val≠23 := fun he => hi 3 (Fin.ext he.symm)
      simp only [data4,h22,h23,ite_false]
  rw [ho] at h
  exact h

theorem ready5 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase5 (4*d+6) (data4 d p g odd) (data5 d p g odd) := by
  have h := bounded_focus slots5 (by decide) _ _ _ (EquationCountTools.word_ready false true (2*d)) (data4 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots5 (data4 d p g odd) (![CompareMachine.word (2*d),UWalkUnary.output false true (2*d),List.replicate (2*d+2) false])=data5 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h24 : i.val≠24 := fun he => hi 1 (Fin.ext he.symm)
      have h25 : i.val≠25 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data5,h24,h25,ite_false]
  rw [ho] at h
  have hb : 2*(2*d)+6=4*d+6 := by omega
  rw [hb] at h
  exact h

theorem ready6 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase6 (2*((2*d+1)*(2*(p+1)+3)+2)+2) (data5 d p g odd) (data6 d p g odd) := by
  have h := bounded_focus slots6 (by decide) _ _ _ (EquationCountTools.product_ready (2*d+1) (p+1)) (data5 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots6 (data5 d p g odd) (![List.replicate (2*d+1) true,CompareMachine.word (p+1),List.replicate ((2*d+1)*(p+1)) true,List.replicate ((2*d+1)*(2*(p+1)+3)+2) false])=data6 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h26 : i.val≠26 := fun he => hi 2 (Fin.ext he.symm)
      have h27 : i.val≠27 := fun he => hi 3 (Fin.ext he.symm)
      simp only [data6,h26,h27,ite_false]
  rw [ho] at h
  exact h

theorem ready7 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase7 (260) (data6 d p g odd) (data7 d p g odd) := by
  have h := bounded_focus slots7 (by decide) _ _ _ (fixed_ready (CompareMachine.word 128)) (data6 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  change ClockJoin.ReadyRun phase7 260 (data6 d p g odd)
    (install slots7 (data6 d p g odd) ![CompareMachine.word 128,List.replicate 129 false]) at h
  have ho : install slots7 (data6 d p g odd) (![CompareMachine.word 128,List.replicate 129 false])=data7 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h28 : i.val≠28 := fun he => hi 0 (Fin.ext he.symm)
      have h29 : i.val≠29 := fun he => hi 1 (Fin.ext he.symm)
      simp only [data7,h28,h29,ite_false]
  rw [ho] at h
  exact h

theorem ready8 (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun phase8 (2*((2*d+1)*(p+1)*(2*128+3)+2)+2) (data7 d p g odd) (data8 d p g odd) := by
  have h := bounded_focus slots8 (by decide) _ _ _ (EquationCountTools.product_ready ((2*d+1)*(p+1)) 128) (data7 d p g odd)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots8 (data7 d p g odd) (![List.replicate ((2*d+1)*(p+1)) true,CompareMachine.word 128,List.replicate ((2*d+1)*(p+1)*128) true,List.replicate ((2*d+1)*(p+1)*(2*128+3)+2) false])=data8 d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h30 : i.val≠30 := fun he => hi 2 (Fin.ext he.symm)
      have h31 : i.val≠31 := fun he => hi 3 (Fin.ext he.symm)
      simp only [data8,h30,h31,ite_false]
  rw [ho] at h
  exact h

noncomputable def first2 := Composition.machine phase1 phase2
noncomputable def first3 := Composition.machine first2 phase3
noncomputable def first4 := Composition.machine first3 phase4
noncomputable def first5 := Composition.machine first4 phase5
noncomputable def first6 := Composition.machine first5 phase6
noncomputable def first7 := Composition.machine first6 phase7
noncomputable def machine := Composition.machine first7 phase8

def budget (d p g : ℕ) := (((((((4)+1+(4*g+6))+1+(4*g+6))+1+(4*d+6))+1+(4*d+6))+1+(2*((2*d+1)*(2*(p+1)+3)+2)+2))+1+(260))+1+(2*((2*d+1)*(p+1)*(2*128+3)+2)+2)
def capacity (d p : ℕ) := 128*(2*d+1)*(p+1)

theorem capacity_ready (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun machine (budget d p g) (input d p g odd) (data8 d p g odd) := by
  have h2 := ClockJoin.join _ _ _ _ _ _ _ (ready1 d p g odd) (ready2 d p g odd)
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 (ready3 d p g odd)
  have h4 := ClockJoin.join _ _ _ _ _ _ _ h3 (ready4 d p g odd)
  have h5 := ClockJoin.join _ _ _ _ _ _ _ h4 (ready5 d p g odd)
  have h6 := ClockJoin.join _ _ _ _ _ _ _ h5 (ready6 d p g odd)
  have h7 := ClockJoin.join _ _ _ _ _ _ _ h6 (ready7 d p g odd)
  have h8 := ClockJoin.join _ _ _ _ _ _ _ h7 (ready8 d p g odd)
  exact h8

theorem result_capacity (d p g : ℕ) (odd : Bool) :
    data8 d p g odd 30=List.replicate (capacity d p) true := by
  change List.replicate ((2*d+1)*(p+1)*128) true=_
  congr 1
  unfold capacity
  ring

theorem result_doubleG (d p g : ℕ) (odd : Bool) :
    data8 d p g odd 20=List.replicate (2*g) true := rfl

theorem retains (d p g : ℕ) (odd : Bool) (i : Fin 16) :
    data8 d p g odd (i.castAdd 16)=EquationCountCopies.data6 d p g odd i := by
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.EquationCountCapacity

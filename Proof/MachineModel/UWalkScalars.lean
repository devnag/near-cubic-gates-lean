import Proof.MachineModel.UWalkArithmetic

/-! Actual width-normalized initial values for the walk. The three zero
fields and the unit field are independently written from blank workspace. -/
namespace NearCubicWires.RepairOrdinary.UWalkNumbers
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def unitOutput (w : ℕ) : Fin 5 → List Bool :=
  ![List.replicate w true,frame [true],frame (binary w 1),[true],List.replicate (2*w+1) false]
theorem unit_ready (w : ℕ) (hw : 1 ≤ w) : ClockJoin.ReadyRun ClockNormalize.machine
    (4*w+4) (ClockNormalize.input w [true]) (unitOutput w) := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockScalarFields.scalar_run w [true] (by simpa using hw)
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i; fin_cases i
  · exact h0
  · exact h1
  · simpa [unitOutput,RadixSemantics.value] using h2
  · exact h3
  · exact h4

def slotsZ1 : Fin 5 → Fin 42 := ![0,25,26,27,28]
theorem injectiveZ1 : Function.Injective slotsZ1 := by decide
noncomputable def phaseZ1 := RecoveryFocus.machine slotsZ1 (UWitnessBootstrap.zeroMachine)
def afterZ1 (w t j c : ℕ) : Store := fun i =>
  if i.val=25 then [false] else if i.val=26 then frame (binary w 0) else if i.val=27 then [true] else if i.val=28 then List.replicate (2*w+1) false else afterC w t j c i

theorem readyZ1 (w t j c : ℕ) : ClockJoin.ReadyRun phaseZ1 (4*w+6)
    (afterC w t j c) (afterZ1 w t j c) := by
  have h := (UWitnessBootstrap.zero_ready w).focus slotsZ1 injectiveZ1 (afterC w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,input,slotsZ1,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases])
  have ho : install slotsZ1 (afterC w t j c) (UWitnessBootstrap.output5 w)=afterZ1 w t j c := by
    apply HierarchyWidth.install_eq _ injectiveZ1
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,input,slotsZ1,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases]
    · intro i hi
      have hn25 : i.val≠25 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      have hn26 : i.val≠26 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      have hn27 : i.val≠27 := by
        intro he
        apply hi 3
        apply Fin.ext
        exact he.symm
      have hn28 : i.val≠28 := by
        intro he
        apply hi 4
        apply Fin.ext
        exact he.symm
      simp [afterZ1,hn25,hn26,hn27,hn28]
  rw [ho] at h
  exact h

def slotsZ2 : Fin 5 → Fin 42 := ![0,29,30,31,32]
theorem injectiveZ2 : Function.Injective slotsZ2 := by decide
noncomputable def phaseZ2 := RecoveryFocus.machine slotsZ2 (UWitnessBootstrap.zeroMachine)
def afterZ2 (w t j c : ℕ) : Store := fun i =>
  if i.val=29 then [false] else if i.val=30 then frame (binary w 0) else if i.val=31 then [true] else if i.val=32 then List.replicate (2*w+1) false else afterZ1 w t j c i

theorem readyZ2 (w t j c : ℕ) : ClockJoin.ReadyRun phaseZ2 (4*w+6)
    (afterZ1 w t j c) (afterZ2 w t j c) := by
  have h := (UWitnessBootstrap.zero_ready w).focus slotsZ2 injectiveZ2 (afterZ1 w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,afterZ2,input,slotsZ2,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases])
  have ho : install slotsZ2 (afterZ1 w t j c) (UWitnessBootstrap.output5 w)=afterZ2 w t j c := by
    apply HierarchyWidth.install_eq _ injectiveZ2
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,afterZ2,input,slotsZ2,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases]
    · intro i hi
      have hn29 : i.val≠29 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      have hn30 : i.val≠30 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      have hn31 : i.val≠31 := by
        intro he
        apply hi 3
        apply Fin.ext
        exact he.symm
      have hn32 : i.val≠32 := by
        intro he
        apply hi 4
        apply Fin.ext
        exact he.symm
      simp [afterZ2,hn29,hn30,hn31,hn32]
  rw [ho] at h
  exact h

def slotsZ3 : Fin 5 → Fin 42 := ![0,33,34,35,36]
theorem injectiveZ3 : Function.Injective slotsZ3 := by decide
noncomputable def phaseZ3 := RecoveryFocus.machine slotsZ3 (UWitnessBootstrap.zeroMachine)
def afterZ3 (w t j c : ℕ) : Store := fun i =>
  if i.val=33 then [false] else if i.val=34 then frame (binary w 0) else if i.val=35 then [true] else if i.val=36 then List.replicate (2*w+1) false else afterZ2 w t j c i

theorem readyZ3 (w t j c : ℕ) : ClockJoin.ReadyRun phaseZ3 (4*w+6)
    (afterZ2 w t j c) (afterZ3 w t j c) := by
  have h := (UWitnessBootstrap.zero_ready w).focus slotsZ3 injectiveZ3 (afterZ2 w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,afterZ2,afterZ3,input,slotsZ3,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases])
  have ho : install slotsZ3 (afterZ2 w t j c) (UWitnessBootstrap.output5 w)=afterZ3 w t j c := by
    apply HierarchyWidth.install_eq _ injectiveZ3
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,afterZ2,afterZ3,input,slotsZ3,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases]
    · intro i hi
      have hn33 : i.val≠33 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      have hn34 : i.val≠34 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      have hn35 : i.val≠35 := by
        intro he
        apply hi 3
        apply Fin.ext
        exact he.symm
      have hn36 : i.val≠36 := by
        intro he
        apply hi 4
        apply Fin.ext
        exact he.symm
      simp [afterZ3,hn33,hn34,hn35,hn36]
  rw [ho] at h
  exact h

def slotsOne : Fin 2 → Fin 42 := ![37,38]
theorem injectiveOne : Function.Injective slotsOne := by decide
noncomputable def phaseOne := RecoveryFocus.machine slotsOne (HierarchyFixedWord.machine (frame [true]))
def afterOne (w t j c : ℕ) : Store := fun i =>
  if i.val=37 then frame [true] else if i.val=38 then List.replicate 3 false else afterZ3 w t j c i

theorem readyOne (w t j c : ℕ) : ClockJoin.ReadyRun phaseOne (8)
    (afterZ3 w t j c) (afterOne w t j c) := by
  have h := (fixed_ready (frame [true])).focus slotsOne injectiveOne (afterZ3 w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,afterZ2,afterZ3,afterOne,input,slotsOne,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases])
  have ho : install slotsOne (afterZ3 w t j c) (![frame [true],List.replicate 3 false])=afterOne w t j c := by
    apply HierarchyWidth.install_eq _ injectiveOne
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,afterZ2,afterZ3,afterOne,input,slotsOne,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases]
    · intro i hi
      have hn37 : i.val≠37 := by
        intro he
        apply hi 0
        apply Fin.ext
        exact he.symm
      have hn38 : i.val≠38 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      simp [afterOne,hn37,hn38]
  change ClockJoin.ReadyRun phaseOne 8 (afterZ3 w t j c)
    (install slotsOne (afterZ3 w t j c) ![frame [true],List.replicate 3 false]) at h
  rw [ho] at h
  exact h

def slotsUnit : Fin 5 → Fin 42 := ![0,37,39,40,41]
theorem injectiveUnit : Function.Injective slotsUnit := by decide
noncomputable def phaseUnit := RecoveryFocus.machine slotsUnit (ClockNormalize.machine)
def afterUnit (w t j c : ℕ) : Store := fun i =>
  if i.val=39 then frame (binary w 1) else if i.val=40 then [true] else if i.val=41 then List.replicate (2*w+1) false else afterOne w t j c i

theorem readyUnit (w t j c : ℕ) (hw : 1 ≤ w) : ClockJoin.ReadyRun phaseUnit (4*w+4)
    (afterOne w t j c) (afterUnit w t j c) := by
  have h := (unit_ready w hw).focus slotsUnit injectiveUnit (afterOne w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,afterZ2,afterZ3,afterOne,afterUnit,input,slotsUnit,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases])
  have ho : install slotsUnit (afterOne w t j c) (unitOutput w)=afterUnit w t j c := by
    apply HierarchyWidth.install_eq _ injectiveUnit
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,afterZ1,afterZ2,afterZ3,afterOne,afterUnit,input,slotsUnit,UWitnessBootstrap.initial5,UWitnessBootstrap.output5,ClockNormalize.input,unitOutput,Fin.addCases]
    · intro i hi
      have hn39 : i.val≠39 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      have hn40 : i.val≠40 := by
        intro he
        apply hi 3
        apply Fin.ext
        exact he.symm
      have hn41 : i.val≠41 := by
        intro he
        apply hi 4
        apply Fin.ext
        exact he.symm
      simp [afterUnit,hn39,hn40,hn41]
  rw [ho] at h
  exact h

noncomputable def core := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine arithmeticMachine phaseZ1) phaseZ2) phaseZ3) phaseOne) phaseUnit

def coreCost (w t j : ℕ) := (((((arithmeticCost w t j+1+(4*w+6))+1+(4*w+6))+1+(4*w+6))+1+8)+1+(4*w+4))

theorem core_ready (w t j c : ℕ) (hw : 1 ≤ w) : ClockJoin.ReadyRun core
    (coreCost w t j) (input w t j c) (afterUnit w t j c) := by
  have h1 := ClockJoin.join _ _ _ _ _ _ _ (arithmetic_ready w t j c) (readyZ1 w t j c)
  have h2 := ClockJoin.join _ _ _ _ _ _ _ h1 (readyZ2 w t j c)
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 (readyZ3 w t j c)
  have h4 := ClockJoin.join _ _ _ _ _ _ _ h3 (readyOne w t j c)
  exact ClockJoin.join _ _ _ _ _ _ _ h4 (readyUnit w t j c hw)

def budget (w t j : ℕ) := 8192*(t+j+1)*(w+1)
theorem core_bound (w t j : ℕ) : coreCost w t j+4 ≤ budget w t j := by
  dsimp [coreCost,arithmeticCost,productCost,d,p,q,budget]
  nlinarith

end NearCubicWires.RepairOrdinary.UWalkNumbers

import Proof.MachineModel.UWalkUnary
import Proof.MachineModel.UWalkCapacity

/-! Actual short arithmetic for the walk capacity. Every installed field
below is the exact endpoint of a physically executed focused supplier. -/
namespace NearCubicWires.RepairOrdinary.UWalkNumbers
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 42 → List Bool
def d (t j : ℕ) := (t+1)+j
def p (w t j : ℕ) := d t j*(w+1)
def q (w t j : ℕ) := p w t j*128
def productCost (a b : ℕ) := 2*(a*(2*b+3)+2)+2

def input (w t j c : ℕ) : Store := fun i =>
  if i.val=0 then List.replicate w true else if i.val=1 then CapMachine.counter c t
  else if i.val=2 then CompareMachine.word j else if i.val=3 then CompareMachine.word w else []

def productInput (a b : ℕ) : Fin 4 → List Bool :=
  ![List.replicate a true,false::List.replicate b true,[],[]]
def productOutput (a b : ℕ) : Fin 4 → List Bool :=
  ![List.replicate a true,false::List.replicate b true,List.replicate (a*b) true,
    List.replicate (a*(2*b+3)+2) false]
theorem product_ready (a b : ℕ) : ClockJoin.ReadyRun ClockUnaryProduct.machine
    (productCost a b) (productInput a b) (productOutput a b) := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run a b
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate a true,false::List.replicate b true,[]] (fun _ : Fin 1 => []))=productInput a b := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem fixed_ready (bits : List Bool) : ClockJoin.ReadyRun (HierarchyFixedWord.machine bits)
    (2*bits.length+2) (fun _ => []) ![bits,List.replicate bits.length false] := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready bits
  exact ⟨r,hr,ht,hh,hs.le⟩

def slotsT : Fin 3 → Fin 42 := ![1,4,5]
theorem injectiveT : Function.Injective slotsT := by decide
noncomputable def phaseT := RecoveryFocus.machine slotsT (UWalkUnary.machine false true)
def afterT (w t j c : ℕ) : Store := fun i =>
  if i.val=4 then List.replicate (t+1) true else if i.val=5 then List.replicate (t+2) false else input w t j c i

theorem readyT (w t j c : ℕ) : ClockJoin.ReadyRun phaseT (2*t+6)
    (input w t j c) (afterT w t j c) := by
  have h := (UWalkUnary.ready false true (c+2) t).focus slotsT injectiveT (input w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,input,slotsT,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases])
  have ho : install slotsT (input w t j c) (UWalkUnary.result false true (c+2) t)=afterT w t j c := by
    apply HierarchyWidth.install_eq _ injectiveT
    · intro k; fin_cases k <;> dsimp [afterT,input,slotsT,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]
    · intro i hi
      have hn4 : i.val≠4 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      have hn5 : i.val≠5 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      simp [afterT,hn4,hn5]
  rw [ho] at h
  simpa [phaseT,productCost,d,p,q] using h

def slotsJ : Fin 3 → Fin 42 := ![2,6,7]
theorem injectiveJ : Function.Injective slotsJ := by decide
noncomputable def phaseJ := RecoveryFocus.machine slotsJ (UWalkUnary.machine false false)
def afterJ (w t j c : ℕ) : Store := fun i =>
  if i.val=6 then List.replicate j true else if i.val=7 then List.replicate (j+2) false else afterT w t j c i

theorem readyJ (w t j c : ℕ) : ClockJoin.ReadyRun phaseJ (2*j+6)
    (afterT w t j c) (afterJ w t j c) := by
  have h := (UWalkUnary.ready false false 0 j).focus slotsJ injectiveJ (afterT w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,input,slotsJ,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]; simp)
  have ho : install slotsJ (afterT w t j c) (UWalkUnary.result false false 0 j)=afterJ w t j c := by
    apply HierarchyWidth.install_eq _ injectiveJ
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,input,slotsJ,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]; simp
    · intro i hi
      have hn6 : i.val≠6 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      have hn7 : i.val≠7 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      simp [afterJ,hn6,hn7]
  rw [ho] at h
  simpa [phaseJ,productCost,d,p,q] using h

def slotsW : Fin 3 → Fin 42 := ![3,8,9]
theorem injectiveW : Function.Injective slotsW := by decide
noncomputable def phaseW := RecoveryFocus.machine slotsW (UWalkUnary.machine true true)
def afterW (w t j c : ℕ) : Store := fun i =>
  if i.val=8 then false::List.replicate (w+1) true else if i.val=9 then List.replicate (w+2) false else afterJ w t j c i

theorem readyW (w t j c : ℕ) : ClockJoin.ReadyRun phaseW (2*w+6)
    (afterJ w t j c) (afterW w t j c) := by
  have h := (UWalkUnary.ready true true 0 w).focus slotsW injectiveW (afterJ w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,input,slotsW,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]; simp)
  have ho : install slotsW (afterJ w t j c) (UWalkUnary.result true true 0 w)=afterW w t j c := by
    apply HierarchyWidth.install_eq _ injectiveW
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,input,slotsW,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]; simp
    · intro i hi
      have hn8 : i.val≠8 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      have hn9 : i.val≠9 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      simp [afterW,hn8,hn9]
  rw [ho] at h
  simpa [phaseW,productCost,d,p,q] using h

def slotsD : Fin 4 → Fin 42 := ![4,6,10,11]
theorem injectiveD : Function.Injective slotsD := by decide
noncomputable def phaseD := RecoveryFocus.machine slotsD (ClockUnarySum.machine)
def afterD (w t j c : ℕ) : Store := fun i =>
  if i.val=10 then List.replicate (d t j) true else if i.val=11 then List.replicate (d t j+2) false else afterW w t j c i

theorem readyD (w t j c : ℕ) : ClockJoin.ReadyRun phaseD (2*d t j+6)
    (afterW w t j c) (afterD w t j c) := by
  have h := (ClockUnarySum.sum_ready (t+1) j).focus slotsD injectiveD (afterW w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,input,slotsD,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases])
  have ho : install slotsD (afterW w t j c) (![List.replicate (t+1) true,List.replicate j true,List.replicate (d t j) true,List.replicate (d t j+2) false])=afterD w t j c := by
    apply HierarchyWidth.install_eq _ injectiveD
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,input,slotsD,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]
    · intro i hi
      have hn10 : i.val≠10 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      have hn11 : i.val≠11 := by
        intro he
        apply hi 3
        apply Fin.ext
        exact he.symm
      simp [afterD,hn10,hn11]
  dsimp only [d] at ho
  rw [ho] at h
  simpa [phaseD,productCost,d,p,q] using h

def slotsP : Fin 4 → Fin 42 := ![10,8,12,13]
theorem injectiveP : Function.Injective slotsP := by decide
noncomputable def phaseP := RecoveryFocus.machine slotsP (ClockUnaryProduct.machine)
def afterP (w t j c : ℕ) : Store := fun i =>
  if i.val=12 then List.replicate (p w t j) true else if i.val=13 then List.replicate (d t j*(2*(w+1)+3)+2) false else afterD w t j c i

theorem readyP (w t j c : ℕ) : ClockJoin.ReadyRun phaseP (productCost (d t j) (w+1))
    (afterD w t j c) (afterP w t j c) := by
  have h := (product_ready (d t j) (w+1)).focus slotsP injectiveP (afterD w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,input,slotsP,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases])
  have ho : install slotsP (afterD w t j c) (productOutput (d t j) (w+1))=afterP w t j c := by
    apply HierarchyWidth.install_eq _ injectiveP
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,input,slotsP,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]
    · intro i hi
      have hn12 : i.val≠12 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      have hn13 : i.val≠13 := by
        intro he
        apply hi 3
        apply Fin.ext
        exact he.symm
      simp [afterP,hn12,hn13]
  rw [ho] at h
  simpa [phaseP,productCost,d,p,q] using h

def slotsK : Fin 2 → Fin 42 := ![14,15]
theorem injectiveK : Function.Injective slotsK := by decide
noncomputable def phaseK := RecoveryFocus.machine slotsK (HierarchyFixedWord.machine (false::List.replicate 128 true))
def afterK (w t j c : ℕ) : Store := fun i =>
  if i.val=14 then false::List.replicate 128 true else if i.val=15 then List.replicate 129 false else afterP w t j c i

theorem readyK (w t j c : ℕ) : ClockJoin.ReadyRun phaseK (260)
    (afterP w t j c) (afterK w t j c) := by
  have h := (fixed_ready (false::List.replicate 128 true)).focus slotsK injectiveK (afterP w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,input,slotsK,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases])
  have ho : install slotsK (afterP w t j c) (![false::List.replicate 128 true,List.replicate 129 false])=afterK w t j c := by
    apply HierarchyWidth.install_eq _ injectiveK
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,input,slotsK,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]
    · intro i hi
      have hn14 : i.val≠14 := by
        intro he
        apply hi 0
        apply Fin.ext
        exact he.symm
      have hn15 : i.val≠15 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      simp [afterK,hn14,hn15]
  change ClockJoin.ReadyRun phaseK 260 (afterP w t j c)
    (install slotsK (afterP w t j c) ![false::List.replicate 128 true,List.replicate 129 false]) at h
  rw [ho] at h
  simpa [phaseK,productCost,d,p,q] using h

def slotsQ : Fin 4 → Fin 42 := ![12,14,16,17]
theorem injectiveQ : Function.Injective slotsQ := by decide
noncomputable def phaseQ := RecoveryFocus.machine slotsQ (ClockUnaryProduct.machine)
def afterQ (w t j c : ℕ) : Store := fun i =>
  if i.val=16 then List.replicate (q w t j) true else if i.val=17 then List.replicate (p w t j*(2*128+3)+2) false else afterK w t j c i

theorem readyQ (w t j c : ℕ) : ClockJoin.ReadyRun phaseQ (productCost (p w t j) 128)
    (afterK w t j c) (afterQ w t j c) := by
  have h := (product_ready (p w t j) 128).focus slotsQ injectiveQ (afterK w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,input,slotsQ,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases])
  have ho : install slotsQ (afterK w t j c) (productOutput (p w t j) 128)=afterQ w t j c := by
    apply HierarchyWidth.install_eq _ injectiveQ
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,input,slotsQ,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]
    · intro i hi
      have hn16 : i.val≠16 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      have hn17 : i.val≠17 := by
        intro he
        apply hi 3
        apply Fin.ext
        exact he.symm
      simp [afterQ,hn16,hn17]
  rw [ho] at h
  simpa [phaseQ,productCost,d,p,q] using h

def slotsC : Fin 8 → Fin 42 := ![16,18,19,20,21,22,23,24]
theorem injectiveC : Function.Injective slotsC := by decide
noncomputable def phaseC := RecoveryFocus.machine slotsC (UWalkCapacity.machine)
def afterC (w t j c : ℕ) : Store := fun i =>
  if i.val=18 then List.replicate (q w t j+1) true else if i.val=19 then List.replicate (q w t j+1) false else if i.val=20 then List.replicate (q w t j+1) false else if i.val=21 then List.replicate (q w t j+1) false else if i.val=22 then List.replicate (q w t j+1) false else if i.val=23 then List.replicate (q w t j+2) false else if i.val=24 then List.replicate (q w t j+2) false else afterQ w t j c i

theorem readyC (w t j c : ℕ) : ClockJoin.ReadyRun phaseC (2*q w t j+6)
    (afterQ w t j c) (afterC w t j c) := by
  have h := (UWalkCapacity.ready (q w t j)).focus slotsC injectiveC (afterQ w t j c)
    (by intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,input,slotsC,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases])
  have ho : install slotsC (afterQ w t j c) (UWalkCapacity.result (q w t j))=afterC w t j c := by
    apply HierarchyWidth.install_eq _ injectiveC
    · intro k; fin_cases k <;> dsimp [afterT,afterJ,afterW,afterD,afterP,afterK,afterQ,afterC,input,slotsC,UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UWalkUnary.source,CapMachine.counter,CompareMachine.word,productInput,productOutput,UWalkCapacity.input,UWalkCapacity.result,d,p,q,Fin.addCases]
    · intro i hi
      have hn18 : i.val≠18 := by
        intro he
        apply hi 1
        apply Fin.ext
        exact he.symm
      have hn19 : i.val≠19 := by
        intro he
        apply hi 2
        apply Fin.ext
        exact he.symm
      have hn20 : i.val≠20 := by
        intro he
        apply hi 3
        apply Fin.ext
        exact he.symm
      have hn21 : i.val≠21 := by
        intro he
        apply hi 4
        apply Fin.ext
        exact he.symm
      have hn22 : i.val≠22 := by
        intro he
        apply hi 5
        apply Fin.ext
        exact he.symm
      have hn23 : i.val≠23 := by
        intro he
        apply hi 6
        apply Fin.ext
        exact he.symm
      have hn24 : i.val≠24 := by
        intro he
        apply hi 7
        apply Fin.ext
        exact he.symm
      simp [afterC,hn18,hn19,hn20,hn21,hn22,hn23,hn24]
  rw [ho] at h
  simpa [phaseC,productCost,d,p,q] using h

noncomputable def arithmeticMachine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine phaseT phaseJ) phaseW) phaseD)
      phaseP) phaseK) phaseQ) phaseC
def arithmeticCost (w t j : ℕ) :=
  (((((((2*t+6)+1+(2*j+6))+1+(2*w+6))+1+(2*d t j+6))+1+
    productCost (d t j) (w+1))+1+260)+1+productCost (p w t j) 128)+1+(2*q w t j+6)
theorem arithmetic_ready (w t j c : ℕ) : ClockJoin.ReadyRun arithmeticMachine
    (arithmeticCost w t j) (input w t j c) (afterC w t j c) := by
  have h1 := ClockJoin.join _ _ _ _ _ _ _ (readyT w t j c) (readyJ w t j c)
  have h2 := ClockJoin.join _ _ _ _ _ _ _ h1 (readyW w t j c)
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 (readyD w t j c)
  have h4 := ClockJoin.join _ _ _ _ _ _ _ h3 (readyP w t j c)
  have h5 := ClockJoin.join _ _ _ _ _ _ _ h4 (readyK w t j c)
  have h6 := ClockJoin.join _ _ _ _ _ _ _ h5 (readyQ w t j c)
  exact ClockJoin.join _ _ _ _ _ _ _ h6 (readyC w t j c)

end NearCubicWires.RepairOrdinary.UWalkNumbers

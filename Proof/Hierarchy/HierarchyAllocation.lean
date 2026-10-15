import Proof.Hierarchy.HierarchyWidth

/-! A paid unary linear allocation from the literal framed x. The
coefficient and constant are fixed program parameters; the scanned product
has length O(|x|), independently of the large binary hierarchy clock. -/
namespace NearCubicWires.RepairOrdinary.HierarchyAllocation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem install_eq {t u : ℕ} (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (ambient target : Fin u → List Bool) (out : Fin t → List Bool)
    (hselected : ∀ j,target (slot j)=out j)
    (houtside : ∀ i,(∀ j,slot j≠i) → target i=ambient i) : install slot ambient out=target := by
  funext i
  cases hp : RecoveryFocus.pick slot i with
  | none =>
    have hn : ∀ j,slot j≠i := by
      intro j he
      have hj := RecoveryFocus.pick_slot slot hi j
      rw [he,hp] at hj
      contradiction
    simpa [install,hp] using (houtside i hn).symm
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    rw [← he,install_slot _ hi]
    exact (hselected j).symm

theorem length_ready (bits : List Bool) :
    ClockJoin.ReadyRun ClockNumericPrep.ellMachine (4*bits.length+5)
      ![frame bits,[]] ![frame bits,false::List.replicate bits.length true] := by
  obtain ⟨base,hb,hf,hs,_⟩ := RepairSource.VerifierDecoding.LengthMachine.length_run bits
  let localData : Fin 2 → List Bool := ![frame bits,false::List.replicate bits.length true]
  let c : Configuration 2 2 := ⟨0,![0,1],localData⟩
  let final : Configuration 2 2 := ⟨1,fun _ => 0,localData⟩
  have hstep : step ClockNumericPrep.ellReset c=some final := by
    simp [step,ClockNumericPrep.ellReset,c]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  let last : ExecutionReceipt 2 2 := ⟨final,1,max c.tapeCells final.tapeCells⟩
  have hl : runFrom ClockNumericPrep.ellReset 1 c=some last :=
    runFrom_step ClockNumericPrep.ellReset c final ⟨final,0,final.tapeCells⟩ (by rfl) hstep
      (runFrom_zero_of_halted ClockNumericPrep.ellReset final (by rfl))
  have hi : Composition.restart base.final ClockNumericPrep.ellReset.start=c := by rw [hf]; rfl
  have hl' : runFrom ClockNumericPrep.ellReset 1 (Composition.restart base.final ClockNumericPrep.ellReset.start)=some last := by
    rw [hi]
    exact hl
  have hr := Composition.run_join RepairSource.VerifierDecoding.LengthMachine.machine ClockNumericPrep.ellReset
    (4*bits.length+3) 1 _ base last hb hl'
  refine ⟨Composition.joinedReceipt base last,?_,rfl,fun _ => rfl,?_⟩
  · have he : 4*bits.length+3+1+1=4*bits.length+5 := by omega
    rw [he] at hr
    exact hr
  · dsimp only [Composition.joinedReceipt,last]
    omega

def degreeSlots : Fin 2 → Fin 10 := ![1,2]
def ellSlots : Fin 2 → Fin 10 := ![0,3]
def productSlots : Fin 4 → Fin 10 := ![1,3,4,5]
def constantSlots : Fin 2 → Fin 10 := ![6,7]
def sumSlots : Fin 4 → Fin 10 := ![4,6,8,9]
theorem degree_injective : Function.Injective degreeSlots := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp [degreeSlots] at h ⊢
theorem ell_injective : Function.Injective ellSlots := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp [ellSlots] at h ⊢
theorem product_injective : Function.Injective productSlots := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp [productSlots] at h ⊢
theorem constant_injective : Function.Injective constantSlots := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp [constantSlots] at h ⊢
theorem sum_injective : Function.Injective sumSlots := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp [sumSlots] at h ⊢

def offset (C : ℕ) := C
def input (bits : List Bool) : Fin 10 → List Bool := fun i => if i.val=0 then frame (bits) else []
def afterDegree (D : ℕ) (bits : List Bool) : Fin 10 → List Bool := fun i =>
  if i.val=1 then List.replicate D true else if i.val=2 then List.replicate D false else input bits i
def afterEll (D : ℕ) (bits : List Bool) : Fin 10 → List Bool := fun i =>
  if i.val=3 then false::List.replicate (bits.length) true else afterDegree D bits i
def afterProduct (D : ℕ) (bits : List Bool) : Fin 10 → List Bool := fun i =>
  if i.val=4 then List.replicate (D*bits.length) true
  else if i.val=5 then List.replicate (D*(2*bits.length+3)+2) false else afterEll D bits i
def afterConstant (D C : ℕ) (bits : List Bool) : Fin 10 → List Bool := fun i =>
  if i.val=6 then List.replicate (offset C) true else if i.val=7 then List.replicate (offset C) false
  else afterProduct D bits i
def output (D C : ℕ) (bits : List Bool) : Fin 10 → List Bool := fun i =>
  if i.val=8 then List.replicate ((D*bits.length+C)) true
  else if i.val=9 then List.replicate ((D*bits.length+C)+2) false else afterConstant D C bits i

noncomputable def degreeProgram (D : ℕ) := RecoveryFocus.machine degreeSlots
  (HierarchyFixedWord.machine (List.replicate D true))
noncomputable def ellProgram := RecoveryFocus.machine ellSlots ClockNumericPrep.ellMachine
noncomputable def productProgram := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def constantProgram (C : ℕ) := RecoveryFocus.machine constantSlots
  (HierarchyFixedWord.machine (List.replicate (offset C) true))
noncomputable def sumProgram := RecoveryFocus.machine sumSlots ClockUnarySum.machine

theorem degree_ready (D : ℕ) (bits : List Bool) :
    ClockJoin.ReadyRun (degreeProgram D) (2*D+2) (input bits) (afterDegree D bits) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (List.replicate D true)
  simp only [List.length_replicate] at hr ht hs
  have h := (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    degreeSlots degree_injective (input bits) (by intro j; fin_cases j <;> rfl)
  have he := install_eq degreeSlots degree_injective (input bits) (afterDegree D bits)
    ![List.replicate D true,List.replicate D false] (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl))
  rw [he] at h
  exact h

theorem ell_ready (D : ℕ) (bits : List Bool) : ClockJoin.ReadyRun ellProgram (4*bits.length+5)
    (afterDegree D bits) (afterEll D bits) := by
  have h := (length_ready bits).focus ellSlots ell_injective (afterDegree D bits)
    (by intro j; fin_cases j <;> rfl)
  have he := install_eq ellSlots ell_injective (afterDegree D bits) (afterEll D bits)
    ![frame (bits),false::List.replicate (bits.length) true]
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl))
  rw [he] at h
  exact h

def productCost (D : ℕ) (bits : List Bool) := 2*(D*(2*bits.length+3)+2)+2
theorem product_ready (D : ℕ) (bits : List Bool) : ClockJoin.ReadyRun productProgram (productCost D bits)
    (afterEll D bits) (afterProduct D bits) := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run D (bits.length)
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate D true,false::List.replicate (bits.length) true,[]]
      (fun _ : Fin 1 => []))=![List.replicate D true,false::List.replicate (bits.length) true,[],[]] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  have ht : r.final.tapes=![List.replicate D true,false::List.replicate (bits.length) true,
      List.replicate (D*bits.length) true,List.replicate (D*(2*bits.length+3)+2) false] := by
    funext i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have h := (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    productSlots product_injective (afterEll D bits) (by intro j; fin_cases j <;> rfl)
  have he := install_eq productSlots product_injective (afterEll D bits) (afterProduct D bits)
    ![List.replicate D true,false::List.replicate (bits.length) true,
      List.replicate (D*bits.length) true,List.replicate (D*(2*bits.length+3)+2) false]
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) |
          exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl))
  rw [he] at h
  exact h

theorem constant_ready (D C : ℕ) (bits : List Bool) : ClockJoin.ReadyRun (constantProgram C) (2*offset C+2)
    (afterProduct D bits) (afterConstant D C bits) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (List.replicate (offset C) true)
  simp only [List.length_replicate] at hr ht hs
  have h := (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    constantSlots constant_injective (afterProduct D bits) (by intro j; fin_cases j <;> rfl)
  have he := install_eq constantSlots constant_injective (afterProduct D bits) (afterConstant D C bits)
    ![List.replicate (offset C) true,List.replicate (offset C) false] (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl))
  rw [he] at h
  exact h

theorem sum_ready (D C : ℕ) (bits : List Bool) : ClockJoin.ReadyRun sumProgram (2*(D*bits.length+C)+6)
    (afterConstant D C bits) (output D C bits) := by
  have hw : D*bits.length+offset C=(D*bits.length+C) := by
    rfl
  have h := (ClockUnarySum.sum_ready (D*bits.length) (offset C)).focus
    sumSlots sum_injective (afterConstant D C bits) (by intro j; fin_cases j <;> rfl)
  rw [hw] at h
  have he := install_eq sumSlots sum_injective (afterConstant D C bits) (output D C bits)
    ![List.replicate (D*bits.length) true,List.replicate (offset C) true,
      List.replicate ((D*bits.length+C)) true,List.replicate ((D*bits.length+C)+2) false]
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) |
          exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl))
  rw [he] at h
  exact h

noncomputable def machine (D C : ℕ) := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (degreeProgram D) ellProgram) productProgram)
    (constantProgram C)) sumProgram
def budget (D C : ℕ) (bits : List Bool) := 2*D+2+1+(4*bits.length+5)+1+productCost D bits+
  1+(2*offset C+2)+1+(2*(D*bits.length+C)+6)
theorem allocation_ready (D C : ℕ) (bits : List Bool) : ClockJoin.ReadyRun (machine D C) (budget D C bits) (input bits) (output D C bits) := by
  have h1 := ClockJoin.join _ _ _ _ _ _ _ (degree_ready D bits) (ell_ready D bits)
  have h2 := ClockJoin.join _ _ _ _ _ _ _ h1 (product_ready D bits)
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 (constant_ready D C bits)
  exact ClockJoin.join _ _ _ _ _ _ _ h3 (sum_ready D C bits)

end NearCubicWires.RepairOrdinary.HierarchyAllocation

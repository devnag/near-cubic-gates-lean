import Proof.Hierarchy.HierarchyBinaryPower

/-! Actual generation of W=D*ell(n)+bits(C).length+3 from framed binary n.
Only short unary lengths and fixed program constants are multiplied. -/
namespace NearCubicWires.RepairOrdinary.HierarchyWidth
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

def offset (C : ℕ) := C.bits.length+3
def input (n : ℕ) : Fin 10 → List Bool := fun i => if i.val=0 then frame (ClockBinary.word n) else []
def afterDegree (D n : ℕ) : Fin 10 → List Bool := fun i =>
  if i.val=1 then List.replicate D true else if i.val=2 then List.replicate D false else input n i
def afterEll (D n : ℕ) : Fin 10 → List Bool := fun i =>
  if i.val=3 then false::List.replicate (PCPResourceLedger.ell n) true else afterDegree D n i
def afterProduct (D n : ℕ) : Fin 10 → List Bool := fun i =>
  if i.val=4 then List.replicate (D*PCPResourceLedger.ell n) true
  else if i.val=5 then List.replicate (D*(2*PCPResourceLedger.ell n+3)+2) false else afterEll D n i
def afterConstant (D C n : ℕ) : Fin 10 → List Bool := fun i =>
  if i.val=6 then List.replicate (offset C) true else if i.val=7 then List.replicate (offset C) false
  else afterProduct D n i
def output (D C n : ℕ) : Fin 10 → List Bool := fun i =>
  if i.val=8 then List.replicate (HierarchyBinary.width C D n) true
  else if i.val=9 then List.replicate (HierarchyBinary.width C D n+2) false else afterConstant D C n i

noncomputable def degreeProgram (D : ℕ) := RecoveryFocus.machine degreeSlots
  (HierarchyFixedWord.machine (List.replicate D true))
noncomputable def ellProgram := RecoveryFocus.machine ellSlots ClockNumericPrep.ellMachine
noncomputable def productProgram := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def constantProgram (C : ℕ) := RecoveryFocus.machine constantSlots
  (HierarchyFixedWord.machine (List.replicate (offset C) true))
noncomputable def sumProgram := RecoveryFocus.machine sumSlots ClockUnarySum.machine

theorem degree_ready (D n : ℕ) :
    ClockJoin.ReadyRun (degreeProgram D) (2*D+2) (input n) (afterDegree D n) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (List.replicate D true)
  simp only [List.length_replicate] at hr ht hs
  have h := (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    degreeSlots degree_injective (input n) (by intro j; fin_cases j <;> rfl)
  have he := install_eq degreeSlots degree_injective (input n) (afterDegree D n)
    ![List.replicate D true,List.replicate D false] (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl))
  rw [he] at h
  exact h

theorem ell_ready (D n : ℕ) : ClockJoin.ReadyRun ellProgram (4*PCPResourceLedger.ell n+5)
    (afterDegree D n) (afterEll D n) := by
  have h := (ClockNumericPrep.ell_ready n).focus ellSlots ell_injective (afterDegree D n)
    (by intro j; fin_cases j <;> rfl)
  have he := install_eq ellSlots ell_injective (afterDegree D n) (afterEll D n)
    ![frame (ClockBinary.word n),false::List.replicate (PCPResourceLedger.ell n) true]
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl))
  rw [he] at h
  exact h

def productCost (D n : ℕ) := 2*(D*(2*PCPResourceLedger.ell n+3)+2)+2
theorem product_ready (D n : ℕ) : ClockJoin.ReadyRun productProgram (productCost D n)
    (afterEll D n) (afterProduct D n) := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run D (PCPResourceLedger.ell n)
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate D true,false::List.replicate (PCPResourceLedger.ell n) true,[]]
      (fun _ : Fin 1 => []))=![List.replicate D true,false::List.replicate (PCPResourceLedger.ell n) true,[],[]] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  have ht : r.final.tapes=![List.replicate D true,false::List.replicate (PCPResourceLedger.ell n) true,
      List.replicate (D*PCPResourceLedger.ell n) true,List.replicate (D*(2*PCPResourceLedger.ell n+3)+2) false] := by
    funext i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have h := (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    productSlots product_injective (afterEll D n) (by intro j; fin_cases j <;> rfl)
  have he := install_eq productSlots product_injective (afterEll D n) (afterProduct D n)
    ![List.replicate D true,false::List.replicate (PCPResourceLedger.ell n) true,
      List.replicate (D*PCPResourceLedger.ell n) true,List.replicate (D*(2*PCPResourceLedger.ell n+3)+2) false]
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) |
          exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl))
  rw [he] at h
  exact h

theorem constant_ready (D C n : ℕ) : ClockJoin.ReadyRun (constantProgram C) (2*offset C+2)
    (afterProduct D n) (afterConstant D C n) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (List.replicate (offset C) true)
  simp only [List.length_replicate] at hr ht hs
  have h := (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    constantSlots constant_injective (afterProduct D n) (by intro j; fin_cases j <;> rfl)
  have he := install_eq constantSlots constant_injective (afterProduct D n) (afterConstant D C n)
    ![List.replicate (offset C) true,List.replicate (offset C) false] (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl))
  rw [he] at h
  exact h

theorem sum_ready (D C n : ℕ) : ClockJoin.ReadyRun sumProgram (2*HierarchyBinary.width C D n+6)
    (afterConstant D C n) (output D C n) := by
  have hw : D*PCPResourceLedger.ell n+offset C=HierarchyBinary.width C D n := by
    dsimp [offset,HierarchyBinary.width]; omega
  have h := (ClockUnarySum.sum_ready (D*PCPResourceLedger.ell n) (offset C)).focus
    sumSlots sum_injective (afterConstant D C n) (by intro j; fin_cases j <;> rfl)
  rw [hw] at h
  have he := install_eq sumSlots sum_injective (afterConstant D C n) (output D C n)
    ![List.replicate (D*PCPResourceLedger.ell n) true,List.replicate (offset C) true,
      List.replicate (HierarchyBinary.width C D n) true,List.replicate (HierarchyBinary.width C D n+2) false]
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) |
          exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl))
  rw [he] at h
  exact h

noncomputable def machine (D C : ℕ) := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (degreeProgram D) ellProgram) productProgram)
    (constantProgram C)) sumProgram
def budget (D C n : ℕ) := 2*D+2+1+(4*PCPResourceLedger.ell n+5)+1+productCost D n+
  1+(2*offset C+2)+1+(2*HierarchyBinary.width C D n+6)
theorem width_ready (D C n : ℕ) : ClockJoin.ReadyRun (machine D C) (budget D C n) (input n) (output D C n) := by
  have h1 := ClockJoin.join _ _ _ _ _ _ _ (degree_ready D n) (ell_ready D n)
  have h2 := ClockJoin.join _ _ _ _ _ _ _ h1 (product_ready D n)
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 (constant_ready D C n)
  exact ClockJoin.join _ _ _ _ _ _ _ h3 (sum_ready D C n)

end NearCubicWires.RepairOrdinary.HierarchyWidth

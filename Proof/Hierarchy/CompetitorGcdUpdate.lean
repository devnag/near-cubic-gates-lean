import Proof.Hierarchy.CompetitorGcdFields

/-! Physical subtraction and register replacement in the same seven-tape
gcd bank. All overwritten fields have the original witness width. -/
namespace NearCubicWires.RepairOrdinary.CompetitorGcd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def subSlots (i : Fin 2) : Fin 4→Fin 7 := ![![0,1] i,![1,0] i,2,6]
def copySlots (i : Fin 2) : Fin 4→Fin 7 := ![2,i.castAdd 5,5,6]
def selectSlots (i : Fin 2) : Fin 4→Fin 7 := ![i.castAdd 5,2,5,6]
theorem subSlots_injective (i : Fin 2) : Function.Injective (subSlots i) := by fin_cases i <;> decide
theorem copySlots_injective (i : Fin 2) : Function.Injective (copySlots i) := by fin_cases i <;> decide
theorem selectSlots_injective (i : Fin 2) : Function.Injective (selectSlots i) := by fin_cases i <;> decide
def minuend (a b : ℕ) : Fin 2→ℕ := ![a,b]
def subtrahend (a b : ℕ) : Fin 2→ℕ := ![b,a]
noncomputable def subtract (i : Fin 2) := RecoveryFocus.machine (subSlots i) subtractMachine
noncomputable def copy (i : Fin 2) := RecoveryFocus.machine (copySlots i) copyMachine
noncomputable def select (i : Fin 2) := RecoveryFocus.machine (selectSlots i) copyMachine

theorem subtract_ready (w a b c : ℕ) (flag : Bool) (i : Fin 2)
    (ha : a<2^w) (hb : b<2^w) (hle : subtrahend a b i≤ minuend a b i) :
    ReadyRun (subtract i) (4*w+4) (data w a b c flag)
      (data w a b (minuend a b i-subtrahend a b i) flag) := by
  have hfit : minuend a b i<2^w := by fin_cases i <;> first | exact ha | exact hb
  have h := RecoveryRootRound.subtract_ready w (minuend a b i) (subtrahend a b i)
    (frame (binary w c)) (4*w+3) hle hfit (by simp)
  rw [Nat.max_eq_left (by omega)] at h
  have hp := h.focus (subSlots i) (subSlots_injective i) (data w a b c flag) (by
    intro j;fin_cases i <;>fin_cases j <;>rfl)
  have he : install (subSlots i) (data w a b c flag)
      ![frame (binary w (minuend a b i)),frame (binary w (subtrahend a b i)),
        frame (binary w (minuend a b i-subtrahend a b i)),List.replicate (4*w+3) false]=
      data w a b (minuend a b i-subtrahend a b i) flag := by
    funext k
    by_cases hk : ∃ j,subSlots i j=k
    · obtain ⟨j,rfl⟩ := hk
      rw [install_slot _ (subSlots_injective i)]
      fin_cases i <;>fin_cases j <;>rfl
    · rw [install_other _ _ _ _ (by intro j hj;exact hk ⟨j,hj⟩)]
      have h2 : k≠2 := by intro h;subst k;exact hk ⟨2,rfl⟩
      fin_cases k <;> first | rfl | exact False.elim (h2 rfl)
  rw [he] at hp
  exact hp

theorem copy_ready (w a b c : ℕ) (flag : Bool) (i : Fin 2) :
    ReadyRun (copy i) (8*w+8) (data w a b c flag)
      (data w (if i.val=0 then c else a) (if i.val=1 then c else b) c flag) := by
  have h := RecoveryRootRound.copy_ready (binary w c) (frame (binary w (minuend a b i)))
    (2*w+1) (4*w+3) (by simp)
  simp only [binary_length,max_self] at h
  have hp := h.focus (copySlots i) (copySlots_injective i) (data w a b c flag) (by
    intro j;fin_cases i <;>fin_cases j <;>rfl)
  have he : install (copySlots i) (data w a b c flag)
      ![frame (binary w c),frame (binary w c),List.replicate (2*w+1) false,List.replicate (4*w+3) false]=
      data w (if i.val=0 then c else a) (if i.val=1 then c else b) c flag := by
    funext k
    by_cases hk : ∃ j,copySlots i j=k
    · obtain ⟨j,rfl⟩ := hk
      rw [install_slot _ (copySlots_injective i)]
      fin_cases i <;>fin_cases j <;>rfl
    · rw [install_other _ _ _ _ (by intro j hj;exact hk ⟨j,hj⟩)]
      have h0 : k≠i.castAdd 5 := by intro h;subst k;exact hk ⟨1,rfl⟩
      fin_cases i <;>fin_cases k <;> first | rfl | exact False.elim (h0 rfl)
  rw [he] at hp
  exact hp

theorem select_ready (w a b c : ℕ) (flag : Bool) (i : Fin 2) :
    ReadyRun (select i) (8*w+8) (data w a b c flag)
      (data w a b (minuend a b i) flag) := by
  have h := RecoveryRootRound.copy_ready (binary w (minuend a b i)) (frame (binary w c))
    (2*w+1) (4*w+3) (by simp)
  simp only [binary_length,max_self] at h
  have hp := h.focus (selectSlots i) (selectSlots_injective i) (data w a b c flag) (by
    intro j;fin_cases i <;>fin_cases j <;>rfl)
  have he : install (selectSlots i) (data w a b c flag)
      ![frame (binary w (minuend a b i)),frame (binary w (minuend a b i)),
        List.replicate (2*w+1) false,List.replicate (4*w+3) false]=
      data w a b (minuend a b i) flag := by
    funext k
    by_cases hk : ∃ j,selectSlots i j=k
    · obtain ⟨j,rfl⟩ := hk
      rw [install_slot _ (selectSlots_injective i)]
      fin_cases i <;>fin_cases j <;>rfl
    · rw [install_other _ _ _ _ (by intro j hj;exact hk ⟨j,hj⟩)]
      have h2 : k≠2 := by intro h;subst k;exact hk ⟨1,rfl⟩
      fin_cases k <;> first | rfl | exact False.elim (h2 rfl)
  rw [he] at hp
  exact hp

noncomputable def update (i : Fin 2) := Composition.machine (subtract i) (copy i)
theorem update_ready (w a b c : ℕ) (flag : Bool) (i : Fin 2)
    (ha : a<2^w) (hb : b<2^w) (hle : subtrahend a b i≤ minuend a b i) :
    ReadyRun (update i) (12*w+13) (data w a b c flag)
      (data w (if i.val=0 then a-b else a) (if i.val=1 then b-a else b)
        (minuend a b i-subtrahend a b i) flag) := by
  have h := HierarchyMultiplyEntry.join_exact (subtract i) (copy i) _ _ _ _ _
    (subtract_ready w a b c flag i ha hb hle)
    (copy_ready w a b (minuend a b i-subtrahend a b i) flag i)
  have ht : (4*w+4)+1+(8*w+8)=12*w+13 := by omega
  rw [ht] at h
  fin_cases i <;>exact h

end NearCubicWires.RepairOrdinary.CompetitorGcd

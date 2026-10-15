import Proof.Hierarchy.CompetitorGcdLoop

/-! Cold gcd initialization from only the two framed numeric fields.
The zero word is physically formed by copying a and subtracting a from it;
no width, zero field, scratch capacity or loop counter is supplied. -/
namespace NearCubicWires.RepairOrdinary.CompetitorGcd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldInput (w a b : ℕ) : Fin 7→List Bool := ![frame (binary w a),frame (binary w b),[],[],[],[],[]]
def copied (w a b : ℕ) : Fin 7→List Bool :=
  ![frame (binary w a),frame (binary w b),frame (binary w a),[],[],
    List.replicate (2*w+1) false,List.replicate (4*w+3) false]
def zeroed (w a b : ℕ) : Fin 7→List Bool :=
  ![frame (binary w a),frame (binary w b),frame (binary w a),frame (binary w 0),[],
    List.replicate (2*w+1) false,List.replicate (4*w+3) false]
def zeroSlots : Fin 4→Fin 7 := ![0,2,3,6]
theorem zeroSlots_injective : Function.Injective zeroSlots := by decide
noncomputable def coldCopy := select 0
noncomputable def coldZero := RecoveryFocus.machine zeroSlots subtractMachine
noncomputable def coldTail := Composition.machine coldZero clear
noncomputable def cold := Composition.machine coldCopy coldTail

def inputWords (a b : List Bool) : Fin 7→List Bool := ![frame a,frame b,[],[],[],[],[]]
def copiedWords (a b : List Bool) : Fin 7→List Bool :=
  ![frame a,frame b,frame a,[],[],List.replicate (2*a.length+1) false,List.replicate (4*a.length+3) false]

theorem coldCopy_install (a b : List Bool) :
    install (selectSlots 0) (inputWords a b)
      ![frame a,frame a,List.replicate (2*a.length+1) false,List.replicate (4*a.length+3) false]=copiedWords a b := by
  funext k
  by_cases hk : ∃ j,selectSlots 0 j=k
  · obtain ⟨j,rfl⟩ := hk
    rw [install_slot _ (selectSlots_injective 0)]
    fin_cases j <;>rfl
  · rw [install_other _ _ _ _ (by intro j hj;exact hk ⟨j,hj⟩)]
    have h2 : k≠2 := by intro h;subst k;exact hk ⟨1,rfl⟩
    have h5 : k≠5 := by intro h;subst k;exact hk ⟨2,rfl⟩
    have h6 : k≠6 := by intro h;subst k;exact hk ⟨3,rfl⟩
    fin_cases k <;> first | rfl | exact False.elim (h2 rfl) | exact False.elim (h5 rfl) | exact False.elim (h6 rfl)

theorem coldCopy_generic (a b : List Bool) :
    ReadyRun coldCopy (8*a.length+8) (inputWords a b) (copiedWords a b) := by
  have h := RecoveryRootRound.copy_ready a [] 0 0 (by simp)
  simp only [Nat.zero_max] at h
  have hp := h.focus (selectSlots 0) (selectSlots_injective 0) (inputWords a b) (by intro j;fin_cases j <;>rfl)
  rw [coldCopy_install] at hp
  exact hp

theorem coldCopy_ready (w a b : ℕ) :
    ReadyRun coldCopy (8*w+8) (coldInput w a b) (copied w a b) := by
  have h := coldCopy_generic (binary w a) (binary w b)
  simpa only [binary_length,inputWords,copiedWords,coldInput,copied] using h

theorem coldZero_ready (w a b : ℕ) (ha : a<2^w) :
    ReadyRun coldZero (4*w+4) (copied w a b) (zeroed w a b) := by
  have h := RecoveryRootRound.subtract_ready w a a [] (4*w+3) (by rfl) ha (by simp)
  rw [Nat.sub_self,Nat.max_eq_left (by omega)] at h
  have hp := h.focus zeroSlots zeroSlots_injective (copied w a b) (by intro j;fin_cases j <;>rfl)
  have he : install zeroSlots (copied w a b)
      ![frame (binary w a),frame (binary w a),frame (binary w 0),List.replicate (4*w+3) false]=zeroed w a b := by
    funext k
    by_cases hk : ∃ j,zeroSlots j=k
    · obtain ⟨j,rfl⟩ := hk
      rw [install_slot _ zeroSlots_injective]
      fin_cases j <;>rfl
    · rw [install_other _ _ _ _ (by intro j hj;exact hk ⟨j,hj⟩)]
      have h3 : k≠3 := by intro h;subst k;exact hk ⟨2,rfl⟩
      fin_cases k <;> first | rfl | exact False.elim (h3 rfl)
  rw [he] at hp
  exact hp

theorem coldClear_ready (w a b : ℕ) :
    ReadyRun clear 1 (zeroed w a b) (data w a b a false) := by
  let final : Configuration 7 2 := ⟨1,fun _=>0,data w a b a false⟩
  have hs : step clear (initialConfiguration clear (zeroed w a b))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;>rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],ht⟩

theorem cold_ready (w a b : ℕ) (ha : a<2^w) :
    ReadyRun cold (12*w+15) (coldInput w a b) (data w a b a false) := by
  have ht := HierarchyMultiplyEntry.join_exact coldZero clear _ _ _ _ _
    (coldZero_ready w a b ha) (coldClear_ready w a b)
  have h := HierarchyMultiplyEntry.join_exact coldCopy coldTail _ _ _ _ _ (coldCopy_ready w a b) ht
  simpa only [cold,show (8*w+8)+1+((4*w+4)+1+1)=12*w+15 by omega] using h

end NearCubicWires.RepairOrdinary.CompetitorGcd

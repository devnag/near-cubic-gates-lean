import Proof.Hierarchy.CompetitorWitnessBounded

/-! Literal reusable scalar operations for canonical-rational gcd checking.
The enclosing witness cap is executed before this numeric loop. -/
namespace NearCubicWires.RepairOrdinary.CompetitorGcd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (w a b c : ℕ) (flag : Bool) : Fin 7→List Bool :=
  ![frame (binary w a),frame (binary w b),frame (binary w c),frame (binary w 0),
    [flag],List.replicate (2*w+1) false,List.replicate (4*w+3) false]
def compareSlots (i : Fin 3) : Fin 4→Fin 7 := ![![0,1,0] i,![3,3,1] i,4,6]
theorem compareSlots_injective (i : Fin 3) : Function.Injective (compareSlots i) := by fin_cases i <;> decide
def left (a b : ℕ) : Fin 3→ℕ := ![a,b,a]
def right (b : ℕ) : Fin 3→ℕ := ![0,0,b]
noncomputable def compare (i : Fin 3) := RecoveryFocus.machine (compareSlots i) compareMachine

theorem compare_input (w a b c : ℕ) (i : Fin 3) (j : Fin 4) :
    data w a b c false (compareSlots i j)=
      ![frame (binary w (left a b i)),frame (binary w (right b i)),[false],List.replicate (4*w+3) false] j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem compare_install (w a b c : ℕ) (i : Fin 3) (flag : Bool) :
    install (compareSlots i) (data w a b c false)
      ![frame (binary w (left a b i)),frame (binary w (right b i)),[flag],List.replicate (4*w+3) false]=
      data w a b c flag := by
  funext k
  by_cases hk : ∃ j,compareSlots i j=k
  · obtain ⟨j,rfl⟩ := hk
    rw [install_slot _ (compareSlots_injective i)]
    fin_cases i <;> fin_cases j <;> rfl
  · rw [install_other _ _ _ _ (by intro j hj; exact hk ⟨j,hj⟩)]
    have h4 : k≠4 := by intro h; subst k; exact hk ⟨2,rfl⟩
    fin_cases k <;> first | rfl | exact False.elim (h4 rfl)

theorem compare_ready (w a b c : ℕ) (i : Fin 3) (ha : a<2^w) (hb : b<2^w) :
    ReadyRun (compare i) (4*w+4) (data w a b c false)
      (data w a b c (decide (left a b i≤right b i))) := by
  have hl : left a b i<2^w := by fin_cases i <;> first | exact ha | exact hb
  have hr : right b i<2^w := by fin_cases i <;> first | exact hb | exact Nat.two_pow_pos w
  have h := RecoveryRootRound.compare_ready (binary w (left a b i)) (binary w (right b i)) (4*w+3) (by simp)
  rw [binary_length,binary_value w _ hl,binary_value w _ hr,Nat.max_eq_left (by omega)] at h
  have hf := h.focus (compareSlots i) (compareSlots_injective i) (data w a b c false) (compare_input w a b c i)
  rw [compare_install] at hf
  exact hf

def clear : Machine 7 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun i=>if i.val=4 then some false else none,fun _=>.stay⟩ else none
theorem clear_ready (w a b c : ℕ) (flag : Bool) :
    ReadyRun clear 1 (data w a b c flag) (data w a b c false) := by
  let final : Configuration 7 2 := ⟨1,fun _=>0,data w a b c false⟩
  have hs : step clear (initialConfiguration clear (data w a b c flag))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],ht⟩
noncomputable def check (i : Fin 3) := Composition.machine clear (compare i)
theorem check_ready (w a b c : ℕ) (flag : Bool) (i : Fin 3) (ha : a<2^w) (hb : b<2^w) :
    ReadyRun (check i) (4*w+6) (data w a b c flag)
      (data w a b c (decide (left a b i≤right b i))) := by
  have h := HierarchyMultiplyEntry.join_exact clear (compare i) _ _ _ _ _
    (clear_ready w a b c flag) (compare_ready w a b c i ha hb)
  simpa only [check,show 1+1+(4*w+4)=4*w+6 by omega] using h

end NearCubicWires.RepairOrdinary.CompetitorGcd

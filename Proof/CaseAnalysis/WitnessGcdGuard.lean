import Proof.Hierarchy.CompetitorGcdLoop
import Proof.CaseAnalysis.WitnessRationalGuard

/-! The actual numeric cap checks precede the subtractive gcd. The limit is
an ordinary same-width input field, so the program is fixed independently of
the runtime native width and cap. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank (w a b c cap : ℕ) (gcdFlag passed : Bool) : Fin 9 → List Bool :=
  Fin.addCases (m := 7) (n := 2) (motive := fun _ => List Bool)
    (CompetitorGcd.data w a b c gcdFlag) ![frame (binary w cap), [passed]]

def clear : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then
    some ⟨1, (fun i => if i = 8 then some false else none), fun _ => .stay⟩ else none

theorem clear_ready (w a b c cap : ℕ) (flag : Bool) :
    ReadyRun clear 1 (bank w a b c cap false flag) (bank w a b c cap false false) := by
  let final : Configuration 9 2 := ⟨1, fun _ => 0, bank w a b c cap false false⟩
  have hs : step clear (initialConfiguration clear (bank w a b c cap false flag)) = some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r, hr, hf, ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r, hr, by rw [hf], by intro i; rw [hf], ht⟩

def slots (j : Fin 2) : Fin 4 → Fin 9 := ![j.castAdd 7, 7, 8, 6]
theorem slots_injective (j : Fin 2) : Function.Injective (slots j) := by fin_cases j <;> decide
def selected (a b : ℕ) (j : Fin 2) := ![a,b] j
noncomputable def compare (j : Fin 2) := RecoveryFocus.machine (slots j) compareMachine
noncomputable def stage (j : Fin 2) := Composition.machine clear (compare j)

theorem compared_ready (w a b c cap : ℕ) (j : Fin 2)
    (ha : a < 2^w) (hb : b < 2^w) (hc : cap < 2^w) :
    ReadyRun (compare j) (4*w+4) (bank w a b c cap false false)
      (bank w a b c cap false (decide (selected a b j ≤ cap))) := by
  have hnum : selected a b j < 2^w := by fin_cases j; exact ha; exact hb
  have h := RecoveryRootRound.compare_ready (binary w (selected a b j)) (binary w cap)
    (4*w+3) (by simp only [binary_length])
  rw [binary_length, binary_value w _ hnum, binary_value w _ hc, Nat.max_eq_left (by omega)] at h
  have hi : ∀ i, bank w a b c cap false false (slots j i) =
      (![frame (binary w (selected a b j)), frame (binary w cap), [false],
        List.replicate (4*w+3) false] : Fin 4 → List Bool) i := by
    intro i; fin_cases j <;> fin_cases i <;> rfl
  have hf := h.focus (slots j) (slots_injective j) (bank w a b c cap false false) hi
  have he : install (slots j) (bank w a b c cap false false)
      ![frame (binary w (selected a b j)), frame (binary w cap),
        [decide (selected a b j ≤ cap)], List.replicate (4*w+3) false] =
      bank w a b c cap false (decide (selected a b j ≤ cap)) := by
    apply HierarchyWidth.install_eq (slots j) (slots_injective j)
    · intro i; fin_cases j <;> fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact False.elim (hi 2 rfl)
  rw [he] at hf
  exact hf

theorem stage_ready (w a b c cap : ℕ) (flag : Bool) (j : Fin 2)
    (ha : a < 2^w) (hb : b < 2^w) (hc : cap < 2^w) :
    ReadyRun (stage j) (4*w+6) (bank w a b c cap false flag)
      (bank w a b c cap false (decide (selected a b j ≤ cap))) := by
  have h := HierarchyMultiplyEntry.join_exact clear (compare j) _ _ _ _ _
    (clear_ready w a b c cap flag) (compared_ready w a b c cap j ha hb hc)
  simpa only [stage, show 1+1+(4*w+4)=4*w+6 by omega] using h

def sizes (_ : Fin 2) := 9
noncomputable def programs (j : Fin 2) : Machine 9 (sizes j) := stage j
def next (j : Fin 2) (_ : Fin (sizes j)) (scanned : Fin 9 → Bool) : Option (Fin 2) :=
  if j.val = 0 ∧ scanned 8 = true then some 1 else none
noncomputable def guards := RecoveryCalls.machine sizes programs 0 next

theorem guards_ready (w a b c cap : ℕ) (flag : Bool)
    (ha : a < 2^w) (hb : b < 2^w) (hc : cap < 2^w) :
    ∃ t, t ≤ 8*w+14 ∧ ReadyRun guards t (bank w a b c cap false flag)
      (bank w a b c cap false (decide (a ≤ cap ∧ b ≤ cap))) := by
  have h0 := stage_ready w a b c cap flag 0 ha hb hc
  change ReadyRun (stage 0) (4*w+6) (bank w a b c cap false flag)
    (bank w a b c cap false (decide (a ≤ cap))) at h0
  by_cases hcap : a ≤ cap
  · rw [decide_eq_true hcap] at h0
    have first := h0.call sizes programs 0 next 0 1 (by intro q; rfl)
    have h1 := stage_ready w a b c cap true 1 ha hb hc
    have last := h1.stop sizes programs 0 next 1 (by intro q; rfl)
    have h := first.trans last
    obtain ⟨r, hr, hf, hs⟩ := h.run (by simp [RecoveryCalls.machine, RecoveryCalls.stopped])
    refine ⟨_, by omega, r, hr, ?_, ?_, hs⟩
    · simp [hf, RecoveryCalls.stopped, selected, hcap]
    · intro i; simp [hf, RecoveryCalls.stopped]
  · rw [decide_eq_false hcap] at h0
    have h := h0.stop sizes programs 0 next 0 (by intro q; rfl)
    obtain ⟨r, hr, hf, hs⟩ := h.run (by simp [RecoveryCalls.machine, RecoveryCalls.stopped])
    refine ⟨_, by omega, r, hr, ?_, ?_, hs⟩
    · simp [hf, RecoveryCalls.stopped, hcap]
    · intro i; simp [hf, RecoveryCalls.stopped]

end NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard

import Proof.MachineModel.ClockIncrement
import Proof.PCP.PCPResourceLedger

/-! Meaning and logarithmic width of the dynamically grown clock counter. -/
namespace NearCubicWires.RepairOrdinary.ClockBinary
open RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def canonical : List Bool → Prop
  | [] => True
  | b::bs => canonical bs ∧ (bs=[] → b=true)

def word : ℕ → List Bool
  | 0 => []
  | n+1 => ClockIncrement.next (word n)

theorem next_ne_nil (bits : List Bool) : ClockIncrement.next bits ≠ [] := by
  cases bits with
  | nil => simp [ClockIncrement.next]
  | cons b bs => cases b <;> simp [ClockIncrement.next]

theorem next_canonical (bits : List Bool) (h : canonical bits) :
    canonical (ClockIncrement.next bits) := by
  induction bits with
  | nil => simp [ClockIncrement.next, canonical]
  | cons b bs ih =>
    cases b with
    | false => exact ⟨h.1, by simp⟩
    | true => exact ⟨ih h.1, fun hn => (next_ne_nil bs hn).elim⟩

theorem word_canonical (n : ℕ) : canonical (word n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact next_canonical (word n) ih

@[simp] theorem word_value (n : ℕ) : value (word n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [word, ClockIncrement.next_value] using congrArg Nat.succ ih

theorem lower (bits : List Bool) (hc : canonical bits) (hn : bits ≠ []) :
    2^(bits.length-1) ≤ value bits := by
  induction bits with
  | nil => contradiction
  | cons b bs ih =>
    cases bs with
    | nil =>
      have hb := hc.2 rfl
      subst b
      simp [value]
    | cons c cs =>
      have ht := ih hc.1 (by simp)
      simp only [List.length_cons, Nat.add_sub_cancel, value] at ht ⊢
      rw [pow_succ]
      nlinarith

theorem length_log (n : ℕ) (hn : 0<n) : (word n).length = Nat.log 2 n+1 := by
  have he : word n ≠ [] := by
    intro h
    have hv := word_value n
    rw [h] at hv
    simp only [value] at hv
    omega
  have hl := lower (word n) (word_canonical n) he
  have hu := value_lt (word n)
  rw [word_value] at hl hu
  have hpos : 0<(word n).length := by cases hw : word n <;> simp_all
  have hlog := Nat.log_eq_of_pow_le_of_lt_pow hl
    (by simpa [Nat.sub_add_cancel hpos] using hu)
  omega

theorem length_bound (n w : ℕ) (hn : n<2^w) : (word n).length ≤ w := by
  by_cases hzero : n=0
  · simp [hzero, word]
  have hpos : 0<n := Nat.pos_of_ne_zero hzero
  rw [length_log n hpos]
  have hlog := Nat.log_lt_of_lt_pow hzero hn
  omega

theorem word_binary (n : ℕ) : SignedSortKey.binary (word n).length n = word n := by
  simpa using BoundedCounter.binary_of_value (word n)

theorem work_bound (n N : ℕ) (hn : n≤N) :
    ClockIncrement.work (word n) ≤ 2*PCPResourceLedger.ell N+3 := by
  have hp : n < 2^PCPResourceLedger.ell N :=
    lt_of_le_of_lt hn (lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_pow_clog (by decide) (N+1)))
  have hw := length_bound n (PCPResourceLedger.ell N) hp
  exact (ClockIncrement.work_bound (word n)).trans (by omega)

end NearCubicWires.RepairOrdinary.ClockBinary

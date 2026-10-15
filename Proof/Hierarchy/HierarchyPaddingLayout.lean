import Proof.Hierarchy.HierarchyBinaryBounds

/-! Literal raw input consumed by the fixed verifier's three-field parser.
Padding changes allocation alone; the printed bound has exactly the original
hierarchy coefficient and witness domain. Machine production is separate. -/
namespace NearCubicWires.RepairOrdinary.HierarchyPadding
open HierarchyBinary SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerBits (C D : ℕ) (code x : List Bool) : List Bool :=
  frame code++frame x++frame (binary (width C D x.length) (bound C D x.length))
def rawInput (k C Cpad : ℕ) (code x : List Bool) : List Bool :=
  headerBits C (k+2) code x++List.replicate
    (inputLength k Cpad code.length C x.length-(headerBits C (k+2) code x).length) false

theorem prefix_fits (k C Cpad : ℕ) (code x : List Bool) (hpad : k+3≤Cpad) :
    (headerBits C (k+2) code x).length < inputLength k Cpad code.length C x.length := by
  have hf := padded_header_fits C Cpad (k+2) x.length code x rfl (by omega)
  exact hf.trans_lt (PowerSlice.length_bounds k _).1

theorem raw_length (k C Cpad : ℕ) (code x : List Bool) (hpad : k+3≤Cpad) :
    (rawInput k C Cpad code x).length=inputLength k Cpad code.length C x.length := by
  have h := (prefix_fits k C Cpad code x hpad).le
  simp only [rawInput,List.length_append,List.length_replicate]
  omega

theorem exact_bound (C D : ℕ) (x : List Bool) :
    RadixSemantics.value (binary (width C D x.length) (bound C D x.length))=
      C*(x.length^D+1) := binary_value _ _ (bound_fits C D x.length)

theorem entry_guards (k C Cpad : ℕ) (code x : List Bool)
    (hC : 0<C) (hcoeff : C≤Cpad) (hpad : k+3≤Cpad) :
    let N := (rawInput k C Cpad code x).length
    code.length≤Nat.log 2 N ∧
    (binary (width C (k+2) x.length) (bound C (k+2) x.length)).length≤ClockDyadicLedger.width N ∧
    x.length≤bound C (k+2) x.length ∧
    bound C (k+2) x.length≤ClockDyadicLedger.limit N ∧ PowerSlice.degree N=k+2 := by
  dsimp only
  rw [raw_length k C Cpad code x hpad]
  have hl := (PowerSlice.length_bounds k (allocation Cpad code.length C x.length)).1
  have hpow : 2^code.length ≤ inputLength k Cpad code.length C x.length := by
    dsimp only [allocation,header] at hl
    dsimp only [inputLength,allocation,header]
    omega
  have hb := exact_slice_and_bound k C Cpad code.length x.length hcoeff
  refine ⟨Nat.le_log_of_pow_le (by decide) hpow,?_,?_,hb.2,hb.1⟩
  · rw [binary_length]
    exact padded_width_fits k C Cpad code.length x.length hC hcoeff
  · have hp := Nat.le_self_pow (by omega : k+2≠0) x.length
    have hc := Nat.mul_le_mul_right (x.length^(k+2)+1) (by omega : 1≤C)
    dsimp only [bound]
    nlinarith

theorem linear_length (k C Cpad : ℕ) (code x : List Bool) (hpad : k+3≤Cpad) :
    x.length+1≤(rawInput k C Cpad code x).length ∧
    (rawInput k C Cpad code x).length≤
      (2*Cpad+1+header code.length C+2^(k+2))*(x.length+1) := by
  rw [raw_length k C Cpad code x hpad]
  exact PowerSlice.linear_length k (2*Cpad) (header code.length C) x.length

end NearCubicWires.RepairOrdinary.HierarchyPadding

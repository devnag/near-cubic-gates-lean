import Proof.Amplification.RecoveryRootIterationSemantics

/-! The physically prepared even stream has exactly one radix-4 digit per
original bit and denotes the original number, including the empty input. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootIteration
open RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream : List Digit → List Bool
  | [] => []
  | (lowBit, highBit) :: ds => highBit :: lowBit :: stream ds

@[simp] theorem stream_length (ds : List Digit) : (stream ds).length = 2 * ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d; simp [stream, ih]; omega

def msbValue (bits : List Bool) (initial : Nat) : Nat := bits.foldl (fun n b => 2 * n + b.toNat) initial

theorem msbValue_eq (bits : List Bool) (initial : Nat) :
    msbValue bits initial = value bits.reverse + 2 ^ bits.length * initial := by
  induction bits generalizing initial with
  | nil => simp [msbValue, value]
  | cons b bits ih =>
    change msbValue bits (2 * initial + b.toNat) = _
    rw [ih]
    simp only [List.reverse_cons, value_append, value, List.length_cons, List.length_reverse, pow_succ]
    ring

theorem numeral_stream (ds : List Digit) (initial : Nat) :
    RepairSource.RecoveryOracle.RestoringRoot.value (ds.map (fun d => digit d.1 d.2)) initial =
      msbValue (stream ds) initial := by
  induction ds generalizing initial with
  | nil => rfl
  | cons d ds ih =>
    rcases d with ⟨lowBit, highBit⟩
    change RepairSource.RecoveryOracle.RestoringRoot.value (ds.map (fun d => digit d.1 d.2))
      (4 * initial + (digit lowBit highBit).val) = msbValue (stream ds) (2 * (2 * initial + highBit.toNat) + lowBit.toNat)
    rw [ih]
    congr 1
    simp only [digit]
    omega

theorem zeros_value (n : Nat) : value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, ih]

theorem prepared_value (bits : List Bool) : msbValue (RecoveryRadixInput.prepared bits) 0 = value bits := by
  rw [msbValue_eq]
  simp [RecoveryRadixInput.prepared, List.reverse_append, value_append, zeros_value]

def pairBits : List Bool → List Digit
  | highBit :: lowBit :: rest => (lowBit, highBit) :: pairBits rest
  | _ => []

theorem stream_pairBits (bits : List Bool) (heven : bits.length % 2 = 0) : stream (pairBits bits) = bits := by
  cases bits with
  | nil => rfl
  | cons highBit tail =>
    cases tail with
    | nil => simp at heven
    | cons lowBit rest =>
      have hr : rest.length % 2 = 0 := by simp at heven; omega
      have ih := stream_pairBits rest hr
      simpa [pairBits, stream] using congrArg (List.cons highBit ∘ List.cons lowBit) ih
termination_by bits.length

def digits (bits : List Bool) : List Digit := pairBits (RecoveryRadixInput.prepared bits)

theorem stream_digits (bits : List Bool) : stream (digits bits) = RecoveryRadixInput.prepared bits :=
  stream_pairBits _ (by rw [RecoveryRadixInput.prepared_length]; omega)

theorem digits_length (bits : List Bool) : (digits bits).length = bits.length := by
  have h := congrArg List.length (stream_digits bits)
  rw [stream_length, RecoveryRadixInput.prepared_length] at h
  omega

theorem digits_value (bits : List Bool) :
    RepairSource.RecoveryOracle.RestoringRoot.value ((digits bits).map (fun d => digit d.1 d.2)) 0 = value bits := by
  rw [numeral_stream, stream_digits, prepared_value]

end NearCubicWires.RepairOrdinary.RecoveryRootIteration

import NineInputs

/-!
`app:sources`, "Full-range amplification interface": a step-capped time-constructor run, including timeout.
`app:sources`, "Uniform three-query PCPP and code interfaces": totalize the promised decoder without changing a promised answer.
proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`: the hierarchy verifier rejects overlong branches.

The first interface works on explicit source tapes plus one supplied unary
clock tape. It does not hide an input loader. The second executes the framing
and loading for a conventional Program and returns a framed status and exact
output word. Failure includes both timeout and a missing transition rule.
-/

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

set_option autoImplicit false

/-- proof of `lem:multitape-refuter`: the caller supplies the prepared unary clock separately
from the original explicit source tapes. -/
def cappedInputTapes {tapes : ℕ} (cap : ℕ)
    (input : Fin tapes → List Bool) : Fin (tapes + 1) → List Bool :=
  fun i => if h : i.val < tapes then input ⟨i.val, h⟩
    else List.replicate cap true

/-- proof of `lem:multitape-refuter`: success preserves the entire source configuration; failure
has the added control state. A halt after exactly cap steps is a success. -/
def CappedResultAgreement {tapes states : ℕ}
    (source : Option (ExecutionReceipt tapes states))
    (result : ExecutionReceipt (tapes + 1) (states + 1)) : Prop :=
  match source with
  | none => result.final.control.val = states
  | some receipt =>
      result.final.control.val = receipt.final.control.val ∧
      (∀ i : Fin tapes,
        result.final.heads i.castSucc = receipt.final.heads i ∧
        result.final.tapes i.castSucc = receipt.final.tapes i)

/-- proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`: a generic local cap transform. The cap is
input data; the finite transition table depends only on the source machine.
The extra failure transition costs at most one step. -/
def CappedMachineRun : Prop :=
  ∀ (tapes states : ℕ) (M : Machine tapes states),
    ∃ bounded : Machine (tapes + 1) (states + 1),
      (∀ q : Fin (states + 1), bounded.halted q =
        if h : q.val < states then M.halted ⟨q.val, h⟩ else true) ∧
      ∀ (cap : ℕ) (input : Fin tapes → List Bool),
        ∃ receipt,
          run bounded (cap + 1) (cappedInputTapes cap input) = some receipt ∧
          CappedResultAgreement (run M cap input) receipt

/-- `app:sources`, "Full-range amplification interface"; `app:sources`, "Uniform three-query PCPP and code interfaces": a unary step bound and an arbitrary word. -/
abbrev CappedRequest := ℕ × List Bool

/-- Each component is delimited; the Program model supplies its usual outer
frame when initializing tape zero. All these bits are paid in the clock. -/
def cappedRequestWord (r : CappedRequest) : List Bool :=
  frame (List.replicate r.1 true) ++ frame r.2

/-- A leading success bit distinguishes an empty successful output from
failure. The inner frame retains the exact physical output length, including
trailing false bits. -/
def cappedResultWord (p : Program) (r : CappedRequest) : List Bool :=
  match run p.machine r.1 (p.inputTapes r.2) with
  | none => false :: frame []
  | some receipt => true :: frame (receipt.final.tapes p.outputTape)

/-- `app:sources`, "Full-range amplification interface"; `app:sources`, "Uniform three-query PCPP and code interfaces": the output is additionally framed so that
ordinary program composition can consume it without a free framing step. -/
def CappedWordRun : Prop :=
  ∀ p : Program, ∃ C : ℕ, 1 ≤ C ∧
    Nonempty (WordFunction CappedRequest cappedRequestWord
      (fun r => frame (cappedResultWord p r))
      (fun r => C * (r.1 + r.2.length + 1)))

/-- Shared cap infrastructure: exact explicit-tape transform and its paid
serialized word interface. Neither conclusion assumes a source runtime bound. -/
def CappedRun : Prop := CappedMachineRun ∧ CappedWordRun

end NearCubicGates.Adapters.Joins

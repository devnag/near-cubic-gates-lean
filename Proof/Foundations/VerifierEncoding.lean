import Proof.Foundations.SourceCore
import StatementSupport

/-! The literal flat finite-verifier code shared by U and the refuter input.
The arbitrary Machine.descriptionBits annotation is deliberately absent.
No decoder execution or universal simulation bound is claimed in this file. -/
namespace NearCubicWires.RepairSource.VerifierEncoding
open SourceInterfaces ExecutableInterfaces LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flat_ofFn_length {n w : ℕ} (f : Fin n → List Bool)
    (h : ∀ i, (f i).length = w) : (List.ofFn f).flatten.length = n*w := by
  simp only [List.length_flatten, List.map_ofFn, Function.comp_def,
    h, List.ofFn_const, List.sum_replicate, smul_eq_mul]

@[simp] theorem actionCode_length {t s : ℕ} (width : ℕ) (a : Option (Action t s)) :
    (actionCode width a).length = 1 + width + 4*t := by
  cases a with
  | none => simp [actionCode]; omega
  | some a =>
    have h : (List.ofFn fun i : Fin t => writeCode (a.write i) ++ moveCode (a.move i)).flatten.length = t*4 := by
      apply flat_ofFn_length
      intro i
      cases hw : a.write i with
      | none => cases hm : a.move i <;> simp [writeCode, moveCode]
      | some b => cases b <;> cases hm : a.move i <;> simp [writeCode, moveCode]
    simp only [actionCode, List.length_cons, List.length_append, fixedBits, List.length_ofFn, h]
    omega

/-- Exact literal length from the U ledger: unary sizes, start, two flags per
state, then all s*2^t fixed-width transition records. -/
theorem code_length (v : OrdinaryVerifier) :
    (code v).length = v.tapeCount + v.stateCount + 2 + natBitLength v.stateCount +
      2*v.stateCount + v.stateCount*2^v.tapeCount*(1 + natBitLength v.stateCount + 4*v.tapeCount) := by
  have flags : (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten.length = v.stateCount*2 :=
    flat_ofFn_length _ (by intro i; rfl)
  have rows : (List.ofFn fun i : Fin v.stateCount =>
      (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
        actionCode (natBitLength v.stateCount)
          (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten).flatten.length =
      v.stateCount*(2^v.tapeCount*(1+natBitLength v.stateCount+4*v.tapeCount)) := by
    apply flat_ofFn_length
    intro i
    exact flat_ofFn_length _ (by intro mask; exact actionCode_length _ _)
  simp only [code, List.length_append, List.length_replicate, List.length_singleton,
    fixedBits, List.length_ofFn, flags, rows]
  ring

theorem tapes_le_code_length (v : OrdinaryVerifier) : v.tapeCount ≤ (code v).length := by
  rw [code_length]
  omega

end NearCubicWires.RepairSource.VerifierEncoding

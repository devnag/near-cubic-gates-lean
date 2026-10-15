import Proof.PCP.VerifierDecodingFields

/-! Exact lookup in the literal verifier table. All queried records are slices
of the supplied word; no natural-valued table description is expanded here. -/
namespace NearCubicWires.RepairSource.VerifierDecoding
open LocalBitMultitape VerifierEncoding RepairOrdinary.RadixSemantics
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem binary_value_word (word : List Bool) : binary word.length (value word) = word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    have hd : (1 + 2 * value word) / 2 = value word := by omega
    cases bit <;> simp [binary, value, ih, hd]

theorem mask_inverse {t : ℕ} (scanned : Fin t → Bool) :
    (fun tape : Fin t => (value (List.ofFn scanned)).testBit tape.val) = scanned := by
  apply List.ofFn_injective
  change fixedBits t (value (List.ofFn scanned)) = List.ofFn scanned
  rw [fixedBits_binary]
  have h := binary_value_word (List.ofFn scanned)
  simpa only [List.length_ofFn] using h

def entryWidth (t s : ℕ) : ℕ := 1 + natBitLength s + 4*t

def flags (v : OrdinaryVerifier) : List Bool :=
  (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten

def table (v : OrdinaryVerifier) : List Bool :=
  (List.ofFn fun i : Fin v.stateCount =>
    (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
      actionCode (natBitLength v.stateCount)
        (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten).flatten

def flagAt (word : List Bool) (state : ℕ) (accept : Bool) : Bool :=
  (slice word (state*2) 2).getD accept.toNat false

def ruleAt {t s : ℕ} (word : List Bool) (state : Fin s)
    (scanned : Fin t → Bool) : Option (Action t s) :=
  let row := slice word (state.val * (2^t * entryWidth t s)) (2^t * entryWidth t s)
  let entry := slice row (value (List.ofFn scanned) * entryWidth t s) (entryWidth t s)
  decodeAction (natBitLength s) entry

theorem flags_length (v : OrdinaryVerifier) : (flags v).length = 2*v.stateCount := by
  rw [flags, flat_ofFn_length (w := 2) _ (by intro i; rfl)]
  omega

theorem table_length (v : OrdinaryVerifier) :
    (table v).length = v.stateCount * 2^v.tapeCount * entryWidth v.tapeCount v.stateCount := by
  unfold table
  rw [flat_ofFn_length _ (fun _ => flat_ofFn_length _ (fun _ => actionCode_length _ _))]
  simp only [entryWidth]
  ring

theorem flagAt_flags (v : OrdinaryVerifier) (state : Fin v.stateCount) (accept : Bool) :
    flagAt (flags v) state.val accept = if accept then v.accepting state else v.machine.halted state := by
  have h := slice_flat (width := 2) (fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i])
    (by intro i; rfl) state
  unfold flagAt flags
  rw [h]
  cases accept <;> rfl

theorem ruleAt_table (v : OrdinaryVerifier) (state : Fin v.stateCount)
    (scanned : Fin v.tapeCount → Bool) : ruleAt (table v) state scanned = v.machine.rule state scanned := by
  have hr := slice_flat (fun i : Fin v.stateCount =>
      (List.ofFn fun mask : Fin (2^v.tapeCount) => actionCode (natBitLength v.stateCount)
        (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten)
    (by intro i; exact flat_ofFn_length _ (fun _ => actionCode_length _ _)) state
  have hm : value (List.ofFn scanned) < 2^v.tapeCount := by
    simpa only [List.length_ofFn] using value_lt (List.ofFn scanned)
  let mask : Fin (2^v.tapeCount) := ⟨value (List.ofFn scanned), hm⟩
  have he := slice_flat (fun mask : Fin (2^v.tapeCount) => actionCode (natBitLength v.stateCount)
      (v.machine.rule state (fun tape => mask.val.testBit tape.val)))
    (fun _ => actionCode_length _ _) mask
  unfold ruleAt
  change decodeAction (natBitLength v.stateCount)
    (slice (slice (table v) (state.val*(2^v.tapeCount*entryWidth v.tapeCount v.stateCount))
      (2^v.tapeCount*entryWidth v.tapeCount v.stateCount))
      (mask.val*entryWidth v.tapeCount v.stateCount) (entryWidth v.tapeCount v.stateCount)) = _
  rw [show slice (table v) (state.val*(2^v.tapeCount*entryWidth v.tapeCount v.stateCount))
      (2^v.tapeCount*entryWidth v.tapeCount v.stateCount) = _ from hr]
  rw [show slice _ (mask.val*entryWidth v.tapeCount v.stateCount)
      (entryWidth v.tapeCount v.stateCount) = _ from he]
  have hs : v.stateCount ≤ 2^natBitLength v.stateCount :=
    (Nat.lt_pow_succ_log_self (by decide) v.stateCount).le
  rw [decodeAction_code (natBitLength v.stateCount) hs]
  have hmask : (fun tape : Fin v.tapeCount => mask.val.testBit tape.val) = scanned := mask_inverse scanned
  rw [hmask]

theorem code_split (v : OrdinaryVerifier) : code v =
    List.replicate v.tapeCount true ++ false ::
    (List.replicate v.stateCount true ++ false ::
      (fixedBits (natBitLength v.stateCount) v.machine.start.val ++ flags v ++ table v)) := by
  simp only [code, flags, table, List.append_assoc, List.cons_append, List.nil_append]

/-- Complete immediate lookup consumer: the same start, flags and transition
table used by claimed-trace validation, with no function-valued lookup input. -/
theorem literal_lookup (v : OrdinaryVerifier) (state : Fin v.stateCount)
    (scanned : Fin v.tapeCount → Bool) :
    flagAt (flags v) state.val false = v.machine.halted state ∧
    flagAt (flags v) state.val true = v.accepting state ∧
    ruleAt (table v) state scanned = v.machine.rule state scanned := by
  exact ⟨flagAt_flags v state false, flagAt_flags v state true, ruleAt_table v state scanned⟩

end NearCubicWires.RepairSource.VerifierDecoding

import Proof.MachineModel.CanonicalRecoveryProgram

namespace NearCubicWires.CanonicalRecoveryProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

private theorem encodeNat_one_code :
    encodeNat 1 = Nat.pair 1 1 := by
  simp [encodeNat, encodeBits, encodeBoolList, encodeBalancedList, boolCode]

@[simp] private theorem encodeNat_one_ne_zero :
    encodeNat 1 ≠ 0 := by
  rw [encodeNat_one_code]
  have hleft := Nat.left_le_pair 1 1
  omega

private theorem runReject
    (extra maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 65)
    (hzero : natBitLength 0 ≤ maximumBits) :
    runNPOracleProgram recoveryEnvelopeProgram maximumBits
        (extra + 2) state =
      some 0 := by
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_set_instruction (fuel := extra + 1) (by rfl) hpc hzero]
  exact run_halt_instruction (fuel := extra) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hzero

private def exactOneSuccessState
    (state : NPOracleState) (code left scratch right : ℕ)
    (pc₁ pc₂ pc₃ pc₄ pc₅ success : ℕ) : NPOracleState :=
  let state₁ :=
    (state.write left (Nat.unpair code).1).jump pc₁
  let state₂ := state₁.jump pc₂
  let state₃ := (state₂.write scratch code).jump pc₃
  let state₄ := (state₃.write scratch (code + 1)).jump pc₄
  let state₅ :=
    (state₄.write right (Nat.unpair (code + 1)).2).jump pc₅
  state₅.jump success

private theorem runExactOne
    (code maximumBits extra : ℕ) (state : NPOracleState)
    (source left scratch right pc₀ pc₁ pc₂ pc₃ pc₄ pc₅ success : ℕ)
    (hpc : state.pc = pc₀)
    (hsource : state.registers source = code)
    (hsourceLeft : source ≠ left)
    (hnonzero : code ≠ 0)
    (hextra : 2 ≤ extra)
    (hcode : natBitLength code ≤ maximumBits)
    (hplus : natBitLength (code + 1) ≤ maximumBits)
    (hat₀ : recoveryEnvelopeProgram[pc₀]? =
      some (.unpairLeft source left pc₁))
    (hat₁ : recoveryEnvelopeProgram[pc₁]? =
      some (.branchZero left pc₂ 65))
    (hat₂ : recoveryEnvelopeProgram[pc₂]? =
      some (.copy source scratch pc₃))
    (hat₃ : recoveryEnvelopeProgram[pc₃]? =
      some (.increment scratch pc₄))
    (hat₄ : recoveryEnvelopeProgram[pc₄]? =
      some (.unpairRight scratch right pc₅))
    (hat₅ : recoveryEnvelopeProgram[pc₅]? =
      some (.branchZero right success 65))
    (hzero : natBitLength 0 ≤ maximumBits) :
    runNPOracleProgram recoveryEnvelopeProgram maximumBits
        (extra + 6) state =
      if code = 1 then
        runNPOracleProgram recoveryEnvelopeProgram maximumBits extra
          (exactOneSuccessState state code left scratch right
            pc₁ pc₂ pc₃ pc₄ pc₅ success)
      else
        some 0 := by
  have hleft :
      natBitLength (Nat.unpair code).1 ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_left_le code)).trans hcode
  have hright :
      natBitLength (Nat.unpair (code + 1)).2 ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_right_le (code + 1))).trans hplus
  rw [show extra + 6 = (extra + 5) + 1 by omega]
  rw [run_unpairLeft_instruction hat₀ hpc
    (by simp [hsource]) hleft]
  rw [show extra + 5 = (extra + 4) + 1 by omega]
  rw [run_branchZero_instruction hat₁ rfl]
  simp only [NPOracleState.write, NPOracleState.jump, eq_self, if_true]
  by_cases hone : code = 1
  · obtain ⟨_, hleftZero, hrightZero⟩ := isOneCode_iff.mpr hone
    rw [if_pos hleftZero, if_pos hone]
    rw [show extra + 4 = (extra + 3) + 1 by omega]
    rw [run_copy_instruction hat₂ rfl
      (by simp [hsourceLeft, hsource]) hcode]
    rw [show extra + 3 = (extra + 2) + 1 by omega]
    rw [run_increment_instruction hat₃ rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hplus]
    rw [show extra + 2 = (extra + 1) + 1 by omega]
    rw [run_unpairRight_instruction hat₄ rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hright]
    rw [show extra + 1 = extra + 1 by rfl]
    rw [run_branchZero_instruction hat₅ rfl]
    simp only [NPOracleState.write, NPOracleState.jump, eq_self, if_true]
    rw [if_pos hrightZero]
    rfl
  · rw [if_neg hone]
    by_cases hleftZero : (Nat.unpair code).1 = 0
    · rw [if_pos hleftZero]
      have hrightNonzero : (Nat.unpair (code + 1)).2 ≠ 0 := by
        intro hrightZero
        exact hone (isOneCode_iff.mp
          ⟨hnonzero, hleftZero, hrightZero⟩)
      rw [show extra + 4 = (extra + 3) + 1 by omega]
      rw [run_copy_instruction hat₂ rfl
        (by simp [hsourceLeft, hsource]) hcode]
      rw [show extra + 3 = (extra + 2) + 1 by omega]
      rw [run_increment_instruction hat₃ rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hplus]
      rw [show extra + 2 = (extra + 1) + 1 by omega]
      rw [run_unpairRight_instruction hat₄ rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hright]
      rw [show extra + 1 = extra + 1 by rfl]
      rw [run_branchZero_instruction hat₅ rfl]
      simp only [NPOracleState.write, NPOracleState.jump, eq_self, if_true]
      rw [if_neg hrightNonzero]
      have hrejected :=
        runReject (extra - 2) maximumBits
          (exactOneSuccessState state code left scratch right
            pc₁ pc₂ pc₃ pc₄ pc₅ 65)
          rfl hzero
      rwa [Nat.sub_add_cancel hextra] at hrejected
    · rw [if_neg hleftZero]
      exact runReject (extra + 2) maximumBits
        (((state.write left (Nat.unpair code).1).jump pc₁).jump 65)
        rfl hzero

private def cellSuccessState
    (state : NPOracleState) (cursor destination start : ℕ) :
    NPOracleState :=
  let outer := Nat.unpair cursor
  let payload := Nat.unpair outer.2
  let state₁ := state.jump (start + 1)
  let state₂ := (state₁.write 12 outer.1).jump (start + 2)
  let state₃ := state₂.jump (start + 3)
  let state₄ :=
    exactOneSuccessState state₃ outer.1 13 14 13
      (start + 4) (start + 5) (start + 6) (start + 7)
      (start + 8) (start + 9)
  let state₅ := (state₄.write 15 outer.2).jump (start + 10)
  let state₆ := (state₅.write destination payload.1).jump (start + 11)
  (state₆.write 2 payload.2).jump (start + 12)

private theorem runCell
    (raw cursor destination start extra maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = start)
    (hcursor : state.registers 2 = cursor)
    (hdestination : 15 ≠ destination)
    (hcursorRaw : cursor ≤ raw)
    (hsmall : ∀ value, value ≤ raw + 2 →
      natBitLength value ≤ maximumBits)
    (hat₀ : recoveryEnvelopeProgram[start]? =
      some (.branchZero 2 65 (start + 1)))
    (hat₁ : recoveryEnvelopeProgram[start + 1]? =
      some (.unpairLeft 2 12 (start + 2)))
    (hat₂ : recoveryEnvelopeProgram[start + 2]? =
      some (.branchZero 12 65 (start + 3)))
    (hat₃ : recoveryEnvelopeProgram[start + 3]? =
      some (.unpairLeft 12 13 (start + 4)))
    (hat₄ : recoveryEnvelopeProgram[start + 4]? =
      some (.branchZero 13 (start + 5) 65))
    (hat₅ : recoveryEnvelopeProgram[start + 5]? =
      some (.copy 12 14 (start + 6)))
    (hat₆ : recoveryEnvelopeProgram[start + 6]? =
      some (.increment 14 (start + 7)))
    (hat₇ : recoveryEnvelopeProgram[start + 7]? =
      some (.unpairRight 14 13 (start + 8)))
    (hat₈ : recoveryEnvelopeProgram[start + 8]? =
      some (.branchZero 13 (start + 9) 65))
    (hat₉ : recoveryEnvelopeProgram[start + 9]? =
      some (.unpairRight 2 15 (start + 10)))
    (hat₁₀ : recoveryEnvelopeProgram[start + 10]? =
      some (.unpairLeft 15 destination (start + 11)))
    (hat₁₁ : recoveryEnvelopeProgram[start + 11]? =
      some (.unpairRight 15 2 (start + 12)))
    (hzero : natBitLength 0 ≤ maximumBits) :
    runNPOracleProgram recoveryEnvelopeProgram maximumBits
        (extra + 12) state =
      if (Nat.unpair cursor).1 = 1 then
        runNPOracleProgram recoveryEnvelopeProgram maximumBits extra
          (cellSuccessState state cursor destination start)
      else
        some 0 := by
  let outer := Nat.unpair cursor
  let payload := Nat.unpair outer.2
  have hcursorBits : natBitLength cursor ≤ maximumBits :=
    hsmall cursor (by omega)
  have houterLeftBits :
      natBitLength outer.1 ≤ maximumBits :=
    hsmall outer.1 (by
      exact (Nat.unpair_left_le cursor).trans (by omega))
  have houterLeftPlusBits :
      natBitLength (outer.1 + 1) ≤ maximumBits :=
    hsmall (outer.1 + 1) (by
      dsimp [outer]
      have := Nat.unpair_left_le cursor
      omega)
  have houterRightBits :
      natBitLength outer.2 ≤ maximumBits :=
    hsmall outer.2 (by
      exact (Nat.unpair_right_le cursor).trans (by omega))
  have hpayloadLeftBits :
      natBitLength payload.1 ≤ maximumBits :=
    hsmall payload.1 (by
      exact (Nat.unpair_left_le outer.2).trans
        ((Nat.unpair_right_le cursor).trans (by omega)))
  have hpayloadRightBits :
      natBitLength payload.2 ≤ maximumBits :=
    hsmall payload.2 (by
      exact (Nat.unpair_right_le outer.2).trans
        ((Nat.unpair_right_le cursor).trans (by omega)))
  rw [show extra + 12 = (extra + 11) + 1 by omega]
  rw [run_branchZero_instruction hat₀ hpc]
  rw [hcursor]
  change
    runNPOracleProgram recoveryEnvelopeProgram maximumBits (extra + 11)
        (state.jump (if cursor = 0 then 65 else start + 1)) =
      _
  by_cases hcursorZero : cursor = 0
  · rw [if_pos hcursorZero]
    have hrejected :=
      runReject (extra + 9) maximumBits (state.jump 65) rfl hzero
    simpa [hcursorZero, outer] using hrejected
  · rw [if_neg hcursorZero]
    rw [show extra + 11 = (extra + 10) + 1 by omega]
    rw [run_unpairLeft_instruction hat₁ rfl
      (by simp [NPOracleState.jump, hcursor, outer]) houterLeftBits]
    rw [show extra + 10 = (extra + 9) + 1 by omega]
    rw [run_branchZero_instruction hat₂ rfl]
    rw [show
      ((((state.jump (start + 1)).write 12 outer.1).jump
          (start + 2)).registers 12) =
        outer.1 by
      simp [NPOracleState.write, NPOracleState.jump]]
    by_cases htagZero : outer.1 = 0
    · rw [if_pos htagZero]
      have hrejected :=
        runReject (extra + 7) maximumBits
          ((((state.jump (start + 1)).write 12 outer.1).jump
            (start + 2)).jump 65)
          rfl hzero
      have hnotOne : (Nat.unpair cursor).1 ≠ 1 := by
        dsimp [outer] at htagZero
        omega
      rw [if_neg hnotOne]
      simpa only [Nat.add_assoc] using hrejected
    · rw [if_neg htagZero]
      have hexact :=
        runExactOne outer.1 maximumBits (extra + 3)
          ((((state.jump (start + 1)).write 12 outer.1).jump
            (start + 2)).jump (start + 3))
          12 13 14 13
          (start + 3) (start + 4) (start + 5) (start + 6)
          (start + 7) (start + 8) (start + 9)
          rfl
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by omega) htagZero (by omega)
          houterLeftBits houterLeftPlusBits
          hat₃ hat₄ hat₅ hat₆ hat₇ hat₈ hzero
      rw [show extra + 9 = (extra + 3) + 6 by omega]
      rw [hexact]
      by_cases htagOne : outer.1 = 1
      · rw [if_pos htagOne, if_pos htagOne]
        rw [show extra + 3 = (extra + 2) + 1 by omega]
        rw [run_unpairRight_instruction hat₉ rfl
          (by
            simp [exactOneSuccessState, NPOracleState.write,
              NPOracleState.jump, hcursor, outer])
          houterRightBits]
        rw [show extra + 2 = (extra + 1) + 1 by omega]
        rw [run_unpairLeft_instruction hat₁₀ rfl
          (by simp [NPOracleState.write, NPOracleState.jump, payload])
          hpayloadLeftBits]
        rw [show extra + 1 = extra + 1 by rfl]
        rw [run_unpairRight_instruction hat₁₁ rfl
          (by simp [NPOracleState.write, NPOracleState.jump, payload,
            hdestination])
          hpayloadRightBits]
        rfl
      · have hnotOne : (Nat.unpair cursor).1 ≠ 1 := by
          simpa only [outer] using htagOne
        rw [if_neg htagOne]
        simp only [hnotOne, if_false]

private theorem runAccept
    (raw tag pc next extra maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = pc)
    (hraw : state.registers 3 = raw)
    (htag : natBitLength tag ≤ maximumBits)
    (houtput : natBitLength (Nat.pair tag raw) ≤ maximumBits)
    (hat₀ : recoveryEnvelopeProgram[pc]? =
      some (.set 11 tag next))
    (hat₁ : recoveryEnvelopeProgram[next]? =
      some (.pair 11 3 0 64)) :
    runNPOracleProgram recoveryEnvelopeProgram maximumBits
        (extra + 3) state =
      some (Nat.pair tag raw) := by
  rw [show extra + 3 = (extra + 2) + 1 by omega]
  rw [run_set_instruction hat₀ hpc htag]
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_pair_instruction hat₁ rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hraw]) houtput]
  exact run_halt_instruction (fuel := extra) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

private theorem runMode
    (raw maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 39)
    (hraw : state.registers 3 = raw)
    (hmodeRaw : state.registers 4 ≤ raw)
    (hsmall : ∀ value, value ≤ raw + 2 →
      natBitLength value ≤ maximumBits)
    (houtOne : natBitLength (Nat.pair 1 raw) ≤ maximumBits)
    (houtTwo : natBitLength (Nat.pair 2 raw) ≤ maximumBits) :
    runNPOracleProgram recoveryEnvelopeProgram maximumBits 28 state =
      let mode := state.registers 4
      some
        (if mode = 0 then Nat.pair 1 raw
          else if mode = encodeNat 1 then Nat.pair 2 raw
          else 0) := by
  let mode := state.registers 4
  change
    runNPOracleProgram recoveryEnvelopeProgram maximumBits 28 state =
      some
        (if mode = 0 then Nat.pair 1 raw
          else if mode = encodeNat 1 then Nat.pair 2 raw
          else 0)
  let outer := Nat.unpair mode
  have hzero : natBitLength 0 ≤ maximumBits :=
    hsmall 0 (by omega)
  have hone : natBitLength 1 ≤ maximumBits :=
    hsmall 1 (by omega)
  have htwo : natBitLength 2 ≤ maximumBits :=
    hsmall 2 (by omega)
  have hmodeBits : natBitLength mode ≤ maximumBits :=
    hsmall mode (by
      dsimp [mode]
      omega)
  have houterLeftBits :
      natBitLength outer.1 ≤ maximumBits :=
    hsmall outer.1 (by
      exact (Nat.unpair_left_le mode).trans (by omega))
  have houterLeftPlusBits :
      natBitLength (outer.1 + 1) ≤ maximumBits :=
    hsmall (outer.1 + 1) (by
      dsimp [outer]
      have := Nat.unpair_left_le mode
      omega)
  have houterRightBits :
      natBitLength outer.2 ≤ maximumBits :=
    hsmall outer.2 (by
      exact (Nat.unpair_right_le mode).trans (by omega))
  have houterRightPlusBits :
      natBitLength (outer.2 + 1) ≤ maximumBits :=
    hsmall (outer.2 + 1) (by
      have hright : outer.2 ≤ mode := Nat.unpair_right_le mode
      have hmode : mode ≤ raw := hmodeRaw
      omega)
  have hsuccessorLeftBits :
      natBitLength (Nat.unpair (outer.2 + 1)).1 ≤ maximumBits :=
    hsmall (Nat.unpair (outer.2 + 1)).1 (by
      have hcomponent := Nat.unpair_left_le (outer.2 + 1)
      have hright : outer.2 ≤ mode := Nat.unpair_right_le mode
      have hmode : mode ≤ raw := hmodeRaw
      omega)
  have houterRightComponentBits :
      natBitLength (Nat.unpair outer.2).2 ≤ maximumBits :=
    hsmall (Nat.unpair outer.2).2 (by
      have hcomponent := Nat.unpair_right_le outer.2
      have hright : outer.2 ≤ mode := Nat.unpair_right_le mode
      have hmode : mode ≤ raw := hmodeRaw
      omega)
  rw [show 28 = 27 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) hpc]
  by_cases hmodeZero : mode = 0
  · have hregisterZero : state.registers 4 = 0 := by
      simpa only [mode] using hmodeZero
    rw [if_pos hregisterZero]
    have haccepted :=
      runAccept raw 1 60 61 24 maximumBits (state.jump 60)
        rfl hraw hone houtOne (by rfl) (by rfl)
    simpa [hmodeZero] using haccepted
  · have hregisterNonzero : state.registers 4 ≠ 0 := by
      simpa only [mode] using hmodeZero
    rw [if_neg hregisterNonzero]
    rw [show 27 = 26 + 1 by omega]
    rw [run_unpairLeft_instruction (by rfl) rfl
      (by simp [NPOracleState.jump, outer, mode]) houterLeftBits]
    let state₁ :=
      ((state.jump 40).write 12 outer.1).jump 41
    change
      runNPOracleProgram recoveryEnvelopeProgram maximumBits 26 state₁ =
        _
    rw [show 26 = 25 + 1 by omega]
    rw [run_branchZero_instruction (by rfl) rfl]
    rw [show state₁.registers 12 = outer.1 by
      simp [state₁, NPOracleState.write, NPOracleState.jump]]
    by_cases houterZero : outer.1 = 0
    · rw [if_pos houterZero]
      have hnotOne : mode ≠ encodeNat 1 := by
        intro hequal
        have hequal' : state.registers 4 = encodeNat 1 := by
          simpa only [mode] using hequal
        have hone' : outer.1 = 1 := by
          dsimp [outer, mode]
          rw [hequal', encodeNat_one_code, Nat.unpair_pair]
        omega
      have hrejected :=
        runReject 23 maximumBits (state₁.jump 65) rfl hzero
      simpa [hmodeZero, hnotOne] using hrejected
    · rw [if_neg houterZero]
      let state₂ := state₁.jump 42
      have hexactOuter :=
        runExactOne outer.1 maximumBits 19 state₂
          12 13 14 13 42 43 44 45 46 47 48
          rfl
          (by simp [state₂, state₁, NPOracleState.write,
            NPOracleState.jump])
          (by omega) houterZero (by omega)
          houterLeftBits houterLeftPlusBits
          (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
          hzero
      change
        runNPOracleProgram recoveryEnvelopeProgram maximumBits 25 state₂ =
          _
      rw [show 25 = 19 + 6 by omega]
      rw [hexactOuter]
      by_cases houterOne : outer.1 = 1
      · rw [if_pos houterOne]
        let state₃ :=
          exactOneSuccessState state₂ outer.1 13 14 13
            43 44 45 46 47 48
        rw [show 19 = 18 + 1 by omega]
        rw [run_unpairRight_instruction (by rfl) rfl
          (by
            simp [exactOneSuccessState, state₂, state₁,
              NPOracleState.write, NPOracleState.jump, outer, mode])
          houterRightBits]
        let state₄ := (state₃.write 15 outer.2).jump 49
        change
          runNPOracleProgram recoveryEnvelopeProgram maximumBits 18 state₄ =
            _
        rw [show 18 = 17 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state₄.registers 15 = outer.2 by
          simp [state₄, NPOracleState.write, NPOracleState.jump]]
        by_cases hrightZero : outer.2 = 0
        · rw [if_pos hrightZero]
          have hnotOne : mode ≠ encodeNat 1 := by
            intro hequal
            have hequal' : state.registers 4 = encodeNat 1 := by
              simpa only [mode] using hequal
            have hrightOne : outer.2 = 1 := by
              dsimp [outer, mode]
              rw [hequal', encodeNat_one_code, Nat.unpair_pair]
            omega
          have hrejected :=
            runReject 15 maximumBits (state₄.jump 65) rfl hzero
          simpa [hmodeZero, hnotOne] using hrejected
        · rw [if_neg hrightZero]
          let state₅ := state₄.jump 50
          have hexactRight :=
            runExactOne outer.2 maximumBits 11 state₅
              15 12 14 13 50 51 52 53 54 55 56
              rfl
              (by simp [state₅, state₄, NPOracleState.write,
                NPOracleState.jump])
              (by omega) hrightZero (by omega)
              houterRightBits houterRightPlusBits
              (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
              hzero
          change
            runNPOracleProgram recoveryEnvelopeProgram maximumBits 17
                state₅ =
              _
          rw [show 17 = 11 + 6 by omega]
          rw [hexactRight]
          by_cases hrightOne : outer.2 = 1
          · rw [if_pos hrightOne]
            let state₆ :=
              exactOneSuccessState state₅ outer.2 12 14 13
                51 52 53 54 55 56
            rw [show 11 = 10 + 1 by omega]
            rw [run_unpairLeft_instruction (by rfl) rfl
              (by
                simp [exactOneSuccessState, state₅, state₄,
                  NPOracleState.write, NPOracleState.jump])
              hsuccessorLeftBits]
            let state₇ :=
              (state₆.write 12 (Nat.unpair (outer.2 + 1)).1).jump 57
            change
              runNPOracleProgram recoveryEnvelopeProgram maximumBits 10
                  state₇ =
                _
            rw [show 10 = 9 + 1 by omega]
            rw [run_branchZero_instruction (by rfl) rfl]
            rw [show state₇.registers 12 =
                (Nat.unpair (outer.2 + 1)).1 by
              simp [state₇, NPOracleState.write, NPOracleState.jump]]
            rw [if_neg (by
              rw [hrightOne]
              norm_num [Nat.unpair])]
            let state₈ := state₇.jump 58
            change
              runNPOracleProgram recoveryEnvelopeProgram maximumBits 9
                  state₈ =
                _
            rw [show 9 = 8 + 1 by omega]
            rw [run_unpairRight_instruction (by rfl) rfl
              (by
                simp [state₈, state₇, state₆, exactOneSuccessState,
                  state₅, state₄, NPOracleState.write,
                  NPOracleState.jump])
              houterRightComponentBits]
            let state₉ :=
              (state₈.write 13 (Nat.unpair outer.2).2).jump 59
            change
              runNPOracleProgram recoveryEnvelopeProgram maximumBits 8
                  state₉ =
                _
            rw [show 8 = 7 + 1 by omega]
            rw [run_branchZero_instruction (by rfl) rfl]
            rw [show state₉.registers 13 = (Nat.unpair outer.2).2 by
              simp [state₉, NPOracleState.write, NPOracleState.jump]]
            rw [if_neg (by
              rw [hrightOne]
              norm_num [Nat.unpair])]
            let state₁₀ := state₉.jump 62
            have hcanonical : mode = encodeNat 1 := by
              calc
                mode = Nat.pair outer.1 outer.2 := by
                  simpa only [outer] using (Nat.pair_unpair mode).symm
                _ = Nat.pair 1 1 := by rw [houterOne, hrightOne]
                _ = encodeNat 1 := encodeNat_one_code.symm
            have haccepted :=
              runAccept raw 2 62 63 4 maximumBits state₁₀ rfl
                (by
                  simp [state₁₀, state₉, state₈, state₇, state₆,
                    exactOneSuccessState, state₅, state₄, state₃,
                    state₂, state₁, NPOracleState.write,
                    NPOracleState.jump, hraw])
                htwo houtTwo (by rfl) (by rfl)
            simpa [hmodeZero, hcanonical] using haccepted
          · rw [if_neg hrightOne]
            have hnotOne : mode ≠ encodeNat 1 := by
              intro hequal
              have hequal' : state.registers 4 = encodeNat 1 := by
                simpa only [mode] using hequal
              apply hrightOne
              dsimp [outer, mode]
              rw [hequal', encodeNat_one_code, Nat.unpair_pair]
            simp [hmodeZero, hnotOne]
      · have hnotOne : mode ≠ encodeNat 1 := by
          intro hequal
          have hequal' : state.registers 4 = encodeNat 1 := by
            simpa only [mode] using hequal
          apply houterOne
          dsimp [outer, mode]
          rw [hequal', encodeNat_one_code, Nat.unpair_pair]
        rw [if_neg houterOne]
        simp [hmodeZero, hnotOne]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The fixed symbolic trace normalizes 67 state transitions and nested writes.
theorem run_recoveryEnvelopeProgram_machine
    (raw inputLength maximumBits : ℕ)
    (hbits : recoveryEnvelopeBits raw ≤ maximumBits) :
    runNPOracleProgram recoveryEnvelopeProgram maximumBits
        recoveryEnvelopeFuel
        (initialNPOracleState inputLength raw) =
      some (recoveryEnvelopeMachineOutput raw) := by
  have hsmall :
      ∀ value, value ≤ raw + 2 →
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply (natBitLength_mono ?_).trans hbits
    exact hvalue.trans
      ((le_max_right (Nat.pair 2 raw) (raw + 2)).trans
        (le_max_right (Nat.pair 1 raw)
          (max (Nat.pair 2 raw) (raw + 2))))
  have houtOne :
      natBitLength (Nat.pair 1 raw) ≤ maximumBits := by
    apply (natBitLength_mono (le_max_left _ _)).trans hbits
  have houtTwo :
      natBitLength (Nat.pair 2 raw) ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hbits
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hrawBits : natBitLength raw ≤ maximumBits :=
    hsmall raw (by omega)
  have hzero : natBitLength 0 ≤ maximumBits :=
    hsmall 0 (by omega)
  let outer₀ := Nat.unpair raw
  let payload₀ := Nat.unpair outer₀.2
  let outer₁ := Nat.unpair payload₀.2
  let payload₁ := Nat.unpair outer₁.2
  let outer₂ := Nat.unpair payload₁.2
  let payload₂ := Nat.unpair outer₂.2
  change
    runNPOracleProgram recoveryEnvelopeProgram maximumBits
        recoveryEnvelopeFuel
        (initialNPOracleState inputLength raw) =
      some
        (if outer₀.1 = 1 ∧ outer₁.1 = 1 ∧ outer₂.1 = 1 ∧
            payload₂.2 = 0 then
          if payload₀.1 = 0 then Nat.pair 1 raw
          else if payload₀.1 = encodeNat 1 then Nat.pair 2 raw
          else 0
        else 0)
  unfold recoveryEnvelopeFuel
  rw [show 67 = 66 + 1 by omega]
  rw [run_copy_instruction (by rfl) rfl
    (by simp [initialNPOracleState]) hrawBits]
  let state₁ :=
    ((initialNPOracleState inputLength raw).write 2 raw).jump 1
  change
    runNPOracleProgram recoveryEnvelopeProgram maximumBits 66 state₁ =
      _
  rw [show 66 = 65 + 1 by omega]
  rw [run_copy_instruction (by rfl) rfl
    (by simp [state₁, NPOracleState.write, NPOracleState.jump,
      initialNPOracleState]) hrawBits]
  let state₂ := (state₁.write 3 raw).jump 2
  change
    runNPOracleProgram recoveryEnvelopeProgram maximumBits 65 state₂ =
      _
  have hcell₀ :=
    runCell raw raw 4 2 53 maximumBits state₂
      rfl
      (by simp [state₂, state₁, NPOracleState.write,
        NPOracleState.jump, initialNPOracleState])
      (by omega) (by omega) hsmall
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      hzero
  rw [show 65 = 53 + 12 by omega]
  rw [hcell₀]
  by_cases htag₀ : outer₀.1 = 1
  · rw [if_pos (by simpa only [outer₀] using htag₀)]
    let state₃ := cellSuccessState state₂ raw 4 2
    have hcell₁ :=
      runCell raw payload₀.2 5 14 41 maximumBits state₃
        rfl
        (by
          simp [state₃, cellSuccessState, exactOneSuccessState,
            state₂, state₁, NPOracleState.write, NPOracleState.jump,
            initialNPOracleState, outer₀, payload₀])
        (by omega)
        (by
          exact (Nat.unpair_right_le outer₀.2).trans
            ((Nat.unpair_right_le raw).trans (by omega)))
        hsmall
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        hzero
    rw [show 53 = 41 + 12 by omega]
    rw [hcell₁]
    by_cases htag₁ : outer₁.1 = 1
    · rw [if_pos (by simpa only [outer₁] using htag₁)]
      let state₄ := cellSuccessState state₃ payload₀.2 5 14
      have hcell₂ :=
        runCell raw payload₁.2 6 26 29 maximumBits state₄
          rfl
          (by
            simp [state₄, state₃, cellSuccessState,
              exactOneSuccessState, state₂, state₁,
              NPOracleState.write, NPOracleState.jump,
              initialNPOracleState, outer₀, payload₀, outer₁,
              payload₁])
          (by omega)
          (by
            exact (Nat.unpair_right_le outer₁.2).trans
              ((Nat.unpair_right_le payload₀.2).trans
                ((Nat.unpair_right_le outer₀.2).trans
                  ((Nat.unpair_right_le raw).trans (by omega)))))
          hsmall
          (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
          (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
          hzero
      rw [show 41 = 29 + 12 by omega]
      rw [hcell₂]
      by_cases htag₂ : outer₂.1 = 1
      · rw [if_pos (by simpa only [outer₂] using htag₂)]
        let state₅ := cellSuccessState state₄ payload₁.2 6 26
        rw [show 29 = 28 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state₅.registers 2 = payload₂.2 by
          simp [state₅, state₄, state₃, cellSuccessState,
            exactOneSuccessState, state₂, state₁,
            NPOracleState.write, NPOracleState.jump,
            initialNPOracleState, outer₀, payload₀, outer₁,
            payload₁, outer₂, payload₂]]
        by_cases htail : payload₂.2 = 0
        · rw [if_pos htail]
          have hmodeRun :=
            runMode raw maximumBits (state₅.jump 39) rfl
              (by
                simp [state₅, state₄, state₃, cellSuccessState,
                  exactOneSuccessState, state₂, state₁,
                  NPOracleState.write, NPOracleState.jump,
                  initialNPOracleState])
              (by
                have hpayload :
                    payload₀.1 ≤ outer₀.2 :=
                  (Nat.unpair_left_le outer₀.2)
                exact hpayload.trans
                  ((Nat.unpair_right_le raw).trans (by omega)))
              hsmall houtOne houtTwo
          simpa [state₅, state₄, state₃, cellSuccessState,
            exactOneSuccessState, state₂, state₁,
            NPOracleState.write, NPOracleState.jump,
            initialNPOracleState, outer₀, payload₀, htag₀, htag₁,
            htag₂, htail] using hmodeRun
        · rw [if_neg htail]
          have hrejected :=
            runReject 26 maximumBits (state₅.jump 65) rfl hzero
          simpa [htag₀, htag₁, htag₂, htail] using hrejected
      · have hnotTag₂ : (Nat.unpair payload₁.2).1 ≠ 1 := by
          simpa only [outer₂] using htag₂
        rw [if_neg hnotTag₂]
        simp [htag₀, htag₁, htag₂]
    · have hnotTag₁ : (Nat.unpair payload₀.2).1 ≠ 1 := by
        simpa only [outer₁] using htag₁
      rw [if_neg hnotTag₁]
      simp [htag₀, htag₁]
  · have hnotTag₀ : (Nat.unpair raw).1 ≠ 1 := by
      simpa only [outer₀] using htag₀
    rw [if_neg hnotTag₀]
    simp [htag₀]

theorem run_recoveryEnvelopeProgram
    (raw inputLength maximumBits : ℕ)
    (hbits : recoveryEnvelopeBits raw ≤ maximumBits) :
    runNPOracleProgram recoveryEnvelopeProgram maximumBits
        recoveryEnvelopeFuel
        (initialNPOracleState inputLength raw) =
      some (recoveryEnvelopeOutput raw) := by
  rw [run_recoveryEnvelopeProgram_machine raw inputLength maximumBits hbits]
  exact congrArg some (recoveryEnvelopeMachineOutput_eq raw)

/-- Even with ample fuel and width, the outer runner cannot be substituted
for the full nested validator. -/
theorem run_recoveryEnvelopeProgram_ne_fullValidatorOutput
    (limits : RecoveryWitnessLimits)
    (inputLength maximumBits : ℕ)
    (hbits :
      recoveryEnvelopeBits malformedNestedRecoveryCode ≤ maximumBits) :
    runNPOracleProgram recoveryEnvelopeProgram maximumBits
        recoveryEnvelopeFuel
        (initialNPOracleState inputLength malformedNestedRecoveryCode) ≠
      some
        (recoveryWitnessValidatorOutput limits
          malformedNestedRecoveryCode) := by
  rw [run_recoveryEnvelopeProgram
    malformedNestedRecoveryCode inputLength maximumBits hbits]
  intro hequal
  exact recoveryEnvelope_is_not_fullRecoveryValidator limits
    (Option.some.inj hequal)

def recoveryEnvelopeMeasure (raw : ℕ) : ℕ :=
  natBitLength raw

private theorem recoveryEnvelopeFuel_le_budget (raw : ℕ) :
    recoveryEnvelopeFuel ≤
      polynomialBudget 128 1 (recoveryEnvelopeMeasure raw) := by
  unfold recoveryEnvelopeFuel polynomialBudget recoveryEnvelopeMeasure
  simp only [pow_one]
  omega

private theorem recoveryEnvelopeBits_le_budget (raw : ℕ) :
    recoveryEnvelopeBits raw ≤
      polynomialBudget 128 1 (recoveryEnvelopeMeasure raw) := by
  have hlinear := recoveryEnvelopeBits_le_linear raw
  unfold polynomialBudget recoveryEnvelopeMeasure
  simp only [pow_one]
  omega

/-- Polynomial execution witness for the raw three-field recovery envelope.
The full nested validator links this fixed front end to the component checks;
it does not receive a decoded envelope or an acceptance side channel. -/
private def recoveryEnvelopeValidatorWitness :
    PolynomialNatProgramWitness ℕ natBitLength id
      recoveryEnvelopeMeasure recoveryEnvelopeOutput where
  runner :=
    { program := recoveryEnvelopeProgram
      coefficient := 128
      coefficientPositive := by omega
      degree := 1
      initialBitsFit := by
        intro raw
        apply (natBitLength_mono ?_).trans
          (recoveryEnvelopeBits_le_budget raw)
        unfold recoveryEnvelopeRegisterBound
        apply max_le
        · calc
            natBitLength raw ≤ raw + 1 := natBitLength_le_succ raw
            _ ≤ raw + 2 := by omega
            _ ≤ max (Nat.pair 2 raw) (raw + 2) := le_max_right _ _
            _ ≤ max (Nat.pair 1 raw)
                (max (Nat.pair 2 raw) (raw + 2)) := le_max_right _ _
        · exact (Nat.right_le_pair 1 raw).trans (le_max_left _ _)
      halts := by
        intro raw
        refine ⟨recoveryEnvelopeOutput raw, ?_⟩
        let budget :=
          polynomialBudget 128 1 (recoveryEnvelopeMeasure raw)
        have hexact :=
          run_recoveryEnvelopeProgram raw (natBitLength raw)
            budget (recoveryEnvelopeBits_le_budget raw)
        have hpadded :=
          run_fuel_add hexact
            (budget - recoveryEnvelopeFuel)
        have htotal :
            recoveryEnvelopeFuel +
                (budget - recoveryEnvelopeFuel) =
              budget :=
          Nat.add_sub_of_le (recoveryEnvelopeFuel_le_budget raw)
        simpa [budget, htotal] using hpadded }
  computes := by
    intro raw
    let budget :=
      polynomialBudget 128 1 (recoveryEnvelopeMeasure raw)
    have hexact :=
      run_recoveryEnvelopeProgram raw (natBitLength raw)
        budget (recoveryEnvelopeBits_le_budget raw)
    have hpadded :=
      run_fuel_add hexact
        (budget - recoveryEnvelopeFuel)
    have htotal :
        recoveryEnvelopeFuel +
            (budget - recoveryEnvelopeFuel) =
          budget :=
      Nat.add_sub_of_le (recoveryEnvelopeFuel_le_budget raw)
    simpa [PolynomialNatProgram.budget, budget, htotal] using hpadded

end NearCubicWires.CanonicalRecoveryProgram

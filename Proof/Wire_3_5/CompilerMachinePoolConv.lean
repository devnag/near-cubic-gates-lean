import Proof.Wire_3_5.CompilerMachinePoolFormat

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WilliamsPublishedForm NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Words -/

/-- The framed cells of a word without the end marker. -/
def fpre (t : List Bool) : List Bool := t.flatMap fun b => [true, b]

theorem fpre_length (t : List Bool) : (fpre t).length = 2 * t.length := by
  induction t with
  | nil => rfl
  | cons b t ih => simp [fpre] at ih ⊢; omega

theorem frame_append' : ∀ t u : List Bool, frame (t ++ u) = fpre t ++ frame u
  | [], _ => rfl
  | b :: t, u => by simp [frame, fpre, frame_append' t u]

theorem fixedWidth_eq_binary : ∀ (w v : ℕ), fixedWidthNatBits w v = binary w v
  | 0, _ => rfl
  | w + 1, v => by
    apply List.ext_getElem
    · simp [fixedWidthNatBits]
    · intro i h1 h2
      simp only [fixedWidthNatBits, List.getElem_ofFn]
      rw [binary_getElem]

/-- The native natural word. -/
theorem natWord_eq (v : ℕ) :
    natWord v = List.replicate (natBitLength v) true ++ false :: binary (natBitLength v) v := by
  simp [natWord, framedNatBits, fixedWidth_eq_binary]

theorem binary_append' : ∀ (a b v : ℕ), binary (a + b) v = binary a v ++ binary b (v / 2 ^ a)
  | 0, b, v => by simp [binary]
  | a + 1, b, v => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [binary, List.cons_append]
    rw [binary_append' a b (v / 2), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (2 ^ a) 2]

theorem binary_zero' : ∀ b : ℕ, binary b 0 = List.replicate b false
  | 0 => rfl
  | b + 1 => by simp [binary, binary_zero' b, List.replicate_succ]

theorem natBitLength_le (v h : ℕ) (h1 : 1 ≤ h) (hv : v < 2 ^ h) : natBitLength v ≤ h := by
  unfold natBitLength
  by_cases h0 : v = 0
  · subst h0; simp; omega
  · have := Nat.log_lt_of_lt_pow h0 hv; omega

theorem lt_pow_natBitLength (v : ℕ) : v < 2 ^ natBitLength v := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by decide) v

/-- The register word of a magnitude of `L` bits inside `h ≥ L` bits. -/
theorem binary_pad (v h : ℕ) (h1 : 1 ≤ h) (hv : v < 2 ^ h) :
    binary h v = binary (natBitLength v) v ++ List.replicate (h - natBitLength v) false := by
  have hL := natBitLength_le v h h1 hv
  have e := binary_append' (natBitLength v) (h - natBitLength v) v
  rw [Nat.add_sub_cancel' hL] at e
  rw [e, Nat.div_eq_of_lt (lt_pow_natBitLength v), binary_zero']

/-! ## The machine -/

/-- State `0` counts the prefix, `1` copies a bit while the counter reads `1`, `2` steps over a marker, `3` halts. -/
def convM : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then ⟨0, fun _ => none, ![.right, .right, .stay]⟩ else ⟨1, fun _ => none, ![.right, .stay, .right]⟩)
    else if q.val = 1 then
      some (if sc 1 then ⟨2, ![none, none, some (sc 0)], ![.right, .left, .right]⟩
        else ⟨3, fun _ => none, fun _ => .stay⟩)
    else if q.val = 2 then some ⟨1, fun _ => none, ![.stay, .stay, .right]⟩
    else none

theorem conv_count (S K M : List Bool) (s k m : ℕ) (hs : readTapeBit S s = true) :
    step convM ⟨0, ![s, k, m], ![S, K, M]⟩ = some ⟨0, ![s + 1, k + 1, m], ![S, K, M]⟩ := by
  simp [step, convM, Configuration.scanned, hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem conv_zero (S K M : List Bool) (s k m : ℕ) (hs : readTapeBit S s = false) :
    step convM ⟨0, ![s, k, m], ![S, K, M]⟩ = some ⟨1, ![s + 1, k, m + 1], ![S, K, M]⟩ := by
  simp [step, convM, Configuration.scanned, hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem conv_bit (S K M : List Bool) (s k m : ℕ) (hk : readTapeBit K (k + 1) = true) :
    step convM ⟨1, ![s, k + 1, m], ![S, K, M]⟩ =
      some ⟨2, ![s + 1, k, m + 1], ![S, K, writeTapeBit M m (readTapeBit S s)]⟩ := by
  simp [step, convM, Configuration.scanned, hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem conv_mark (S K M : List Bool) (s k m : ℕ) :
    step convM ⟨2, ![s, k, m], ![S, K, M]⟩ = some ⟨1, ![s, k, m + 1], ![S, K, M]⟩ := by
  simp [step, convM]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem conv_end (S K M : List Bool) (s m : ℕ) (hk : readTapeBit K 0 = false) :
    step convM ⟨1, ![s, 0, m], ![S, K, M]⟩ = some ⟨3, ![s, 0, m], ![S, K, M]⟩ := by
  simp [step, convM, Configuration.scanned, hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

/-- The prefix count: `j` ones on the source move the source and counter heads `j` cells. -/
theorem conv_prefix (S K M : List Bool) (s0 m : ℕ) :
    ∀ j, (∀ i < j, readTapeBit S (s0 + i) = true) →
      RecoveryExecution.Timed convM j ⟨0, ![s0, 0, m], ![S, K, M]⟩ ⟨0, ![s0 + j, j, m], ![S, K, M]⟩
  | 0, _ => by simpa using RecoveryExecution.Timed.refl (p := convM) ⟨0, ![s0, 0, m], ![S, K, M]⟩
  | j + 1, h => by
    have t1 := conv_prefix S K M s0 m j (fun i hi => h i (by omega))
    have t2 := RecoveryExecution.Timed.single (p := convM) rfl
      (conv_count S K M (s0 + j) j m (h j (by omega)))
    have := t1.trans t2
    simpa [Nat.add_assoc] using this

/-- The register while copying: `j` bits written into a zero frame of width `h`. -/
def regAt (h : ℕ) (bits : List Bool) (j : ℕ) (R : List Bool) : List Bool :=
  frame (bits.take j ++ List.replicate (h - j) false) ++ R

theorem write_frame_bit (t r R : List Bool) (x b : Bool) :
    writeTapeBit (frame (t ++ x :: r) ++ R) (2 * t.length + 1) b = frame (t ++ b :: r) ++ R := by
  rw [frame_append', frame_append']
  simp only [frame, List.cons_append, List.append_assoc]
  have e := StablePartition.Workspace.write_boundary (fpre t ++ [true]) (x :: (frame r ++ R)) b
  have hl : (fpre t ++ [true]).length = 2 * t.length + 1 := by simp [fpre_length]
  rw [hl] at e
  simpa only [List.append_assoc, List.singleton_append, List.drop_one, List.tail_cons] using e

/-- The copy loop: from bit `j`, the remaining `L − j` bits go into the register's bit cells. -/
theorem conv_copy (h : ℕ) (bits S K R : List Bool) (b0 : ℕ) (hL : bits.length ≤ h)
    (hS : ∀ i < bits.length, readTapeBit S (b0 + i) = bits[i]!)
    (hK : ∀ i, 1 ≤ i → i ≤ bits.length → readTapeBit K i = true) :
    ∀ c j, j + c = bits.length →
      RecoveryExecution.Timed convM (2 * c)
        ⟨1, ![b0 + j, c, 2 * j + 1], ![S, K, regAt h bits j R]⟩
        ⟨1, ![b0 + bits.length, 0, 2 * bits.length + 1], ![S, K, regAt h bits bits.length R]⟩
  | 0, j, hj => by
    have : j = bits.length := by omega
    subst this
    simpa using RecoveryExecution.Timed.refl (p := convM) ⟨1, ![b0 + bits.length, 0, 2 * bits.length + 1],
      ![S, K, regAt h bits bits.length R]⟩
  | c + 1, j, hj => by
    have hj' : j < bits.length := by omega
    have hk := hK (c + 1) (by omega) (by omega)
    have s1 := conv_bit S K (regAt h bits j R) (b0 + j) c (2 * j + 1) hk
    have hw : writeTapeBit (regAt h bits j R) (2 * j + 1) (readTapeBit S (b0 + j)) = regAt h bits (j + 1) R := by
      unfold regAt
      have hr : h - j = (h - (j + 1)) + 1 := by omega
      rw [hr, List.replicate_succ, hS j hj']
      have ht : (bits.take j).length = j := by simp; omega
      have e := write_frame_bit (bits.take j) (List.replicate (h - (j + 1)) false) R false bits[j]!
      rw [ht] at e
      rw [e, List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.append_assoc]
      simp [hj']
    rw [hw] at s1
    have t1 := RecoveryExecution.Timed.single (p := convM) rfl s1
    have t2 := RecoveryExecution.Timed.single (p := convM) rfl
      (conv_mark S K (regAt h bits (j + 1) R) (b0 + j + 1) c (2 * j + 1 + 1))
    have t3 := conv_copy h bits S K R b0 hL hS hK c (j + 1) (by omega)
    have := (t1.trans t2).trans t3
    rw [show 1 + 1 + 2 * c = 2 * (c + 1) by omega] at this
    exact this

/-- The cost of one conversion. -/
def convCost (v : ℕ) : ℕ := 3 * natBitLength v + 2

theorem conv_run (h v : ℕ) (h1 : 1 ≤ h) (hv : v < 2 ^ h) (pre post Y : List Bool) (cap : ℕ)
    (hcap : natBitLength v ≤ cap) :
    Step convM (convCost v) ![pre.length, 0, 0]
      ![pre ++ natWord v ++ post, false :: List.replicate cap true, overlay (frame (binary h 0)) Y]
      ![pre.length + (natWord v).length, 0, 2 * natBitLength v + 1]
      ![pre ++ natWord v ++ post, false :: List.replicate cap true, overlay (frame (binary h v)) Y] := by
  set L := natBitLength v
  set bits := binary L v
  set S := pre ++ natWord v ++ post
  set K := false :: List.replicate cap true
  set R := Y.drop (2 * h + 1)
  have hbl : bits.length = L := binary_length L v
  have hLh : L ≤ h := natBitLength_le v h h1 hv
  have hS : S = pre ++ List.replicate L true ++ false :: (bits ++ post) := by
    simp only [S, natWord_eq, List.append_assoc, List.cons_append]; rfl
  have hpre : ∀ i < L, readTapeBit S (pre.length + i) = true := by
    intro i hi
    rw [hS, List.append_assoc, read_suffix, read_prefix _ _ _ (by simpa using hi)]
    simp [readTapeBit, List.getD_eq_getElem?_getD, hi]
  have hzero : readTapeBit S (pre.length + L) = false := by
    rw [hS, List.append_assoc, read_suffix]
    have := read_suffix (List.replicate L true) (false :: (bits ++ post)) 0
    rw [List.length_replicate, Nat.add_zero] at this
    rw [this]; rfl
  have hbits : ∀ i < bits.length, readTapeBit S (pre.length + L + 1 + i) = bits[i]! := by
    intro i hi
    rw [hS]
    have e : pre ++ List.replicate L true ++ false :: (bits ++ post) = (pre ++ List.replicate L true ++ [false]) ++
        bits ++ post := by simp [List.append_assoc]
    rw [e, show pre.length + L + 1 + i = (pre ++ List.replicate L true ++ [false]).length + i by simp; omega,
      read_shift _ _ _ _ hi]
    simp [readTapeBit, List.getD_eq_getElem?_getD, hi]
  have hK : ∀ i, 1 ≤ i → i ≤ bits.length → readTapeBit K i = true := by
    intro i h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp only [K, readTapeBit, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp
  have hK0 : readTapeBit K 0 = false := rfl
  have hM0 : overlay (frame (binary h 0)) Y = regAt h bits 0 R := by
    simp [regAt, overlay, binary_zero', R]
  have hM1 : overlay (frame (binary h v)) Y = regAt h bits bits.length R := by
    have ht : bits.take bits.length = bits := List.take_length
    have hb : binary h v = bits ++ List.replicate (h - bits.length) false := by
      rw [hbl]; exact binary_pad v h h1 hv
    have hfl : (frame (binary h v)).length = 2 * h + 1 := by simp
    unfold regAt overlay
    rw [ht, hfl, ← hb]
  have t1 := conv_prefix S K (regAt h bits 0 R) pre.length 0 L hpre
  have t2 := RecoveryExecution.Timed.single (p := convM) rfl
    (conv_zero S K (regAt h bits 0 R) (pre.length + L) L 0 hzero)
  have t3 := conv_copy h bits S K R (pre.length + L + 1) (by omega) hbits hK L 0 (by omega)
  rw [hbl] at t3
  have t4 := RecoveryExecution.Timed.single (p := convM) rfl
    (conv_end S K (regAt h bits bits.length R) (pre.length + L + 1 + L) (2 * L + 1) hK0)
  rw [hbl] at t4
  have t := ((t1.trans t2).trans t3).trans t4
  rw [show L + 1 + 2 * L + 1 = convCost v by unfold convCost; omega] at t
  obtain ⟨r, hr, hf, hs⟩ := t.run rfl
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · rw [hM0]; exact hr
  · rw [hf]
    funext i; fin_cases i <;> simp [natWord_eq, L]
    omega
  · rw [hf, hM1, hbl]
  · exact hs.le

/-- The conversion with its register head returned to `0` (log on tape 3). -/
noncomputable def convR := MaskedReset.machine convM ![false, false, true]

theorem convR_run (h v : ℕ) (h1 : 1 ≤ h) (hv : v < 2 ^ h) (pre post Y : List Bool) (cap cap' : ℕ)
    (hcap : natBitLength v ≤ cap) (hcap' : convCost v ≤ cap') :
    Step convR (2 * convCost v + 2) ![pre.length, 0, 0, 0]
      ![pre ++ natWord v ++ post, false :: List.replicate cap true, overlay (frame (binary h 0)) Y,
        List.replicate cap' false]
      ![pre.length + (natWord v).length, 0, 0, 0]
      ![pre ++ natWord v ++ post, false :: List.replicate cap true, overlay (frame (binary h v)) Y,
        List.replicate cap' false] := by
  have h0 := conv_run h v h1 hv pre post Y cap hcap
  have hm := h0.mask ![false, false, true] (by intro i hi; fin_cases i <;> simp_all) hcap'
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool

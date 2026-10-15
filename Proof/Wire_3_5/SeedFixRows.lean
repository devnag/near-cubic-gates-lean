import Proof.Wire_3_5.SeedFixRowPass

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

/-! ## The rows of one label (tapes 0 the target word, 1 the table stream, 2 the prefix word, 3 the mask `2^c`, 4 the
register, 5 the bit cell, 6 the accumulator cell, 7 the rows tape, 8 the modulus, 9 the flag cell, 10 the capacity
tape, 11 and 12 the rewind logs) -/

def r13P : Fin 10 → Fin 13 := ![2, 1, 3, 4, 5, 6, 7, 10, 11, 12]

theorem install_r13P (A : Fin 13 → List Bool) (v : Fin 10 → List Bool) :
    RecoveryRootRound.install r13P A v = ![A 0, v 1, v 0, v 2, v 3, v 4, v 5, v 6, A 8, A 9, v 7, v 8, v 9] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 9
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_r13P (H : Fin 13 → ℕ) (v : Fin 10 → ℕ) :
    dockH r13P H v = ![H 0, v 1, v 0, v 2, v 3, v 4, v 5, v 6, H 8, H 9, v 7, v 8, v 9] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_slot _ (by decide) _ _ 7
    | exact dockH_slot _ (by decide) _ _ 8
    | exact dockH_slot _ (by decide) _ _ 9
    | exact dockH_other _ _ _ _ (by decide)

def r13Rhs : Fin 3 → Fin 13 := ![0, 6, 7]

theorem install_r13Rhs (A : Fin 13 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install r13Rhs A v = ![v 0, A 1, A 2, A 3, A 4, A 5, v 1, v 2, A 8, A 9, A 10, A 11, A 12] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_r13Rhs (H : Fin 13 → ℕ) (v : Fin 3 → ℕ) :
    dockH r13Rhs H v = ![v 0, H 1, H 2, H 3, H 4, H 5, v 1, v 2, H 8, H 9, H 10, H 11, H 12] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def r13Lfsr : Fin 4 → Fin 13 := ![3, 8, 9, 10]

theorem install_r13Lfsr (A : Fin 13 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install r13Lfsr A v = ![A 0, A 1, A 2, v 0, A 4, A 5, A 6, A 7, v 1, v 2, v 3, A 11, A 12] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_r13Lfsr (H : Fin 13 → ℕ) (v : Fin 4 → ℕ) :
    dockH r13Lfsr H v = ![H 0, H 1, H 2, v 0, H 4, H 5, H 6, H 7, v 1, v 2, v 3, H 11, H 12] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def r13Clr : Fin 3 → Fin 13 := ![6, 5, 9]

theorem install_r13Clr (A : Fin 13 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install r13Clr A v = ![A 0, A 1, A 2, A 3, A 4, v 1, v 0, A 7, A 8, v 2, A 10, A 11, A 12] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_r13Clr (H : Fin 13 → ℕ) (v : Fin 3 → ℕ) :
    dockH r13Clr H v = ![H 0, H 1, H 2, H 3, H 4, v 1, v 0, H 7, H 8, v 2, H 10, H 11, H 12] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)
def selTab : Fin 9 → Bool := ![false, true, false, false, false, false, false, false, false]

noncomputable def rowBody :=
  Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine r13P (MaskedReset.machine passesM selTab)) (RecoveryFocus.machine r13Rhs AppendRhs.machine))
    (RecoveryFocus.machine r13Lfsr lfsrM)) (RecoveryFocus.machine r13Clr (CellOp.machine fun _ _ _ => false))

/-- **The rows machine**: one pass per bit of the target word. -/
noncomputable def rowsM := StreamController.machine rowBody 0

theorem lfsr_two_pow (p ℓ c : ℕ) (hc : c + 1 < ℓ) : lfsr p ℓ (2 ^ c) = 2 ^ (c + 1) := by
  unfold lfsr
  have : (2 * 2 ^ c).testBit ℓ = false := by
    rw [← pow_succ', Nat.testBit_two_pow]; simp; omega
  rw [if_neg (by simp [this]), pow_succ']

theorem lfsr_iterate_one (p ℓ : ℕ) : ∀ c, c < ℓ → (lfsr p ℓ)^[c] 1 = 2 ^ c
  | 0, _ => rfl
  | c + 1, hc => by
    rw [Function.iterate_succ_apply', lfsr_iterate_one p ℓ c (by omega), lfsr_two_pow p ℓ c hc]

/-- One row's framed record: the mask pairs, then the right-hand side pair, then the end marker. -/
def rowFrame (tab : List ℕ) (plen pfx v c : ℕ) : List Bool :=
  maskBits tab plen c (tab.length - plen) ++ [true, xor (v.testBit c) (fixAcc tab pfx c plen), false]

def rowsOut (tab : List ℕ) (plen pfx v c : ℕ) : List Bool := (List.range c).flatMap fun c' => rowFrame tab plen pfx v c'

theorem rowsOut_succ (tab : List ℕ) (plen pfx v c : ℕ) :
    rowsOut tab plen pfx v (c + 1) = rowsOut tab plen pfx v c ++ rowFrame tab plen pfx v c := by
  unfold rowsOut
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem rowFrame_length (tab : List ℕ) (plen pfx v c : ℕ) :
    (rowFrame tab plen pfx v c).length = 2 * (tab.length - plen) + 3 := by
  simp [rowFrame, maskBits_length]

theorem rowsOut_length (tab : List ℕ) (plen pfx v : ℕ) :
    ∀ c, (rowsOut tab plen pfx v c).length = c * (2 * (tab.length - plen) + 3)
  | 0 => by simp [rowsOut]
  | c + 1 => by rw [rowsOut_succ, List.length_append, rowsOut_length tab plen pfx v c, rowFrame_length]; ring

/-- The register and bit cell after `c` rows. -/
def recRow (ℓ : ℕ) (tab : List ℕ) (plen : ℕ) (r0 : List Bool) : ℕ → List Bool
  | 0 => r0
  | c + 1 => regB ℓ tab plen (regAt ℓ tab (recRow ℓ tab plen r0 c) plen) (tab.length - plen)

def bitRow (tab : List ℕ) (plen : ℕ) (b0 : Bool) : ℕ → Bool
  | 0 => b0
  | c + 1 => bitB tab c plen (bitAt tab c (bitRow tab plen b0 c) plen) (tab.length - plen)

theorem recRow_length (ℓ : ℕ) (tab : List ℕ) (plen : ℕ) (r0 : List Bool) (hr0 : r0.length ≤ 2 * ℓ + 1) :
    ∀ c, (recRow ℓ tab plen r0 c).length ≤ 2 * ℓ + 1
  | 0 => hr0
  | c + 1 => regB_length ℓ tab plen _ (regAt_length ℓ tab _ (recRow_length ℓ tab plen r0 hr0 c) plen) _

def rowsH (tab : List ℕ) (plen n0 c : ℕ) : Fin 13 → ℕ :=
  ![2 * c, 0, 0, 0, 0, 0, 0, n0 + c * (2 * (tab.length - plen) + 3), 0, 0, 0, 0, 0]

def rowsA (p ℓ k v plen pfx cap cap2 cap3 : ℕ) (tab : List ℕ) (tail r0 : List Bool) (b0 : Bool)
    (out backing : List Bool) (c : ℕ) : Fin 13 → List Bool :=
  ![frame (binary k v), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary plen pfx),
    frame (binary ℓ ((lfsr p ℓ)^[c] 1)), recRow ℓ tab plen r0 c, [bitRow tab plen b0 c], [false],
    overlay (out ++ rowsOut tab plen pfx v c) backing, frame (binary ℓ p), [false], List.replicate cap false,
    List.replicate cap2 false, List.replicate cap3 false]

def rowCost (ℓ plen n : ℕ) : ℕ := 2 * passesCost ℓ plen n + 2 + 1 + 4 + 1 + lfsrCost ℓ + 1 + 1

theorem rows_step (p ℓ k v plen pfx cap cap2 cap3 : ℕ) (tab : List ℕ) (tail r0 : List Bool) (b0 : Bool)
    (out backing : List Bool) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ) (hr0 : r0.length ≤ 2 * ℓ + 1) (hcap : 2 * ℓ + 2 ≤ cap)
    (hcap2 : plen * (phACost ℓ + 2) + 1 ≤ cap2) (hcap3 : passesCost ℓ plen tab.length ≤ cap3)
    (hplen : plen ≤ tab.length) (c : ℕ) (hc : c < k) :
    Step rowBody (rowCost ℓ plen tab.length) (rowsH tab plen out.length c)
      (rowsA p ℓ k v plen pfx cap cap2 cap3 tab tail r0 b0 out backing c)
      (rowsH tab plen out.length (c + 1)) (rowsA p ℓ k v plen pfx cap cap2 cap3 tab tail r0 b0 out backing (c + 1)) := by
  have hcl : c < ℓ := by omega
  set R := 2 * (tab.length - plen) + 3 with hR
  set O := out ++ rowsOut tab plen pfx v c with hO
  have hOl : O.length = out.length + c * R := by rw [hO, List.length_append, rowsOut_length]
  set W := tab.map (binary ℓ) with hW
  set S := streamOf W ++ tail with hS
  set PR := frame (binary plen pfx)
  set rc := recRow ℓ tab plen r0 c
  set bc := bitRow tab plen b0 c
  set fx := fixAcc tab pfx c plen
  set rest := tab.length - plen
  set MB := maskBits tab plen c rest
  have hMBl : MB.length = 2 * rest := maskBits_length tab plen c rest
  have hOMB : (O ++ MB).length = O.length + 2 * rest := by simp only [List.length_append, hMBl]
  set r' := regB ℓ tab plen (regAt ℓ tab rc plen) rest
  set b' := bitB tab c plen (bitAt tab c bc plen) rest
  -- 1: the passes, the table rewound
  have hP := passes_run ℓ plen pfx c cap cap2 tab tail rc bc O backing hℓ hcl
    (recRow_length ℓ tab plen r0 hr0 c) (by omega) hcap2 hplen
  have hPm := hP.mask (cap := cap3) selTab (by intro i hi; fin_cases i <;> first | rfl | simp [selTab] at hi) hcap3
  have hPm' : Step (MaskedReset.machine passesM selTab) (2 * passesCost ℓ plen tab.length + 2)
      ![0, 0, 0, 0, 0, 0, O.length, 0, 0, 0]
      ![PR, S, frame (binary ℓ (2 ^ c)), rc, [bc], [false], overlay O backing, List.replicate cap false,
        List.replicate cap2 false, List.replicate cap3 false]
      ![0, 0, 0, 0, 0, 0, O.length + 2 * rest, 0, 0, 0]
      ![PR, S, frame (binary ℓ (2 ^ c)), r', [b'], [fx], overlay (O ++ MB) backing, List.replicate cap false,
        List.replicate cap2 false, List.replicate cap3 false] := by
    refine (hPm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have eMC : (lfsr p ℓ)^[c] 1 = 2 ^ c := lfsr_iterate_one p ℓ c hcl
  have s1 := dockRun hPm' r13P (by decide) (rowsH tab plen out.length c)
    ![frame (binary k v), S, PR, frame (binary ℓ (2 ^ c)), rc, [bc], [false], overlay O backing, frame (binary ℓ p),
      [false], List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false]
    (by intro i; fin_cases i <;> first | rfl | exact hOl.symm) (by intro i; fin_cases i <;> rfl)
  rw [dockH_r13P, install_r13P] at s1
  -- 2: the right-hand side and the frame end
  have hr := AppendRhs.run (frame (binary k v)) (2 * c) fx (O ++ MB) backing
  have hvb : readTapeBit (frame (binary k v)) (2 * c + 1) = v.testBit c := by
    rw [read_frame_bit _ c (by simpa using hc), binary_getElem]
  rw [hvb] at hr
  have s2 := dockRun hr r13Rhs (by decide) ![2 * c, 0, 0, 0, 0, 0, 0, O.length + 2 * rest, 0, 0, 0, 0, 0]
    ![frame (binary k v), S, PR, frame (binary ℓ (2 ^ c)), r', [b'], [fx], overlay (O ++ MB) backing,
      frame (binary ℓ p), [false], List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false]
    (by
      intro i; fin_cases i
      · rfl
      · rfl
      · exact hOMB.symm)
    (by intro i; fin_cases i <;> rfl)
  rw [dockH_r13Rhs, install_r13Rhs, hOMB] at s2
  -- 3: the next mask
  have hl := lfsr_run p ℓ (2 ^ c) hℓ false cap hcap
  have hl' : Step lfsrM (lfsrCost ℓ) (fun _ => 0)
      ![frame (binary ℓ (2 ^ c)), frame (binary ℓ p), [false], List.replicate cap false] (fun _ => 0)
      ![frame (binary ℓ (lfsr p ℓ (2 ^ c))), frame (binary ℓ p), [false], List.replicate cap false] :=
    (hl.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  set T3 := overlay ((O ++ MB) ++ [true, xor (v.testBit c) fx, false]) backing
  have s3 := dockKeep hl' r13Lfsr (by decide) ![2 * c + 2, 0, 0, 0, 0, 0, 0, O.length + 2 * rest + 3, 0, 0, 0, 0, 0]
    ![frame (binary k v), S, PR, frame (binary ℓ (2 ^ c)), r', [b'], [fx], T3, frame (binary ℓ p), [false],
      List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [install_r13Lfsr] at s3
  -- 4: the accumulator cleared
  have hk0 := CellOp.run (fun _ _ _ => false) fx b' false
  have hk1 : Step (CellOp.machine fun _ _ _ => false) 1 (fun _ => 0) ![[fx], [b'], [false]] (fun _ => 0)
      ![[false], [b'], [false]] :=
    (hk0.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  have s4 := dockKeep hk1 r13Clr (by decide) ![2 * c + 2, 0, 0, 0, 0, 0, 0, O.length + 2 * rest + 3, 0, 0, 0, 0, 0]
    ![frame (binary k v), S, PR, frame (binary ℓ (lfsr p ℓ (2 ^ c))), r', [b'], [fx], T3, frame (binary ℓ p), [false],
      List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [install_r13Clr] at s4
  have s1' := s1.congr (hout' := ![2 * c, 0, 0, 0, 0, 0, 0, O.length + 2 * rest, 0, 0, 0, 0, 0])
    (tout' := ![frame (binary k v), S, PR, frame (binary ℓ (2 ^ c)), r', [b'], [fx], overlay (O ++ MB) backing,
      frame (binary ℓ p), [false], List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false])
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have s2' := s2.congr (hout' := ![2 * c + 2, 0, 0, 0, 0, 0, 0, O.length + 2 * rest + 3, 0, 0, 0, 0, 0])
    (tout' := ![frame (binary k v), S, PR, frame (binary ℓ (2 ^ c)), r', [b'], [fx], T3,
      frame (binary ℓ p), [false], List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false])
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have s3' := s3.congr (hout' := ![2 * c + 2, 0, 0, 0, 0, 0, 0, O.length + 2 * rest + 3, 0, 0, 0, 0, 0])
    (tout' := ![frame (binary k v), S, PR, frame (binary ℓ (lfsr p ℓ (2 ^ c))), r', [b'], [fx], T3,
      frame (binary ℓ p), [false], List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false])
    rfl (by funext i; fin_cases i <;> rfl)
  have hall := ((s1'.seq s2').seq s3').seq s4
  have e7 : out.length + (c + 1) * (2 * (tab.length - plen) + 3) = O.length + 2 * rest + 3 := by
    rw [hOl]; ring
  have eMC1 : (lfsr p ℓ)^[c + 1] 1 = lfsr p ℓ (2 ^ c) := by rw [Function.iterate_succ_apply', eMC]
  have eO1 : out ++ rowsOut tab plen pfx v (c + 1) = (O ++ MB) ++ [true, xor (v.testBit c) fx, false] := by
    rw [rowsOut_succ, rowFrame, hO]
    simp only [List.append_assoc]
    rfl
  unfold rowsH rowsA
  rw [e7, eMC1, eMC, eO1]
  exact hall

/-- **The rows of one constraint as one `Step`**: `k` rows appended to the rows tape. -/
theorem rows_run (p ℓ k v plen pfx cap cap2 cap3 : ℕ) (tab : List ℕ) (tail r0 : List Bool) (b0 : Bool)
    (out backing : List Bool) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ) (hr0 : r0.length ≤ 2 * ℓ + 1) (hcap : 2 * ℓ + 2 ≤ cap)
    (hcap2 : plen * (phACost ℓ + 2) + 1 ≤ cap2) (hcap3 : passesCost ℓ plen tab.length ≤ cap3)
    (hplen : plen ≤ tab.length) :
    Step rowsM (k * (rowCost ℓ plen tab.length + 2) + 1) (rowsH tab plen out.length 0)
      (rowsA p ℓ k v plen pfx cap cap2 cap3 tab tail r0 b0 out backing 0)
      (rowsH tab plen out.length k) (rowsA p ℓ k v plen pfx cap cap2 cap3 tab tail r0 b0 out backing k) := by
  let W : WhileBody 13 _ :=
    { body := rowBody
      tape := 0
      bound := k
      H := rowsH tab plen out.length
      A := rowsA p ℓ k v plen pfx cap cap2 cap3 tab tail r0 b0 out backing
      cost := fun _ => rowCost ℓ plen tab.length
      step := fun c hc => rows_step p ℓ k v plen pfx cap cap2 cap3 tab tail r0 b0 out backing hℓ hkl hr0 hcap hcap2
        hcap3 hplen c hc
      cont := fun c hc => by
        show readTapeBit (frame (binary k v)) (2 * c) = true
        exact read_frame_mark _ c (by simpa using hc)
      halt := by
        show readTapeBit (frame (binary k v)) (2 * k) = false
        have := read_frame_end (binary k v)
        rwa [binary_length] at this }
  have h := W.run
  rw [W.rest_const (rowCost ℓ plen tab.length) (fun _ => rfl)] at h
  exact h

/-! ## The rows are the elimination system's records -/

theorem frame_append_single (l : List Bool) (r : Bool) :
    frame (l ++ [r]) = l.flatMap (fun b => [true, b]) ++ [true, r, false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [frame, ih]

/-- A row's framed record is the framed `Gauss.rowBits` of `rowOf`. -/
theorem rowFrame_eq (tab : List ℕ) (plen pfx v c : ℕ) :
    rowFrame tab plen pfx v c =
      frame (Gauss.rowBits (tab.length - plen) (rowOf tab (tab.length - plen) plen pfx c (v.testBit c))) := by
  rw [rowBits_rowOf, frame_append_single]
  unfold rowFrame maskBits rhsOf fixAcc
  rw [List.flatMap_map]

/-- **The rows machine writes the records of the elimination system of `(λ, v)`** (`JoinElimination.system`). -/
theorem rowsOut_system (p ℓ twoH k plen pfx lam v : ℕ) (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ)
    (hplen : plen ≤ twoH * ℓ) (hlam : lam < 2 ^ ℓ) :
    rowsOut (colTable p ℓ twoH lam) plen pfx v k =
      ((JoinElimination.system p ℓ twoH k plen pfx [(lam, v)]).map (Gauss.rowBits (twoH * ℓ - plen))).flatMap frame := by
  rw [system_eq_rowOf p ℓ twoH k plen pfx [(lam, v)] hp hℓ hplen (by simpa using hlam)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
  unfold rowsOut
  rw [List.flatMap_map]
  refine List.flatMap_congr fun c _ => ?_
  rw [rowFrame_eq, colTable_length]
  rfl

end NearCubicWires.WireExponent3_5.SeedFix

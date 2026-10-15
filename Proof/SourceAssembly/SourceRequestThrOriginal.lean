import Proof.SourceAssembly.SourceRequestThrOriginalForward
import Proof.SourceAssembly.SourceRequestThrKinds

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics
noncomputable section

namespace NearCubicWires.SourceRequest.ThrOriginal
open PacketProduction
attribute [local irreducible] CloseoutRowsSupportStream.Threshold.machine CloseoutRowsSupportStream.Threshold.program

/-! ## The writer and its two framed chains -/

/-- The original THR writer from zero heads: one move puts head 1674 at 1 (the writer's start heads). -/
def writer := Composition.machine (CompetitorCountTable.moveMachine (1674 : Fin 1704))
  CloseoutRowsSupportStream.Threshold.machine

theorem writer_native_forward : CursorRestore.NoLeft writer (1688 : Fin 1704) :=
  CursorRestore.composition_forward _ _ _ (ThrOriginalForward.move_forward _ _)
    ThrOriginalForward.native_forward

theorem writer_support_forward : CursorRestore.NoLeft writer (1703 : Fin 1704) :=
  CursorRestore.composition_forward _ _ _ (ThrOriginalForward.move_forward _ _)
    ThrOriginalForward.support_forward

/-- The retained-bottom support stream of `c` (the writer's tape 1703). -/
def stream {q : Nat} (c : NormalizedThresholdThresholdCircuit q) : List Bool :=
  CloseoutRowsSupportStream.supportWord (List.ofFn (fun i => c.bottom (retainedTopIndex c i)))

/-- The writer's input words (`Threshold.input P q W L bits [] []`). -/
abbrev input (P q W L : Nat) (bits : List Bool) : Fin 1704 → List Bool :=
  CloseoutRowsSupportStream.Threshold.input P q W L bits [] []

theorem heads_native (n s : List Bool) :
    CloseoutRowsSupportStream.Threshold.heads n s (1688 : Fin 1704) = n.length := by
  change Fin.addCases (m := 1703) (n := 1) (motive := fun _ => Nat)
    (CloseoutRowsCircuitColdEntry.heads n) (fun _ => s.length) (Fin.castAdd 1 (1688 : Fin 1703)) = _
  rw [Fin.addCases_left]
  simp [CloseoutRowsCircuitColdEntry.heads]

theorem heads_support (n s : List Bool) :
    CloseoutRowsSupportStream.Threshold.heads n s (1703 : Fin 1704) = s.length := by
  change Fin.addCases (m := 1703) (n := 1) (motive := fun _ => Nat)
    (CloseoutRowsCircuitColdEntry.heads n) (fun _ => s.length) (Fin.natAdd 1703 (0 : Fin 1)) = _
  rw [Fin.addCases_right]

/-- One move of `target`, then `M`, at a SYMBOLIC machine `M` (so no concrete rule table is ever unfolded). -/
theorem move_then {t s : Nat} (target : Fin t) (M : Machine t s) (fuel : Nat) (a : Fin t → List Bool)
    (f : ExecutionReceipt t s)
    (hf : runFrom M fuel ⟨M.start, fun i => if i = target then 1 else 0, a⟩ = some f) :
    ∃ r : ExecutionReceipt t (2 + s),
      run (Composition.machine (CompetitorCountTable.moveMachine target) M) (1 + 1 + fuel) a = some r ∧
      r.steps = 1 + 1 + f.steps ∧ r.final.heads = f.final.heads ∧ r.final.tapes = f.final.tapes := by
  obtain ⟨m, hm, mh, mt, ms⟩ := CompetitorCountTable.move_run target (fun _ => 0) a
  have hre : Composition.restart m.final M.start = ⟨M.start, fun i => if i = target then 1 else 0, a⟩ := by
    apply configuration_ext
    · rfl
    · change m.final.heads = _
      rw [mh]
    · change m.final.tapes = _
      rw [mt]
  have hj := Composition.run_join _ _ 1 _ _ m f hm (by rw [hre]; exact hf)
  refine ⟨Composition.joinedReceipt m f, hj, ?_, rfl, rfl⟩
  change m.steps + 1 + f.steps = _
  rw [ms]

theorem start_heads :
    CloseoutRowsSupportStream.Threshold.heads [] [] = fun i : Fin 1704 => if i = 1674 then 1 else 0 := by
  funext i
  rw [SourceAssemblyCircuitNative.empty_heads]
  by_cases h : i = 1674
  · rw [if_pos h, if_pos (show i.val = 1674 from congrArg Fin.val h)]
  · rw [if_neg h, if_neg (show ¬ i.val = 1674 from fun e => h (Fin.ext e))]

/-- **The writer's raw run** (no rewind): the bare native word and the support stream, each with its
head at its length. -/
theorem writer_run {q : Nat} (c : NormalizedThresholdThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedThresholdThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ source : ExecutionReceipt 1704 (2 + CloseoutRowsSupportStream.Threshold.program.1),
      run writer (1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length)
        (input P q W L bits) = some source ∧
      source.steps ≤ 1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length ∧
      source.final.tapes 1688 = thrWord c ∧ source.final.heads 1688 = (thrWord c).length ∧
      source.final.tapes 1703 = stream c ∧ source.final.heads 1703 = (stream c).length := by
  obtain ⟨typed, native⟩ := CloseoutRowsCircuitMeaning.threshold_typed c W L bits hd
  have hp := typed.mpr ⟨hW, hL⟩
  obtain ⟨f, hf, hfs, _fh, _flag, _rh, _raw, _dh, _drv, good⟩ :=
    CloseoutRowsSupportStream.Threshold.cold_run P q W L bits [] [] hcap
  obtain ⟨heads, word, _arity, _driver, _W, _L, _raw', support, _bound⟩ := good hp
  rw [start_heads] at hf
  obtain ⟨r, hr, rs, rh, rt⟩ := move_then (1674 : Fin 1704) CloseoutRowsSupportStream.Threshold.machine _ _ f hf
  have hsup := CloseoutRowsSupportStream.Threshold.support_typed c bits hd
  refine ⟨r, hr, by omega, ?_, ?_, ?_, ?_⟩
  · rw [rt, word, List.nil_append, native]
    rfl
  · rw [rh, heads, heads_native, List.nil_append, native]
    rfl
  · rw [rt, support, List.nil_append, hsup]
    rfl
  · rw [rh, heads, heads_support, List.nil_append, hsup]
    rfl

/-- The writer's fuel bound. -/
def wFuel (P q : Nat) (bits : List Bool) : Nat :=
  1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length

def chainA := AppendOutputFrame.machine writer (1688 : Fin 1704)
def chainD := AppendOutputFrame.machine writer (1703 : Fin 1704)

/-- **Chain A**: `frame (thrWord c)` on 1706 and the bare `thrWord c` kept on 1688; every head `0`. -/
theorem chainA_run {q : Nat} (c : NormalizedThresholdThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedThresholdThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ A, Step chainA (2 * wFuel P q bits + 4 * (thrWord c).length + 7) (fun _ => 0)
        (AppendOutputFrame.input (input P q W L bits)) (fun _ => 0) A ∧
      A 1706 = frame (thrWord c) ∧ A 1688 = thrWord c := by
  obtain ⟨source, hr, hs, t88, h88, -, -⟩ := writer_run c P W L bits hcap hd hW hL
  obtain ⟨s, sr, st, sh, sk, ss⟩ := PCPPNativeFrame.frame_run writer 1688 writer_native_forward
    _ _ source hr (thrWord c) t88 h88
  refine ⟨s.final.tapes, (Step.of_run sr (funext sh) rfl).enlarge (by unfold wFuel; omega), st, ?_⟩
  exact (sk 1688).trans t88

/-- **Chain D**: `frame (stream c)` on 1706; every head `0`. -/
theorem chainD_run {q : Nat} (c : NormalizedThresholdThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedThresholdThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ A, Step chainD (2 * wFuel P q bits + 4 * (stream c).length + 7) (fun _ => 0)
        (AppendOutputFrame.input (input P q W L bits)) (fun _ => 0) A ∧
      A 1706 = frame (stream c) := by
  obtain ⟨source, hr, hs, -, -, t03, h03⟩ := writer_run c P W L bits hcap hd hW hL
  obtain ⟨s, sr, st, sh, sk, ss⟩ := PCPPNativeFrame.frame_run writer 1703 writer_support_forward
    _ _ source hr (stream c) t03 h03
  exact ⟨s.final.tapes, (Step.of_run sr (funext sh) rfl).enlarge (by unfold wFuel; omega), st⟩

/-! ## The writer's entry bank, tape by tape -/

/-- The writer's input word at tape number `n` (`CloseoutRowsCircuit.input` with empty streams). -/
def thrAt (P q W L : Nat) (bits : List Bool) (n : Nat) : List Bool :=
  if n = 1 then frame bits else if n = 1674 then UnaryTemplate.tape q else
    if n = 1694 then List.replicate P true else
      if n = 1698 then List.replicate W true else if n = 1699 then List.replicate L true else []

theorem thrAt_nil (P q W L : Nat) (bits : List Bool) (n : Nat) (h1 : n ≠ 1) (h2 : n ≠ 1674)
    (h3 : n ≠ 1694) (h4 : n ≠ 1698) (h5 : n ≠ 1699) : thrAt P q W L bits n = [] := by
  unfold thrAt
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

theorem thrAt_high (P q W L : Nat) (bits : List Bool) (n : Nat) (h : 1700 ≤ n) :
    thrAt P q W L bits n = [] :=
  thrAt_nil P q W L bits n (by omega) (by omega) (by omega) (by omega) (by omega)

theorem stepAt {m n : Nat} (g : Nat → List Bool) (hg : ∀ k, m ≤ k → g k = []) (f : Fin m → List Bool)
    (hf : ∀ j : Fin m, f j = g j.val) (i : Fin (m + n)) :
    Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin n => []) i = g i.val := by
  rw [Gen.ChainIn.addCases_nil]
  by_cases h : i.val < m
  · rw [dif_pos h, hf]
  · rw [dif_neg h, hg _ (by omega)]

theorem cold_at (P q W L : Nat) (bits : List Bool) (j : Fin 1703) :
    CloseoutRowsCircuitColdEntry.input P q W L bits [] j = thrAt P q W L bits j.val := by
  unfold CloseoutRowsCircuitColdEntry.input
  by_cases h : j = 1688
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    rfl

theorem input_at0 (P q W L : Nat) (bits : List Bool) (j : Fin 1704) :
    input P q W L bits j = thrAt P q W L bits j.val :=
  stepAt (n := 1) _ (fun k hk => thrAt_high P q W L bits k (by omega)) _ (cold_at P q W L bits) j

/-- **The chains' entry**, tape by tape. -/
theorem input_at (P q W L : Nat) (bits : List Bool) (i : Fin 1708) :
    AppendOutputFrame.input (input P q W L bits) i = thrAt P q W L bits i.val := by
  have hg : ∀ m, 1700 ≤ m → ∀ k, m ≤ k → thrAt P q W L bits k = [] :=
    fun m hm k hk => thrAt_high P q W L bits k (by omega)
  have l1 : ∀ j : Fin 1705, AppendOutputLength.input (input P q W L bits) j = thrAt P q W L bits j.val :=
    stepAt (n := 1) _ (hg 1704 (by omega)) _ (input_at0 P q W L bits)
  have l2 : ∀ j : Fin 1706, AppendOutputLength.input (AppendOutputLength.input (input P q W L bits)) j
      = thrAt P q W L bits j.val :=
    stepAt (n := 1) _ (hg 1705 (by omega)) _ l1
  exact stepAt (n := 2) _ (hg 1706 (by omega)) _ l2 i

/-! ## The five-stage layout in `Fin (3425 + Tn a)` -/

open ThrSystematic (oT oT_val away fo_input zeroH)

/-- TopNative's tape count (`ThrSystematic.T`). -/
abbrev Tn (a : DecompositionAlgorithm) : Nat := ThrSystematic.T a
theorem Tn_eq (a : DecompositionAlgorithm) : Tn a = 4 + ((DecompositionSource.Counted.tapes a + 2) + 2) :=
  ThrSystematic.T_eq a

def bVal (i : Nat) : Nat := if i = 0 then 1706 else 1707 + i
def cVal (i : Nat) : Nat := if i = 0 then 1688 else 1712 + i
def eVal (a : DecompositionAlgorithm) (i : Nat) : Nat :=
  if i = 0 then 1712 + (DecompositionSource.Counted.tapes a + 6) else 1711 + Tn a + i
def dVal (a : DecompositionAlgorithm) (i : Nat) : Nat := 1717 + Tn a + i
/-- The writer's five input positions. -/
def posVal (j : Nat) : Nat :=
  if j = 0 then 1 else if j = 1 then 1674 else if j = 2 then 1694 else if j = 3 then 1698 else 1699
def descVal (a : DecompositionAlgorithm) (k : Nat) : Nat :=
  if k < 5 then posVal k else 1717 + Tn a + posVal (k - 5)

theorem posVal_range (j : Nat) : 1 ≤ posVal j ∧ posVal j ≤ 1699 := by
  unfold posVal; split_ifs <;> omega

def slotA (a : DecompositionAlgorithm) (i : Fin 1708) : Fin (3425 + Tn a) := ⟨i.val, by omega⟩
def slotB (a : DecompositionAlgorithm) (i : Fin 6) : Fin (3425 + Tn a) :=
  ⟨bVal i.val, by have := i.isLt; unfold bVal; split_ifs <;> omega⟩
def slotC (a : DecompositionAlgorithm) (i : Fin (Tn a)) : Fin (3425 + Tn a) :=
  ⟨cVal i.val, by have := i.isLt; unfold cVal; split_ifs <;> omega⟩
def slotE (a : DecompositionAlgorithm) (i : Fin 6) : Fin (3425 + Tn a) :=
  ⟨eVal a i.val, by have := i.isLt; have := Tn_eq a; unfold eVal; split_ifs <;> omega⟩
def slotD (a : DecompositionAlgorithm) (i : Fin 1708) : Fin (3425 + Tn a) :=
  ⟨dVal a i.val, by have := i.isLt; unfold dVal; omega⟩
def descSlots (a : DecompositionAlgorithm) (k : Fin 10) : Fin (3425 + Tn a) :=
  ⟨descVal a k.val, by
    have := k.isLt; have := posVal_range k.val; have := posVal_range (k.val - 5)
    unfold descVal; split_ifs <;> omega⟩

theorem slotA_inj (a : DecompositionAlgorithm) : Function.Injective (slotA a) := by
  intro i j h
  have hv : (slotA a i).val = (slotA a j).val := congrArg Fin.val h
  exact Fin.ext hv
theorem slotB_inj (a : DecompositionAlgorithm) : Function.Injective (slotB a) := by
  intro i j h
  have hv : bVal i.val = bVal j.val := congrArg Fin.val h
  apply Fin.ext
  unfold bVal at hv
  split_ifs at hv <;> omega
theorem slotC_inj (a : DecompositionAlgorithm) : Function.Injective (slotC a) := by
  intro i j h
  have hv : cVal i.val = cVal j.val := congrArg Fin.val h
  apply Fin.ext
  unfold cVal at hv
  split_ifs at hv <;> omega
theorem slotE_inj (a : DecompositionAlgorithm) : Function.Injective (slotE a) := by
  intro i j h
  have hv : eVal a i.val = eVal a j.val := congrArg Fin.val h
  have := Tn_eq a
  apply Fin.ext
  unfold eVal at hv
  split_ifs at hv <;> omega
theorem slotD_inj (a : DecompositionAlgorithm) : Function.Injective (slotD a) := by
  intro i j h
  have hv : dVal a i.val = dVal a j.val := congrArg Fin.val h
  apply Fin.ext
  unfold dVal at hv
  omega
theorem posVal_inj (i j : Nat) (hi : i < 5) (hj : j < 5) (h : posVal i = posVal j) : i = j := by
  unfold posVal at h
  split_ifs at h <;> omega
theorem descSlots_inj (a : DecompositionAlgorithm) : Function.Injective (descSlots a) := by
  intro i j h
  have hv : descVal a i.val = descVal a j.val := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  have r1 := posVal_range i.val
  have r2 := posVal_range j.val
  have r3 := posVal_range (i.val - 5)
  have r4 := posVal_range (j.val - 5)
  apply Fin.ext
  unfold descVal at hv
  split_ifs at hv with h1 h2 h2
  · exact posVal_inj _ _ h1 h2 hv
  · omega
  · omega
  · have := posVal_inj (i.val - 5) (j.val - 5) (by omega) (by omega) (by omega)
    omega

/-- The ten descriptor words: the writer's five input words, once per chain. -/
def desc (P q W L : Nat) (bits : List Bool) (k : Fin 10) : List Bool :=
  thrAt P q W L bits (posVal (if k.val < 5 then k.val else k.val - 5))

def entryVal (a : DecompositionAlgorithm) (P q W L : Nat) (bits : List Bool) (x : Nat) : List Bool :=
  if x < 1708 then thrAt P q W L bits x
  else if 1717 + Tn a ≤ x then thrAt P q W L bits (x - (1717 + Tn a)) else []

def st0 (a : DecompositionAlgorithm) (P q W L : Nat) (bits : List Bool) : Fin (3425 + Tn a) → List Bool :=
  fun x => entryVal a P q W L bits x.val

theorem thrAt_off (P q W L : Nat) (bits : List Bool) (n : Nat) (h : ∀ j, j < 5 → n ≠ posVal j) :
    thrAt P q W L bits n = [] :=
  thrAt_nil P q W L bits n (h 0 (by omega)) (h 1 (by omega)) (h 2 (by omega)) (h 3 (by omega))
    (h 4 (by omega))

theorem entry_eq (a : DecompositionAlgorithm) (P q W L : Nat) (bits : List Bool) :
    install (descSlots a) (fun _ => []) (desc P q W L bits) = st0 a P q W L bits := by
  funext x
  by_cases hx : ∃ k, descSlots a k = x
  · obtain ⟨k, rfl⟩ := hx
    rw [install_slot _ (descSlots_inj a)]
    have hk := k.isLt
    show desc P q W L bits k = entryVal a P q W L bits (descVal a k.val)
    unfold desc entryVal descVal
    by_cases h5 : k.val < 5
    · have r := posVal_range k.val
      rw [if_pos h5, if_pos h5, if_pos (by omega)]
    · have r := posVal_range (k.val - 5)
      rw [if_neg h5, if_neg h5, if_neg (by omega), if_pos (by omega),
        show 1717 + Tn a + posVal (k.val - 5) - (1717 + Tn a) = posVal (k.val - 5) by omega]
  · rw [install_other _ _ _ _ (fun k e => hx ⟨k, e⟩)]
    show [] = entryVal a P q W L bits x.val
    have hlow : ∀ j, j < 5 → x.val ≠ posVal j := fun j hj e =>
      hx ⟨⟨j, by omega⟩, Fin.ext (by
        show descVal a j = x.val
        unfold descVal
        rw [if_pos hj, e])⟩
    have hhigh : ∀ j, j < 5 → x.val - (1717 + Tn a) ≠ posVal j ∨ x.val < 1717 + Tn a := fun j hj => by
      by_cases hle : 1717 + Tn a ≤ x.val
      · refine Or.inl (fun e => hx ⟨⟨j + 5, by omega⟩, Fin.ext ?_⟩)
        show descVal a (j + 5) = x.val
        unfold descVal
        rw [if_neg (by omega), show j + 5 - 5 = j by omega, ← e]
        omega
      · exact Or.inr (by omega)
    unfold entryVal
    split_ifs with h1 h2
    · exact (thrAt_off P q W L bits _ hlow).symm
    · refine (thrAt_off P q W L bits _ (fun j hj => ?_)).symm
      rcases hhigh j hj with h | h
      · exact h
      · omega
    · rfl

/-! ### Stage entries -/

theorem A_entry (a : DecompositionAlgorithm) (P q W L : Nat) (bits : List Bool) (j : Fin 1708) :
    st0 a P q W L bits (slotA a j) = AppendOutputFrame.input (input P q W L bits) j := by
  rw [input_at]
  show entryVal a P q W L bits j.val = _
  unfold entryVal
  rw [if_pos j.isLt]

theorem B_entry (a : DecompositionAlgorithm) (P q W L : Nat) (bits : List Bool) (A1 : Fin 1708 → List Bool)
    (w : List Bool) (h1706 : A1 1706 = w) (j : Fin 6) :
    install (slotA a) (st0 a P q W L bits) A1 (slotB a j)
      = AppendOutputFrame.input (![w, []] : Fin 2 → List Bool) j := by
  rw [fo_input]
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show slotB a j = slotA a 1706 from Fin.ext (by
      show bVal j.val = 1706; unfold bVal; rw [if_pos h0]),
      install_slot _ (slotA_inj a), h1706]
  · have hj := j.isLt
    rw [if_neg h0, install_other _ _ _ _ (away _ _ (fun k => by
      have := k.isLt; show k.val ≠ bVal j.val; unfold bVal; rw [if_neg h0]; omega))]
    show entryVal a P q W L bits (bVal j.val) = []
    unfold bVal entryVal
    rw [if_neg h0, if_neg (by omega), if_neg (by omega)]

theorem C_entry (a : DecompositionAlgorithm) (P q W L : Nat) (bits : List Bool) (A1 : Fin 1708 → List Bool)
    (B1 : Fin 6 → List Bool) (w : List Bool) (h1688 : A1 1688 = w) (j : Fin (Tn a)) :
    install (slotB a) (install (slotA a) (st0 a P q W L bits) A1) B1 (slotC a j)
      = if j.val = 0 then w else [] := by
  have hj := j.isLt
  have hT := Tn_eq a
  rw [install_other _ _ _ _ (away _ _ (fun k => by
    have := k.isLt; show bVal k.val ≠ cVal j.val; unfold bVal cVal; split_ifs <;> omega))]
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show slotC a j = slotA a 1688 from Fin.ext (by
      show cVal j.val = 1688; unfold cVal; rw [if_pos h0]),
      install_slot _ (slotA_inj a), h1688]
  · rw [if_neg h0, install_other _ _ _ _ (away _ _ (fun k => by
      have := k.isLt; show k.val ≠ cVal j.val; unfold cVal; rw [if_neg h0]; omega))]
    show entryVal a P q W L bits (cVal j.val) = []
    unfold cVal entryVal
    rw [if_neg h0, if_neg (by omega), if_neg (by omega)]

theorem E_entry (a : DecompositionAlgorithm) (P q W L : Nat) (bits : List Bool) (A1 : Fin 1708 → List Bool)
    (B1 : Fin 6 → List Bool) (C1 : Fin (Tn a) → List Bool) (w : List Bool) (hC : C1 (oT a) = w) (j : Fin 6) :
    install (slotC a) (install (slotB a) (install (slotA a) (st0 a P q W L bits) A1) B1) C1 (slotE a j)
      = AppendOutputFrame.input (![w, []] : Fin 2 → List Bool) j := by
  have hj := j.isLt
  have hT := Tn_eq a
  have ho := oT_val a
  rw [fo_input]
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show slotE a j = slotC a (oT a) from Fin.ext (by
      show eVal a j.val = cVal (oT a).val; unfold eVal cVal; rw [if_pos h0, if_neg (by omega)]; omega),
      install_slot _ (slotC_inj a), hC]
  · rw [if_neg h0,
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show cVal k.val ≠ eVal a j.val; unfold cVal eVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show bVal k.val ≠ eVal a j.val; unfold bVal eVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show k.val ≠ eVal a j.val; unfold eVal; rw [if_neg h0]; omega))]
    show entryVal a P q W L bits (eVal a j.val) = []
    unfold eVal entryVal
    rw [if_neg h0, if_neg (by omega), if_neg (by omega)]

theorem D_entry (a : DecompositionAlgorithm) (P q W L : Nat) (bits : List Bool) (A1 : Fin 1708 → List Bool)
    (B1 : Fin 6 → List Bool) (C1 : Fin (Tn a) → List Bool) (E1 : Fin 6 → List Bool) (j : Fin 1708) :
    install (slotE a) (install (slotC a) (install (slotB a) (install (slotA a) (st0 a P q W L bits) A1) B1) C1) E1
      (slotD a j) = AppendOutputFrame.input (input P q W L bits) j := by
  have hj := j.isLt
  have hT := Tn_eq a
  rw [install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show eVal a k.val ≠ dVal a j.val; unfold eVal dVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show cVal k.val ≠ dVal a j.val; unfold cVal dVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show bVal k.val ≠ dVal a j.val; unfold bVal dVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show k.val ≠ dVal a j.val; unfold dVal; omega)),
      input_at]
  show entryVal a P q W L bits (dVal a j.val) = _
  unfold dVal entryVal
  rw [if_neg (by omega), if_pos (by omega), show 1717 + Tn a + j.val - (1717 + Tn a) = j.val by omega]

/-! ### The machine and its run -/

def outN (a : DecompositionAlgorithm) : Fin (3425 + Tn a) := slotB a 4
def outT (a : DecompositionAlgorithm) : Fin (3425 + Tn a) := slotE a 4
def outS (a : DecompositionAlgorithm) : Fin (3425 + Tn a) := slotD a 1706

def machine (a : DecompositionAlgorithm) :=
  Composition.machine (RecoveryFocus.machine (slotA a) chainA)
    (Composition.machine (RecoveryFocus.machine (slotB a) SourceAssemblyFrameOuter.machine)
      (Composition.machine (RecoveryFocus.machine (slotC a) (SourceAssemblyTopNative.machine a))
        (Composition.machine (RecoveryFocus.machine (slotE a) SourceAssemblyFrameOuter.machine)
          (RecoveryFocus.machine (slotD a) chainD))))

/-- The five stages' cost: the writer twice (source polynomial), the TOP budget, linear framing. -/
def cost (a : DecompositionAlgorithm) {q : Nat} (c : NormalizedThresholdThresholdCircuit q) (P : Nat)
    (bits : List Bool) : Nat :=
  (2 * wFuel P q bits + 4 * (thrWord c).length + 7) + 1 +
    ((12 * (thrWord c).length + 13) + 1 +
      (SourceAssemblyTopNative.budget a c.top.wireCount
          ⟨c.top.support.card, nonStrictAsStrict (SupplierPipeline.retainedTopGate c)⟩ + 1 +
        ((12 * (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c)).length + 13) + 1 +
          (2 * wFuel P q bits + 4 * (stream c).length + 7))))

theorem exact_run (a : DecompositionAlgorithm) {q : Nat} (c : NormalizedThresholdThresholdCircuit q)
    (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedThresholdThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ F, Step (machine a) (cost a c P bits) (fun _ => 0) (st0 a P q W L bits) (fun _ => 0) F ∧
      F (outN a) = frame (frame (thrWord c)) ∧
      F (outS a) = frame (stream c) ∧
      F (outT a) = frame (frame (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))) := by
  obtain ⟨A1, sA, a1706, a1688⟩ := chainA_run c P W L bits hcap hd hW hL
  obtain ⟨B1, sB, b4⟩ := SourceAssemblyFrameOuter.run (thrWord c)
  obtain ⟨C1, sC, cOut, -⟩ := SourceAssemblyTopNative.threshold_run a c
  obtain ⟨E1, sE, e4⟩ := SourceAssemblyFrameOuter.run
    (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))
  obtain ⟨D1, sD, d1706⟩ := chainD_run c P W L bits hcap hd hW hL
  have dA := sA.dock (slotA a) (slotA_inj a) (fun _ => 0) (st0 a P q W L bits) (fun _ => rfl)
    (A_entry a P q W L bits)
  rw [zeroH] at dA
  have dB := sB.dock (slotB a) (slotB_inj a) (fun _ => 0) (install (slotA a) (st0 a P q W L bits) A1)
    (fun _ => rfl) (B_entry a P q W L bits A1 _ a1706)
  rw [zeroH] at dB
  have dC := sC.dock (slotC a) (slotC_inj a) (fun _ => 0)
    (install (slotB a) (install (slotA a) (st0 a P q W L bits) A1) B1) (fun _ => rfl)
    (C_entry a P q W L bits A1 B1 _ a1688)
  rw [zeroH] at dC
  have dE := sE.dock (slotE a) (slotE_inj a) (fun _ => 0)
    (install (slotC a) (install (slotB a) (install (slotA a) (st0 a P q W L bits) A1) B1) C1) (fun _ => rfl)
    (E_entry a P q W L bits A1 B1 C1 _ cOut)
  rw [zeroH] at dE
  have dD := sD.dock (slotD a) (slotD_inj a) (fun _ => 0)
    (install (slotE a) (install (slotC a) (install (slotB a) (install (slotA a) (st0 a P q W L bits) A1) B1) C1) E1)
    (fun _ => rfl) (D_entry a P q W L bits A1 B1 C1 E1)
  rw [zeroH] at dD
  have hT := Tn_eq a
  have ho := oT_val a
  refine ⟨_, dA.seq (dB.seq (dC.seq (dE.seq dD))), ?_, ?_, ?_⟩
  · rw [outN,
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show dVal a k.val ≠ 1711; unfold dVal; omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show eVal a k.val ≠ bVal 4; unfold eVal bVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show cVal k.val ≠ bVal 4; unfold cVal bVal; split_ifs <;> omega)),
      install_slot _ (slotB_inj a), b4]
  · rw [outS, install_slot _ (slotD_inj a), d1706]
  · rw [outT,
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show dVal a k.val ≠ 1711 + Tn a + 4; unfold dVal; omega)),
      install_slot _ (slotE_inj a), e4]

section normal
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- The support segment of an original THR factor is the writer's retained-bottom stream. -/
theorem supSeg_threshold (c : NormalizedThresholdThresholdCircuit q) :
    supSeg false (C10TotalDecode.Atom.threshold c : C10TotalDecode.Atom pcpp) = stream c := rfl

theorem produce (a : DecompositionAlgorithm) (c : NormalizedThresholdThresholdCircuit q)
    (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedThresholdThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) (R : Nat) :
    ∃ F, Step (machine a) (cost a c P bits) (fun _ => 0)
      (install (descSlots a) (fun _ => List.replicate R false)
        (fun k => ZeroPadding.pad R (desc P q W L bits k)))
      (fun _ => 0) F ∧
      F (outN a) = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segN false (some (C10TotalDecode.Atom.threshold c : C10TotalDecode.Atom pcpp)))) ∧
      F (outS a) = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segS false (some (C10TotalDecode.Atom.threshold c : C10TotalDecode.Atom pcpp)))) ∧
      F (outT a) = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segT a false (some (C10TotalDecode.Atom.threshold c : C10TotalDecode.Atom pcpp)))) := by
  obtain ⟨F, hF, hN, hS, hT⟩ := exact_run a c P W L bits hcap hd hW hL
  have hnil : (fun _ : Fin (3425 + Tn a) => ZeroPadding.pad R ([] : List Bool))
      = fun _ => List.replicate R false := by
    funext i
    simp [ZeroPadding.pad]
  refine ⟨_, (hF.pad (fun _ => R)).congr_in rfl ?_, ?_, ?_, ?_⟩
  · rw [← entry_eq]
    refine (SourceAssemblyReuse.pad_install (descSlots a) (fun _ => R) (fun _ => [])
      (desc P q W L bits)).trans ?_
    show install (descSlots a) (fun _ => ZeroPadding.pad R []) _ = _
    rw [hnil]
  · show ZeroPadding.pad R (F (outN a)) = _
    rw [hN]
    rfl
  · show ZeroPadding.pad R (F (outS a)) = _
    rw [hS]
    rfl
  · show ZeroPadding.pad R (F (outT a)) = _
    rw [hT]
    rfl

end normal
end NearCubicWires.SourceRequest.ThrOriginal


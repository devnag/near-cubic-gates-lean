import Proof.SourceAssembly.SourceRequestSymOriginalForward
import Proof.SourceAssembly.SourceRequestThrSwitch

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics
noncomputable section

namespace NearCubicWires.SourceRequest.SymOriginal
open PacketProduction
open ThrOriginal (thrAt input input_at move_then start_heads heads_native heads_support)
attribute [local irreducible] CloseoutRowsSupportStream.Symmetric.machine CloseoutRowsSupportStream.Symmetric.program

/-! ## The code -/

theorem witness_code {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) :
    symmetricCircuitCodec.encode c = encodeNormalizedSymmetricThresholdCircuit c := by
  simp only [symmetricCircuitCodec]

def symCodeWidth (L : Nat) : Nat := RecoveryWitnessPolicy.canonicalSymmetricCircuitCodeBitBound L

def symCodeBits (L : Nat) {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) : List Bool :=
  SignedSortKey.binary (symCodeWidth L) (encodeNormalizedSymmetricThresholdCircuit c)

theorem symCodeBits_length (L : Nat) {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) :
    (symCodeBits L c).length = symCodeWidth L :=
  SignedSortKey.binary_length _ _

theorem symCodeBits_decode (L : Nat) {q : Nat} (c : NormalizedSymmetricThresholdCircuit q)
    (h4 : 4 ≤ L) (hL : c.descriptionBits ≤ L) :
    decodeNormalizedSymmetricThresholdCircuit q (value (symCodeBits L c)) = some c := by
  have hb := RecoveryWitnessPolicy.encodeNormalizedSymmetricCircuit_bits_le_parameter c h4 hL
  have hlt : encodeNormalizedSymmetricThresholdCircuit c < 2 ^ symCodeWidth L :=
    lt_of_lt_of_le (ThrSwitch.code_lt _) (Nat.pow_le_pow_right (by omega) hb)
  unfold symCodeBits
  rw [SignedSortKey.binary_value _ _ hlt]
  exact decodeNormalizedSymmetricThresholdCircuit_encode c

/-! ## The writer and its two framed chains -/

def writer := Composition.machine (CompetitorCountTable.moveMachine (1674 : Fin 1704))
  CloseoutRowsSupportStream.Symmetric.machine

theorem writer_native_forward : CursorRestore.NoLeft writer (1688 : Fin 1704) :=
  CursorRestore.composition_forward _ _ _ (ThrOriginalForward.move_forward _ _)
    SymOriginalForward.native_forward

theorem writer_support_forward : CursorRestore.NoLeft writer (1703 : Fin 1704) :=
  CursorRestore.composition_forward _ _ _ (ThrOriginalForward.move_forward _ _)
    SymOriginalForward.support_forward

/-- The bottom support stream of `c` (the writer's tape 1703). -/
def stream {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) : List Bool :=
  CloseoutRowsSupportStream.supportWord (List.ofFn c.bottom)

theorem sym_input (P q W L : Nat) (bits : List Bool) :
    CloseoutRowsSupportStream.Symmetric.input P q W L bits [] [] = input P q W L bits := rfl
theorem sym_heads (n s : List Bool) :
    CloseoutRowsSupportStream.Symmetric.heads n s = CloseoutRowsSupportStream.Threshold.heads n s := rfl

theorem writer_run {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedSymmetricThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ source : ExecutionReceipt 1704 (2 + CloseoutRowsSupportStream.Symmetric.program.1),
      run writer (1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length)
        (input P q W L bits) = some source ∧
      source.steps ≤ 1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length ∧
      source.final.tapes 1688 = symWord c ∧ source.final.heads 1688 = (symWord c).length ∧
      source.final.tapes 1703 = stream c ∧ source.final.heads 1703 = (stream c).length := by
  obtain ⟨typed, native⟩ := CloseoutRowsCircuitMeaning.symmetric_typed c W L bits hd
  have hp := typed.mpr ⟨hW, hL⟩
  obtain ⟨f, hf, hfs, _fh, _flag, _rh, _raw, _dh, _drv, good⟩ :=
    CloseoutRowsSupportStream.Symmetric.cold_run P q W L bits [] [] hcap
  obtain ⟨heads, word, _arity, _driver, _W, _L, _raw', support, _bound⟩ := good hp
  rw [sym_heads, start_heads, sym_input] at hf
  obtain ⟨r, hr, rs, rh, rt⟩ := move_then (1674 : Fin 1704) CloseoutRowsSupportStream.Symmetric.machine _ _ f hf
  have hsup := CloseoutRowsSupportStream.Symmetric.support_typed c bits hd
  refine ⟨r, hr, by omega, ?_, ?_, ?_, ?_⟩
  · rw [rt, word, List.nil_append, native]
    rfl
  · rw [rh, heads, sym_heads, heads_native, List.nil_append, native]
    rfl
  · rw [rt, support, List.nil_append, hsup]
    rfl
  · rw [rh, heads, sym_heads, heads_support, List.nil_append, hsup]
    rfl

def chainA := AppendOutputFrame.machine writer (1688 : Fin 1704)
def chainD := AppendOutputFrame.machine writer (1703 : Fin 1704)

theorem chainA_run {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedSymmetricThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ A, Step chainA (2 * ThrOriginal.wFuel P q bits + 4 * (symWord c).length + 7) (fun _ => 0)
        (AppendOutputFrame.input (input P q W L bits)) (fun _ => 0) A ∧
      A 1706 = frame (symWord c) := by
  obtain ⟨source, hr, hs, t88, h88, -, -⟩ := writer_run c P W L bits hcap hd hW hL
  obtain ⟨s, sr, st, sh, sk, ss⟩ := PCPPNativeFrame.frame_run writer 1688 writer_native_forward
    _ _ source hr (symWord c) t88 h88
  exact ⟨s.final.tapes, (Step.of_run sr (funext sh) rfl).enlarge (by unfold ThrOriginal.wFuel; omega), st⟩

theorem chainD_run {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedSymmetricThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ A, Step chainD (2 * ThrOriginal.wFuel P q bits + 4 * (stream c).length + 7) (fun _ => 0)
        (AppendOutputFrame.input (input P q W L bits)) (fun _ => 0) A ∧
      A 1706 = frame (stream c) := by
  obtain ⟨source, hr, hs, -, -, t03, h03⟩ := writer_run c P W L bits hcap hd hW hL
  obtain ⟨s, sr, st, sh, sk, ss⟩ := PCPPNativeFrame.frame_run writer 1703 writer_support_forward
    _ _ source hr (stream c) t03 h03
  exact ⟨s.final.tapes, (Step.of_run sr (funext sh) rfl).enlarge (by unfold ThrOriginal.wFuel; omega), st⟩

/-! ## The three-stage layout in `Fin 3422` -/

def bVal (i : Nat) : Nat := if i = 0 then 1706 else 1707 + i
def dVal (i : Nat) : Nat := 1713 + i
def descVal (k : Nat) : Nat :=
  if k < 5 then ThrOriginal.posVal k else 1713 + ThrOriginal.posVal (k - 5)

def slotA (i : Fin 1708) : Fin 3422 := ⟨i.val, by omega⟩
def slotB (i : Fin 6) : Fin 3422 := ⟨bVal i.val, by have := i.isLt; unfold bVal; split_ifs <;> omega⟩
def slotD (i : Fin 1708) : Fin 3422 := ⟨dVal i.val, by have := i.isLt; unfold dVal; omega⟩
def descSlots (k : Fin 10) : Fin 3422 :=
  ⟨descVal k.val, by
    have := k.isLt; have := ThrOriginal.posVal_range k.val; have := ThrOriginal.posVal_range (k.val - 5)
    unfold descVal; split_ifs <;> omega⟩

theorem slotA_inj : Function.Injective slotA := by
  intro i j h
  have hv : (slotA i).val = (slotA j).val := congrArg Fin.val h
  exact Fin.ext hv
theorem slotB_inj : Function.Injective slotB := by
  intro i j h
  have hv : bVal i.val = bVal j.val := congrArg Fin.val h
  apply Fin.ext
  unfold bVal at hv
  split_ifs at hv <;> omega
theorem slotD_inj : Function.Injective slotD := by
  intro i j h
  have hv : dVal i.val = dVal j.val := congrArg Fin.val h
  apply Fin.ext
  unfold dVal at hv
  omega
theorem descSlots_inj : Function.Injective descSlots := by
  intro i j h
  have hv : descVal i.val = descVal j.val := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  have r1 := ThrOriginal.posVal_range i.val
  have r2 := ThrOriginal.posVal_range j.val
  have r3 := ThrOriginal.posVal_range (i.val - 5)
  have r4 := ThrOriginal.posVal_range (j.val - 5)
  apply Fin.ext
  unfold descVal at hv
  split_ifs at hv with h1 h2 h2
  · exact ThrOriginal.posVal_inj _ _ h1 h2 hv
  · omega
  · omega
  · have := ThrOriginal.posVal_inj (i.val - 5) (j.val - 5) (by omega) (by omega) (by omega)
    omega

def desc (P q W L : Nat) (bits : List Bool) (k : Fin 10) : List Bool :=
  thrAt P q W L bits (ThrOriginal.posVal (if k.val < 5 then k.val else k.val - 5))

def entryVal (P q W L : Nat) (bits : List Bool) (x : Nat) : List Bool :=
  if x < 1708 then thrAt P q W L bits x
  else if 1713 ≤ x then thrAt P q W L bits (x - 1713) else []

def st0 (P q W L : Nat) (bits : List Bool) : Fin 3422 → List Bool := fun x => entryVal P q W L bits x.val

theorem entry_eq (P q W L : Nat) (bits : List Bool) :
    install descSlots (fun _ => []) (desc P q W L bits) = st0 P q W L bits := by
  funext x
  by_cases hx : ∃ k, descSlots k = x
  · obtain ⟨k, rfl⟩ := hx
    rw [install_slot _ descSlots_inj]
    have hk := k.isLt
    show desc P q W L bits k = entryVal P q W L bits (descVal k.val)
    unfold desc entryVal descVal
    by_cases h5 : k.val < 5
    · have r := ThrOriginal.posVal_range k.val
      rw [if_pos h5, if_pos h5, if_pos (by omega)]
    · have r := ThrOriginal.posVal_range (k.val - 5)
      rw [if_neg h5, if_neg h5, if_neg (by omega), if_pos (by omega),
        show 1713 + ThrOriginal.posVal (k.val - 5) - 1713 = ThrOriginal.posVal (k.val - 5) by omega]
  · rw [install_other _ _ _ _ (fun k e => hx ⟨k, e⟩)]
    show [] = entryVal P q W L bits x.val
    have hlow : ∀ j, j < 5 → x.val ≠ ThrOriginal.posVal j := fun j hj e =>
      hx ⟨⟨j, by omega⟩, Fin.ext (by
        show descVal j = x.val
        unfold descVal
        rw [if_pos hj, e])⟩
    have hhigh : ∀ j, j < 5 → x.val - 1713 ≠ ThrOriginal.posVal j ∨ x.val < 1713 := fun j hj => by
      by_cases hle : 1713 ≤ x.val
      · refine Or.inl (fun e => hx ⟨⟨j + 5, by omega⟩, Fin.ext ?_⟩)
        show descVal (j + 5) = x.val
        unfold descVal
        rw [if_neg (by omega), show j + 5 - 5 = j by omega, ← e]
        omega
      · exact Or.inr (by omega)
    unfold entryVal
    split_ifs with h1 h2
    · exact (ThrOriginal.thrAt_off P q W L bits _ hlow).symm
    · refine (ThrOriginal.thrAt_off P q W L bits _ (fun j hj => ?_)).symm
      rcases hhigh j hj with h | h
      · exact h
      · omega
    · rfl

theorem A_entry (P q W L : Nat) (bits : List Bool) (j : Fin 1708) :
    st0 P q W L bits (slotA j) = AppendOutputFrame.input (input P q W L bits) j := by
  rw [input_at]
  show entryVal P q W L bits j.val = _
  unfold entryVal
  rw [if_pos j.isLt]

theorem B_entry (P q W L : Nat) (bits : List Bool) (A1 : Fin 1708 → List Bool)
    (w : List Bool) (h1706 : A1 1706 = w) (j : Fin 6) :
    install slotA (st0 P q W L bits) A1 (slotB j)
      = AppendOutputFrame.input (![w, []] : Fin 2 → List Bool) j := by
  rw [ThrSystematic.fo_input]
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show slotB j = slotA 1706 from Fin.ext (by
      show bVal j.val = 1706; unfold bVal; rw [if_pos h0]),
      install_slot _ slotA_inj, h1706]
  · have hj := j.isLt
    rw [if_neg h0, install_other _ _ _ _ (ThrSystematic.away _ _ (fun k => by
      have := k.isLt; show k.val ≠ bVal j.val; unfold bVal; rw [if_neg h0]; omega))]
    show entryVal P q W L bits (bVal j.val) = []
    unfold bVal entryVal
    rw [if_neg h0, if_neg (by omega), if_neg (by omega)]

theorem D_entry (P q W L : Nat) (bits : List Bool) (A1 : Fin 1708 → List Bool)
    (B1 : Fin 6 → List Bool) (j : Fin 1708) :
    install slotB (install slotA (st0 P q W L bits) A1) B1 (slotD j)
      = AppendOutputFrame.input (input P q W L bits) j := by
  have hj := j.isLt
  rw [install_other _ _ _ _ (ThrSystematic.away _ _ (fun k => by
        have := k.isLt; show bVal k.val ≠ dVal j.val; unfold bVal dVal; split_ifs <;> omega)),
      install_other _ _ _ _ (ThrSystematic.away _ _ (fun k => by
        have := k.isLt; show k.val ≠ dVal j.val; unfold dVal; omega)),
      input_at]
  show entryVal P q W L bits (dVal j.val) = _
  unfold dVal entryVal
  rw [if_neg (by omega), if_pos (by omega), show 1713 + j.val - 1713 = j.val by omega]

def outN : Fin 3422 := slotB 4
def outS : Fin 3422 := slotD 1706
def outT : Fin 3422 := ⟨3421, by omega⟩

def machine :=
  Composition.machine (RecoveryFocus.machine slotA chainA)
    (Composition.machine (RecoveryFocus.machine slotB SourceAssemblyFrameOuter.machine)
      (RecoveryFocus.machine slotD chainD))

def cost {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) (P : Nat) (bits : List Bool) : Nat :=
  (2 * ThrOriginal.wFuel P q bits + 4 * (symWord c).length + 7) + 1 +
    ((12 * (symWord c).length + 13) + 1 + (2 * ThrOriginal.wFuel P q bits + 4 * (stream c).length + 7))

/-- **The SYM original factor, exact.** -/
theorem exact_run {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedSymmetricThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ F, Step machine (cost c P bits) (fun _ => 0) (st0 P q W L bits) (fun _ => 0) F ∧
      F outN = frame (frame (symWord c)) ∧ F outS = frame (stream c) ∧ F outT = st0 P q W L bits outT := by
  obtain ⟨A1, sA, a1706⟩ := chainA_run c P W L bits hcap hd hW hL
  obtain ⟨B1, sB, b4⟩ := SourceAssemblyFrameOuter.run (symWord c)
  obtain ⟨D1, sD, d1706⟩ := chainD_run c P W L bits hcap hd hW hL
  have dA := sA.dock slotA slotA_inj (fun _ => 0) (st0 P q W L bits) (fun _ => rfl) (A_entry P q W L bits)
  rw [ThrSystematic.zeroH] at dA
  have dB := sB.dock slotB slotB_inj (fun _ => 0) (install slotA (st0 P q W L bits) A1)
    (fun _ => rfl) (B_entry P q W L bits A1 _ a1706)
  rw [ThrSystematic.zeroH] at dB
  have dD := sD.dock slotD slotD_inj (fun _ => 0) (install slotB (install slotA (st0 P q W L bits) A1) B1)
    (fun _ => rfl) (D_entry P q W L bits A1 B1)
  rw [ThrSystematic.zeroH] at dD
  refine ⟨_, dA.seq (dB.seq dD), ?_, ?_, ?_⟩
  · rw [outN,
      install_other _ _ _ _ (ThrSystematic.away _ _ (fun k => by
        have := k.isLt; show dVal k.val ≠ 1711; unfold dVal; omega)),
      install_slot _ slotB_inj, b4]
  · rw [outS, install_slot _ slotD_inj, d1706]
  · rw [outT,
      install_other _ _ _ _ (ThrSystematic.away _ _ (fun k => by
        have := k.isLt; show dVal k.val ≠ 3421; unfold dVal; omega)),
      install_other _ _ _ _ (ThrSystematic.away _ _ (fun k => by
        have := k.isLt; show bVal k.val ≠ 3421; unfold bVal; split_ifs <;> omega)),
      install_other _ _ _ _ (ThrSystematic.away _ _ (fun k => by
        have := k.isLt; show k.val ≠ 3421; omega))]

section normal
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

theorem supSeg_symmetric (c : NormalizedSymmetricThresholdCircuit q) :
    supSeg true (C10TotalDecode.Atom.symmetric c : C10TotalDecode.Atom pcpp) = stream c := rfl

theorem st0_outT (P W L : Nat) (bits : List Bool) : st0 P q W L bits outT = [] := by
  show entryVal P q W L bits 3421 = []
  unfold entryVal
  rw [if_neg (by omega), if_pos (by omega)]
  exact ThrOriginal.thrAt_high P q W L bits _ (by omega)

/-- **The SYM original factor producer, in `FactorProducer` normal form** (`R ≥ 1` for the blank TOP output). -/
theorem produce (a : DecompositionAlgorithm) (c : NormalizedSymmetricThresholdCircuit q) (P W L : Nat)
    (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedSymmetricThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) (R : Nat) (hR : 1 ≤ R) :
    ∃ F, Step machine (cost c P bits) (fun _ => 0)
      (install descSlots (fun _ => List.replicate R false) (fun k => ZeroPadding.pad R (desc P q W L bits k)))
      (fun _ => 0) F ∧
      F outN = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segN true (some (C10TotalDecode.Atom.symmetric c : C10TotalDecode.Atom pcpp)))) ∧
      F outS = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segS true (some (C10TotalDecode.Atom.symmetric c : C10TotalDecode.Atom pcpp)))) ∧
      F outT = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segT a true (some (C10TotalDecode.Atom.symmetric c : C10TotalDecode.Atom pcpp)))) := by
  obtain ⟨F, hF, hN, hS, hT⟩ := exact_run c P W L bits hcap hd hW hL
  have hnil : (fun _ : Fin 3422 => ZeroPadding.pad R ([] : List Bool)) = fun _ => List.replicate R false := by
    funext i
    simp [ZeroPadding.pad]
  refine ⟨_, (hF.pad (fun _ => R)).congr_in rfl ?_, ?_, ?_, ?_⟩
  · rw [← entry_eq]
    refine (SourceAssemblyReuse.pad_install descSlots (fun _ => R) (fun _ => [])
      (desc P q W L bits)).trans ?_
    show install descSlots (fun _ => ZeroPadding.pad R []) _ = _
    rw [hnil]
  · show ZeroPadding.pad R (F outN) = _
    rw [hN]
    rfl
  · show ZeroPadding.pad R (F outS) = _
    rw [hS]
    rfl
  · show ZeroPadding.pad R (F outT) = ZeroPadding.pad R (RepairOrdinary.frame [])
    rw [hT, st0_outT, ← ThrSwitch.frame_nil_pad R hR]
    simp [ZeroPadding.pad]

end normal
end NearCubicWires.SourceRequest.SymOriginal


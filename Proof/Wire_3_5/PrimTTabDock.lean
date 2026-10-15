import Proof.Wire_3_5.PrimTTabPrep
import Proof.SourceAssembly.SourceRequestSymOriginal
import Proof.MachineModel.BlockUnaryCalc
import Proof.Circuits.CanonicalWitnessCodec
import Proof.Wire_3_5.Shared.Carrier

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.SupplierPipeline

/-! ## The result cell -/

/-- One write of `[false]` on a blank tape. -/
noncomputable def cellM := (Prog.act (fun _ : Fin 1 => some false) (fun _ => .stay) : Prog 1).compile

theorem cell_step : Step cellM 1 (fun _ => 0) (fun _ => []) (fun _ => 0) (fun _ => [false]) := by
  have hs := Exec.step (Exec.act (⟨fun _ => 0, fun _ => []⟩ : Bank 1) (fun _ : Fin 1 => some false)
    (fun _ => .stay))
  have hH : ((⟨fun _ => 0, fun _ => []⟩ : Bank 1).act (fun _ : Fin 1 => some false) (fun _ => .stay)).H =
      fun _ => 0 := by funext i; simp [Bank.act, HeadMove.apply]
  have hA : ((⟨fun _ => 0, fun _ => []⟩ : Bank 1).act (fun _ : Fin 1 => some false) (fun _ => .stay)).A =
      fun _ => [false] := by funext i; simp [Bank.act, writeTapeBit]
  rw [hH, hA] at hs
  exact hs

/-! ## Word programs as Steps -/

/-- **A word program as a Step**: compiled, then every head returned by base's `Rewind` (one fresh log tape). -/
theorem wm_step {ns nr : ℕ} (cap : ℕ) (P : WM ns nr) (σ τ : WState ns nr) (n : ℕ) (hw : WExec cap P σ τ n)
    (hH : (wenc cap σ).H = fun _ => 0) :
    ∃ out : Fin (ns + 2 + nr + 1) → List Bool,
      Step (Rewind.machine P.toProg.compile) (2 * n + 2) (fun _ => 0) (Fin.addCases (wenc cap σ).A (fun _ => []))
        (fun _ => 0) out ∧ ∀ i, out (Fin.castAdd 1 i) = (wenc cap τ).A i := by
  have hs := (WExec.exec cap hw).step
  rw [hH] at hs
  obtain ⟨r, hr, -, ht, hsteps⟩ := hs
  obtain ⟨r', hr', ht', hh', hs', -⟩ := Rewind.reset_run P.toProg.compile n (wenc cap σ).A r hr
  refine ⟨r'.final.tapes, (Step.of_run hr' (funext hh') rfl).enlarge (by omega), fun i => by rw [ht', ht]⟩

theorem wenc_H_zero {ns nr : ℕ} (cap : ℕ) (σ : WState ns nr) (hs : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) :
    (wenc cap σ).H = fun _ => 0 := by
  funext j; simp only [wenc]; split <;> simp [hs, hv]

/-! ## The SYM decoder chain -/

open PacketProduction in
/-- **Base's SYM decoder chain**: `frame (symWord c)` on tape `1706` and the bare `symWord c` kept on `1688`. -/
theorem symChain_run {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) (P W L : ℕ) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : CanonicalWitnessCodec.decodeNormalizedSymmetricThresholdCircuit q (RadixSemantics.value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ A, Step SourceRequest.SymOriginal.chainA (2 * SourceRequest.ThrOriginal.wFuel P q bits + 4 * (symWord c).length + 7)
        (fun _ => 0) (AppendOutputFrame.input (SourceRequest.ThrOriginal.input P q W L bits)) (fun _ => 0) A ∧
      A 1706 = frame (symWord c) ∧ A 1688 = symWord c := by
  obtain ⟨source, hr, hs, t88, h88, -, -⟩ := SourceRequest.SymOriginal.writer_run c P W L bits hcap hd hW hL
  obtain ⟨s, sr, st, sh, sk, ss⟩ := PCPPNativeFrame.frame_run SourceRequest.SymOriginal.writer 1688
    SourceRequest.SymOriginal.writer_native_forward _ _ source hr (symWord c) t88 h88
  exact ⟨s.final.tapes, (Step.of_run sr (funext sh) rfl).enlarge (by unfold SourceRequest.ThrOriginal.wFuel; omega),
    st, (sk 1688).trans t88⟩

/-! ## The decoder's side conditions -/

theorem natWord_bits_value (code : ℕ) : RadixSemantics.value (binary (natBitLength code) code) = code :=
  SignedSortKey.binary_value _ _ (CompilerMachine.Pool.lt_pow_natBitLength code)

theorem symBits_decode {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) :
    CanonicalWitnessCodec.decodeNormalizedSymmetricThresholdCircuit q
      (RadixSemantics.value (binary (natBitLength (encodeNormalizedSymmetricThresholdCircuit c))
        (encodeNormalizedSymmetricThresholdCircuit c))) = some c := by
  rw [natWord_bits_value]; exact CanonicalWitnessCodec.decodeNormalizedSymmetricThresholdCircuit_encode c

theorem thrBits_decode {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    CanonicalWitnessCodec.decodeNormalizedThresholdThresholdCircuit q
      (RadixSemantics.value (binary (natBitLength (encodeNormalizedThresholdThresholdCircuit c))
        (encodeNormalizedThresholdThresholdCircuit c))) = some c := by
  rw [natWord_bits_value]; exact CanonicalWitnessCodec.decodeNormalizedThresholdThresholdCircuit_encode c

theorem gate_wire_le {q : ℕ} (g : SupportedNormalizedGate q) : g.wireCount + 1 ≤ g.descriptionBits + 1 := by
  unfold SupportedNormalizedGate.wireCount SupportedNormalizedGate.descriptionBits
  have := Finset.card_le_univ g.support
  simp at this; omega

/-- **`W = L` suffices** for a SYM circuit: `wireCount ≤ descriptionBits`. -/
theorem sym_wire_le_desc {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) : c.wireCount ≤ c.descriptionBits := by
  unfold NormalizedSymmetricThresholdCircuit.wireCount NormalizedSymmetricThresholdCircuit.descriptionBits
  have h : ∑ i, ((c.bottom i).wireCount + 1) ≤ ∑ i, ((c.bottom i).descriptionBits + 1) :=
    Finset.sum_le_sum fun i _ => gate_wire_le (c.bottom i)
  have e : ∑ i, ((c.bottom i).descriptionBits + 1) = ∑ i, (c.bottom i).descriptionBits + c.bottomCount := by
    rw [Finset.sum_add_distrib]; simp
  omega

/-- **`W = L` suffices** for a THR circuit: `wireCount ≤ descriptionBits`. -/
theorem thr_wire_le_desc {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) : c.wireCount ≤ c.descriptionBits := by
  unfold NormalizedThresholdThresholdCircuit.wireCount NormalizedThresholdThresholdCircuit.descriptionBits
  have h1 : ∑ i ∈ c.top.support, ((c.bottom i).wireCount + 1) ≤ ∑ i, ((c.bottom i).wireCount + 1) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h2 : ∑ i, ((c.bottom i).wireCount + 1) ≤ ∑ i, ((c.bottom i).descriptionBits + 1) :=
    Finset.sum_le_sum fun i _ => gate_wire_le (c.bottom i)
  have e : ∑ i, ((c.bottom i).descriptionBits + 1) = ∑ i, (c.bottom i).descriptionBits + c.bottomCount := by
    rw [Finset.sum_add_distrib]; simp
  have h3 : c.bottomCount ≤ c.top.descriptionBits := by
    unfold SupportedNormalizedGate.descriptionBits; omega
  omega

/-! ## The native words -/

open PacketProduction in
/-- The SYM native word: the bottom count, the top's table, the framed bottom region of `symGates`. -/
theorem symWord_eq {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) :
    symWord c = natWord c.bottomCount ++ (frame (List.ofFn c.top) ++ tabSeg (Stars.symGates c)) := by
  unfold symWord tabSeg Stars.symGates
  rw [List.append_assoc]
  congr 2
  rw [List.ofFn_eq_map, List.flatMap_map, List.flatMap_map]
  rfl

open PacketProduction in
/-- The THR native word: the top's wire count, the top's word, the framed region of the retained bottoms. -/
theorem thrWord_eq {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    thrWord c = natWord c.top.wireCount ++ (frame (thresholdWord (CompilerSemantics.nonStrictAsStrict
      (retainedTopGate c))) ++ tabSeg ((SupplierEstimator.thresholdCircuitOccurrences c).map (·.gate))) := by
  unfold thrWord tabSeg SupplierEstimator.thresholdCircuitOccurrences
  rw [List.append_assoc]
  congr 2
  rw [List.flatMap_map]
  rfl

end NearCubicWires.WireExponent3_5.PrimT

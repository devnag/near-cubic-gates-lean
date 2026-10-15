import Proof.CaseAnalysis.RowsCircuitSyntax

/-! The complete physical decisions enforce the exact original public
wire/description bounds, and retain the original ordered source requests. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitMeaning
open LocalBitMultitape RadixSemantics CanonicalBinary CanonicalWitnessCodec SupplierPipeline RepairRepresentation
open CloseoutRowsCircuitHeader CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitCanonicalFields CloseoutRowsCircuitSyntax
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def symmetricWord {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core):=
  natWord c.bottomCount++frame (List.ofFn c.top)++
    (List.ofFn c.bottom).flatMap (fun g=>frame (CloseoutRowsCircuitBottom.nativeWord g))
def thresholdWord {core : ℕ} (c : NormalizedThresholdThresholdCircuit core):=
  natWord c.top.wireCount++frame (CloseoutRowsCircuitThresholdRun.top c.top)++
    (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))).flatMap
      (fun g=>frame (CloseoutRowsCircuitBottom.nativeWord g))

theorem symmetric_typed {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core)
    (W L : ℕ) (bits : List Bool)
    (hd : decodeNormalizedSymmetricThresholdCircuit core (value bits)=some c) :
    (CloseoutRowsCircuitSymmetricRun.passed core W L bits ↔ c.wireCount ≤ W ∧ c.descriptionBits ≤ L) ∧
      CloseoutRowsCircuitSymmetricRun.native core bits=symmetricWord c:=by
  obtain ⟨hp,hn,hbottom,ht,hvalid⟩:=symmetric_fields c bits hd
  have bottomValid:=typed_validity c.bottom (words bits) hn hbottom
  have desc:CloseoutRowsCircuitArithmeticDock.amount false
      (descriptions core (words bits) 0 (words bits).length) (words bits).length=c.descriptionBits:=by
    rw [hn]
    exact CloseoutRowsCircuitDescriptionMeaning.symmetric_exact c (words bits) hbottom
  have wire:wires false core 1 [] (words bits) 0 (words bits).length=c.wireCount:=by
    rw [hn,symmetric_wires c (words bits) [] 1 0 hbottom,Nat.zero_add]
  have table:CloseoutRowsCircuitSymmetricRun.top bits=List.ofFn c.top:=
    (CloseoutRowsBooleanVector.checks_of_typed (List.ofFn c.top) (codeWord bits 3) ht).2
  constructor
  · simp only [CloseoutRowsCircuitSymmetricRun.passed,hp,hvalid,bottomValid,desc,wire,true_and]
    exact and_comm
  · unfold CloseoutRowsCircuitSymmetricRun.native symmetricWord
    rw [table,hn,symmetric_output c (words bits) [] 1 hbottom]

theorem threshold_typed {core : ℕ} (c : NormalizedThresholdThresholdCircuit core)
    (W L : ℕ) (bits : List Bool)
    (hd : decodeNormalizedThresholdThresholdCircuit core (value bits)=some c) :
    (CloseoutRowsCircuitThresholdRun.passed core W L bits ↔ c.wireCount ≤ W ∧ c.descriptionBits ≤ L) ∧
      CloseoutRowsCircuitThresholdRun.native core bits=thresholdWord c:=by
  rcases c with ⟨n,bottom,topGate⟩
  obtain ⟨hp,hn,hbottom,ht⟩:=threshold_fields ⟨n,bottom,topGate⟩ bits hd
  change (words bits).length=n at hn
  subst n
  let c : NormalizedThresholdThresholdCircuit core:=⟨(words bits).length,bottom,topGate⟩
  have hg:CloseoutRowsCircuitThresholdRun.decoded bits=some topGate:=by
    unfold CloseoutRowsCircuitThresholdRun.decoded
    rw [ht]
    exact decodeSupportedNormalizedGate_encode topGate
  have bottomValid:=typed_validity bottom (words bits) rfl hbottom
  have desc:CloseoutRowsCircuitArithmeticDock.amount true
      (descriptions core (words bits) (CloseoutRowsCircuitThresholdRun.initial topGate) (words bits).length)
      (words bits).length=c.descriptionBits:=
    (CloseoutRowsCircuitDescriptionMeaning.threshold_exact c (words bits) hbottom).2
  have wire:wires true core 1 (CloseoutRowsCircuitThresholdRun.members topGate) (words bits) 0
      (words bits).length=c.wireCount:=by
    exact (threshold_wires c (words bits) 0 hbottom).trans (Nat.zero_add _)
  constructor
  · rw [CloseoutRowsCircuitThresholdRun.passed_decode core W L bits topGate hg]
    simp only [hp,bottomValid,desc,wire,true_and]
    exact and_comm
  · unfold CloseoutRowsCircuitThresholdRun.native
    rw [hg]
    change natWord c.top.wireCount++frame (CloseoutRowsCircuitThresholdRun.top c.top)++
      (List.range c.bottomCount).flatMap (outputs true core 1
        (frame (CloseoutRowsGateSupport.gateMembers c.top.support)) (words bits))=thresholdWord c
    rw [threshold_output c (words bits) hbottom]
    rfl

theorem symmetric_exact (core W L : ℕ) (bits : List Bool) :
    CloseoutRowsCircuitSymmetricRun.passed core W L bits ↔
      ∃ c,decodeNormalizedSymmetricThresholdCircuit core (value bits)=some c ∧
        c.wireCount ≤ W ∧ c.descriptionBits ≤ L:=by
  constructor
  · intro h
    have hs:=(CloseoutRowsCircuitSyntax.symmetric core bits).mpr ⟨h.1,h.2.1,h.2.2.1⟩
    obtain ⟨c,hc⟩:=Option.isSome_iff_exists.mp hs
    exact ⟨c,hc,(symmetric_typed c W L bits hc).1.mp h⟩
  · rintro ⟨c,hc,limits⟩
    exact (symmetric_typed c W L bits hc).1.mpr limits

theorem threshold_exact (core W L : ℕ) (bits : List Bool) :
    CloseoutRowsCircuitThresholdRun.passed core W L bits ↔
      ∃ c,decodeNormalizedThresholdThresholdCircuit core (value bits)=some c ∧
        c.wireCount ≤ W ∧ c.descriptionBits ≤ L:=by
  constructor
  · intro h
    obtain ⟨g,hg,hbottom,_rest⟩:=h.2
    have hs:=(CloseoutRowsCircuitSyntax.threshold core bits).mpr
      ⟨h.1,Option.isSome_iff_exists.mpr ⟨g,hg⟩,hbottom⟩
    obtain ⟨c,hc⟩:=Option.isSome_iff_exists.mp hs
    exact ⟨c,hc,(threshold_typed c W L bits hc).1.mp h⟩
  · rintro ⟨c,hc,limits⟩
    exact (threshold_typed c W L bits hc).1.mpr limits

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitMeaning

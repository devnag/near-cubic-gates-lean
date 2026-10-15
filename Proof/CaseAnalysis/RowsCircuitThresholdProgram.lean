import Proof.CaseAnalysis.RowsCircuitSymmetricProgram

/-! The full threshold controller keeps the original top support and
uses the common bottom/resource body. Padding never changes membership. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdRun
open LocalBitMultitape RecoveryRootRound RepairRepresentation SupplierPipeline CanonicalWitnessCodec RadixSemantics
open CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def test (b : Fin 1703 → Bool):=b 638 && b 1676
noncomputable def program : Σ s,Machine 1703 s:=
  ⟨_,CloseoutRowsGateColdPair.machine CloseoutRowsCircuitColdThreshold.machine
    (CloseoutRowsCircuitBody.machine true) test⟩
noncomputable def machine : Machine 1703 program.1:=program.2
def decoded (bits : List Bool):=decodeSupportedNormalizedGate (words bits).length
  (value (CloseoutRowsCircuitHeader.codeWord bits 3))
def members {n : ℕ} (g : SupportedNormalizedGate n):=frame (CloseoutRowsGateSupport.gateMembers g.support)
def initial {n : ℕ} (g : SupportedNormalizedGate n):=
  CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g
def top {n : ℕ} (g : SupportedNormalizedGate n):=thresholdWord (CloseoutRowsGateSource.request true g).gate
def native (core : ℕ) (bits : List Bool):=match decoded bits with
  | none=>[]
  | some g=>natWord g.wireCount++frame (top g)++
      (List.range (words bits).length).flatMap (outputs true core 1 (members g) (words bits))
def passed (core W L : ℕ) (bits : List Bool) : Prop:=
  CloseoutRowsCircuitPrefix.valid true bits ∧ ∃ g,decoded bits=some g ∧
    validity core true (words bits) (words bits).length=true ∧
    CloseoutRowsCircuitArithmeticDock.amount true
      (descriptions core (words bits) (initial g) (words bits).length) (words bits).length ≤ L ∧
    wires true core 1 (members g) (words bits) 0 (words bits).length ≤ W

theorem outputs_pad (C core pos : ℕ) (m : List Bool) (ws : List (List Bool)) :
    outputs true core pos (ZeroPadding.pad C m) ws=outputs true core pos m ws:=by
  funext j
  simp [outputs,choose,CloseoutRowsCircuitBottom.kept,ZeroPadding.read_pad]

theorem wires_pad (C core pos : ℕ) (m : List Bool) (ws : List (List Bool)) (a j : ℕ) :
    wires true core pos (ZeroPadding.pad C m) ws a j=wires true core pos m ws a j:=by
  simp [wires,choose,CloseoutRowsCircuitBottom.kept,ZeroPadding.read_pad]

theorem passed_decode (core W L : ℕ) (bits : List Bool) (g : SupportedNormalizedGate (words bits).length)
    (hg : decoded bits=some g) : passed core W L bits ↔
    CloseoutRowsCircuitPrefix.valid true bits ∧ validity core true (words bits) (words bits).length=true ∧
      CloseoutRowsCircuitArithmeticDock.amount true
        (descriptions core (words bits) (initial g) (words bits).length) (words bits).length ≤ L ∧
      wires true core 1 (members g) (words bits) 0 (words bits).length ≤ W:=by
  simp [passed,hg]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdRun

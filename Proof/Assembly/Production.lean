import Proof.Assembly.Adapter

/-! Concrete family input and paid raw-packet producer. The producer is shared
by the two actual constructors, has no arbitrary selector/polynomial oracle,
and writes exactly the existing per-packet raw stream. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PacketProduction
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.CompilerSemantics
open NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierRadix
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets
noncomputable section

/-- The outer monomial supplies at most four circuits, with occurrence order. -/
inductive Request where
  /-- Protocol sentinel only; distinct from a real empty-factor request. -/
  | terminal
  | sym (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
      (four : r.circuits.length ≤ 4) (liveScale target : Nat)
  | thr (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
      (four : r.circuits.length ≤ 4) (liveScale target : Nat)

def Request.q : Request → Nat
  | .terminal => 400
  | .sym r _ _ _ => r.q
  | .thr r _ _ _ => r.q

def Request.liveScale : Request → Nat
  | .terminal => 0
  | .sym _ _ L _ => L
  | .thr _ _ L _ => L

def Request.family (a : DecompositionAlgorithm) : (r : Request) → Packets.Family r.q r.liveScale
  | .terminal => ⟨[],[]⟩
  | .sym r _ L target => Packets.symFamily r L target
  | .thr r _ L target => Packets.thrFamily a r L target

/-- The native circuit payloads have exactly the existing CircuitMeaning
shape; bottom membership bits are a separate stream in occurrence order. -/
def bottomWord {q : Nat} (g : SupportedNormalizedGate q) : List Bool :=
  thresholdWord (nonStrictAsStrict g.gate)

def symWord {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) : List Bool :=
  natWord c.bottomCount ++ RepairOrdinary.frame (List.ofFn c.top) ++
    (List.ofFn c.bottom).flatMap (fun g => RepairOrdinary.frame (bottomWord g))

def thrWord {q : Nat} (c : NormalizedThresholdThresholdCircuit q) : List Bool :=
  natWord c.top.wireCount ++ RepairOrdinary.frame (thresholdWord (nonStrictAsStrict (retainedTopGate c))) ++
    (List.ofFn (fun i => c.bottom (retainedTopIndex c i))).flatMap
      (fun g => RepairOrdinary.frame (bottomWord g))

def Request.nativeWord : Request → List Bool
  | .terminal => natWord 2
  | .sym r _ L target => natWord 0 ++ natWord r.q ++ natWord L ++ natWord target ++
      natWord r.circuits.length ++ r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))
  | .thr r _ L target => natWord 1 ++ natWord r.q ++ natWord L ++ natWord target ++
      natWord r.circuits.length ++ r.circuits.flatMap (fun c => RepairOrdinary.frame (thrWord c))

/-- Interleaved original/constant child counts determine the absolute-index
cache. Its actual production, including the count header, belongs to setup. -/
def Request.indexWord (a : DecompositionAlgorithm) (r : Request) : List Bool :=
  let F := r.family a
  natListWord (ExtDecompositionBatch.counts a (CloseoutRowsUniversal.pool (Packets.live F) F.occurrences))

def Request.supportWord (a : DecompositionAlgorithm) (r : Request) : List Bool :=
  (r.family a).occurrences.flatMap (fun (g : SupportedNormalizedGate r.q) =>
    RepairOrdinary.frame (List.ofFn (fun i : Fin r.q => decide (i ∈ g.support))))

/-- THR coefficients require the actual retained TOP children, not bottom
counts. Setup must run/pay the source constructor and supply these words. -/
def Request.topWord (a : DecompositionAlgorithm) : Request → List Bool
  | .terminal => []
  | .sym _ _ _ _ => []
  | .thr r _ _ _ => r.circuits.flatMap (fun c =>
      RepairOrdinary.frame (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c)))

def Request.input (a : DecompositionAlgorithm) (r : Request) : List Bool :=
  RepairOrdinary.frame r.nativeWord ++ RepairOrdinary.frame (r.supportWord a) ++
    RepairOrdinary.frame (CyclicChoice.mask (r.family a).occurrences r.liveScale) ++
    RepairOrdinary.frame (r.indexWord a) ++ RepairOrdinary.frame (r.topWord a)

/-- Do not replace this with a flattened-polynomial stream: each existing
rawWord carries its own delimiter convention. -/
def Request.raw (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (r : Request) : List Bool :=
  let F := r.family a
  let g := Packets.geometry selector F
  F.rows.flatMap (ExternalRowFamily.rawWord a F g)

def Request.degree (a : DecompositionAlgorithm) (r : Request) : Nat :=
  ((r.family a).rows.map Packets.Row.degree).foldl max 0

def Request.denominator (a : DecompositionAlgorithm) : Request → Nat
  | .terminal => 0
  | .sym r _ _ target => symmetricListDenominator r target
  | .thr r _ _ target => CloseoutFinalC10ThresholdRows.listDenominator a r target

/-- Actual tuple dimension, not a q-only estimate for unguarded syntax. -/
def Request.tupleWork (a : DecompositionAlgorithm) : Request → Nat
  | .terminal => 1
  | .sym r _ _ _ => (symmetricFourfoldOccurrences r).length+1
  | .thr r _ _ target =>
      ((thresholdFourfoldOccurrences r).length+1)^
        (modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target))

def Request.smallSize (a : DecompositionAlgorithm) (r : Request) : Nat :=
  let F := r.family a
  let d := r.degree a+1
  r.q + (r.input a).length + 2^(Packets.live F).card +
    (F.occurrences.length+2)^d + (Packets.alphabet a F)^d +
    r.tupleWork a + 2^(canonicalWalkLength (r.denominator a)) +
    (F.occurrences.length+2)^(canonicalGradedDepth (LiveRows.bound F.occurrences (Packets.live F))+1) + 1

def packetBudget (a : DecompositionAlgorithm) (coefficient degree : Nat) (r : Request) : Nat :=
  coefficient * ((r.family a).rows.length+1) * (r.smallSize a)^degree

/-- Ordinary code and its cost degree are selected independently of every
runtime request and independently of the later hierarchy index. -/
structure PacketWriter (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) where
  coefficient : Nat
  degree : Nat
  positive : 0 < coefficient
  ordinary : RewoundWordFunction Request (Request.input a) (Request.raw selector a)
    (packetBudget a coefficient degree)

/-- The residual asks for one actual source-global generator, not existence of
arbitrary rows. Raw input production and reuse are not included in this field. -/
def PacketConstruction (selector : CyclicChoice.Laws) : Prop :=
  ∀ a : DecompositionAlgorithm, Nonempty (PacketWriter selector a)

/-- Exact output and heads of the chosen ordinary producer; private final
contents may be retained until the paid setup/reset clears them. -/
theorem PacketWriter.run (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (p : PacketWriter selector a) (r : Request) :
    ∃ A : Fin p.ordinary.program.tapeCount → List Bool,
      Step p.ordinary.program.machine (packetBudget a p.coefficient p.degree r)
        (fun _ => 0) (p.ordinary.program.inputTapes (r.input a)) (fun _ => 0) A ∧
      A p.ordinary.program.outputTape = r.raw selector a := by
  obtain ⟨receipt,run,out⟩ := p.ordinary.realizes r
  have heads := p.ordinary.headsReset r receipt run
  refine ⟨receipt.final.tapes,?_,out⟩
  exact Step.of_run run (funext heads) rfl

/-- The caller surrounds the actual packet machine with its two paid input
and output joins. Slots and code are fixed before a runtime request. -/
structure SeedCode {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (p : PacketWriter selector a) (U : Nat) where
  slots : Fin p.ordinary.program.tapeCount → Fin U
  injective : Function.Injective slots
  loadStates : Nat
  load : Machine U loadStates
  tailStates : Nat
  tail : Machine U tailStates

def SeedCode.machine {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {p : PacketWriter selector a} {U : Nat} (c : SeedCode p U) :=
  Composition.machine c.load
    (Composition.machine (RecoveryFocus.machine c.slots p.ordinary.program.machine) c.tail)

/-- The final-bank quantifier ranges over the actual packet Step, with its
certified output. It supplies no semantic word as a resident input for free. -/
def SeedCode.Ready {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {p : PacketWriter selector a} {U : Nat} (c : SeedCode p U)
    (r : Request) (fuel : Nat) (H H' : Fin U → Nat) (A A' : Fin U → List Bool) : Prop :=
  ∃ (reserve : Fin p.ordinary.program.tapeCount → Nat)
    (ambientH : Fin U → Nat) (ambientA : Fin U → List Bool) (loadFuel tailFuel : Nat),
  Step c.load loadFuel H A
    (dockH c.slots ambientH (fun _ => 0))
    (install c.slots ambientA (fun i => ZeroPadding.pad (reserve i)
      (p.ordinary.program.inputTapes (r.input a) i))) ∧
  (∀ B : Fin p.ordinary.program.tapeCount → List Bool,
    Step p.ordinary.program.machine (packetBudget a p.coefficient p.degree r)
      (fun _ => 0) (p.ordinary.program.inputTapes (r.input a)) (fun _ => 0) B →
    B p.ordinary.program.outputTape = r.raw selector a →
    Step c.tail tailFuel
      (dockH c.slots ambientH (fun _ => 0))
      (install c.slots ambientA (fun i => ZeroPadding.pad (reserve i) (B i))) H' A') ∧
  loadFuel+1+(packetBudget a p.coefficient p.degree r+1+tailFuel) ≤ fuel

theorem SeedCode.run {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {p : PacketWriter selector a} {U : Nat} (c : SeedCode p U)
    (r : Request) (fuel : Nat) (H H' : Fin U → Nat) (A A' : Fin U → List Bool)
    (ready : c.Ready r fuel H H' A A') : Step c.machine fuel H A H' A' := by
  obtain ⟨reserve,ambientH,ambientA,loadFuel,tailFuel,load,tail,bound⟩ := ready
  obtain ⟨B,packet,output⟩ := p.run selector a r
  have middle := (packet.pad reserve).focus c.slots c.injective ambientH ambientA
  exact (load.seq (middle.seq (tail B packet output))).enlarge bound

end
end PacketProduction

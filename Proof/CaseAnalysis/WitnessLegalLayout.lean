import Proof.CaseAnalysis.WitnessLegalFields
import Proof.CaseAnalysis.RowsCircuitGuarded

/-! One size-guarded native source path enters the legal-family policy.
The actual source-derived q0/clause/width and retained cache are aliased. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces CanonicalWitnessCodec
open private flag_outside from Proof.CaseAnalysis.WitnessNativePipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tapes (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=ColdNative.tapes source a k D G+LegalTemplate.Call.extra e
def old (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (i : Fin (ColdNative.tapes source a k D G)):=LegalTemplate.Call.old e i
def slots (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=LegalTemplate.Call.slots e (fields source a k D G)
def flagSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=old source a k D G e (ColdNative.flagSlot source a k D G)
def lengthSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=old source a k D G e (ColdNative.lengthSlot source a k D G)
def first (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e : ℕ) (delta : ℚ) (code : List Bool):=
  TapeEmbedding.machine (LegalTemplate.Call.extra e) (ColdNative.machine source a k CH Cpad cutoff D G copies delta code)
def second (a : PointwisePCPPAlgorithm) (k D G e den copies : ℕ) (delta : ℚ) (sym : Bool):=
  LegalTemplate.Call.machine e den delta copies sym (fields source a k D G)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool):=
  CloseoutRowsGateColdPair.machine (first source a k CH Cpad cutoff D G copies e delta code)
    (second source a k D G e den copies delta sym) (fun scanned=>scanned (flagSlot source a k D G e))
def input (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (x raw : List Bool):=
  LegalTemplate.Call.input e (ColdNative.input source a k D G x raw)
def tailBudget (a : PointwisePCPPAlgorithm) (k CH Cpad D copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (hpad : k+3 ≤ Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  let cb:=(a.output r).clauseBits
  let q0:=CorePolicy.q0 D r.arity
  let b:=natBitLength (CloseoutXor.cap delta q0 copies*max 1 (2*2^cb))
  LegalTemplate.budget e den delta copies sym r.arity q0 cb b

def budget (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw : List Bool) (hpad : k+3 ≤ Cpad):=
  ColdNative.budget source a k CH Cpad cutoff D G copies delta code x raw hpad+1+
    (if ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw=true then
      (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)).elim 0
        (fun oracle=>tailBudget source a k CH Cpad D copies e den delta code sym x hpad oracle+1) else 0)

theorem fields_ne_flag (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    ∀ i,fields source a k D G i≠ColdNative.flagSlot source a k D G:=by
  intro i he
  have hs:=(NativePipeline.Dock.slots_injective a D G (ColdNative.fields source k)
    (ColdNative.fields_injective source k)) he
  exact (NativePolicy.Call.outside a D (NativePipeline.counter G) (NativeScreen.flagSlot G)
    (flag_outside G) (NativePolicy.policySlots a D (localFields D i))) hs

theorem fields_ne_length (a : PointwisePCPPAlgorithm) (k D G : ℕ) :
    ∀ i,fields source a k D G i≠ColdNative.lengthSlot source a k D G:=by
  intro i he
  exact (NativePipeline.Dock.outside a D G (ColdNative.fields source k) (ColdOracle.lengthSlot source k)
    (ColdNative.fields_ne_length source k)
    (NativePipeline.localSlots a D G (NativePolicy.policySlots a D (localFields D i)))) he

theorem core_positive (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool)
    {n : ℕ} (x : BitInput n) (hpad : k+3 ≤ Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))) :
    0<(ColdNative.request source a k CH Cpad code x hpad oracle).arity:=by
  have hr:0<SelectedOracle.width source k CH Cpad code (List.ofFn x):=by
    unfold SelectedOracle.width Dimensions.width natBitLength
    omega
  exact hr.trans_le (Nat.le_max_left _ _)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal

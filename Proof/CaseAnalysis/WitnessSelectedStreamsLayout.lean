import Proof.CaseAnalysis.WitnessStreamCall
import Proof.Hierarchy.HierarchyStreamScalars

/-! Exact source fields and disjoint retained scalars at the stream join.
The same selected PCP word is consumed directly, without another call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedStreams
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=SelectedOracle.tapes source k
abbrev tapes (k : ℕ):=base source k+48
def old (k : ℕ) : Fin (base source k)→Fin (tapes source k):=StreamCall.old
def selectedFields (k : ℕ) : Fin 3→Fin (HierarchySelectedSource.tapes source k):=
  ![HierarchySelectedSource.outputTape source k,
    HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.rawR source.degrees.proofLog source.degrees.queries)),
    HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.rawQ source.degrees.proofLog source.degrees.queries))]
def fields (k : ℕ) : Fin 3→Fin (base source k):=SelectedOracle.old source k ∘ selectedFields source k
def ports : Fin 3→Fin 48:=![0,13,14]
def selectedBits (k : ℕ) : Fin 2→Fin (HierarchySelectedSource.tapes source k):=
  ![HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.bitsR source.degrees.proofLog source.degrees.queries)),
    HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.bitsQ source.degrees.proofLog source.degrees.queries))]
def bits (k : ℕ) : Fin 2→Fin (base source k):=SelectedOracle.old source k ∘ selectedBits source k

theorem shadow (k : ℕ) (i : Fin 3) :
    HierarchyStreams.old source k (HierarchySourceInput.slots source k (selectedFields source k i))=
      HierarchyStreams.slots source k (ports i):=by fin_cases i <;> rfl

theorem fields_injective (k : ℕ) : Function.Injective (fields source k):=by
  intro a b h
  have hs:=OracleCall.old_injective _ h
  have hm:=congrArg (HierarchyStreams.old source k ∘ HierarchySourceInput.slots source k) hs
  simp only [Function.comp_apply,shadow] at hm
  exact (by decide : Function.Injective ports) ((HierarchyStreams.slots_injective source k) hm)

theorem parser_not_field (k : ℕ) (i : Fin (Oracle.tapes+1)) (j : Fin 3) :
    OracleCall.parserSlots (SelectedOracle.base source k) i≠fields source k j:=by
  exact Ne.symm (OracleCall.old_ne_extra (selectedFields source k j) (i.castAdd 4))

theorem bits_not_fields (k : ℕ) (i : Fin 2) (j : Fin 3) : bits source k i≠fields source k j:=by
  intro h
  have hs:=OracleCall.old_injective _ h
  have hm:=congrArg (HierarchySourceInput.slots source k) hs
  fin_cases i <;> fin_cases j
  · exact (HierarchyStreams.source_distinct source k _ ) hm.symm
  · exact (HierarchyStreams.bit_distinct source k).1 hm
  · exact (HierarchyStreams.bit_distinct source k).2.1 hm
  · exact (HierarchyStreams.source_distinct source k _) hm.symm
  · exact (HierarchyStreams.bit_distinct source k).2.2.1 hm
  · exact (HierarchyStreams.bit_distinct source k).2.2.2 hm

def pcp (k CH Cpad : ℕ) (code x : List Bool):=
  source.output (HierarchySelectedSource.request (HierarchyPadding.rawInput k CH Cpad code x))
def queries (k CH Cpad : ℕ) (code x : List Bool):=
  Dimensions.queries source (HierarchyPadding.rawInput k CH Cpad code x).length
def input (k : ℕ) (x raw : List Bool):=StreamCall.input (SelectedOracle.input source k x raw)
def first (k CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (old source k) (SelectedOracle.machine source k CH Cpad code)
def second (k : ℕ):=StreamCall.machine (fields source k)
def machine (k CH Cpad : ℕ) (code : List Bool):=Composition.machine (first source k CH Cpad code) (second source k)
def budget (k CH Cpad : ℕ) (code x raw : List Bool):=
  SelectedOracle.budget source k CH Cpad code x raw+1+
    Streams.budget (pcp source k CH Cpad code x) (SelectedOracle.width source k CH Cpad code x)
      (queries source k CH Cpad code x)

theorem initial_install (k : ℕ) (x raw : List Bool) (prior : Fin (base source k)→List Bool) :
    install (old source k) (input source k x raw) prior=StreamCall.input prior:=by
  funext i
  refine Fin.addCases (m:=base source k) (n:=48) ?_ ?_ i
  · intro j
    change install (old source k) _ _ (old source k j)=_
    rw [install_slot (old source k) (StreamCall.old_injective _)]
    exact (StreamCall.input_old prior j).symm
  · intro j
    rw [install_other _ _ _ _ (by
      intro l hl
      have hv:=congrArg Fin.val hl
      change l.val=base source k+j.val at hv
      omega)]
    simp only [input,StreamCall.input,Fin.addCases_right]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedStreams

import Proof.Hierarchy.HierarchySourceOutputBounds
import Proof.PCP.ProjectionNormalizationStreams

/-! Static wiring from the actual selected-source endpoint into the complete
normalization stream producer. Only three retained input tapes are selected;
all stream workspace is fresh. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
open LocalBitMultitape RepairOrdinary RecoveryRootRound SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def base (k : ℕ) := HierarchySourceInput.tapes source k
def tapes (k : ℕ) := base source k+48
def old (k : ℕ) (i : Fin (base source k)) : Fin (tapes source k) := i.castAdd 48
def field (k : ℕ) (i : Fin (HierarchySelectedSource.base source k)) : Fin (base source k) :=
  HierarchySourceInput.slots source k (HierarchySelectedSource.old source k i)
def dimension (k : ℕ) (i : Fin (DimensionsFromInput.tapes source.degrees.proofLog source.degrees.queries)) :=
  field source k (HierarchySelectedSource.dimension source k i)
def rawR (k : ℕ) := dimension source k (DimensionsFromInput.rawR source.degrees.proofLog source.degrees.queries)
def rawQ (k : ℕ) := dimension source k (DimensionsFromInput.rawQ source.degrees.proofLog source.degrees.queries)
def bitsR (k : ℕ) := dimension source k (DimensionsFromInput.bitsR source.degrees.proofLog source.degrees.queries)
def bitsQ (k : ℕ) := dimension source k (DimensionsFromInput.bitsQ source.degrees.proofLog source.degrees.queries)
def sourceSlot (k : ℕ) := HierarchySourceInput.outputTape source k

theorem raw_values (p q : ℕ) :
    (DimensionsFromInput.rawR p q).val=51+2*p ∧ (DimensionsFromInput.rawQ p q).val=64+2*p+2*q := by
  simp [DimensionsFromInput.rawR,DimensionsFromInput.rawQ,DimensionsFromInput.dimensionSlots,
    DimensionProducer.rawR,DimensionProducer.rawQ,DimensionProducer.old,DimensionProducer.querySlots,
    DimensionWidth.rawSlot,DimensionWidth.binarySlots,DimensionWidth.fresh,DimensionWidth.base,DimensionWidth.tapes,
    DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots,DimensionPolynomial.tapes]
  omega

theorem raw_distinct (k : ℕ) : rawR source k≠rawQ source k := by
  intro he
  have h1 := HierarchySourceInput.slots_injective source k he
  have h2 := HierarchySelectedSource.old_injective source k h1
  have h3 := HierarchyPrefix.dimension_injective k source.degrees.proofLog source.degrees.queries h2
  have hv := congrArg Fin.val h3
  rw [(raw_values source.degrees.proofLog source.degrees.queries).1,
    (raw_values source.degrees.proofLog source.degrees.queries).2] at hv
  omega

theorem source_distinct (k : ℕ) (i : Fin (HierarchySelectedSource.base source k)) :
    sourceSlot source k≠field source k i := by
  have hout : 2 ≤ (SourceCall.outputTape source).val := by
    dsimp [SourceCall.outputTape,SourceCall.slots,SourceCall.old]
    split_ifs <;> simp
    omega
  intro he
  have h1 := HierarchySourceInput.slots_injective source k he
  have hv := congrArg Fin.val h1
  have hi := i.isLt
  simp only [HierarchySelectedSource.outputTape,HierarchySelectedSource.slots,
    show (SourceCall.outputTape source).val≠0 by omega,
    show (SourceCall.outputTape source).val≠1 by omega,if_false,
    HierarchySelectedSource.old,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

def slots (k : ℕ) (i : Fin 48) : Fin (tapes source k) :=
  if i=0 then old source k (sourceSlot source k)
  else if i=13 then old source k (rawR source k)
  else if i=14 then old source k (rawQ source k)
  else i.natAdd (base source k)

theorem slots_injective (k : ℕ) : Function.Injective (slots source k) := by
  intro a b he
  have hsr : (sourceSlot source k).val≠(rawR source k).val :=
    fun h => source_distinct source k _ (Fin.ext h)
  have hsq : (sourceSlot source k).val≠(rawQ source k).val :=
    fun h => source_distinct source k _ (Fin.ext h)
  have hrq : (rawR source k).val≠(rawQ source k).val := fun h => raw_distinct source k (Fin.ext h)
  have hs : (sourceSlot source k).val < base source k := (sourceSlot source k).isLt
  have hr := (rawR source k).isLt
  have hq := (rawQ source k).isLt
  apply Fin.ext
  have hv := congrArg Fin.val he
  dsimp only [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> subst_vars <;> omega

noncomputable def first (k CH Cpad : ℕ) (code : List Bool) :=
  TapeEmbedding.machine 48 (HierarchySourceInput.machine source k CH Cpad code)
noncomputable def second (k : ℕ) := RecoveryFocus.machine (slots source k) Streams.machine
noncomputable def machine (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (first source k CH Cpad code) (second source k)
def request (k CH Cpad : ℕ) (code x : List Bool) :=
  HierarchySelectedSource.request (HierarchyPadding.rawInput k CH Cpad code x)
def R (k CH Cpad : ℕ) (code x : List Bool) := Dimensions.width source (request k CH Cpad code x).1
def Q (k CH Cpad : ℕ) (code x : List Bool) := Dimensions.queries source (request k CH Cpad code x).1
def budget (k CH Cpad : ℕ) (code x : List Bool) :=
  HierarchySourceInput.budget source k CH Cpad code x+1+
    Streams.budget (source.output (request k CH Cpad code x)) (R source k CH Cpad code x) (Q source k CH Cpad code x)

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams

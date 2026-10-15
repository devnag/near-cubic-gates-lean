import Proof.Hierarchy.HierarchyQuerySerializer
import Proof.PCP.PCPClauseListProducer

/-! Static query-to-clause nesting and the four literal fields consumed by
the final balanced encoder. All indices refer to the same physical prefix. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyClauses
open LocalBitMultitape RepairOrdinary PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def base (k : ℕ) := HierarchyStreams.tapes source k+128
def tapes (k : ℕ) := base source k+309
def sourceSlot (k : ℕ) : Fin (base source k) := (HierarchyStreams.slots source k 38).castAdd 128
def countSlot (k : ℕ) : Fin (base source k) := (HierarchyStreams.slots source k 46).castAdd 128
theorem slots_ne (k : ℕ) : sourceSlot source k≠countSlot source k := by
  intro h
  have hv := congrArg (fun i : Fin (base source k) => i.val) h
  have he : HierarchyStreams.slots source k 38=HierarchyStreams.slots source k 46 := Fin.ext hv
  have hf := HierarchyStreams.slots_injective source k he
  contradiction

def groups (k CH Cpad : ℕ) (code x : List Bool) :=
  PCPTripleNative.groups (source.output (HierarchyStreams.request k CH Cpad code x))
def machine (k CH Cpad : ℕ) (code : List Bool) :=
  PCPClauseBank.producerMachine (sourceSlot source k) (countSlot source k)
    (HierarchyQuery.machine source k CH Cpad code)
def entry (k CH Cpad : ℕ) (code x bound : List Bool) :=
  let c := TapeEmbedding.config (fun _ : Fin 309 => 0) (fun _ : Fin 309 => [])
    (HierarchyQuery.entry source k CH Cpad code x bound)
  (⟨(machine source k CH Cpad code).start,c.heads,c.tapes⟩ : Configuration (tapes source k) _)
def budget (k CH Cpad : ℕ) (code x : List Bool) :=
  HierarchyQuery.budget source k CH Cpad code x+1+PCPClauseList.budget (groups source k CH Cpad code x)

def widthSlot (k : ℕ) : Fin (tapes source k) :=
  ((HierarchyStreams.old source k (HierarchyStreams.bitsR source k)).castAdd 128).castAdd 309
def queriesSlot (k : ℕ) : Fin (tapes source k) :=
  ((HierarchyStreams.old source k (HierarchyStreams.bitsQ source k)).castAdd 128).castAdd 309
def querySlot (k : ℕ) : Fin (tapes source k) :=
  ((77 : Fin 128).natAdd (HierarchyStreams.tapes source k)).castAdd 309
def clauseSlot (k : ℕ) : Fin (tapes source k) := (258 : Fin 309).natAdd (base source k)
def fieldSlots (k : ℕ) : Fin 4 → Fin (tapes source k) :=
  ![widthSlot source k,queriesSlot source k,querySlot source k,clauseSlot source k]
def words (k CH Cpad : ℕ) (code x : List Bool) : Fin 4 → List Bool :=
  ![(HierarchyStreams.R source k CH Cpad code x).bits,
    (HierarchyStreams.Q source k CH Cpad code x).bits,
    (PCPTraversal.code (HierarchyQuery.fields source k CH Cpad code x)).bits,
    (PCPTraversal.code (PCPClauseList.fields (groups source k CH Cpad code x))).bits]
def suffixes (k CH Cpad : ℕ) (code x : List Bool) : Fin 4 → List Bool :=
  ![[],[],
    List.replicate (PCPPairReusable.capacity (mass (HierarchyQuery.fields source k CH Cpad code x))-
      (frame (words source k CH Cpad code x 2)).length) false,
    List.replicate (PCPPairReusable.capacity (mass (PCPClauseList.fields (groups source k CH Cpad code x)))-
      (frame (words source k CH Cpad code x 3)).length) false]

theorem old_not_slot (k : ℕ) (i : Fin (HierarchyStreams.base source k))
    (j : Fin 48) (h0 : j≠0) (h13 : j≠13) (h14 : j≠14) :
    HierarchyStreams.old source k i≠HierarchyStreams.slots source k j := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [HierarchyStreams.slots,h0,h13,h14,ite_false,HierarchyStreams.old,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyClauses

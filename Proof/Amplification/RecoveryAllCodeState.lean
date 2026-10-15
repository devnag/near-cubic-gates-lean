import Proof.Amplification.RecoveryBranchDisjunctionRuns

/-! The selected all-code checker retains the unchanged raw/default and
compact branches on disjoint banks, with a physical final disjunction.
The entry predicate below lists exactly what the cold producer must prove. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  raw : RecoveryRawBranch.State
  marker : RecoveryMarkerHandoff.MarkerState
  compact : RecoveryMarkerHandoff.CheckState

def State.width (x : State) := x.raw.view.width
def State.code (x : State) := x.raw.eval.code
noncomputable def cfg {s : Nat} (x : State) (q : Fin s) : Configuration 348 s :=
  RecoveryBankPair.cfg (RecoveryRawBranch.cfg x.raw 0 (0 : Fin 1)).heads
    (RecoveryRawBranch.cfg x.raw 0 (0 : Fin 1)).tapes
    (RecoveryMarkerHandoff.heads x.compact) (RecoveryMarkerHandoff.tapes x.marker x.compact) q
noncomputable def machine := RecoveryBranchDisjunction.machine RecoveryRawBranch.machine
  RecoveryCompactBranch.machine (93 : Fin 136) (107 : Fin 212)
def budget (width : Nat) := RecoveryRawBranch.budget width+RecoveryCompactBranch.budget width+4

structure Prepared (x : State) (limit : Nat) (word : List Bool) (k : Nat)
    (innerBits outerBits innerPre outerPre : List Bool) : Prop where
  raw_valid : x.raw.view.Valid
  raw_source : x.raw.view.inner.stream.source=frame word
  raw_pos : x.raw.view.inner.stream.pos=2*k
  raw_eval : RecoveryRawSAT.Inv x.width x.raw.eval.valuation.cap 0 0 word x.raw.eval
  raw_code : RecoveryRawViewBody.code x.raw.view=x.code
  raw_tags : x.raw.view.inner.tags=true
  raw_bound : RadixSemantics.value x.raw.view.inner.bound=natBitLength x.code
  compact_ready : RecoveryNestedTable.Prepared x.compact limit word innerBits outerBits innerPre outerPre
  limit_bound : limit ≤ 3*(x.compact.inner.base.state.bits.length+1)
  marker_valid : x.marker.Valid
  marker_width : x.marker.width=x.compact.inner.base.state.bits.length
  width_eq : x.compact.inner.base.state.bits.length=x.width
  code_eq : RecoveryMarker.outerCode x.marker=x.code
  committed_zero : (RecoveryMarkerMetadata.read x.marker).committed=frame (List.replicate x.marker.width false)
  count_zero : (RecoveryMarkerMetadata.read x.marker).count=frame (List.replicate x.marker.width false)
  valuation_parse : ∃ table rest,readList x.compact.inner.base.extra.cap
    (readEntry x.compact.inner.base.state.bits.length) word=some (table,rest)

theorem budget_le (width : Nat) : budget width ≤ 4294967296*(width+1)^4 := by
  have hc := RecoveryCompactBranch.budget_le width
  have hp : (width+1)^3 ≤ (width+1)^4 := by
    calc
      _ = 1*(width+1)^3 := by omega
      _ ≤ (width+1)*(width+1)^3 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hpos : 1 ≤ (width+1)^4 := Nat.one_le_pow _ _ (by omega)
  unfold budget RecoveryRawBranch.budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryAllCode

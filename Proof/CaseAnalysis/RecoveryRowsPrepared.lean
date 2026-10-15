import Proof.CaseAnalysis.RecoveryRowsMeaning

/-! The paid physical row-loop bank, with its uniform resource premises.
All source, prototype and backing words occur in the actual input tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
variable {n bound : ℕ} (x : BitInput n) (count : ℕ) (hc : count≤bound)

structure Resources where
  W : ℕ
  G : ℕ
  D : ℕ
  L : ℕ
  B : ℕ
  S : ℕ
  pre : List Bool
  sourceTail : List Bool
  packetTail : List Bool
  graph_bound : G≤W
  native_bound : R≤W
  query_bound : Q≤W
  dock_bound : 8388608*(W+1)^3≤D
  log_bound : RecoveryBoundedSelectorFinish.logCapacity W≤L
  log_capacity : capacity W+5*W+7≤L
  backing_capacity : capacity W+2≤B
  backing_dock : D≤B
  backing_log : L≤B
  support_positive : 1≤S
  backing_row : S+RecoveryBoundedRow.budget Q (Codec.clauses p).length W+3≤B
  projector_bound : RecoveryProjectionRowsRewind.batchBudget R Q+2≤B
  metadata_bound : ∀ j∈RecoveryBoundedRowReload.ports,
    (RecoveryBoundedRowPrototype.fields (capacity W) D (OuterPCPRecovery.boundedCircuitFieldLimit R bound)
      L R count Q (Codec.clauses p).length j).length≤B
  packet_bound : (RecoveryBoundedRowReload.word
    (RecoveryBoundedRowPrototype.fields (capacity W) D (OuterPCPRecovery.boundedCircuitFieldLimit R bound)
      L R count Q (Codec.clauses p).length)).length≤B
  output_bound : ∀ b : BooleanDAGBuilder (descriptionWidth R bound), b.nodes.length≤G →
    (pre++b.nodes.flatMap PCPPRequestNodeSchema.native).length≤S
  input_bound : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (r : BitInput R), b.nodes.length≤G →
    ∀ i,(RecoveryBoundedRow.data b.nodes.length (capacity W) D (OuterPCPRecovery.boundedCircuitFieldLimit R bound) L
      (pre++b.nodes.flatMap PCPPRequestNodeSchema.native) R count
      (RecoveryBoundedQueries.addressWord (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x r)) [] Q
      (DedupBytes.fields p++sourceTail) [] (Codec.clauses p).length i).length≤S
  query_fits : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (r : BitInput R),
    (compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc r).compiled.final.nodes.length≤G →
    RecoveryBoundedQueries.Fits b count W hc
      (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x r)

variable {p R Q hr hq x count hc}

def Resources.word (z : Resources p R Q hr hq x count hc) (b : BooleanDAGBuilder (descriptionWidth R bound)):=
  z.pre++b.nodes.flatMap PCPPRequestNodeSchema.native
def Resources.packet (z : Resources p R Q hr hq x count hc):=
  RecoveryBoundedRowReload.word (RecoveryBoundedRowPrototype.fields (capacity z.W) z.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L R count Q (Codec.clauses p).length)++z.packetTail
def Resources.rowBank (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool):=
  rowData b.nodes.length (capacity z.W) z.D (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L z.B
    (z.word b) R count Q (Codec.clauses p).length [] (DedupBytes.fields p++z.sourceTail) stack z.packet
noncomputable def Resources.bank (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool):=
  data (z.rowBank b stack) (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) z.B)
def Resources.heads (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool):=
  RecoveryBoundedRows.heads (RecoveryBoundedRowAfter.heads (z.word b) stack)

theorem Resources.word_extension (z : Resources p R Q hr hq x count hc)
    {b c : BooleanDAGBuilder (descriptionWidth R bound)} (e : BooleanDAGExtension b c) :
    z.word b++e.suffix.flatMap PCPPRequestNodeSchema.native=z.word c := by
  unfold Resources.word
  rw [e.nodes_eq,List.flatMap_append,List.append_assoc]

theorem Resources.finish_original (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool)
    (hg : (compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)).compiled.final.nodes.length≤z.G) :
    let row:=compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)
    let saved:=RecoveryBoundedClauseCollect.pushed row.compiled.output.val stack
    ∃ r,runFrom finishMachine (finishBudget z.B)
      ⟨finishMachine.start,z.heads b stack,z.bank b k stack⟩=some r ∧ r.steps≤finishBudget z.B ∧
      r.final.heads=z.heads row.compiled.final saved ∧ r.final.tapes=z.bank row.compiled.final k saved := by
  let row:=compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)
  let saved:=RecoveryBoundedClauseCollect.pushed row.compiled.output.val stack
  let fields:=RecoveryProjectionRows.addressFields p R Q hr hq x (bitInputOfCode R k)
  have hb : b.nodes.length≤z.G:=row.compiled.extension.length_le.trans hg
  have ha : RecoveryBoundedRowAddress.budget fields+2≤z.B:=
    (Nat.add_le_add_right (RecoveryBoundedRowAddress.source_budget p R Q hr hq x (bitInputOfCode R k)
      z.W z.native_bound z.query_bound) 2).trans z.backing_capacity
  obtain ⟨a,ar,as,ah,aT⟩:=row_run p R Q hr hq x b count hc (bitInputOfCode R k)
    z.W z.D z.L z.B z.S (z.word b) z.sourceTail stack z.packetTail (z.query_fits b _ hg)
    z.native_bound z.query_bound (hg.trans z.graph_bound) z.dock_bound z.log_bound z.log_capacity
    (by have h:=z.backing_capacity;omega) z.backing_dock z.backing_log z.support_positive
    (z.output_bound b hb) z.projector_bound ha (z.input_bound b _ hb) z.backing_row z.metadata_bound z.packet_bound
  have he : z.word b++row.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native=z.word row.compiled.final:=z.word_extension _
  change a.final.heads=RecoveryBoundedRows.heads (RecoveryBoundedRowAfter.heads
    (z.word b++row.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native) saved) at ah
  change a.final.tapes=data
    (rowData row.compiled.final.nodes.length (capacity z.W) z.D (OuterPCPRecovery.boundedCircuitFieldLimit R bound)
      z.L z.B (z.word b++row.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native) R count Q
      (Codec.clauses p).length [] (DedupBytes.fields p++z.sourceTail) saved z.packet)
    (Function.update (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) z.B) 31
      (ZeroPadding.pad z.B (FieldList.stream fields))) at aT
  rw [he] at ah aT
  have hw : (ZeroPadding.pad z.B (FieldList.stream fields)).length≤z.B := by
    have hlen : (FieldList.stream fields).length≤z.B:=by unfold RecoveryBoundedRowAddress.budget at ha;omega
    simp only [ZeroPadding.pad,List.length_append,List.length_replicate]
    omega
  exact finish_run z.B (z.heads b stack) (z.bank b k stack)
    (RecoveryBoundedRowAfter.heads (z.word row.compiled.final) saved) (z.rowBank row.compiled.final saved)
    (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) z.B) _ a ar as ah aT
    rfl rfl rfl rfl (RecoveryBoundedRowProjection.bank_output p R Q _ z.B) hw

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows

import Proof.CaseAnalysis.RecoveryCountBody

/-! One uniform resource bank for the original count traversal. Only the
four count-dependent proof fields vary; all actual words and capacities remain
the same, and each prototype has its explicit paid trailing zero backing. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
variable {n bound : ℕ} (x : BitInput n)

structure Resources where
  base : RecoveryBoundedRows.Resources p R Q hr hq x 0 (Nat.zero_le bound)
  metadata_all : ∀ count, count≤bound → ∀ j∈RecoveryBoundedRowReload.ports,
    (RecoveryBoundedRowPrototype.fields (capacity base.W) base.D
      (OuterPCPRecovery.boundedCircuitFieldLimit R bound) base.L R count Q (Codec.clauses p).length j).length≤base.B
  packet_all : ∀ count, count≤bound → (RecoveryBoundedRowReload.word
    (RecoveryBoundedRowPrototype.fields (capacity base.W) base.D
      (OuterPCPRecovery.boundedCircuitFieldLimit R bound) base.L R count Q (Codec.clauses p).length)).length≤base.B
  input_all : ∀ count, count≤bound →
    ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (r : BitInput R), b.nodes.length≤base.G →
      ∀ i,(RecoveryBoundedRow.data b.nodes.length (capacity base.W) base.D
        (OuterPCPRecovery.boundedCircuitFieldLimit R bound) base.L
        (base.pre++b.nodes.flatMap PCPPRequestNodeSchema.native) R count
        (RecoveryBoundedQueries.addressWord (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x r)) [] Q
        (DedupBytes.fields p++base.sourceTail) [] (Codec.clauses p).length i).length≤base.S
  queries_all : ∀ count (hc : count≤bound),
    ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (r : BitInput R),
      (compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc r).compiled.final.nodes.length≤base.G →
      RecoveryBoundedQueries.Fits b count base.W hc
        (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x r)
  P : ℕ
  room : RecoveryBoundedGrammarCold.Room base.W (capacity base.W) base.D base.L base.S base.B P
  allocation : RecoveryBoundedGrammarCold.Allocation R bound base.G base.W
  clauses_bound : (Codec.clauses p).length≤base.W
  source_bound : (DedupBytes.fields p++base.sourceTail).length≤base.B

variable {p R Q hr hq x}

def Resources.fields (z : Resources p R Q hr hq (bound:=bound) x) (count : ℕ):=
  RecoveryBoundedRowPrototype.fields (capacity z.base.W) z.base.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.base.L R count Q (Codec.clauses p).length
def Resources.packet (z : Resources p R Q hr hq (bound:=bound) x) (count : ℕ):=
  ZeroPadding.pad z.base.B (RecoveryBoundedRowReload.word (z.fields count))
def Resources.atCount (z : Resources p R Q hr hq (bound:=bound) x) (count : ℕ) (hc : count≤bound) :
    RecoveryBoundedRows.Resources p R Q hr hq x count hc :=
  {z.base with
    packetTail:=List.replicate (z.base.B-(RecoveryBoundedRowReload.word (z.fields count)).length) false
    metadata_bound:=z.metadata_all count hc
    packet_bound:=z.packet_all count hc
    input_bound:=z.input_all count hc
    query_fits:=z.queries_all count hc}

def Resources.currentFields (z : Resources p R Q hr hq (bound:=bound) x) (count : ℕ) : Fin 78→List Bool:=
  if count=0 then fun _=>[] else z.fields count
def Resources.currentPacket (z : Resources p R Q hr hq (bound:=bound) x) (count : ℕ):=
  if count=0 then [] else z.packet count
def extraAt (B count : ℕ) (extra : Fin 12→List Bool):=
  Function.update extra 1 (RecoveryBoundedGrammarScalarAdd.unary B count)

theorem next_extra (B count : ℕ) (extra : Fin 12→List Bool) :
    RecoveryBoundedCountPacketBank.nextExtra B count (extraAt B count extra)=extraAt B (count+1) extra := by
  simp only [RecoveryBoundedCountPacketBank.nextExtra,extraAt,Function.update_idem]

theorem Resources.current_fields_bound (z : Resources p R Q hr hq (bound:=bound) x)
    (count : ℕ) (hc : count≤bound) :
    ∀ j∈RecoveryBoundedRowReload.ports,(z.currentFields count j).length≤z.base.B := by
  intro j hj
  by_cases h : count=0
  · simp only [currentFields,h,if_pos,List.length_nil];omega
  · simp only [currentFields,h,if_false]
    exact z.metadata_all count hc j hj

theorem Resources.current_packet_bound (z : Resources p R Q hr hq (bound:=bound) x)
    (count : ℕ) (hc : count≤bound) : (z.currentPacket count).length≤z.base.B := by
  by_cases h : count=0
  · simp only [currentPacket,h,if_pos,List.length_nil];omega
  · simp only [currentPacket,h,if_false,packet,ZeroPadding.pad,List.length_append,List.length_replicate]
    have hp:=z.packet_all count hc
    change (RecoveryBoundedRowReload.word (z.fields count)).length≤z.base.B at hp
    omega

noncomputable def Resources.bank (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (count : ℕ) (stack : List Bool) (extra : Fin 12→List Bool):=
  RecoveryBoundedCountBank.data z.base.B z.P
    (RecoveryBoundedGrammarBank.ready (z.currentFields count) b.nodes.length z.base.B
      (z.base.word b) stack (z.currentPacket count) (DedupBytes.fields p++z.base.sourceTail))
    (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B) (2^R)
    (RecoveryBoundedGrammarCold.metadata R bound 0 (capacity z.base.W) z.base.B (extraAt z.base.B count extra))
    (ZeroPadding.pad z.base.B (VerifierDecoding.CompareMachine.word (bound+1)))
    (ZeroPadding.pad z.base.B (VerifierDecoding.CompareMachine.word (count+1)))

def Resources.heads (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool):=
  RecoveryBoundedCountBank.heads (z.base.word b) stack 1 1

theorem Resources.packet_eq (z : Resources p R Q hr hq (bound:=bound) x) (count : ℕ) (hc : count≤bound) :
    (z.atCount count hc).packet=z.packet count := by
  simp only [RecoveryBoundedRows.Resources.packet,atCount,packet,fields,ZeroPadding.pad]

theorem Resources.row_ready (z : Resources p R Q hr hq (bound:=bound) x) (count : ℕ) (hc : count≤bound)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) :
    (z.atCount count hc).rowBank b stack=RecoveryBoundedGrammarBank.ready (z.fields count)
      b.nodes.length z.base.B (z.base.word b) stack (z.packet count) (DedupBytes.fields p++z.base.sourceTail) := by
  have h:=RecoveryBoundedCountRowsDock.row_ready (p:=p) (R:=R) (Q:=Q) (hr:=hr) (hq:=hq)
    (n:=n) (bound:=bound) (x:=x) (count:=count) (hc:=hc) (z.atCount count hc) b stack
  change (z.atCount count hc).rowBank b stack=RecoveryBoundedGrammarBank.ready (z.fields count)
    b.nodes.length z.base.B (z.base.word b) stack (z.atCount count hc).packet (DedupBytes.fields p++z.base.sourceTail) at h
  rw [z.packet_eq] at h
  exact h

theorem Resources.next_bank (z : Resources p R Q hr hq (bound:=bound) x) (count : ℕ) (hc : count+1≤bound)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (extra : Fin 12→List Bool) :
    RecoveryBoundedCountBank.data z.base.B z.P ((z.atCount (count+1) hc).rowBank b stack)
      (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B) (2^R)
      (RecoveryBoundedGrammarCold.metadata R bound 0 (capacity z.base.W) z.base.B
        (RecoveryBoundedCountPacketBank.nextExtra z.base.B count (extraAt z.base.B count extra)))
      (ZeroPadding.pad z.base.B (VerifierDecoding.CompareMachine.word (bound+1)))
      (ZeroPadding.pad z.base.B (VerifierDecoding.CompareMachine.word (count+2)))=
      z.bank b (count+1) stack extra := by
  rw [z.row_ready,next_extra]
  simp only [bank,currentFields,currentPacket,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform

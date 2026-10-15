import Proof.CaseAnalysis.RecoveryPreparedOutput
import Proof.CaseAnalysis.RecoveryPreparedBank
import Proof.CaseAnalysis.RecoveryPreparedResources

/-! The paid cold bank feeds the complete original count compiler. Five
actual scalar words remain untouched beside the unchanged graph worker. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdCompile
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedCountUniform
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Join
def machine {s t : ℕ} (first : Machine 158 s) (last : Machine 153 t):=
  Composition.machine first (TapeEmbedding.machine 5 last)

theorem run {s t : ℕ} {ι : Type} (first : Machine 158 s) (last : Machine 153 t)
    (u v : ℕ) (input : Fin 158→List Bool) (H : Fin 153→ℕ) (A : Fin 153→List Bool)
    (E : Fin 5→List Bool) (F : ι→Fin 153→ℕ) (T : ι→Fin 153→List Bool)
    (hp : ∃ p,LocalBitMultitape.run first u input=some p ∧ p.steps≤u ∧
      p.final.heads=Fin.addCases (m:=153) (n:=5) H (fun _ : Fin 5=>0) ∧
      p.final.tapes=Fin.addCases (m:=153) (n:=5) A E)
    (hq : ∃ i,∃ q,runFrom last v ⟨last.start,H,A⟩=some q ∧ q.steps≤v ∧
      q.final.heads=F i ∧ q.final.tapes=T i) :
    ∃ i,∃ r,LocalBitMultitape.run (machine first last) (u+1+v) input=some r ∧
      r.steps≤u+1+v ∧ r.final.heads=Fin.addCases (m:=153) (n:=5) (F i) (fun _ : Fin 5=>0) ∧
      r.final.tapes=Fin.addCases (m:=153) (n:=5) (T i) E := by
  obtain ⟨p,pr,ps,ph,pt⟩:=hp
  obtain ⟨i,q,qr,qs,qh,qt⟩:=hq
  let b:=TapeEmbedding.receipt (fun _ : Fin 5=>0) E q
  have br:=TapeEmbedding.run_embed last (fun _ : Fin 5=>0) E v _ q qr
  have br' : runFrom (TapeEmbedding.machine 5 last) v
      (Composition.restart p.final (TapeEmbedding.machine 5 last).start)=some b := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some b
    rw [ph,pt]
    exact br
  refine ⟨i,Composition.joinedReceipt p b,
    Composition.run_join first (TapeEmbedding.machine 5 last) _ _ _ p b pr br',
    Nat.add_le_add (Nat.add_le_add_right ps 1) qs,?_,?_⟩
  · change Fin.addCases (m:=153) (n:=5) (motive:=fun _=>ℕ) q.final.heads (fun _ : Fin 5=>0)=
      Fin.addCases (m:=153) (n:=5) (motive:=fun _=>ℕ) (F i) (fun _ : Fin 5=>0)
    rw [qh]
  · change Fin.addCases (m:=153) (n:=5) (motive:=fun _=>List Bool) q.final.tapes E=
      Fin.addCases (m:=153) (n:=5) (motive:=fun _=>List Bool) (T i) E
    rw [qt]
end Join

noncomputable def machine:=Join.machine RecoveryBoundedColdPrepared.machine compiledMachine
def budget (B W R bound : ℕ):=RecoveryBoundedColdPrepared.budget B+1+compiledBudget B W R bound
def raw (R bound C Q clauses : ℕ) : Fin 5→List Bool:=
  fun j=>List.replicate (RecoveryBoundedColdScalarMetadata.values R bound C Q clauses j) true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

theorem target_full (z : Resources p R Q hr hq (bound:=bound) x)
    (hpre : z.base.pre=[]) (htail : z.base.sourceTail=[]) (hP : z.P=z.base.B) :
    RecoveryBoundedColdPrepared.targetData R bound (capacity z.base.W) Q (Codec.clauses p).length z.base.B
      (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B) (DedupBytes.fields p)=
    Fin.addCases (m:=153) (n:=5)
      (scanData (z.bank (BooleanDAGBuilder.empty (descriptionWidth R bound)) 0 []
        (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)) bound)
      (raw R bound (capacity z.base.W) Q (Codec.clauses p).length) := by
  funext i
  refine Fin.addCases (m:=153) (n:=5) ?_ ?_ i
  · intro j
    simp only [Fin.addCases_left]
    exact congrFun (RecoveryBoundedColdPrepared.target_bank z hpre htail hP) j
  · intro j
    simp only [RecoveryBoundedColdPrepared.targetData,Fin.addCases_right,raw]

theorem run (z : Resources p R Q hr hq (bound:=bound) x)
    (hpre : z.base.pre=[]) (htail : z.base.sourceTail=[]) (hP : z.P=z.base.B)
    (hb : 0<bound)
    (hS : (bound+z.base.W)*(2*z.base.W+1)≤z.base.S)
    (hstack : (bound+2^R+1)*(2*z.base.W+1)≤z.P)
    (hFinal : (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x
      (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound)).final.nodes.length≤z.base.G) :
    ∃ f : Forward z (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound), ∃ r,
      LocalBitMultitape.run machine (budget z.base.B z.base.W R bound)
        (RecoveryBoundedColdPrepared.input R bound (capacity z.base.W) Q (Codec.clauses p).length z.base.B
          (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B) (DedupBytes.fields p))=some r ∧
      r.steps≤budget z.base.B z.base.W R bound ∧
      r.final.heads=Fin.addCases (m:=153) (n:=5)
        (z.foldResult f.next [] f.refs (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)).heads
        (fun _ : Fin 5=>0) ∧
      r.final.tapes=Fin.addCases (m:=153) (n:=5)
        (z.foldResult f.next [] f.refs (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)).tapes
        (raw R bound (capacity z.base.W) Q (Codec.clauses p).length) := by
  have first:=RecoveryBoundedColdPrepared.allocated_run z.allocation z.room z.base.query_bound z.clauses_bound
    (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B) (DedupBytes.fields p)
  rw [RecoveryBoundedColdPrepared.prepared_target,target_full z hpre htail hP,
    RecoveryBoundedColdPrepared.target_heads z hpre] at first
  have fields:=RecoveryBoundedColdPrepared.extra_fields R bound Q (Codec.clauses p).length z.base.B
  have last:=compiled_run z (BooleanDAGBuilder.empty (descriptionWidth R bound)) []
    (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)
    hb fields.1 fields.2.1 fields.2.2.1 fields.2.2.2
    (by simpa only [List.length_nil,Nat.zero_add] using hS)
    (by simpa only [List.length_nil,Nat.zero_add] using hstack) hFinal
  exact Join.run RecoveryBoundedColdPrepared.machine compiledMachine
    (RecoveryBoundedColdPrepared.budget z.base.B) (compiledBudget z.base.B z.base.W R bound)
    _ _ _ _ _ _ first last

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdCompile

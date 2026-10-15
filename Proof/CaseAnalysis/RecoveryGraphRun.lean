import Proof.CaseAnalysis.RecoveryGraphJoin

/-! Execute the complete original graph construction and unchanged cold
serializer. The result is the exact framed CNF for the shared description. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdGraph
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedCountUniform BalancedCNFSATEncoding
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Join.machine RecoveryBoundedColdCompile.machine RecoveryBoundedGraphSerialize.machine
def budget {arity : ℕ} (B W R bound : ℕ) (c : BooleanCircuit arity):=
  RecoveryBoundedColdCompile.budget B W R bound+1+RecoveryBoundedGraphSerialize.budget B c

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

theorem run (z : Resources p R Q hr hq (bound:=bound) x)
    (hpre : z.base.pre=[]) (htail : z.base.sourceTail=[]) (hP : z.P=z.base.B)
    (hb : 0<bound)
    (hS : (bound+z.base.W)*(2*z.base.W+1)≤z.base.S)
    (hstack : (bound+2^R+1)*(2*z.base.W+1)≤z.P)
    (hFinal : (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x
      (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound)).final.nodes.length≤z.base.G)
    (hg : (RecoveryBoundedGraphSerialize.graph z.circuit).length≤z.base.B)
    (ho : z.circuit.output.val+1≤z.base.B) (ha : descriptionWidth R bound+1≤z.base.B) :
    ∃ r,LocalBitMultitape.run machine (budget z.base.B z.base.W R bound z.circuit)
      (insert [] (RecoveryBoundedColdPrepared.input R bound (capacity z.base.W) Q (Codec.clauses p).length z.base.B
        (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B) (DedupBytes.fields p)))=some r ∧
      r.steps≤budget z.base.B z.base.W R bound z.circuit ∧
      r.final.tapes 1657=frame (balancedCNFPayload (CircuitInputCNF.circuitInputFormula z.circuit)).bits ∧
      r.final.heads 1657=0 ∧
      r.final.tapes 144=ZeroPadding.pad z.base.B (List.replicate (descriptionWidth R bound) true) ∧
      r.final.heads 144=0 ∧
      (∀ j : Fin 5,r.final.tapes (j.natAdd 1659)=
        RecoveryBoundedColdCompile.raw R bound (capacity z.base.W) Q (Codec.clauses p).length j ∧
        r.final.heads (j.natAdd 1659)=0) := by
  have first:=RecoveryBoundedColdCompile.run z hpre htail hP hb hS hstack hFinal
  apply Join.run RecoveryBoundedColdCompile.machine RecoveryBoundedGraphSerialize.machine
    (RecoveryBoundedColdCompile.budget z.base.B z.base.W R bound)
    (RecoveryBoundedGraphSerialize.budget z.base.B z.circuit) _ _ _ _ _ _ first
  intro f
  let e:=RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B
  obtain ⟨q,qr,qt,qh,qs,keep⟩:=RecoveryBoundedGraphSerialize.original_run z.base.B z.circuit
    (Fin.addCases (m:=153) (n:=1506) (z.foldResult f.next [] f.refs e).heads (fun _=>0))
    (Fin.addCases (m:=153) (n:=1506) (z.foldResult f.next [] f.refs e).tapes (fun _=>[]))
    (RecoveryBoundedColdCompile.serializer_entry z f hpre) (z.circuit_last f) hg ho ha
  have k:=keep 144 (by decide) (by decide) (by decide) (by decide)
  exact ⟨q,qr,qt,qh,qs,
    k.2.trans (congrFun (RecoveryBoundedColdCompile.fold_retained_words z f.next f.refs) 2),
    k.1.trans (RecoveryBoundedColdCompile.fold_retained_heads z f.next f.refs 2)⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdGraph

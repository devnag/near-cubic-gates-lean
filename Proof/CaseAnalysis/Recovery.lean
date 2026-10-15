import Proof.CaseAnalysis.RecoverySearchJoin
import Proof.CaseAnalysis.RecoverySourceGraphBudget
import Proof.CaseAnalysis.RecoverySearchGraphBudget

/-! Original full Tseitin construction followed by the same SAT query and
total canonical search. Only the hierarchy word and paid W are inputs. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedCold
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose SourceInterfaces
open ProjectionNormalization RecoveryRootRound BalancedCNFSATEncoding
open RecoveryScheduleEnvelope CloseoutRecoveryWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

abbrev oldTapes (k d : Nat):=RecoveryBoundedColdSourceGraph.tapes source k d
abbrev tapes (k d : Nat):=oldTapes source k d+790
abbrev program (k d CH Cpad : Nat) (code : List Bool):=
  RecoveryBoundedColdSearchJoin.program (RecoveryBoundedColdSourceGraph.machine source k d CH Cpad code)
def input (k d : Nat) (word : List Bool) (W : Nat) : Fin (tapes source k d)→List Bool:=
  Fin.addCases (m:=oldTapes source k d) (n:=790)
    (RecoveryBoundedColdSourceGraph.input source k d word W) (fun _=>[])
def payload (k d CH Cpad : Nat) (code : List Bool) {n : Nat} (x : BitInput n) (hpad : k+3 ≤ Cpad):=
  balancedCNFPayload (CircuitInputCNF.circuitInputFormula
    (RecoveryBoundedColdSourceGraph.circuit source k d CH Cpad code x hpad))
def total (k d CH Cpad : Nat) (code : List Bool) {n : Nat} (x : BitInput n):=
  BoundedOracleStructuralCircuit.descriptionWidth (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
    (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
def budget (k d CH Cpad : Nat) (code : List Bool) {n : Nat} (x : BitInput n) (W : Nat) (hpad : k+3 ≤ Cpad):=
  RecoveryBoundedColdSourceGraph.budget source k d CH Cpad code x W hpad+2+
    1099511627776*(RecoveryPrefixCold.radius (payload source k d CH Cpad code x hpad)
      (total source k d CH Cpad code x))^3

theorem run (k d CH Cpad : Nat) (code : List Bool) {n : Nat} (x : BitInput n)
    (clock : List Bool) (W : Nat) (hpad : k+3 ≤ Cpad)
    (hb : 0 < oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
    (hW : originalWorkspace (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
      (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
      (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
      (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length ≤ W)
    (hsource : (DedupBytes.fields (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length ≤ W)
    (htwo : 2^(PCPPNativeHierarchyNodes.width source k CH Cpad code x) ≤ W) :
    ∃ cost ≤ budget source k d CH Cpad code x W hpad,∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program source k d CH Cpad code) cost
        (initialConfiguration (program source k d CH Cpad code).base.machine
          (input source k d (frame (List.ofFn x)++frame clock) W)) final ∧
      (program source k d CH Cpad code).base.machine.halted final.control=true ∧
      readTapeBit (final.tapes ((369 : Fin 790).natAdd (oldTapes source k d))) 0=
        RecoveryOracle.correctedSat (RecoveryQuery.code true (payload source k d CH Cpad code x hpad) 0 0) ∧
      final.tapes ((787 : Fin 790).natAdd (oldTapes source k d))=
        frame (RecoveryPrefixBody.search true (payload source k d CH Cpad code x hpad)
          (total source k d CH Cpad code x) []) ∧
      (final.tapes ((356 : Fin 790).natAdd (oldTapes source k d))).length ≤ cost ∧
      final.heads ((356 : Fin 790).natAdd (oldTapes source k d))=0 ∧
      (∀ j : Fin 5,final.tapes ((RecoveryBoundedColdSourceGraph.graphSlots source k d (j.natAdd 1659)).castAdd 790)=
        RecoveryBoundedColdCompile.raw (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
          (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
          (RecoveryBoundedSelectorLoop.capacity W) (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
          (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length j ∧
        final.heads ((RecoveryBoundedColdSourceGraph.graphSlots source k d (j.natAdd 1659)).castAdd 790)=0) ∧
      final.tapes ((RecoveryBoundedColdSourceGraph.hierarchyPort source k d).castAdd 790)=
        frame (List.ofFn x)++frame clock ∧
      final.heads ((RecoveryBoundedColdSourceGraph.hierarchyPort source k d).castAdd 790)=0 ∧
      final.tapes ((RecoveryBoundedColdSourceGraph.wPort source k d).castAdd 790)=List.replicate W true ∧
      final.heads ((RecoveryBoundedColdSourceGraph.wPort source k d).castAdd 790)=0 ∧
      (∀ j : Fin 790,final.heads (j.natAdd (oldTapes source k d))=0) := by
  obtain ⟨r,hr,_hs,hp,hhp,ha,hha,scalars,hw,hhw,hWraw,hhW⟩:=
    RecoveryBoundedColdSourceGraph.cold_run source k d CH Cpad code x clock W hpad hb hW hsource htwo
  obtain ⟨cost,hcost,final,trace,halt,heads,flag,description,queryBound,queryHead,keep⟩:=
    RecoveryBoundedColdSearchJoin.run (RecoveryBoundedColdSourceGraph.machine source k d CH Cpad code)
      _ _ _ _ _ r hr hp ha hhp hha
  have retain (i : Fin (oldTapes source k d))
      (hp : i≠RecoveryBoundedSearchGraphDock.payloadPort (RecoveryBoundedColdSuppliers.tapes source k d))
      (ha : i≠RecoveryBoundedSearchGraphDock.arityPort (RecoveryBoundedColdSuppliers.tapes source k d)) :
      final.tapes (i.castAdd 790)=r.final.tapes i ∧ final.heads (i.castAdd 790)=r.final.heads i:=
    ⟨keep i hp ha,(congrFun heads _).trans (Fin.addCases_left i)⟩
  have hi:=retain (RecoveryBoundedColdSourceGraph.hierarchyPort source k d)
    (by rw [RecoveryBoundedColdSourceGraph.hierarchy_fresh];exact fun he=>
      RecoveryBoundedColdSourceGraph.graph_fresh source k d 1657 _ he.symm)
    (by rw [RecoveryBoundedColdSourceGraph.hierarchy_fresh];exact fun he=>
      RecoveryBoundedColdSourceGraph.graph_fresh source k d 144 _ he.symm)
  have hwi:=retain (RecoveryBoundedColdSourceGraph.wPort source k d)
    (by rw [RecoveryBoundedColdSourceGraph.w_fresh];exact fun he=>
      RecoveryBoundedColdSourceGraph.graph_fresh source k d 1657 _ he.symm)
    (by rw [RecoveryBoundedColdSourceGraph.w_fresh];exact fun he=>
      RecoveryBoundedColdSourceGraph.graph_fresh source k d 144 _ he.symm)
  refine ⟨cost,hcost,final,trace,halt,flag,description,queryBound,queryHead,?_,
    hi.1.trans hw,hi.2.trans hhw,hwi.1.trans hWraw,hwi.2.trans hhW,
    fun j=>(congrFun heads _).trans (Fin.addCases_right j)⟩
  intro j
  have hj:=retain (RecoveryBoundedColdSourceGraph.graphSlots source k d (j.natAdd 1659))
    (by intro he;have hv:=congrArg Fin.val he;change 1659+j.val=1657 at hv;omega)
    (by intro he;have hv:=congrArg Fin.val he;change 1659+j.val=144 at hv;omega)
  exact ⟨hj.1.trans (scalars j).1,hj.2.trans (scalars j).2⟩

end
end NearCubicWires.RepairSource.RecoveryBoundedCold

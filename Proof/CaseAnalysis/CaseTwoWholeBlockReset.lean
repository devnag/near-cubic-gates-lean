import Proof.CaseAnalysis.CaseTwoWholeBlockRun

/-! Paid reset of the complete original block, starting with every head at
zero. The hierarchy, converted descriptor and final address survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBlock
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def resetMachine (k D block CH Cpad : ℕ) (code : List Bool):=
  Rewind.machine (machine source a k D block CH Cpad code)
def resetInput (k D : ℕ) (hierarchy descriptor address : List Bool) : Fin (tapes source a k D+1)→List Bool:=
  Fin.addCases (input source a k D hierarchy descriptor address) (fun _ : Fin 1=>[])
theorem reset_run {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (D block : ℕ) (hD : 1≤D)
    (u : BitInput (request source a H Cpad hpad r oracle).arity)
    (clause : BitInput (a.output (request source a H Cpad hpad r oracle)).clauseBits)
    (pad pre tail : List Bool) (position : Bool)
    (hcap : (a.output (request source a H Cpad hpad r oracle)).clauseBits+pad.length=
      CloseoutLanguage.clauseWidth D (request source a H Cpad hpad r oracle).arity)
    (hpre : pre.length=block*((request source a H Cpad hpad r oracle).arity+
      CloseoutLanguage.clauseWidth D (request source a H Cpad hpad r oracle).arity+1)) :
    let address:=pre++AddressFields.word u clause pad position++tail
    let req:=request source a H Cpad hpad r oracle
    ∃ out,ClockJoin.ReadyRun
      (resetMachine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (2*budget source a H Cpad hpad r oracle D block u clause position pad.length+2)
      (resetInput source a k D (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address) out ∧
      out ((outputSlot source a k D).castAdd 1)=
        [(a.output req).assignment u ((a.output req).honestAuxiliary u)
          (OccurrenceBit.named a req (binaryAddress clause) position)] ∧
      ∀ i : Fin 3,out ((old source a k D (SourceBlock.old source a k (i.castAdd 5))).castAdd 1)=
        ![frame (HierarchySourceInput.hierarchyInput H r),frame (PCPPNative.descriptor oracle),frame address] i:=by
  dsimp only
  obtain ⟨p,hp,ps,pb,pr⟩:=block_run source a H Cpad hcoeff hpad r oracle D block hD
    u clause pad pre tail position hcap hpre
  obtain ⟨out,hr,ht,hh,hs,_⟩:=Rewind.reset_run
    (machine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier)) _ _ p hp
  have ready : ClockJoin.ReadyRun
      (resetMachine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (2*p.steps+2)
      (resetInput source a k D (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)
        (pre++AddressFields.word u clause pad position++tail)) out.final.tapes:=⟨out,hr,rfl,hh,hs.le⟩
  refine ⟨out.final.tapes,ClockJoin.enlarge _ _ _ _ _ ready ?_,(ht _).trans pb,?_⟩
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 ps) 2
  · intro i
    exact (ht _).trans (pr i)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBlock

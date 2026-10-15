import Proof.CaseAnalysis.CaseTwoXorFamilyInput

/-! Every fixed worker is the checked complete original source block, paid
head reset, and physical XOR step. The worker family is fixed before inputs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def workers (k D CH Cpad : ℕ) (code : List Bool) (block : ℕ) : Σ s,Machine (tapes source a k D) s:=
  ⟨_,XorBody.machine (WholeBlock.resetMachine source a k D block CH Cpad code)
    ((WholeBlock.outputSlot source a k D).castAdd 1)⟩
def sizes (k D CH Cpad : ℕ) (code : List Bool) (block : ℕ):=(workers source a k D CH Cpad code block).1
def programs (k D CH Cpad : ℕ) (code : List Bool) (block : ℕ) :
    Machine (tapes source a k D) (sizes source a k D CH Cpad code block):=
  (workers source a k D CH Cpad code block).2
def machine (k D copies CH Cpad : ℕ) (code : List Bool):=
  FixedFold.machine (sizes source a k D CH Cpad code) (programs source a k D CH Cpad code)
    (accumulator source a k D) copies

theorem worker_ready {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (D block : ℕ) (hD : 1≤D)
    (u : BitInput (WholeBlock.request source a H Cpad hpad r oracle).arity)
    (clause : BitInput (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits)
    (pad pre tail : List Bool) (position parity : Bool)
    (hcap : (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits+pad.length=
      CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity)
    (hpre : pre.length=block*((WholeBlock.request source a H Cpad hpad r oracle).arity+
      CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity+1)) :
    let address:=pre++AddressFields.word u clause pad position++tail
    let req:=WholeBlock.request source a H Cpad hpad r oracle
    let inputs:=words (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address
    ∃ out,ClockJoin.ReadyRun (programs source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier) block)
      (2*WholeBlock.budget source a H Cpad hpad r oracle D block u clause position pad.length+4)
      (FixedFold.bodyInput (accumulator source a k D) inputs parity) out ∧
      (∀ i : Fin 3,out (FixedFold.ports (accumulator source a k D) (accumulator_lower source a k D) i)=inputs i) ∧
      out (accumulator source a k D)=[xor parity
        ((a.output req).assignment u ((a.output req).honestAuxiliary u)
          (OccurrenceBit.named a req (binaryAddress clause) position))]:=by
  dsimp only
  obtain ⟨native,hr,hbit,hwords⟩:=WholeBlock.reset_run source a H Cpad hcoeff hpad r oracle D block hD
    u clause pad pre tail position hcap hpre
  obtain ⟨out,ho,hparity,keep⟩:=XorBody.ready
    (WholeBlock.resetMachine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier))
    ((WholeBlock.outputSlot source a k D).castAdd 1) _ _ native parity _ hr hbit
  refine ⟨out,?_,?_,hparity⟩
  · rw [←body_input]
    exact ho
  · intro i
    exact (keep ((WholeBlock.old source a k D (SourceBlock.old source a k (i.castAdd 5))).castAdd 1)).trans (hwords i)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorFamily

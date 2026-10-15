import Proof.CaseAnalysis.CaseTwoXorFamily
import Proof.CaseAnalysis.CaseTwoXorMeaning

/-! Fixed-copy Case 2 execution on the actual final address. Every block
rebuilds the same original request, then contributes its unsigned honest bit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
open RecoveryPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def cost {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3≤Cpad)
    (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (D : ℕ) {target : ℕ} (point : BitInput target) (block : ℕ):=
  let req:=WholeBlock.request source a H Cpad hpad r oracle
  let cap:=CloseoutLanguage.clauseWidth D req.arity
  let offset:=block*(req.arity+cap+1)
  2*WholeBlock.budget source a H Cpad hpad r oracle D block
    (AddressWindow.field point offset req.arity)
    (AddressWindow.field point (offset+req.arity) (a.output req).clauseBits)
    (AddressWindow.read point (offset+req.arity+cap)) (cap-(a.output req).clauseBits)+4

theorem run {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (D copies : ℕ) (hD : 1≤D) {target : ℕ} (point : BitInput target)
    (hcb : (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits≤
      CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity)
    (hfit : copies*((WholeBlock.request source a H Cpad hpad r oracle).arity+
      CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity+1)≤target) :
    let req:=WholeBlock.request source a H Cpad hpad r oracle
    let inputs:=words (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) (List.ofFn point)
    ∃ out,ClockJoin.ReadyRun
      (machine source a k D copies H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (FixedFold.budget (cost source a H Cpad hpad r oracle D point) copies)
      (FixedFold.initial (tapes source a k D) copies inputs) out ∧
      (∀ i : Fin 3,out (FixedFold.low (tapes source a k D) copies (i.castAdd 1))=inputs i) ∧
      out (FixedFold.low (tapes source a k D) copies 3)=
        [padCore (xorPower (CloseoutLanguage.paddedUnsigned (a.output req) hcb) copies) hfit point]:=by
  dsimp only
  let req:=WholeBlock.request source a H Cpad hpad r oracle
  let cap:=CloseoutLanguage.clauseWidth D req.arity
  let width:=req.arity+cap+1
  let inputs:=words (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) (List.ofFn point)
  let seed:=CloseoutLanguage.paddedUnsigned (a.output req) hcb
  let bit:=fun n=>seed (AddressWindow.field point (n*width) width)
  have hworkers : ∀ n<copies,∀ parity,∃ out,
      ClockJoin.ReadyRun (programs source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier) n)
        (cost source a H Cpad hpad r oracle D point n)
        (FixedFold.bodyInput (accumulator source a k D) inputs parity) out ∧
      (∀ i : Fin 3,out (FixedFold.ports (accumulator source a k D) (accumulator_lower source a k D) i)=inputs i) ∧
      out (accumulator source a k D)=[xor parity (bit n)]:=by
    intro n hn parity
    let offset:=n*width
    have hwindow : offset+width≤target:=by
      have h:=Nat.mul_le_mul_right width (Nat.succ_le_of_lt hn)
      rw [Nat.succ_mul] at h
      exact h.trans hfit
    have fields:=AddressWindow.fields point offset req.arity (a.output req).clauseBits cap hcb hwindow
    have hcapLocal : (a.output req).clauseBits≤cap:=hcb
    obtain ⟨out,hr,hw,hp⟩:=worker_ready source a H Cpad hcoeff hpad r oracle D n hD
      (AddressWindow.field point offset req.arity)
      (AddressWindow.field point (offset+req.arity) (a.output req).clauseBits)
      (AddressWindow.padding point offset req.arity (a.output req).clauseBits cap)
      (AddressWindow.pre point offset) (AddressWindow.tail point offset width)
      (AddressWindow.read point (offset+req.arity+cap)) parity
      (by simp only [AddressWindow.padding,List.length_ofFn];exact Nat.add_sub_of_le hcapLocal)
      (by simp only [AddressWindow.pre,List.length_ofFn];rfl)
    rw [←fields] at hr hw
    simp only [AddressWindow.padding,List.length_ofFn] at hr
    have semantic:=AddressWindow.padded_value (a.output req) point offset cap hcb
    refine ⟨out,hr,hw,?_⟩
    change out (accumulator source a k D)=
      [xor parity (CloseoutLanguage.paddedUnsigned (a.output req) hcb
        (AddressWindow.field point offset (req.arity+cap+1)))]
    rw [semantic]
    exact hp
  obtain ⟨out,hr,fields⟩:=FixedFold.run
    (sizes source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (programs source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (accumulator source a k D) (accumulator_lower source a k D) inputs
    (cost source a H Cpad hpad r oracle D point) bit copies hworkers
  have meaning:=FixedFold.padded_xor seed point hfit bit (by intro block;rfl)
  refine ⟨out,hr,fields.words,?_⟩
  exact fields.parity.trans (congrArg (fun b=>[b]) meaning)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorFamily

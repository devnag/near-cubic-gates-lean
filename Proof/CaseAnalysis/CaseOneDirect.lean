import Proof.CaseAnalysis.HierarchyRequestBound
import Proof.Amplification.RecoveryCaseOnePaddedBitInput
import Proof.Amplification.RecoveryPrefixPrepareCall

/-! The common recovery program's direct Case1 worker. Genuine original
input produces the hierarchy request on the existing builder's output tape;
that tape is the original padded bit program's input. The requested address
is retained on its actual input port. No external wrapper is built or parsed. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOneDirect
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)

def tapes (k : Nat) := CloseoutHierarchyRequest.tapes k + RecoveryCaseOnePaddedBit.tapes source amp k
def old (k : Nat) (i : Fin (CloseoutHierarchyRequest.tapes k)) : Fin (tapes source amp k) :=
  i.castAdd (RecoveryCaseOnePaddedBit.tapes source amp k)
def bank (k : Nat) (i : Fin (RecoveryCaseOnePaddedBit.tapes source amp k)) : Fin (tapes source amp k) :=
  if i.val = 0 then old source amp k (CloseoutHierarchyRequest.fresh k 0)
  else i.natAdd (CloseoutHierarchyRequest.tapes k)
def input (k : Nat) (bits address : List Bool) : Fin (tapes source amp k) → List Bool :=
  Fin.addCases (CloseoutHierarchyRequest.input k bits)
    (RecoveryCaseOnePaddedBit.input source amp k [] address)

theorem old_injective (k : Nat) : Function.Injective (old source amp k) := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes source amp k) => i.val) h)
theorem bank_injective (k : Nat) : Function.Injective (bank source amp k) := by
  intro a b h
  have hv := congrArg Fin.val h
  have hr := (CloseoutHierarchyRequest.fresh k 0).isLt
  apply Fin.ext
  dsimp only [bank] at hv
  split_ifs at hv <;> simp only [old, Fin.val_castAdd, Fin.val_natAdd] at hv <;> omega
theorem old_bank_ne (k : Nat) (i : Fin (CloseoutHierarchyRequest.tapes k))
    (j : Fin (RecoveryCaseOnePaddedBit.tapes source amp k)) (hj : j.val ≠ 0) :
    old source amp k i ≠ bank source amp k j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [bank, hj, if_false, old, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

def ports (k : Nat) : Ports (tapes source amp k) where
  twoTapes := by
    have h := (RecoveryCaseOnePaddedBit.ports source amp k).twoTapes
    unfold tapes
    omega
  outputTape := bank source amp k (RecoveryCaseOnePaddedBit.ports source amp k).outputTape
  outputFresh := by
    have h := (RecoveryCaseOnePaddedBit.ports source amp k).outputFresh
    simp only [bank, h, if_false, Fin.val_natAdd]
    omega
  queryTape := bank source amp k (RecoveryCaseOnePaddedBit.ports source amp k).queryTape
  queryFresh := by
    have h := (RecoveryCaseOnePaddedBit.ports source amp k).queryFresh
    simp only [bank, h, if_false, Fin.val_natAdd]
    omega

def first (k C : Nat) :=
  RecoveryFocus.machine (old source amp k) (CloseoutHierarchyRequest.machine k C)
def pieces (k C Cpad : Nat) (code : List Bool) : Fin 2 → Piece (tapes source amp k) :=
  ![ordinary (first source amp k C), focused
    (RecoveryCaseOnePaddedBit.program source amp k C Cpad code) (bank source amp k)]
def next (k C Cpad : Nat) (code : List Bool) (j : Fin 2)
    (_ : Fin (pieces source amp k C Cpad code j).states)
    (_ : Fin (tapes source amp k) → Bool) : Option (Fin 2) :=
  if j = 0 then some 1 else none
def program (k C Cpad : Nat) (code : List Bool) :=
  (ports source amp k).program
    (graph (pieces source amp k C Cpad code) 0 (next source amp k C Cpad code))

theorem assembled_bank (k : Nat) (bits address word : List Bool)
    (out : Fin (CloseoutHierarchyRequest.tapes k) → List Bool)
    (hword : out (CloseoutHierarchyRequest.fresh k 0) = word)
    (j : Fin (RecoveryCaseOnePaddedBit.tapes source amp k)) :
    install (old source amp k) (input source amp k bits address) out (bank source amp k j) =
      RecoveryCaseOnePaddedBit.input source amp k word address j := by
  by_cases hj : j.val = 0
  · simp only [bank, if_true, install_slot _ (old_injective source amp k),
      RecoveryCaseOnePaddedBit.input_lookup, hj, if_true]
    exact hword
  · rw [install_other _ _ _ _ (fun i => old_bank_ne source amp k i j hj)]
    simp only [bank, if_false, input, Fin.addCases_right,
      RecoveryCaseOnePaddedBit.input_lookup, hj, if_false]

def budget {c d k target : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n => n^(k + 2))) (Cpad : Nat) (hpad : k + 3 ≤ Cpad)
    (r : InputRequest)
    (hn : (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).arity ≤ target)
    (address : BitInput target) :=
  CloseoutHierarchyRequest.budget k H.coefficient (List.ofFn r.2) + 2 +
    RecoveryCaseOnePaddedBit.budget source amplifier H Cpad hpad r hn address

theorem direct_ready {c d k target : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n => n^(k + 2))) (Cpad : Nat) (hpad : k + 3 ≤ Cpad)
    (r : InputRequest)
    (hn : (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).arity ≤ target)
    (address : BitInput target) :
    ∃ cost ≤ budget source amplifier H Cpad hpad r hn address, ∃ out,
      Ready RecoveryOracle.correctedSat
        (program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier))
        cost (input source amplifier.constructor.program k (List.ofFn r.2) (List.ofFn address)) out ∧
      out (ports source amplifier.constructor.program k).outputTape =
        frame (RecoveryPipeline.padCore
          (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).function hn address).toNat.bits := by
  obtain ⟨request, hr, hw⟩ := CloseoutHierarchyRequest.request_run H (List.ofFn r.2)
  let ambient := input source amplifier.constructor.program k (List.ofFn r.2) (List.ofFn address)
  let a := install (old source amplifier.constructor.program k) ambient request
  have hf := hr.focus (old source amplifier.constructor.program k)
    (old_injective source amplifier.constructor.program k) ambient (fun i => Fin.addCases_left i)
  obtain ⟨ca, hca, ha⟩ := RecoveryPrefixCold.ordinary_ready
    (o := RecoveryOracle.correctedSat) (ports source amplifier.constructor.program k)
    (first source amplifier.constructor.program k H.coefficient) _ _ hf
  obtain ⟨cb, hcb, answer, hb, hv⟩ :=
    RecoveryCaseOnePaddedBit.bit_ready source amplifier H Cpad hpad r hn address
  have hword : request (CloseoutHierarchyRequest.fresh k 0) =
      HierarchySourceInput.hierarchyInput H r := by
    simpa only [List.length_ofFn, HierarchySourceInput.hierarchyInput] using hw
  have hlast := hb.focus (ports source amplifier.constructor.program k)
    (bank source amplifier.constructor.program k) (bank_injective source amplifier.constructor.program k)
    rfl a (assembled_bank source amplifier.constructor.program k _ _ _ request hword)
  have ta := ha.call (ports source amplifier.constructor.program k)
    (pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 0
    (next source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    0 1 (by intro q; rfl)
  have tb := hlast.stop (ports source amplifier.constructor.program k)
    (pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 0
    (next source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    1 (by intro q; rfl)
  have ht := trans ta tb
  refine ⟨(ca + 1) + (cb + 1), ?_, _, ⟨_, ht, ?_, fun _ => rfl, rfl⟩, ?_⟩
  · unfold budget
    omega
  · simp [program, Ports.program, graph, RecoveryCalls.machine, RecoveryCalls.stopped]
  · exact (install_slot _ (bank_injective source amplifier.constructor.program k) _ _
      (RecoveryCaseOnePaddedBit.ports source amplifier.constructor.program k).outputTape).trans hv

end
end NearCubicWires.RepairSource.CloseoutCaseOneDirect

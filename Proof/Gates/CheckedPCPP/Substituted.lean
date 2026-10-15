import Proof.Gates.CheckedPCPP.SubstitutedDescriptor
import Proof.Amplification.RecoveryCaseOnePaddedBitRun
import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyActual
import Proof.Hierarchy.HierarchyStreamReady
import Proof.PCP.PCPPSubstitutionCircuit
import Proof.PCP.PCPPRequestSourceInput

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization

noncomputable section

namespace Substituted

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def width (k : ℕ) := PCPPNativeHierarchyNodes.slots source k 72
def size (k : ℕ) := PCPPNativeHierarchyNodes.slots source k 91
def index (k : ℕ) := PCPPNativeHierarchyNodes.slots source k 89
def native (k CH Cpad : ℕ) (code : List Bool) :=
  consumer (PCPPNativeHierarchyNodes.machine source k CH Cpad code) (PCPPNativeHierarchyNodes.slots source k 177)
    (width source k) (size source k) (index source k)
def target (k : ℕ) := PCPPNativeClauseDescriptorConsumer.slots (width source k) (size source k) (index source k) 26

def machine (k CH Cpad : ℕ) (code : List Bool) :=
  AppendOutputFrame.machine (native source k CH Cpad code) (target source k)
def base (k : ℕ) := PCPPNativeClauseDescriptorConsumer.tapes (PCPPNativeHierarchyNodes.tapes source k)
def tapes (k : ℕ) := (base source k + 2) + 2
/-- The tape holding `frame (descriptor D_B.padToArity)` at the end. -/
def frameSlot (k : ℕ) : Fin (tapes source k) := (0 : Fin 2).natAdd (base source k + 2)
/-- The entry bank: `frame h ++ frame d` on tape 0, every other tape empty. -/
def input (k : ℕ) (hierarchy oracle : List Bool) :=
  AppendOutputFrame.input (PCPPNativeClauseDescriptorConsumer.input
    (PCPPNativeHierarchyNodes.input source k hierarchy oracle))

theorem input_word (k : ℕ) (hierarchy oracle : List Bool) :
    input source k hierarchy oracle =
      (fun i : Fin (tapes source k) => if i.val = 0 then PCPPNativeInputFields.word hierarchy oracle else []) := by
  unfold input AppendOutputFrame.input AppendOutputLength.input PCPPNativeClauseDescriptorConsumer.input
  rw [PCPPNativeHierarchyNodes.input_word]
  have h0 : 0 < PCPPNativeHierarchyNodes.tapes source k := by
    have := (PCPPNativeHierarchyNodes.slots source k 0).isLt
    omega
  repeat' apply PCPPRequestSource.single_input_from (by first | positivity | exact h0 | (unfold PCPPNativeClauseDescriptorConsumer.tapes; omega))
  rfl

/-- The budget, in the emitter's own (normalized) width. -/
def budget {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2)) :=
  let c := PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
    oracle
  2 * consumerBudget c (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle) +
    4 * (PCPPNative.descriptor c.padToArity).length + 7

/-- The run, with the emitter's circuit. -/
theorem native_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad)
    (hpad : k+3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2)) :
    ∃ out, ClockJoin.ReadyRun (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source H Cpad hpad r oracle)
      (input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)) out ∧
      out (frameSlot source k) = RepairOrdinary.frame (PCPPNative.descriptor
        (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
          oracle).padToArity) := by
  obtain ⟨nodes, hn, _, nt, nh, _, ni, _, ns, _, nw⟩ :=
    PCPPNativeHierarchyNodes.original_run source H Cpad hcoeff hpad r oracle
  have hn' : run (PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle)
      (PCPPNativeHierarchyNodes.input source k (HierarchySourceInput.hierarchyInput H r)
        (PCPPNative.descriptor oracle)) = some nodes := by
    rw [PCPPNativeHierarchyNodes.input_word]
    exact hn
  have hd := PCPPNativeHierarchyNodes.scalar_distinct source k
  obtain ⟨nativeResult, hr, hs, ht, hh⟩ := consumer_run
    (PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (PCPPNativeHierarchyNodes.slots source k 177) (width source k) (size source k) (index source k)
    hd.1 hd.2.1 hd.2.2 (PCPPNativeHierarchyNodes.forward source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    _ _ _ nodes hn' nt nh nw ns ni
  have forward := consumer_forward
    (PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (PCPPNativeHierarchyNodes.slots source k 177) (width source k) (size source k) (index source k)
    hd.1 hd.2.1 hd.2.2
  obtain ⟨result, rr, rt, rh, _, rs⟩ := PCPPNativeFrame.frame_run
    (native source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (target source k) forward _ _ nativeResult hr _ ht hh
  have ready : ClockJoin.ReadyRun (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (2 * nativeResult.steps + 4 * (PCPPNative.descriptor (PCPPNativeHierarchyNodes.circuit source k H.coefficient
        Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle).padToArity).length + 7)
      (input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)) result.final.tapes :=
    ⟨result, rr, rfl, rh, rs⟩
  exact ⟨result.final.tapes, ClockJoin.enlarge _ _ _ _ _ ready (by dsimp only [budget]; omega), rt⟩

/-- The native descriptor of a size-padded compact substituted circuit. -/
def substDescriptor {W Q R : ℕ} (o : BooleanCircuit W) (proj : Fin Q → Fin W → ProjectedRandomBit R)
    (f : ThreeCNF Q) : List Bool :=
  PCPPNative.descriptor (PCPPSubstitution.compactSubstituted o proj f).padToArity

/-- The native descriptor of the size-padded substituted circuit of a projection PCP at one input. -/
def descriptorAt {M : TimedDecisionMachine} {T : ℕ → ℕ} (p : ProjectionPCP M T) (r : InputRequest)
    (oracle : BooleanCircuit (p.nativeWidth r.1)) : List Bool :=
  substDescriptor oracle (p.queryAddressBits r.2) (p.decision r.2 (fun _ => false))

theorem descriptorAt_congr {M : TimedDecisionMachine} {T : ℕ → ℕ} {p q : ProjectionPCP M T} (h : p = q)
    (r : InputRequest) (o : BooleanCircuit (p.nativeWidth r.1)) (o' : BooleanCircuit (q.nativeWidth r.1))
    (ho : HEq o o') : descriptorAt p r o = descriptorAt q r o' := by
  subst h
  cases ho
  rfl

theorem descriptor_heq {n m : ℕ} (h : n = m) (o : BooleanCircuit n) (o' : BooleanCircuit m) (ho : HEq o o') :
    PCPPNative.descriptor o = PCPPNative.descriptor o' := by
  subst h
  cases ho
  rfl

/-- The global PCP of the recovery stack and the gate sources. -/
abbrev globalPCP {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad) :=
  RecoveryCaseOnePaddedBit.pcp source H Cpad hpad

theorem compact_idem {n r q : ℕ} (oracle : BooleanCircuit n) (projections : Fin q → Fin n → ProjectedRandomBit r)
    (formula : ThreeCNF q) :
    PCPPSubstitution.compactSubstituted oracle projections (compactThreeCNF formula) =
      PCPPSubstitution.compactSubstituted oracle projections formula := by
  simp only [PCPPSubstitution.compactSubstituted, compactThreeCNF, List.dedup_idem]

theorem substDescriptor_compact {W Q R : ℕ} (o : BooleanCircuit W) (proj : Fin Q → Fin W → ProjectedRandomBit R)
    (f : ThreeCNF Q) : substDescriptor o proj (compactThreeCNF f) = substDescriptor o proj f := by
  unfold substDescriptor
  rw [compact_idem]

/-- Compaction is idempotent: the global PCP and `hierarchyNormalized` give the same substituted circuit. -/
theorem descriptorAt_global {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (oracle : BooleanCircuit ((globalPCP source H Cpad hpad).nativeWidth r.1)) :
    descriptorAt (globalPCP source H Cpad hpad) r oracle =
      descriptorAt (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r) r oracle :=
  calc descriptorAt (globalPCP source H Cpad hpad) r oracle
      = substDescriptor (W := (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).nativeWidth
          r.1) oracle
          ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).queryAddressBits r.2)
          (compactThreeCNF ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).decision
            r.2 (fun _ => false))) := rfl
    _ = substDescriptor (W := (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).nativeWidth
          r.1) oracle
          ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).queryAddressBits r.2)
          ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).decision
            r.2 (fun _ => false)) := substDescriptor_compact _ _ _
    _ = descriptorAt (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r) r oracle := rfl

/-- The emitter's circuit is the substituted circuit of the per-input normalized PCP. -/
theorem native_descriptor_eq {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad)
    (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2)) :
    PCPPNative.descriptor (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) r.2 hpad oracle).padToArity =
      descriptorAt (RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad) r oracle := rfl

/-- The transported oracle has the same descriptor and the same substituted circuit. -/
theorem descriptorAt_transport {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (oracle : BooleanCircuit ((globalPCP source H Cpad hpad).nativeWidth r.1))
    (oracle' : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2)) (hheq : HEq oracle' oracle) :
    descriptorAt (RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad) r oracle' =
      descriptorAt (globalPCP source H Cpad hpad) r oracle := by
  rw [descriptorAt_global]
  exact descriptorAt_congr (RecoveryPCPFormulaResumeHierarchy.normalized_hierarchy source H Cpad hpad r) r
    oracle' oracle hheq

theorem global_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad)
    (hpad : k+3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit ((globalPCP source H Cpad hpad).nativeWidth r.1)) :
    ∃ fuel out, ClockJoin.ReadyRun (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier)) fuel
      (input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)) out ∧
      out (frameSlot source k) = RepairOrdinary.frame (descriptorAt (globalPCP source H Cpad hpad) r oracle) := by
  obtain ⟨_, hR, _⟩ := HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  obtain ⟨oracle', hheq⟩ : ∃ o : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2), HEq o oracle :=
    ⟨cast (congrArg BooleanCircuit hR.symm) oracle, cast_heq _ _⟩
  obtain ⟨out, hrun, hout⟩ := native_run source H Cpad hcoeff hpad r oracle'
  have hd : PCPPNative.descriptor oracle' = PCPPNative.descriptor oracle := descriptor_heq hR oracle' oracle hheq
  have hrun' : ClockJoin.ReadyRun (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source H Cpad hpad r oracle')
      (input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)) out := by
    rw [← hd]
    exact hrun
  have hval := (native_descriptor_eq source H Cpad hpad r oracle').trans
    (descriptorAt_transport source H Cpad hpad r oracle oracle' hheq)
  exact ⟨_, out, hrun', hout.trans (congrArg RepairOrdinary.frame hval)⟩

end Substituted

end

end NearCubicGates.Close.CheckedPCPP

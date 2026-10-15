import Proof.Gates.CheckedPCPP.Substituted
import Proof.Gates.CheckedPCPP.PolyClass
import Proof.Gates.CheckedPCPP.Dock
import Proof.PCP.PCPPNativeHierarchyCost
import Proof.PCP.PCPPNativeHierarchyEnvelope
import Proof.Foundations.BooleanCircuitSizePadding

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP.SubstitutedPoly

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicGates.Close.CheckedPCPP

noncomputable section

/-- The descriptor consumer's budget with minimum arity `0` (the shared `descriptor_budget` at minimum `0`). -/
theorem clause_budget0 {n : ℕ} (c : BooleanCircuit n) :
    PCPPNativeClauseDescriptor.budget 0 n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native) ≤
      9216 * (n + c.size + 1) ^ 2 + 2 * (c.nodes.flatMap PCPPRequestNodeSchema.native).length + 3 := by
  have he := PCPPNativeDescriptorBounds.entry_budget 0 n c.size
  have ht := PCPPNativeDescriptorTail.budget_bound (PCPPNativeColdMetadata.padding 0 n c.size) c.output.val
  have hi := c.output.isLt
  change c.output.val < c.size at hi
  have hp : PCPPNativeColdMetadata.padding 0 n c.size + c.output.val + 1 ≤ 0 + n + c.size + 1 := by
    unfold PCPPNativeColdMetadata.padding PCPPNativeColdMetadata.domain
    omega
  have hsq := Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hp 2)
  unfold PCPPNativeClauseDescriptor.budget
  simp only [Nat.zero_add] at he hsq ⊢
  omega

theorem natWord_len_le (x : ℕ) : (natWord x).length ≤ 2 * x + 3 := by
  simp only [natWord, WilliamsPublishedForm.framedNatBits, List.length_append, List.length_replicate,
    List.length_cons, WilliamsPublishedForm.fixedWidthNatBits, List.length_ofFn]
  have : natBitLength x ≤ x + 1 := by
    have := Nat.log_lt_self 2 (show x + 1 ≠ 0 by omega)
    have := Nat.log_mono_right (show x ≤ x + 1 by omega) (b := 2)
    simp only [natBitLength]; omega
  omega

theorem padSize_nodes {n : ℕ} (c : BooleanCircuit n) (k : ℕ) :
    (c.padSize k).nodes = c.nodes ++ List.replicate k (.const false) := by
  simp only [BooleanCircuit.padSize, BooleanDAGBuilder.finish, BooleanDAGBuilder.appendFalse_nodes,
    BooleanCircuit.toBuilder]

theorem padSize_output {n : ℕ} (c : BooleanCircuit n) (k : ℕ) : (c.padSize k).output.val = c.output.val := by
  simp only [BooleanCircuit.padSize, BooleanDAGBuilder.finish, BooleanDAGExtension.lift_val]

/-- The size-padded descriptor is at most linear in the arity, the size and the node bytes. -/
theorem pad_descriptor_len {n : ℕ} (c : BooleanCircuit n) :
    (PCPPNative.descriptor c.padToArity).length ≤
      13 * n + 4 * c.size + (c.nodes.flatMap PCPPRequestNodeSchema.native).length + 9 := by
  rw [PCPPNative.descriptor_eq]
  unfold BooleanCircuit.padToArity
  rw [padSize_output, padSize_nodes]
  have h1 := natWord_len_le n
  have h2 := natWord_len_le (c.nodes ++ List.replicate (n - c.size) (BooleanNode.const false)).length
  have h3 := natWord_len_le c.output.val
  have hi := c.output.isLt
  change c.output.val < c.size at hi
  have hpad : ((List.replicate (n - c.size) (BooleanNode.const false : BooleanNode n)).flatMap
      PCPPRequestNodeSchema.native).length = 9 * (n - c.size) := by
    induction (n - c.size) with
    | zero => rfl
    | succ k ih =>
      have h9 : (PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode n)).length = 9 := by
        simp [PCPPRequestNodeSchema.native, PCPPRequestNodeSchema.fields, natWord,
          WilliamsPublishedForm.framedNatBits, natBitLength, WilliamsPublishedForm.fixedWidthNatBits]
      simp only [List.replicate_succ, List.flatMap_cons, List.length_append, ih, h9]; ring
  simp only [List.length_append, List.length_replicate, List.flatMap_append] at h2 ⊢
  rw [hpad]
  have hs : c.size = c.nodes.length := rfl
  omega

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem budget_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad)
    (hpad : k+3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2)) :
    Substituted.budget source H Cpad hpad r oracle ≤
      20 * (HierarchyStreamCost.coefficient source H Cpad * (r.1 + 1) ^ HierarchyStreamCost.inputExponent source *
        (natBitLength (H.time r.1) + 1) ^ HierarchyStreamCost.logExponent source) +
      (20 * PCPPNativeResourceCost.counterCoefficient + 10 ^ 12) *
        (PCPPNativeHierarchySource.parameter source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
          oracle + 1) ^ 12 := by
  let p := PCPPNativeHierarchyNodes.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let R := PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let Q := PCPPNativeHierarchyNodes.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let c := PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle
  let Z := PCPPNativeHierarchySource.parameter source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 oracle
  let T := HierarchyStreamCost.coefficient source H Cpad * (r.1 + 1) ^ HierarchyStreamCost.inputExponent source *
    (natBitLength (H.time r.1) + 1) ^ HierarchyStreamCost.logExponent source
  let OB := PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle
  have hrp : p.width ≤ R := PCPPNativeHierarchyNodes.width_fits source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) r.2 hpad
  have hqp : p.queries ≤ Q := PCPPNativeHierarchyNodes.queries_fit source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) r.2 hpad
  have hz : 1 ≤ Z := by dsimp [Z, PCPPNativeHierarchySource.parameter, PCPPNativeResourceCost.sourceParameter]; omega
  have hL : (PCPPNative.descriptor oracle).length ≤ Z := by
    dsimp [Z, PCPPNativeHierarchySource.parameter, PCPPNativeResourceCost.sourceParameter]; omega
  have hcsize : c.size = PCPPNativeCount.nativeSize Q oracle.size (Codec.clauses p).length :=
    PCPPNativeCompactNodes.circuit_size p R Q hrp hqp r.2 oracle
  have carrier := PCPPNativeResourceCost.carrier_bound oracle p Q hrp hqp
  have hsize := (PCPPNativeResources.bounds R Q oracle.size (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length).2.2.2.1
  have hR' : R ≤ Z := by
    dsimp [R, Z, PCPPNativeHierarchySource.parameter, PCPPNativeResourceCost.sourceParameter]; omega
  have h13 : Z ≤ Z ^ 3 := Nat.le_self_pow (by decide) Z
  have hS : R + c.size + 1 ≤ 4098 * Z ^ 3 := by
    rw [hcsize]
    dsimp only [PCPPNativeResourceCost.carrier] at carrier
    change _ ≤ 4096 * Z ^ 3 at carrier
    dsimp only [R] at hsize
    omega
  have hcounter := PCPPNativeResourceCost.source_counter_budget oracle p Q hrp hqp
  change PCPPNativeCounterNodes.budget oracle p Q ≤ PCPPNativeResourceCost.counterCoefficient * Z ^ 12 at hcounter
  obtain ⟨native, hn, ns, _, head, _⟩ := PCPPNativeHierarchyNodes.original_run source H Cpad hcoeff hpad r oracle
  have hlen := SelectiveReset.prefix_head (prefix_of_run _ _ _ native hn).1 (PCPPNativeHierarchyNodes.slots source k 177)
  rw [head] at hlen
  change (c.nodes.flatMap PCPPRequestNodeSchema.native).length ≤ 0 + native.steps at hlen
  have hpaid : (c.nodes.flatMap PCPPRequestNodeSchema.native).length ≤ OB := by omega
  have hOB : OB = T + 4 * (PCPPNative.descriptor oracle).length + 7 + PCPPNativeCounterNodes.budget oracle p Q := rfl
  have hcl := clause_budget0 c
  have hpd := pad_descriptor_len c
  -- powers of Z
  have hZ1 : Z ≤ (Z + 1) ^ 12 := by
    calc Z ≤ Z + 1 := by omega
      _ = (Z + 1) ^ 1 := by ring
      _ ≤ (Z + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hZ3 : Z ^ 3 ≤ (Z + 1) ^ 12 :=
    (Nat.pow_le_pow_left (by omega : Z ≤ Z + 1) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hZ6 : (4098 * Z ^ 3) ^ 2 ≤ 4098 ^ 2 * (Z + 1) ^ 12 := by
    rw [mul_pow, ← pow_mul]
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega : Z ≤ Z + 1) 6).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hZ12 : Z ^ 12 ≤ (Z + 1) ^ 12 := Nat.pow_le_pow_left (by omega) 12
  have hsq : (R + c.size + 1) ^ 2 ≤ (4098 * Z ^ 3) ^ 2 := Nat.pow_le_pow_left hS 2
  have hcc := Nat.mul_le_mul_left PCPPNativeResourceCost.counterCoefficient hZ12
  unfold Substituted.budget consumerBudget
  change 2 * (6 * OB + 8 + PCPPNativeClauseDescriptor.budget 0 R c.size c.output.val
    (c.nodes.flatMap PCPPRequestNodeSchema.native)) + 4 * (PCPPNative.descriptor c.padToArity).length + 7 ≤
    20 * T + (20 * PCPPNativeResourceCost.counterCoefficient + 10 ^ 12) * (Z + 1) ^ 12
  have hR : R ≤ 4098 * Z ^ 3 := by omega
  have hcs : c.size ≤ 4098 * Z ^ 3 := by omega
  nlinarith

theorem frame_len' (w : List Bool) : (RepairOrdinary.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [RepairOrdinary.frame, ih]; ring

theorem bitLen_le_bits (v : ℕ) : natBitLength v ≤ v.bits.length + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp [natBitLength]
  · rw [Nat.size_eq_bits_len]
    unfold natBitLength
    have := Nat.lt_size_self v
    have : Nat.log 2 v < Nat.size v := by
      rw [Nat.lt_size]; exact Nat.pow_log_le_self 2 (by omega)
    omega

theorem size_le_desc {n : ℕ} (c : BooleanCircuit n) : c.size ≤ (PCPPNative.descriptor c).length := by
  rw [PCPPNative.descriptor_eq]
  have : ∀ nds : List (BooleanNode n), nds.length ≤ (nds.flatMap PCPPRequestNodeSchema.native).length := by
    intro nds
    induction nds with
    | nil => simp
    | cons nd nds ih =>
      have h1 : 1 ≤ (PCPPRequestNodeSchema.native nd).length := by
        simp only [PCPPRequestNodeSchema.native, List.length_append]
        simp only [natWord, WilliamsPublishedForm.framedNatBits, List.length_append, List.length_cons]
        omega
      simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega
  have := this c.nodes
  simp only [List.length_append]
  change c.nodes.length ≤ _
  omega

theorem budget_poly {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad)
    (hpad : k+3 ≤ Cpad) :
    PolyB (fun i : Σ r : InputRequest, BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) r.2) =>
        (HierarchySourceInput.hierarchyInput H i.1).length + (PCPPNative.descriptor i.2).length)
      (fun i => Substituted.budget source H Cpad hpad i.1 i.2) := by
  set S := fun i : Σ r : InputRequest, BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) r.2) =>
        (HierarchySourceInput.hierarchyInput H i.1).length + (PCPPNative.descriptor i.2).length with hSdef
  have hh : ∀ i : Σ r : InputRequest, BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2), i.1.1 + 1 ≤ S i + 1 ∧ natBitLength (H.time i.1.1) + 1 ≤ S i + 1 ∧
        i.2.size + (PCPPNative.descriptor i.2).length + 1 ≤ 2 * (S i + 1) := by
    intro i
    have hl : (HierarchySourceInput.hierarchyInput H i.1).length =
        2 * i.1.1 + 1 + (2 * (H.time i.1.1).bits.length + 1) := by
      simp only [HierarchySourceInput.hierarchyInput, List.length_append, frame_len', List.length_ofFn]
    have hb := bitLen_le_bits (H.time i.1.1)
    have hs := size_le_desc i.2
    simp only [hSdef]
    omega
  have pN : PolyB S (fun i => i.1.1 + 1) := (PolyB.add PolyB.size (PolyB.const 1)).mono (fun i => (hh i).1)
  have pB : PolyB S (fun i => natBitLength (H.time i.1.1) + 1) :=
    (PolyB.add PolyB.size (PolyB.const 1)).mono (fun i => (hh i).2.1)
  have pO : PolyB S (fun i => i.2.size + (PCPPNative.descriptor i.2).length + 1) :=
    (PolyB.mul (PolyB.const 2) (PolyB.add PolyB.size (PolyB.const 1))).mono (fun i => (hh i).2.2)
  have pT : PolyB S (fun i => HierarchyStreamCost.coefficient source H Cpad * (i.1.1 + 1) ^
      HierarchyStreamCost.inputExponent source * (natBitLength (H.time i.1.1) + 1) ^
      HierarchyStreamCost.logExponent source) :=
    PolyB.mul (PolyB.mul (PolyB.const _) (PolyB.pow pN _)) (PolyB.pow pB _)
  have pZ : PolyB S (fun i => PCPPNativeHierarchySource.parameter source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) i.1.2 i.2) := by
    refine (PolyB.mul (PolyB.mul (PolyB.mul (PolyB.const (HierarchyStreamCost.sizeCoefficient source H Cpad + 1))
      (PolyB.pow pN (HierarchySourceCost.inputExponent source))) (PolyB.pow pB (HierarchyStreamCost.logBase source)))
      pO).mono (fun i => ?_)
    have := PCPPNativeHierarchySource.parameter_bound source H Cpad hcoeff hpad i.1 i.2
    unfold PCPPNativeHierarchySource.oracleParameter at this
    exact this
  exact (PolyB.add (PolyB.mul (PolyB.const 20) pT)
    (PolyB.mul (PolyB.const (20 * PCPPNativeResourceCost.counterCoefficient + 10 ^ 12))
      (PolyB.pow (PolyB.add pZ (PolyB.const 1)) 12))).mono
    (fun i => budget_bound source H Cpad hcoeff hpad i.1 i.2)

theorem global_run_poly {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad)
    (hpad : k+3 ≤ Cpad) : ∃ C e : ℕ, ∀ (r : InputRequest)
      (oracle : BooleanCircuit ((Substituted.globalPCP source H Cpad hpad).nativeWidth r.1)),
      ∃ out, ClockJoin.ReadyRun (Substituted.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
        (C * ((HierarchySourceInput.hierarchyInput H r).length + (PCPPNative.descriptor oracle).length + 1) ^ e)
        (Substituted.input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)) out ∧
      out (Substituted.frameSlot source k) =
        RepairOrdinary.frame (Substituted.descriptorAt (Substituted.globalPCP source H Cpad hpad) r oracle) := by
  obtain ⟨C, e, hC⟩ := budget_poly source H Cpad hcoeff hpad
  refine ⟨C, e, fun r oracle => ?_⟩
  obtain ⟨_, hR, _⟩ := HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  obtain ⟨oracle', hheq⟩ : ∃ o : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2), HEq o oracle :=
    ⟨cast (congrArg BooleanCircuit hR.symm) oracle, cast_heq _ _⟩
  obtain ⟨out, hrun, hout⟩ := Substituted.native_run source H Cpad hcoeff hpad r oracle'
  have hd : PCPPNative.descriptor oracle' = PCPPNative.descriptor oracle :=
    Substituted.descriptor_heq hR oracle' oracle hheq
  have hb := hC ⟨r, oracle'⟩
  simp only at hb
  rw [hd] at hb hrun
  have hval := (Substituted.native_descriptor_eq source H Cpad hpad r oracle').trans
    (Substituted.descriptorAt_transport source H Cpad hpad r oracle oracle' hheq)
  exact ⟨out, ClockJoin.enlarge _ _ _ _ _ hrun hb, hout.trans (congrArg RepairOrdinary.frame hval)⟩

end

end NearCubicGates.Close.CheckedPCPP.SubstitutedPoly

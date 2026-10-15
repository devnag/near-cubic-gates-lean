import Proof.Wire_3_5.CompilerMachineEmitGlue

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Poly (cbits groupWord groupOf groupsRef)
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut cutWord signMagnitude)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The pool's label count -/

theorem densePool_flatten (a : DecompositionAlgorithm) {n : ℕ} (gates : List (SupportedNormalizedGate n))
    (side : List Bool) (width : ℕ) (flips : List (List Bool)) :
    (densePool a gates side width flips).flatten =
      (poolChildren a gates flips).map fun fe => pullDense side fe.1 width fe.2 := by
  induction flips with
  | nil => rfl
  | cons f fs ih =>
    unfold densePool poolChildren at *
    rw [List.flatMap_cons, List.flatMap_cons, List.flatten_append, List.map_append, ih]
    congr 1
    rw [← List.flatMap_def, List.map_flatMap]
    apply List.flatMap_congr
    intro g _
    rw [List.map_map]
    rfl

/-- The pool shape's label count is the number of pool children `P_ex`. -/
theorem shapeOf_flatten_length (a : DecompositionAlgorithm) {n : ℕ} (gates : List (SupportedNormalizedGate n))
    (side : List Bool) (width : ℕ) (flips : List (List Bool)) :
    (shapeOf (densePool a gates side width flips)).flatten.length = (poolChildren a gates flips).length := by
  unfold shapeOf
  rw [← List.map_flatten, List.length_map, densePool_flatten, List.length_map]

/-! ## The groups -/

theorem mem_xsOf {m : ℕ} {V : IntExpression ℕ} {x : ℕ × (ℤ × List (F2Poly ℕ))} (hx : x ∈ xsOf m V) : x.2 ∈ V := by
  unfold xsOf at hx
  obtain ⟨j, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact ht

/-- One group per counter value `j < 2^m` and term. -/
theorem xsOf_length (m : ℕ) (V : IntExpression ℕ) : (xsOf m V).length = 2 ^ m * V.length := by
  unfold xsOf
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_range]

theorem unionsM_length_le (pool : List (List SynEq)) (Q d : ℕ) (F : F2Poly ℕ) (hd : ∀ mono ∈ F, mono.length ≤ d) :
    (unionsM Q (oddMasksM pool F)).length ≤ Q * (pool.flatten.length + 1) ^ (Q * d) := by
  rw [(unionsM_perm Q _).length_eq, (combosAll_perm Q (oddMasksM_perm pool F)).length_eq]
  have e : (combosAll Q (oddMasks pool F)).length = (liftSyn pool 1 Q 0 (oddMasks pool F)).length := by
    rw [liftSyn_eq, List.length_map]
  rw [e, length_liftSyn]
  have hG := oddMasks_length_le pool d F hd
  calc ∑ j ∈ Finset.range Q, (oddMasks pool F).length.choose (j + 1)
      ≤ Q * max 1 (oddMasks pool F).length ^ Q := binLift_count_le Q _
    _ ≤ Q * ((pool.flatten.length + 1) ^ d) ^ Q := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        exact max_le (Nat.one_le_pow _ _ (by omega)) hG
    _ = Q * (pool.flatten.length + 1) ^ (Q * d) := by rw [← pow_mul, mul_comm d Q]

/-! ## The coefficient field -/

/-- A coefficient with `|c|·2^{Q'} ≤ 2^p` has at most `p` bits. -/
theorem bits_le (c Q p : ℕ) (hQ : 1 ≤ Q) (h : c * 2 ^ Q ≤ 2 ^ p) : (Nat.bits c).length ≤ p := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  have h2 : 2 ≤ 2 ^ Q := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ Q := Nat.pow_le_pow_right (by norm_num) hQ
  have h3 := Nat.mul_le_mul_left c h2
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · subst h0
    exact Nat.two_pow_pos p
  · omega

/-- **The coefficient field fits**: `|c|·2^{k−1}` (`1 ≤ k ≤ Q'`, `c ≠ 0`) has fewer than `p + 1` bits. -/
theorem bits_fit (c Q p k : ℕ) (hc0 : c ≠ 0) (hk1 : 1 ≤ k) (hkQ : k ≤ Q) (h : c * 2 ^ Q ≤ 2 ^ p) :
    k - 1 + (Nat.bits c).length < p + 1 := by
  rw [Nat.size_eq_bits_len]
  have hs : 0 < c.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hc0)
  have h1 : 2 ^ (c.size - 1) ≤ c := Nat.lt_size.mp (by omega)
  have h2 : 2 ^ k ≤ 2 ^ Q := Nat.pow_le_pow_right (by norm_num) hkQ
  have h3 : 2 ^ (c.size - 1 + k) ≤ 2 ^ p := by
    rw [pow_add]
    calc 2 ^ (c.size - 1) * 2 ^ k ≤ c * 2 ^ Q := Nat.mul_le_mul h1 h2
      _ ≤ 2 ^ p := h
  have h4 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp h3
  omega

/-! ## The emit stage -/

/-- The emit stage's cost: one group pass per `(counter value, term)` (`NX` groups of at most `Emax` entries). -/
def emitCost (NX Emax CB Q W P h width Lmax : ℕ) : ℕ :=
  NX * (groupCost Emax (CB + 1) (2 * entryCost Q W P h width Lmax CB + 2) + 2) + 1

variable (a : DecompositionAlgorithm)

/-- **The emit stage** (C3.6 stack + C3.7 emit): on a C3 v2 request satisfying `C3Req.Pre`, the group loop over the
compiler stages' output `groupsRef` writes the request's cut words `(c3v2Ref a R).flatMap (cutWord (p+1))` and one
count mark per stacked cut, within `emitCost` steps (`2^m·|V|` groups of at most `Q'(P_ex+1)^{Q'd}` entries, label
stacks of at most `h·Q'd` bits, coefficients of at most `p` bits). -/
theorem emit_run (R : C3Req) (hR : R.Pre a) (Pg post tlPL tz tsStale postQ postW BW CNT₀ : List Bool) (g0 : GSt)
    (cap capA capC capCut capCoef capEnt : ℕ)
    (hpostQ : readTapeBit postQ 0 = false) (hpostW : readTapeBit postW 0 = false)
    (hcap1 : 2 * (R.p + 1) + 1 ≤ cap) (hcapL : 2 * (R.P.h * R.P.Q * R.d) + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hcapE : 2 * (R.P.Q + (poolChildren a R.P.gates R.P.flips).length + 1) + 1 ≤ cap)
    (hcapS : appendCost 0 (2 * (R.P.width + R.P.width + 1)) 1 ≤ cap)
    (hA1 : mergeAllCost (2 * (R.P.width + R.P.width + 1))
      (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h ≤ capA)
    (hA2 : skipCost (2 * (R.P.width + R.P.width + 1))
      (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h ≤ capA)
    (hC : appendCost 0 (2 * (R.P.width + R.P.width + 1))
      (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h + R.P.h) ≤ capC)
    (hcut0 : cut0Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width) ≤ capCut)
    (hcut1 : cut1Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width) ≤ capCut)
    (hcoef : coefRawCost R.P.Q (R.p + 1) R.p ≤ capCoef)
    (hent : entryCost R.P.Q (R.p + 1) (poolChildren a R.P.gates R.P.flips).length R.P.h R.P.width
      (R.P.h * R.P.Q * R.d) R.p ≤ capEnt) :
    ∃ gf : GSt, gf.en.out = g0.en.out ++ (c3v2Ref a R).flatMap (cutWord (R.p + 1)) ∧
      gf.en.cnt = g0.en.cnt + (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length ∧
      Step (StreamController.machine groupBodyM 0)
        (emitCost (2 ^ R.m * R.V.length)
          (R.P.Q * ((poolChildren a R.P.gates R.P.flips).length + 1) ^ (R.P.Q * R.d)) R.p R.P.Q (R.p + 1)
          (poolChildren a R.P.gates R.P.flips).length R.P.h R.P.width (R.P.h * R.P.Q * R.d))
        (enBH Pg.length g0.en)
        (enBA (Pg ++ groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ false :: post)
          (((poolChildren a R.P.gates R.P.flips).flatMap (labRecs R.P.h R.P.side R.P.width)).flatMap frame ++ tlPL)
          (frame (List.replicate (R.p + 1) false) ++ tz)
          (streamTape (stackRecs R.P.h R.P.side R.P.width ([] : List (List Bool × ExactThresholdGate R.P.n))) tsStale)
          (List.replicate R.P.Q true ++ postQ) (List.replicate (R.P.width + R.P.width) true ++ postW) g0.rcb g0.rpar
          BW CNT₀ cap capA capC capCut capCoef capEnt g0.en)
        (enBH (Pg.length + (groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V).length) gf.en)
        (enBA (Pg ++ groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ false :: post)
          (((poolChildren a R.P.gates R.P.flips).flatMap (labRecs R.P.h R.P.side R.P.width)).flatMap frame ++ tlPL)
          (frame (List.replicate (R.p + 1) false) ++ tz)
          (streamTape (stackRecs R.P.h R.P.side R.P.width ([] : List (List Bool × ExactThresholdGate R.P.n))) tsStale)
          (List.replicate R.P.Q true ++ postQ) (List.replicate (R.P.width + R.P.width) true ++ postW) gf.rcb gf.rpar
          BW CNT₀ cap capA capC capCut capCoef capEnt gf.en) := by
  obtain ⟨_, _, hQ, _, hmono, hPN, _, hp, hc, _⟩ := hR
  have hDe : R.D a = densePool a R.P.gates R.P.side R.P.width R.P.flips := rfl
  have hflat : (shapeOf (R.D a)).flatten.length = (poolChildren a R.P.gates R.P.flips).length :=
    shapeOf_flatten_length a R.P.gates R.P.side R.P.width R.P.flips
  have hdeg : ∀ x ∈ xsOf R.m R.V, ∀ mono ∈ (selectBits x.2.2 x.1).flatten, mono.length ≤ R.d := by
    intro x hx mono hmn
    obtain ⟨f, hf, hmf⟩ := List.mem_flatten.mp hmn
    exact (hmono x.2 (mem_xsOf hx) f ((Poly.selectBits_sublist x.2.2 x.1).subset hf) mono hmf).1
  have hU : ∀ x ∈ xsOf R.m R.V, ∀ e ∈ unionsM R.P.Q (oddMasksM (shapeOf (R.D a)) (selectBits x.2.2 x.1).flatten),
      e.1 ≤ R.P.Q ∧ cnt (R.D a).flatten.length e.2 ≤ e.1 * R.d := fun x hx =>
    unionsM_cnt _ _ _ _ (oddMasksM_cnt _ _ _ _ (hdeg x hx))
  have b := groups_loop R.P.h R.P.width R.P.Q (R.p + 1) R.P.side (poolChildren a R.P.gates R.P.flips) (xsOf R.m R.V)
    (fun x => x.2.1) (fun x => decide ((selectBits x.2.2 x.1).length % 2 = 1))
    (fun x => unionsM R.P.Q (oddMasksM (shapeOf (R.D a)) (selectBits x.2.2 x.1).flatten))
    (fun x => groupOf R.P.Q (shapeOf (R.D a)) x.1 x.2)
    (by intro x; unfold groupOf; rw [hflat]; rfl)
    Pg post tlPL tz tsStale postQ postW BW CNT₀ g0 (R.P.h * R.P.Q * R.d)
    (R.P.Q * ((poolChildren a R.P.gates R.P.flips).length + 1) ^ (R.P.Q * R.d)) R.p
    cap capA capC capCut capCoef capEnt hpostQ hpostW
    (fun x hx e he => ⟨unionsM_pos _ _ e he, (hU x hx e he).1⟩)
    (by
      intro x hx e he
      have hl : (selAt (poolChildren a R.P.gates R.P.flips) e.2 (poolChildren a R.P.gates R.P.flips).length).length =
          cnt (R.D a).flatten.length e.2 := by
        rw [← denseLabels_length, hDe, denseLabels_eq, List.length_map]
      rw [hl]
      obtain ⟨h1, h2⟩ := hU x hx e he
      calc cnt (R.D a).flatten.length e.2 * R.P.h ≤ (R.P.Q * R.d) * R.P.h :=
            Nat.mul_le_mul_right _ (h2.trans (Nat.mul_le_mul_right _ h1))
        _ = R.P.h * R.P.Q * R.d := by ring)
    (Nat.lt_succ_of_le hp)
    (fun x hx e he hc0 => bits_fit x.2.1.natAbs R.P.Q R.p e.1 (Int.natAbs_ne_zero.mpr hc0) (unionsM_pos _ _ e he)
      (hU x hx e he).1 (hc x.2 (mem_xsOf hx)))
    (by
      intro x hx
      have := unionsM_length_le (shapeOf (R.D a)) R.P.Q R.d _ (hdeg x hx)
      rwa [hflat] at this)
    (fun x hx => bits_le x.2.1.natAbs R.P.Q R.p hQ (hc x.2 (mem_xsOf hx)))
    hcap1 hcapL hcapE hcapS hcap1 hA1 hA2 hC hcut0 hcut1 hcoef hent
  rw [← groupsRef_eq] at b
  refine ⟨_, ?_, ?_, b.enlarge (le_of_eq (by unfold emitCost; rw [xsOf_length]))⟩
  · rw [gfold_out]
    unfold c3v2Ref
    rw [hDe, emit_words_eq R.P.h R.P.width R.p R.P.side a R.P.gates R.P.flips R.m R.P.Q R.V hPN]
  · rw [gfold_cnt, emit_count_eq]

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit

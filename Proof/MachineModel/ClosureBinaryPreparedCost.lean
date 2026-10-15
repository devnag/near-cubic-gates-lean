import Proof.MachineModel.ClosureBinaryPreparedWriter
import Proof.MachineModel.ClosureRawFamilyCost
import Proof.MachineModel.ClosureCompactCacheCost

/-! The actual prepared binary writer is bounded from the original cache,
original polynomial degree, and lowered monomial count. No packet-specific
size premises or already relabelled input are assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryPreparedCost
open RepairOrdinary RepairRepresentation ExtIncidence
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput

def rawBound (C D K w : Nat) : Nat := 2^w*(D*(2^K*C+2)+2)+1

def envelope (q C D K w : Nat) : Nat :=
  q+C+D+K+w+2^K+4*(2^K*C+2)*(q+1)*(C+1)+
    (C*(D*(K+1))+(K+1))+rawBound C D K w+1

theorem stream_bound (P : List (List Nat)) (D B : Nat)
    (hd : ∀ m∈P,m.length ≤ D) (hc : ∀ m∈P,∀ c∈m,c < B) :
    (stream P).length ≤ P.length*(D*(B+1)+2)+1 := by
  have blocks (m : List Nat) (hm : ∀ c∈m,c < B) :
      (m.flatMap block).length ≤ m.length*(B+1) := by
    induction m with
    | nil => simp
    | cons c m ih =>
      have h := ih (fun d hd=>hm d (by simp [hd]))
      have hhead := hm c (by simp)
      simp only [List.flatMap_cons,List.length_append,block_length,List.length_cons]
      nlinarith
  have rows : (P.flatMap monomialWord).length ≤ P.length*(D*(B+1)+2) := by
    induction P with
    | nil => simp
    | cons m P ih =>
      have hm := (blocks m (hc m (by simp))).trans
        (Nat.mul_le_mul_right (B+1) (hd m (by simp)))
      have ht := ih (fun m hm=>hd m (by simp [hm])) (fun m hm=>hc m (by simp [hm]))
      simp only [List.flatMap_cons,List.length_append,monomialWord_length,List.length_cons]
      nlinarith
  simpa only [stream,List.length_append,List.length_singleton] using Nat.add_le_add_right rows 1

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) (C D w : Nat)

theorem child_bound (hcache : CompactBounds.radix a live occ ≤ C) :
    (childList a live occ).length ≤ C := by
  have h := DecompositionSource.children_le_output (childList a live occ)
  unfold CompactBounds.radix at hcache
  omega

theorem lower_stream_bound (hcache : CompactBounds.radix a live occ ≤ C)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost D P)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w) :
    (stream (CloseoutRowsUniversal.lower a live occ P)).length ≤ rawBound C D live.card w := by
  have hn := child_bound a live occ C hcache
  have hy : 1 ≤ 2^live.card := Nat.one_le_two_pow
  have hi : (childList a live occ).length+1 ≤ 2^live.card*C+2 := by nlinarith
  exact (stream_bound _ D _ (CloseoutRowsUniversal.lower_degree a live occ P D hdegree)
    (RawRelabelShape.lower_valid a live occ P)).trans (by unfold rawBound; gcongr)

theorem budget_bound (hcache : CompactBounds.radix a live occ ≤ C)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost D P)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w) :
    BinaryPreparedWriter.budget a live occ s harity P w D (rawBound C D live.card w) ≤
      2^120*(envelope q C D live.card w+1)^22*2^(w*(live.card+2)) := by
  letI := BinaryRequest.radix a live occ s harity D
  let X := envelope q C D live.card w
  let gs := BinaryPool.pool a live occ s harity
  let packets := BinaryWriter.packets a live occ s harity P
  have hx : X=q+C+D+live.card+w+2^live.card+
      4*(2^live.card*C+2)*(q+1)*(C+1)+
      (C*(D*(live.card+1))+(live.card+1))+rawBound C D live.card w+1 := rfl
  have hn := child_bound a live occ C hcache
  have hq : (s+1)/2+s/2 ≤ q := by
    rw [harity]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin q)
  have hp : gs.length ≤ 2^live.card*C+1 := by
    dsimp only [gs]
    rw [BinaryPool.pool_length,pool_length,liveList_length]
    gcongr
  have hps : (pool a live occ s harity).length ≤ 2^live.card*C+1 := by
    rw [pool_length,liveList_length]
    gcongr
  have hcacheBytes : (exactListWord gs).length ≤ 4*(2^live.card*C+2)*(q+1)*(C+1) := by
    have h := CompactCacheCost.cache_bytes gs
    change (exactListWord gs).length ≤ 4*(gs.length+1)*((s+1)/2+s/2+1)*
      (CompactBounds.radix a live occ+1) at h
    exact h.trans (Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left 4 (by omega)) (by omega)) (by omega))
  have hwidth : P1CompactNativeWidth.width gs (live.card+1) ≤
      C*(D*(live.card+1))+(live.card+1) := by
    change CompactBounds.radix a live occ*(min D gs.length*(live.card+1))+(live.card+1) ≤ _
    gcongr
    exact Nat.min_le_left _ _
  have hrawX : rawBound C D live.card w ≤ X := by
    have dom (A B : Nat) : B ≤ A+B+1 := by omega
    exact dom _ _
  have hraw : ∀ ms∈packets,(P1CompactNativeFamily.rawWord ms).length ≤ X := by
    intro ms hm
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
    rw [BinaryWriter.rawWord_cast]
    have h := CompactColdCost.actual_raw_word_bound a live occ s harity P D hdegree old ho
    have hr : (P1CompactNativeFamily.rawWord old).length ≤ rawBound C D live.card w :=
      h.trans (Nat.add_le_add_right (Nat.mul_le_mul hmon.le
        (Nat.add_le_add_right (Nat.mul_le_mul_left D (by omega)) 2)) 1)
    exact hr.trans hrawX
  have hfamily : packets.length=2^live.card := by
    dsimp only [packets]
    rw [BinaryWriter.packets_length,CompactColdCost.actual_family_length]
  have hpoolX : gs.length ≤ X := by
    have hdom : 2^live.card*C+1 ≤ 4*(2^live.card*C+2)*(q+1)*(C+1) := by
      have h1 := Nat.le_mul_of_pos_right (4*(2^live.card*C+2)) (by omega : 0 < q+1)
      have h2 := Nat.le_mul_of_pos_right (4*(2^live.card*C+2)*(q+1)) (by omega : 0 < C+1)
      omega
    omega
  have cold := CompactColdCost.budget_bound gs (live.card+1) w X packets
    (by omega) hpoolX (by omega) (by change CompactBounds.radix a live occ ≤ X; omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun ms hm=>(BinaryWriter.rows_lt a live occ s harity P w hmon ms hm).le)
    hraw (by omega)
  have result := RawFamilyCost.prepared_bound (childList a live occ).length (2^live.card)
    (rawBound C D live.card w) X w (live.card+1) (CompactColdFamily.budget gs (live.card+1) w packets)
    (by omega) (by omega) (by omega) cold
  simpa only [BinaryPreparedWriter.budget,show live.card+1+1=live.card+2 by omega,
    show 2*RawRelabelFamily.budget (childList a live occ).length (2^live.card)
      (rawBound C D live.card w)+2+1=
      2*RawRelabelFamily.budget (childList a live occ).length (2^live.card)
      (rawBound C D live.card w)+3 by omega] using result

end NearCubicWires.P1Closure.BinaryPreparedCost

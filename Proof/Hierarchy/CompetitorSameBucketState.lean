import Proof.Hierarchy.CompetitorSameBucketSignedMeaning
import Proof.Hierarchy.CompetitorMatrixPlaneTable

/-! Exact interoperability of the executed same-bucket dense bytes with
the existing indexed table state, and combined P/N fits at the SAME width.
The cross-bank bound is the actual table-loop invariant, with no wider bank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketState
open MatrixScoreBatch SupplierPrinter CompetitorSameBucketGroup CompetitorSameBucketEntries
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def state (r : Request) : CompetitorPlaneTable.State (r.U*r.U) where
  positive := fun i=>positive (atCell i.divNat.val (r.U+i.modNat.val) (entries r))
  negative := fun i=>negative (atCell i.divNat.val (r.U+i.modNat.val) (entries r))

theorem signed_meaning (r : Request) (i : Fin (r.U*r.U)) :
    ((state r).positive i : ℤ)-(state r).negative i=
      sameBucketContribution (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize)
        (weight r) i.divNat i.modNat := same_signed r i.divNat i.modNat

theorem canonical_cells (r : Request) :
    CompetitorPlaneTable.canonical (state r)=CompetitorSameBucketGroup.cells r.U (entries r) := by
  unfold CompetitorPlaneTable.canonical CompetitorPlaneTable.cells
  rw [List.ofFn_mul]
  have right : CompetitorSameBucketGroup.cells r.U (entries r)=
      (List.ofFn (fun row : Fin r.U=>List.ofFn (fun col : Fin r.U=>cell row.val (r.U+col.val) (entries r)))).flatten := by
    simp only [CompetitorSameBucketGroup.cells,List.ofFn_eq_map,List.flatMap_def]
  rw [right]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext col
  have hu:=dimension_positive r
  have hd : (row.val*r.U+col.val)/r.U=row.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hu,Nat.div_eq_of_lt col.isLt,Nat.zero_add]
  have hm : (row.val*r.U+col.val)%r.U=col.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt col.isLt]
  simp [CompetitorPlaneTable.cell,state,cell,Fin.divNat,Fin.modNat,hd,hm]

theorem dense_word (r : Request) (w : ℕ) :
    CompetitorPlaneStream.oldWords w (CompetitorPlaneTable.canonical (state r))=
      dense w r.U (entries r) := by rw [canonical_cells];rfl

theorem parts_bound (r : Request) (i : Fin (r.U*r.U)) :
    (state r).positive i+(state r).negative i ≤ CompetitorPlaneWidth.unit (natBitLength r.U) r.p := by
  have hg : r.Gates ≤ r.U :=
    (Nat.le_mul_self r.Gates).trans (r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U))
  have hu : r.U < 2^natBitLength r.U := Nat.lt_pow_succ_log_self (by decide) r.U
  have hb:=cell_parts_bound r i.divNat.val (r.U+i.modNat.val)
  have hm:=Nat.mul_le_mul_right (2^r.p) (hg.trans hu.le)
  change (state r).positive i+(state r).negative i ≤ r.Gates*2^r.p at hb
  exact hb.trans (by simpa only [CompetitorPlaneWidth.unit,pow_add] using hm)

theorem combined_total_fit (b p : ℕ) :
    (2*p+1)*CompetitorPlaneWidth.unit b p < 2^CompetitorPlaneWidth.width b p := by
  have hp : p < 2^p := Nat.lt_two_pow_self
  have hf : 2*p+1 < 2^(p+2) := by rw [pow_add];norm_num;nlinarith
  have hm:=Nat.mul_lt_mul_of_pos_right hf (show 0 < CompetitorPlaneWidth.unit b p by
    unfold CompetitorPlaneWidth.unit;positivity)
  have he : 2^(p+2)*CompetitorPlaneWidth.unit b p=2^CompetitorPlaneWidth.width b p := by
    unfold CompetitorPlaneWidth.unit CompetitorPlaneWidth.width
    rw [← pow_add]
    congr 1
    omega
  rwa [he] at hm

theorem combined_fit (r : Request) (cross : CompetitorPlaneTable.State (r.U*r.U))
    (hc : CompetitorPlaneTable.Bounded (natBitLength r.U) r.p (2*r.p) cross) :
    ∀ i,cross.positive i+(state r).positive i < 2^CompetitorSameBucketColdDense.width r ∧
      cross.negative i+(state r).negative i < 2^CompetitorSameBucketColdDense.width r := by
  intro i
  have hs:=parts_bound r i
  have hb:=hc i
  have hf:=combined_total_fit (natBitLength r.U) r.p
  change _ < 2^CompetitorSameBucketColdDense.width r at hf
  constructor <;> nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketState

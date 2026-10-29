import SourceAdapters.RAMACSP.GenItemsInput
import SourceAdapters.RAMACSP.GenItemsSpec
import SourceAdapters.RAMACSP.GenTCoord
import SourceAdapters.RAMACSP.CheckDegree
import SourceAdapters.Routing.TermsMachineMatrix

/-!
# The input-record block (B5) at the instance's coordinate rows

Paper: (B5) of `def:event-trace`, "Input subspace" in
`app:affine-embedding`, and `lem:generator`. The item printer uses coordinate
polynomials for input-address bits and retains the zero equations on dummy
records; the direct input clause supplies the input value bits.

`mask_bridge`: the `f`-bit block `j·mH + r` of the coordinate word of `Joins/CoordinateArray` (held in `vD`) is the
reduced mask of `c_{j,r}`, the constant `termsMask` writes (via `Joins/TermsCircuit`'s array and its packing,
`Routing.TermsMachine.packed_coordinates`, `coordMasks_get`). Hence `lamP` prints `λ_j` exactly as the item stream
writes `termsLam j` (`den_lamP_terms`), and `den_b5`: the block prints the (B5) items of `machineItems`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary
open Polynomial

variable {G : Glob} (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])
  (hI : NearCubicGates.Published.Shoup.IrreducibleChoice irrPoly)

include hI in
/-- With an irreducible choice of degree `f`, the modulus condition holds at every request. -/
theorem modulusGood (r : ClockRequest) : ModulusGood V irrPoly r := by
  have hf := domExp_add_two_le_fieldExp V r.2
  obtain ⟨hi, hd⟩ := hI (fieldExp V r.2) (by omega)
  have he := baseIrr_eq V irrPoly r hd
  exact ⟨he ▸ hi, he ▸ hd⟩

attribute [local irreducible] ownLayout baseIrr in
/-- **The coordinate array in `vD` holds the masks of the constants of `λ_j`.** -/
theorem mask_bridge (r : ClockRequest) (hM : ModulusGood V irrPoly r) (j rr : ℕ)
    (hj : j < (ownLayout V r.2).m) (hr : rr < (ownLayout V r.2).m) :
    CanonicalBinary.bitsValue (Joins.coordWord (coordRequest V irrPoly r) (coordRequest_ok V irrPoly hI r)) /
        2 ^ ((j * (ownLayout V r.2).m + rr) * fieldExp V r.2) % 2 ^ fieldExp V r.2 =
      termsMask (termsRequest V irrPoly r hM) (termsRequest_ok V irrPoly r hM)
        (termsCoeff (termsRequest V irrPoly r hM) (termsRequest_ok V irrPoly r hM) ⟨j, hj⟩ ⟨rr, hr⟩) := by
  have hf := domExp_add_two_le_fieldExp V r.2
  obtain ⟨-, hd⟩ := hI (fieldExp V r.2) (by omega)
  have hirr : WireExponent3_5.GF.toPoly (coordRequest V irrPoly r).irr = (termsRequest V irrPoly r hM).irr := by
    rw [coordRequest_toPoly V irrPoly r hd]
    exact (baseIrr_eq V irrPoly r hd).symm
  have hm : (coordRequest V irrPoly r).m = (termsRequest V irrPoly r hM).l.m := by
    show domExp V r.2 = (ownLayout V r.2).m; rw [ownLayout_m]
  rw [coordWord_terms (termsRequest V irrPoly r hM) (termsRequest_ok V irrPoly r hM) _ _ rfl hm hirr,
    Routing.TermsMachine.packed_coordinates]
  have hget := Routing.TermsMachine.coordMasks_get (termsRequest V irrPoly r hM) (termsRequest_ok V irrPoly r hM)
    ⟨j, hj⟩ ⟨rr, hr⟩
  have hp := packW_get (termsRequest V irrPoly r hM).f _
    (Routing.TermsMachine.coordMasks_lt (termsRequest V irrPoly r hM) (termsRequest_ok V irrPoly r hM))
    (j * (ownLayout V r.2).m + rr)
  exact hp.trans hget

attribute [local irreducible] ownLayout baseIrr in
/-- **`lamP` prints the row `λ_j` of the item stream.** -/
theorem den_lamP_terms (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (hc : CoordV V irrPoly hI r s)
    (j : ℕ) (hj : s.env vJ = j) (hjt : j < tau V r.2) :
    den G s lamP = (Joins.exprToks (termsMask (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
      (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)))
      (termsLam V irrPoly r (modulusGood V irrPoly hI r) j)).flatMap tokNums := by
  have hjm : j < (ownLayout V r.2).m := by rw [ownLayout_m]; have := tau_lt_domExp V r.2; omega
  have hf1 : 1 ≤ fieldExp V r.2 := by have := domExp_add_two_le_fieldExp V r.2; omega
  have hmm : (ownLayout V r.2).m = domExp V r.2 := ownLayout_m V r.2
  have hcapF := hR.capF
  have hdK := hR.dK
  have h8 : 2 ^ fieldExp V r.2 + 8 ≤ 2 ^ (fieldExp V r.2 + 8) := by
    rw [pow_add]; have := Nat.two_pow_pos (fieldExp V r.2); omega
  have hcap1 : (ownLayout V r.2).m * (ownLayout V r.2).m * fieldExp V r.2 + 8 ≤ G.cap := by
    rw [hmm]; have := cap_ge G; omega
  have hcap2 : 2 ^ fieldExp V r.2 + 8 ≤ G.cap := by omega
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨(modulusGood V irrPoly hI r).1⟩
  have hl := lamToks (F := Field2 (baseIrr V irrPoly r)) (termsMask (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
      (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r))) (Routing.TermsMachine.termsMask_zero _ _)
    (termsCoeff (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
      (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)) ⟨j, hjm⟩)
    (fun rr => CanonicalBinary.bitsValue (Joins.coordWord (coordRequest V irrPoly r) (coordRequest_ok V irrPoly hI r)) /
        2 ^ ((j * (ownLayout V r.2).m + rr) * fieldExp V r.2) % 2 ^ fieldExp V r.2)
    (fun rr => (mask_bridge V irrPoly hI r (modulusGood V irrPoly hI r) j rr.val hjm rr.isLt).symm)
  have hrow : termsLam V irrPoly r (modulusGood V irrPoly hI r) j = lamExpr (F := Field2 (baseIrr V irrPoly r)) (termsCoeff
      (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
      (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)) ⟨j, hjm⟩) := by
    dsimp only [termsLam]
    split
    · unfold termsCoeff termsRequest
      rfl
    · rename_i hn; exact absurd hjm hn
  have hd := den_lamP (G := G) j (ownLayout V r.2).m (fieldExp V r.2) _ _ hj (by rw [hmm]; exact hb.pv.mH) hb.pv.f hc
    (fun rr _ => rfl) hjm hf1 hcap1 hcap2 (by rw [hmm]; have := hR.mN; omega)
  have h2 := congrArg (fun e => (Joins.exprToks (termsMask (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
      (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r))) e).flatMap tokNums) hrow
  exact hd.trans (h2.trans hl).symm

/-! ## The block -/

theorem recCell_ok_gen (W K L τ β om dt : ℕ) (hw : W = 2 ^ om) (hτ : τ < W) (hβ : β ≤ τ)
    (hF : 32 + 3 * K + 2 * L ≤ 2 ^ dt) (f : RecField) (i : ℕ) (hi : i < f.width W τ) :
    (recCell (f, i)).Ok om dt :=
  recCell_ok ⟨W, K, L, τ, β⟩ K L om dt rfl rfl hw hτ hβ hF (f, i) hi

/-- **The printer of (B5).** -/
def b5P : P :=
  seqL [Pc.prog ⟨.w, .idx, inP .va⟩, Pc.prog ⟨.w, .idx, inP .ad⟩, Pc.prog ⟨.tau, .idx, inP .ts⟩,
    Pc.prog ⟨.one, .zero, inP .ph⟩, Pc.prog ⟨.one, .zero, inP .rgn⟩, Pc.prog ⟨.one, .zero, inP .act⟩,
    Pc.prog ⟨.one, .zero, inP .st⟩]

theorem coordV_setv {r : ClockRequest} {s : FS} (h : CoordV V irrPoly hI r s) (i : Var) (hi : i ≠ vD) (v : ℕ) :
    CoordV V irrPoly hI r (s.setv i v) := by
  unfold CoordV at h ⊢; rw [FS.setv_env, Function.update_of_ne (Ne.symm hi)]; exact h

theorem inV_of (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) :
    InV (G := G) (ownLayout V r.2) (wordExp V r.2) (tagExp V) (tau V r.2) (tau V r.2 - (tau V r.2 - inRecExp V r)) s := by
  obtain ⟨hcap, hmN, hmK, hk1, hkm⟩ := room_basic V r hR
  refine ⟨hb.lay, hb.pv.ta, hb.pv.T, hk1, hkm, ?_, Nat.sub_le _ _, hcap, hmN, hmK⟩
  show s.env 27 - (s.env 27 - (s.env 29 - s.env 25)) = _
  rw [hb.pv.ta, hb.pv.m, hb.pv.om]; rfl

theorem recSlotList_split (d : Dims) :
    recSlotList d = (List.range d.w).map (fun j => (RecField.va, j)) ++ (List.range d.w).map (fun j => (RecField.ad, j)) ++
      (List.range d.τ).map (fun j => (RecField.ts, j)) ++ [(RecField.ph, 0), (RecField.rgn, 0), (RecField.act, 0),
      (RecField.st, 0)] := by
  simp [recSlotList, recFields, RecField.width, List.flatMap_cons, List.append_assoc]

/-- The (B5) block for any per-slot item numbers `g`. -/
theorem den_b5_gen (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (hc : CoordV V irrPoly hI r s)
    (g : RecSlot → List ℕ)
    (hg : ∀ (f : RecField) (i : ℕ), i < f.width (wordW V r.2) (tau V r.2) → ∀ s' : FS, Base V r s' →
      CoordV V irrPoly hI r s' → s'.env vJ = i → den G s' (inP f) = g (f, i)) :
    den G s b5P = (recSlotList (dims (ownRam V r) (tau V r.2))).flatMap g := by
  have hdw := dims_w V r
  have hdt := dims_tau V r
  have piece : ∀ (f : RecField) (c : Cnt) (jk : JK)
      (hc : c.val (dims (ownRam V r) (tau V r.2)) ≤ f.width (wordW V r.2) (tau V r.2))
      (hjk : ∀ i < c.val (dims (ownRam V r) (tau V r.2)), jk.val i = i),
      den G s (Pc.prog ⟨c, jk, inP f⟩) =
        ((List.range (c.val (dims (ownRam V r) (tau V r.2)))).map fun j => (f, j)).flatMap g := by
    intro f c jk hcw hjk
    rw [List.flatMap_map]
    exact den_pc V r hR (CoordV V irrPoly hI r) (fun s i v h => coordV_setv V irrPoly hI
        (coordV_setv V irrPoly hI h vI (by decide) i) vJ (by decide) v) hb hc ⟨c, jk, inP f⟩ _
      (fun i hi s' hb' hc' hj => hg f i (by have := hi; simp only at this; omega) s' hb' hc'
        (by rw [hj]; exact hjk i hi))
  rw [recSlotList_split, hdw, hdt]
  simp only [b5P, den_seqL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append]
  rw [piece .va .w .idx (by simp [Cnt.val, hdw, RecField.width]) (fun _ _ => rfl),
    piece .ad .w .idx (by simp [Cnt.val, hdw, RecField.width]) (fun _ _ => rfl),
    piece .ts .tau .idx (by simp [Cnt.val, hdt, RecField.width]) (fun _ _ => rfl),
    piece .ph .one .zero (by simp [Cnt.val, RecField.width]) (fun i hi => by simp only [Cnt.val] at hi; simp [JK.val]; omega),
    piece .rgn .one .zero (by simp [Cnt.val, RecField.width]) (fun i hi => by simp only [Cnt.val] at hi; simp [JK.val]; omega),
    piece .act .one .zero (by simp [Cnt.val, RecField.width]) (fun i hi => by simp only [Cnt.val] at hi; simp [JK.val]; omega),
    piece .st .one .zero (by simp [Cnt.val, RecField.width]) (fun i hi => by simp only [Cnt.val] at hi; simp [JK.val]; omega)]
  simp [Cnt.val, hdw, hdt, List.append_assoc]

attribute [local irreducible] ownLayout baseIrr in
/-- **The (B5) block prints the input-record items of `machineItems`.** -/
theorem den_b5 (r : ClockRequest) [Fact (Irreducible (baseIrr V irrPoly r))] (hR : Room V r G) {s : FS}
    (hb : Base V r s) (hc : CoordV V irrPoly hI r s) :
    den G s b5P = (recSlotList (dims (ownRam V r) (tau V r.2))).flatMap (fun sl =>
      (inItems (ownLayout V r.2) (wordExp V r.2) (tau V r.2) (inRecExp V r)
        (termsLam V irrPoly r (modulusGood V irrPoly hI r)) sl).flatMap
        (itemNums (termsMask (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
          (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r))))) := by
  have hτ := tau_lt_wordW_all V r.2
  have hF := ftags_bound V
  have hwo : wordW V r.2 = 2 ^ wordExp V r.2 := wordW_eq V r.2
  have hm0 := Routing.TermsMachine.termsMask_zero (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
    (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r))
  have hm1 := Routing.TermsMachine.termsMask_one (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
    (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r))
  refine den_b5_gen V irrPoly hI r hR hb hc _ (fun f i hiw s' hb' hc' hj2 => ?_)
  have hok : (recCell (f, i)).Ok (wordExp V r.2) (tagExp V) :=
    recCell_ok_gen _ (regCount V) (codeLen V) _ (tau V r.2 - wordExp V r.2) _ _ hwo hτ (Nat.sub_le _ _) hF f i hiw
  have e := inItems_min (F := Field2 (baseIrr V irrPoly r)) (ownLayout V r.2) (wordExp V r.2) (tau V r.2)
    (inRecExp V r) (termsLam V irrPoly r (modulusGood V irrPoly hI r)) (f, i)
  have d := den_inP (F := Field2 (baseIrr V irrPoly r)) (termsMask
    (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
    (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r))) hm0 hm1 (inV_of V r hR hb')
    (termsLam V irrPoly r (modulusGood V irrPoly hI r)) f i hj2 hok
    (fun _ hit => den_lamP_terms V irrPoly hI r hR hb' hc' i hj2 hit)
  exact d.trans (congrArg (fun L => List.flatMap (itemNums (termsMask
    (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
    (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)))) L) e.symm)

end NearCubicGates.Adapters.RAMACSP.Gen.Items

import Proof.Wire_3_5.FinalPassFiltTabWalk

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
open NearCubicWires.RepairSource.VerifierDecoding Theorem25Completion NearCubicWires.WireExponent3_5.Filters

variable (cap : ℕ)

/-! ## The seed's walk -/

theorem baseSize_eq (P : GapParams) : P.baseSize = 2 ^ (wOf P.fieldBits P.labelBits * 128) := by
  unfold GapParams.baseSize
  rw [copySize_eq, wOf_seedW, ← pow_mul]

/-- The seed's walk over `2^{128 w}`: the same vertices. -/
theorem walk_transport {N N' t : ℕ} [NeZero N] [NeZero N'] (h : N = N') (e : MargulisWalkSample N t) :
    ∃ e' : MargulisWalkSample N' t, ∀ i, (e'.vertex i).1.val = (e.vertex i).1.val := by
  subst h
  exact ⟨e, fun _ => rfl⟩

/-! ## The table from the builder's word -/

theorem finRange_map_val {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.finRange n).map (fun i => f i.val) = (List.range n).map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem copyList_eq (P : GapParams) (X L : ℕ) :
    copyList (GF.firstPrimitive P.fieldBits) P.fieldBits P.labelBits P.prefixBits
      (tau (GF.firstPrimitive P.fieldBits) P.fieldBits) X L 128 =
      (List.finRange 128).map fun (j : Fin 128) => coefBits P X (j : ℕ) L := by
  unfold copyList
  rw [finRange_map_val 128 (fun j => coefBits P X j L)]
  apply List.map_congr_left
  intro j _
  exact coefOf_eq P X j L

/-- **The builder's word is the seed's table.** -/
theorem tableBits_eq (P : GapParams) (e : GapSeed P) (L : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1))
    (hvert : ∀ i, (sample.vertex i).1.val = (e.vertex i).1.val) :
    owOf (GF.firstPrimitive P.fieldBits) (tau (GF.firstPrimitive P.fieldBits) P.fieldBits) P.fieldBits P.labelBits
      P.prefixBits L 128 sample (2 * (P.errExp / 4) + 1) ++ [false] = tableWord (filterTable P e L) := by
  rw [filterTable_bits, tableWord, owOf]
  congr 1
  rw [List.flatMap_map]
  have e : (List.range (2 * (P.errExp / 4) + 1)).flatMap (fun i' => visitWord (copyList (GF.firstPrimitive P.fieldBits)
      P.fieldBits P.labelBits P.prefixBits (tau (GF.firstPrimitive P.fieldBits) P.fieldBits)
      (WalkTimeLoop.vertex sample i').1.val L 128)) =
      (List.finRange (2 * (P.errExp / 4) + 1)).flatMap (fun i => visitWord (copyList (GF.firstPrimitive P.fieldBits)
      P.fieldBits P.labelBits P.prefixBits (tau (GF.firstPrimitive P.fieldBits) P.fieldBits)
      (WalkTimeLoop.vertex sample i.val).1.val L 128)) := by
    have hr : List.range (2 * (P.errExp / 4) + 1) = (List.finRange (2 * (P.errExp / 4) + 1)).map (fun i => i.val) := by
      have := finRange_map_val (2 * (P.errExp / 4) + 1) id
      rw [List.map_id] at this
      exact this.symm
    rw [hr, List.flatMap_map]
  rw [e]
  apply List.flatMap_congr
  intro i _
  rw [copyList_eq]
  have hi : (i : ℕ) ≤ 2 * (P.errExp / 4) := by have := i.isLt; omega
  have hv : WalkTimeLoop.vertex sample i = sample.vertex i := by
    unfold WalkTimeLoop.vertex
    congr 1
    exact Fin.ext (by simp; omega)
  rw [hv, hvert]

/-! ## The block -/

theorem one_le_labelBits (P : GapParams) (hU : 1 ≤ P.cap) : 1 ≤ P.labelBits := by
  have h1 : 0 < P.prefixBits := Nat.clog_pos (by norm_num) (by omega)
  have h2 := prefixBits_le P
  omega

theorem one_le_fieldBits' (P : GapParams) : 1 ≤ P.fieldBits := by unfold GapParams.fieldBits; omega

/-- The trace mask word and the modulus word of the filter's field. -/
def tauWord (P : GapParams) : List Bool :=
  frame (binary P.fieldBits (tau (GF.firstPrimitive P.fieldBits) P.fieldBits))
def modWord (P : GapParams) : List Bool := frame (binary P.fieldBits (GF.firstPrimitive P.fieldBits))

/-- **Stage 6, the seed's filter table**: the builder writes `tableWord (filterTable P e L)`. The input
is the seed's walk (the vertex word and the walk's tapes of `sample`, a copy of `e` over `2^{128 w}`), the field's
words, the counts `m = fieldBits`, `ℓ = labelBits`, `a = prefixBits`, `L` in registers, and blank scratch; the output
tape ends with the table, its head at `0`. -/
theorem stage6_step (P : GapParams) (e : GapSeed P) (L c R LW : ℕ) (tail : List Bool) (hU : 1 ≤ P.cap)
    (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1))
    (hvert : ∀ i, (sample.vertex i).1.val = (e.vertex i).1.val)
    (hR : 2 * (wOf P.fieldBits P.labelBits * 128) + 1 ≤ R) (hLW : 2 * (wOf P.fieldBits P.labelBits * 128) + 1 ≤ LW)
    (hcap : 2 * (wOf P.fieldBits P.labelBits * 128) + 4 * P.labelBits + 2 * P.fieldBits + L + 10 ≤ c)
    (hO : (2 * (P.errExp / 4) + 1) * (128 * (2 * L + 2) + 2) + 12 < c) :
    Step builderM
      (2 * (P.errExp / 4) * (bodyCost P.fieldBits P.labelBits P.prefixBits L 128 R + 3) + 3 + 1 +
        lastCost P.fieldBits P.labelBits P.prefixBits L 128 (2 * (P.errExp / 4)))
      (Fin.addCases (loopH c P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
        (GF.firstPrimitive P.fieldBits) (tau (GF.firstPrimitive P.fieldBits) P.fieldBits) 128 R LW sample tail 0)
        (fun _ : Fin 1 => 1))
      (Fin.addCases (loopA c P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
        (GF.firstPrimitive P.fieldBits) (tau (GF.firstPrimitive P.fieldBits) P.fieldBits) 128 R LW sample tail 0)
        (fun _ : Fin 1 => CompareMachine.word (2 * (P.errExp / 4))))
      (Fin.addCases (m := 11 + 2 + 19) (n := 8)
        (wenc c (finalW P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
          (WalkTimeLoop.A R LW sample tail (2 * (P.errExp / 4)) 0) (tableWord (filterTable P e L)))).H
        (Fin.addCases (m := 7) (n := 1) (fun k => WalkTimeLoop.H (2 * (P.errExp / 4)) (2 * (P.errExp / 4)) k.succ)
          (fun _ => 1)))
      (Fin.addCases (m := 11 + 2 + 19) (n := 8)
        (wenc c (finalW P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
          (WalkTimeLoop.A R LW sample tail (2 * (P.errExp / 4)) 0) (tableWord (filterTable P e L)))).A
        (Fin.addCases (m := 7) (n := 1) (fun k => WalkTimeLoop.A R LW sample tail (2 * (P.errExp / 4)) k.succ)
          (fun _ => CompareMachine.word (2 * (P.errExp / 4))))) := by
  have h := builderStep c (GF.firstPrimitive P.fieldBits) (tau (GF.firstPrimitive P.fieldBits) P.fieldBits)
    P.fieldBits P.labelBits P.prefixBits L 128 (tauWord P) (modWord P) R LW sample tail hR hLW (by norm_num)
    (one_le_fieldBits' P) (one_le_labelBits P hU) (prefixBits_le P) rfl rfl hcap hO
  rw [tableBits_eq P e L sample hvert] at h
  exact h

end NearCubicWires.WireExponent3_5.FinalPass.Filt

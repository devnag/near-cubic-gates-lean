import Proof.Gates.Codec.FieldCircuit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-- The preconditions of `circuitW` on the start state `σ`. -/
structure CirPre (W o : Fin (ns + 1)) (A : Fin 18 ↪ Fin nr) (σ : WState ns nr) (q : ℕ) : Prop where
  hWo : W ≠ o
  hq : σ.val (A 6) = q
  hz : ∀ i : Fin 18, i ≠ 6 → i ≠ 13 → σ.val (A i) = 0
  ho : σ.sh o = (σ.st o).length
  cap1 : (σ.st W).length + q + 1 ≤ cap
  capO : σ.val (A 13) + 2 * (Interfaces.circuitWord (readCircuit q ((σ.st W).drop (σ.sh W))).1).length + q +
    7 * (σ.st W).length + 6 * natBitLength q + 20 ≤ cap

section Steps
variable {cap} {W o : Fin (ns + 1)} {A : Fin 18 ↪ Fin nr} {σ : WState ns nr} {q : ℕ}

theorem CirPre.zero (h : CirPre cap W o A σ q) (pos : ℕ) (out : List Bool) (kv c2 : ℕ) {i : Fin 18}
    (h6 : i ≠ 6) (h13 : i ≠ 13) (h14 : i ≠ 14) (h17 : i ≠ 17) : (shp W o A σ pos out kv c2).val (A i) = 0 := by
  rw [shp_other pos out kv c2 (A i) (Ane A h13) (Ane A h14) (Ane A h17)]; exact h.hz i h6 h13

theorem CirPre.six (h : CirPre cap W o A σ q) (pos : ℕ) (out : List Bool) (kv c2 : ℕ) :
    (shp W o A σ pos out kv c2).val (A 6) = q := by
  rw [shp_other pos out kv c2 (A 6) (Ane A (by decide)) (Ane A (by decide)) (Ane A (by decide))]; exact h.hq

/-- A count: `K := fieldLen`, head past the unary run. -/
theorem step_count (h : CirPre cap W o A σ q) (pos : ℕ) (out : List Bool) (hc : fieldLen (σ.st W) pos ≤ cap) :
    WExec cap (countW W (A 14)) (shp W o A σ pos out 0 0)
      (shp W o A σ (pos + fieldLen (σ.st W) pos + 1) out (fieldLen (σ.st W) pos) 0)
      (7 * fieldLen (σ.st W) pos + 3) := by
  have e := countW_spec cap W (A 14) (shp W o A σ pos out 0 0)
    (by rw [shp_K, shp_stW h.hWo, shp_shW h.hWo]; exact (Nat.zero_add _).symm ▸ hc)
  rw [shp_K, shp_stW h.hWo, shp_shW h.hWo, Nat.zero_add, shp_count h.hWo] at e
  exact e

/-- `writeNatM` prints the count `K`. -/
theorem step_write (h : CirPre cap W o A σ q) (pos : ℕ) (out : List Bool) (kv : ℕ)
    (hc : σ.val (A 13) + 2 * out.length + kv + 6 * natBitLength kv + 6 ≤ cap) :
    WExec cap (writeNatM o (AR A 14 (Or.inr rfl))) (shp W o A σ pos out kv 0)
      (shp W o A σ pos (out ++ natWord kv) kv 0) ((natBitLength kv + 10) * (100 * kv + 200)) := by
  have hR : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → (shp W o A σ pos out kv 0).val (AR A 14 (Or.inr rfl) i) = 0 := by
    intro i h0 h7
    rw [AR_val]
    fin_cases i <;> simp at h0 h7 <;> exact h.zero pos out kv 0 (by decide) (by decide) (by decide) (by decide)
  have e := writeNatM_spec cap o (AR A 14 (Or.inr rfl)) (shp W o A σ pos out kv 0) (hR 1 (by decide) (by decide))
    (hR 2 (by decide) (by decide)) (hR 3 (by decide) (by decide)) (hR 4 (by decide) (by decide))
    (hR 5 (by decide) (by decide)) (hR 6 (by decide) (by decide)) (shp_ho h.hWo h.ho pos out kv 0)
    (by
      have h0 : (shp W o A σ pos out kv 0).val (AR A 14 (Or.inr rfl) 0) = kv := shp_K pos out kv 0
      have h7 : (shp W o A σ pos out kv 0).val (AR A 14 (Or.inr rfl) 7) = σ.val (A 13) + 2 * out.length :=
        shp_OP pos out kv 0
      rw [h0, h7]; omega)
  have h0 : (shp W o A σ pos out kv 0).val (AR A 14 (Or.inr rfl) 0) = kv := shp_K pos out kv 0
  rw [h0] at e
  exact WExec.cast cap e (shp_app0 h.hWo pos out (natWord kv) kv 0) le_rfl

theorem step_dup (h : CirPre cap W o A σ q) (pos : ℕ) (out : List Bool) (kv : ℕ) (hc : kv ≤ cap) :
    WExec cap (dupR (A 14) (A 17) (A 16)) (shp W o A σ pos out kv 0) (shp W o A σ pos out kv kv) (18 * kv + 3) := by
  have e := dupR_spec cap (A 14) (A 17) (A 16) (Ane A (by decide)) (Ane A (by decide)) (Ane A (by decide))
    (shp W o A σ pos out kv 0) (h.zero pos out kv 0 (by decide) (by decide) (by decide) (by decide))
    (by rw [shp_K, shp_C]; omega)
  rw [shp_K, shp_C, Nat.zero_add, shp_setC] at e
  exact e

/-- `K := 0`. -/
theorem step_clear (_h : CirPre cap W o A σ q) (pos : ℕ) (out : List Bool) (kv : ℕ) (hc : kv ≤ cap) :
    WExec cap (WM.clear (A 14)) (shp W o A σ pos out kv 0) (shp W o A σ pos out 0 0) (3 * kv + 1) := by
  have e := wclear_spec cap (A 14) kv (shp W o A σ pos out kv 0) (shp_K pos out kv 0) (by rw [shp_K]; exact hc)
  rw [shp_setK] at e
  exact e

theorem CirPre.body (h : CirPre cap W o A σ q) {pos0 : ℕ} {out : List Bool} {kv m : ℕ} {τ : WState ns nr}
    (h1 : ∀ r, r ≠ A 13 → r ≠ A 17 → τ.val r = (shp W o A σ pos0 out kv m).val r) (j : Fin 18)
    (h6 : j ≠ 6) (h13 : j ≠ 13) (h14 : j ≠ 14) (h17 : j ≠ 17) : τ.val (A j) = 0 :=
  (h1 _ (Ane A h13) (Ane A h17)).trans (h.zero pos0 out kv m h6 h13 h14 h17)

/-- The gate loop: `m` gate fields from `pos0`. -/
theorem step_gates (h : CirPre cap W o A σ q) (pos0 : ℕ) (out : List Bool) (kv m : ℕ) (hm : m ≤ cap)
    (hc : σ.val (A 13) + 2 * out.length + 2 * (emitted (fun r => (readGate q ((σ.st W).drop r)).1) Interfaces.gateWord
        (fun r => gateEnd (σ.st W) r q) pos0 m).length + q + 4 * (σ.st W).length + 6 * natBitLength q + 12 ≤ cap) :
    WExec cap (repLoop (A 17) (gateW W o (AX A) (A 5) (AR A 6 (Or.inl rfl)) (A 15) (A 16)))
      (shp W o A σ pos0 out kv m)
      (shp W o A σ (iter (fun r => gateEnd (σ.st W) r q) pos0 m)
        (out ++ emitted (fun r => (readGate q ((σ.st W).drop r)).1) Interfaces.gateWord (fun r => gateEnd (σ.st W) r q)
          pos0 m) kv 0)
      (m * (fGateCost q (σ.st W).length + 4) + 1) := by
  set w := σ.st W with hw
  set gv : ℕ → NormalizedThresholdGate q := fun r => (readGate q (w.drop r)).1 with hgv
  set gn : ℕ → ℕ := fun r => gateEnd w r q with hgn
  have hbody : ∀ i < m, ∀ τ : WState ns nr,
      (∀ r, r ≠ A 13 → r ≠ A 17 → τ.val r = (shp W o A σ pos0 out kv m).val r) →
      τ.val (A 17) = m - i - 1 → τ.st W = (shp W o A σ pos0 out kv m).st W →
      τ.sh W = iter gn ((shp W o A σ pos0 out kv m).sh W) i → τ.sh o = (τ.st o).length →
      τ.val (A 13) = (shp W o A σ pos0 out kv m).val (A 13) +
        2 * (emitted gv Interfaces.gateWord gn ((shp W o A σ pos0 out kv m).sh W) i).length →
      WExec cap (gateW W o (AX A) (A 5) (AR A 6 (Or.inl rfl)) (A 15) (A 16)) τ
        (appendO (τ.seth W (gn (τ.sh W))) o (A 13) (marks (Interfaces.gateWord (gv (τ.sh W))))) (fGateCost q w.length) := by
    intro i hi τ h1 _ h3 h4 h5 h6
    rw [shp_stW h.hWo] at h3
    rw [shp_shW h.hWo] at h4 h6
    rw [shp_OP] at h6
    have hX : ∀ j : Fin 5, A ⟨j.val, by omega⟩ ≠ A 13 ∧ A ⟨j.val, by omega⟩ ≠ A 5 ∧ A ⟨j.val, by omega⟩ ≠ A 15 := by
      intro j
      have hj := j.isLt
      exact ⟨Ane A (fun e => by have := congrArg Fin.val e; simp at this; omega),
        Ane A (fun e => by have := congrArg Fin.val e; simp at this; omega),
        Ane A (fun e => by have := congrArg Fin.val e; simp at this; omega)⟩
    have hlen : (emitted gv Interfaces.gateWord gn pos0 i).length + (Interfaces.gateWord (gv (iter gn pos0 i))).length ≤
        (emitted gv Interfaces.gateWord gn pos0 m).length := by
      have := emitted_mono gv Interfaces.gateWord gn pos0 (i + 1) m (by omega)
      rw [emitted_succ, List.length_append] at this; exact this
    have e := gateW_spec cap W o (AX A) (A 5) (AR A 6 (Or.inl rfl)) (A 15) (A 16) h.hWo (fun j => (hX j).1)
      (fun j => (hX j).2.1) (Ane A (by decide)) (fun j => (hX j).2.2) (Ane A (by decide)) (Ane A (by decide))
      (Ane A (by decide)) (Ane A (by decide)) (Ane A (by decide)) (Ane A (by decide)) τ q
      ((h1 _ (Ane A (by decide)) (Ane A (by decide))).trans (h.six pos0 out kv m))
      (fun j => by fin_cases j <;> exact h.body h1 _ (by decide) (by decide) (by decide) (by decide))
      (h.body h1 5 (by decide) (by decide) (by decide) (by decide))
      (fun j h0 h7 => by
        rw [AR_val]
        fin_cases j <;> simp at h0 h7 <;> exact h.body h1 _ (by decide) (by decide) (by decide) (by decide))
      (h.body h1 15 (by decide) (by decide) (by decide) (by decide))
      (h.body h1 16 (by decide) (by decide) (by decide) (by decide)) h5
      (by rw [h3]; exact h.cap1)
      (by
        have hr : τ.val (AR A 6 (Or.inl rfl) 7) = τ.val (A 13) := rfl
        have hg : (Interfaces.gateWord (readGate q ((τ.st W).drop (τ.sh W))).1).length =
            (Interfaces.gateWord (gv (iter gn pos0 i))).length := by rw [h3, h4]
        rw [hr, hg, h3, ← hw]
        omega)
    rw [h3] at e
    exact e
  have e := repEmit_spec cap W o (A 13) (A 17) _ gv Interfaces.gateWord gn (fGateCost q w.length) m
    (shp W o A σ pos0 out kv m) h.hWo (Ane A (by decide)) (shp_C pos0 out kv m) hm (shp_ho h.hWo h.ho pos0 out kv m)
    hbody
  rw [shp_shW h.hWo, shp_app h.hWo, shp_setC] at e
  exact e

/-- The coefficient loop: `m` integer fields from `pos0`. -/
theorem step_ints (h : CirPre cap W o A σ q) (pos0 : ℕ) (out : List Bool) (kv m : ℕ) (hm : m ≤ cap)
    (hc : σ.val (A 13) + 2 * out.length +
        2 * (emitted (ival (σ.st W)) Interfaces.intWord (intEnd (σ.st W)) pos0 m).length + 4 * (σ.st W).length + 12 ≤ cap) :
    WExec cap (repLoop (A 17) (intW W o (AX A) (A 5) (A 13)))
      (shp W o A σ pos0 out kv m)
      (shp W o A σ (iter (intEnd (σ.st W)) pos0 m) (out ++ emitted (ival (σ.st W)) Interfaces.intWord (intEnd (σ.st W)) pos0 m)
        kv 0)
      (m * (fIntCost (σ.st W).length + 4) + 1) := by
  set w := σ.st W with hw
  have hbody : ∀ i < m, ∀ τ : WState ns nr,
      (∀ r, r ≠ A 13 → r ≠ A 17 → τ.val r = (shp W o A σ pos0 out kv m).val r) →
      τ.val (A 17) = m - i - 1 → τ.st W = (shp W o A σ pos0 out kv m).st W →
      τ.sh W = iter (intEnd w) ((shp W o A σ pos0 out kv m).sh W) i → τ.sh o = (τ.st o).length →
      τ.val (A 13) = (shp W o A σ pos0 out kv m).val (A 13) +
        2 * (emitted (ival w) Interfaces.intWord (intEnd w) ((shp W o A σ pos0 out kv m).sh W) i).length →
      WExec cap (intW W o (AX A) (A 5) (A 13)) τ
        (appendO (τ.seth W (intEnd w (τ.sh W))) o (A 13) (marks (Interfaces.intWord (ival w (τ.sh W))))) (fIntCost w.length) := by
    intro i hi τ h1 _ h3 h4 h5 h6
    rw [shp_stW h.hWo] at h3
    rw [shp_shW h.hWo] at h4 h6
    rw [shp_OP] at h6
    have hX : ∀ j : Fin 5, A ⟨j.val, by omega⟩ ≠ A 13 ∧ A ⟨j.val, by omega⟩ ≠ A 5 := by
      intro j
      have hj := j.isLt
      exact ⟨Ane A (fun e => by have := congrArg Fin.val e; simp at this; omega),
        Ane A (fun e => by have := congrArg Fin.val e; simp at this; omega)⟩
    have hlen : (emitted (ival w) Interfaces.intWord (intEnd w) pos0 i).length ≤
        (emitted (ival w) Interfaces.intWord (intEnd w) pos0 m).length := emitted_mono _ _ _ pos0 i m (by omega)
    have e := intW_spec' cap W o (AX A) (A 5) (A 13) h.hWo (fun j => (hX j).1) (fun j => (hX j).2)
      (Ane A (by decide)) τ
      (fun j => by fin_cases j <;> exact h.body h1 _ (by decide) (by decide) (by decide) (by decide))
      (h.body h1 5 (by decide) (by decide) (by decide) (by decide)) h5
      (by rw [h3, ← hw]; omega)
    rw [h3] at e
    exact e
  have e := repEmit_spec cap W o (A 13) (A 17) _ (ival w) Interfaces.intWord (intEnd w) (fIntCost w.length) m
    (shp W o A σ pos0 out kv m) h.hWo (Ane A (by decide)) (shp_C pos0 out kv m) hm (shp_ho h.hWo h.ho pos0 out kv m)
    hbody
  rw [shp_shW h.hWo, shp_app h.hWo, shp_setC] at e
  exact e

/-- The table loop: `m` bits from `pos0`. -/
theorem step_bits (h : CirPre cap W o A σ q) (pos0 : ℕ) (out : List Bool) (kv m : ℕ) (hm : m ≤ cap)
    (hc : σ.val (A 13) + 2 * out.length +
        2 * (emitted (fun r => (σ.st W).getD r false) Interfaces.bitWord (· + 1) pos0 m).length + 6 ≤ cap) :
    WExec cap (repLoop (A 17) (bitW W o (A 13)))
      (shp W o A σ pos0 out kv m)
      (shp W o A σ (iter (· + 1) pos0 m)
        (out ++ emitted (fun r => (σ.st W).getD r false) Interfaces.bitWord (· + 1) pos0 m) kv 0)
      (m * (51 + 4) + 1) := by
  set w := σ.st W with hw
  have hbody : ∀ i < m, ∀ τ : WState ns nr,
      (∀ r, r ≠ A 13 → r ≠ A 17 → τ.val r = (shp W o A σ pos0 out kv m).val r) →
      τ.val (A 17) = m - i - 1 → τ.st W = (shp W o A σ pos0 out kv m).st W →
      τ.sh W = iter (· + 1) ((shp W o A σ pos0 out kv m).sh W) i → τ.sh o = (τ.st o).length →
      τ.val (A 13) = (shp W o A σ pos0 out kv m).val (A 13) +
        2 * (emitted (fun r => w.getD r false) Interfaces.bitWord (· + 1) ((shp W o A σ pos0 out kv m).sh W) i).length →
      WExec cap (bitW W o (A 13)) τ
        (appendO (τ.seth W (τ.sh W + 1)) o (A 13) (marks (Interfaces.bitWord (w.getD (τ.sh W) false)))) 51 := by
    intro i hi τ _ _ h3 _ h5 h6
    rw [shp_stW h.hWo] at h3
    rw [shp_shW h.hWo] at h6
    rw [shp_OP] at h6
    have hlen : (emitted (fun r => w.getD r false) Interfaces.bitWord (· + 1) pos0 i).length ≤
        (emitted (fun r => w.getD r false) Interfaces.bitWord (· + 1) pos0 m).length := emitted_mono _ _ _ pos0 i m (by omega)
    have e := bitW_spec cap W o (A 13) h.hWo τ h5 (by rw [h6]; have := hc; omega)
    rw [h3] at e
    exact e
  have e := repEmit_spec cap W o (A 13) (A 17) _ (fun r => w.getD r false) Interfaces.bitWord (· + 1) 51 m
    (shp W o A σ pos0 out kv m) h.hWo (Ane A (by decide)) (shp_C pos0 out kv m) hm (shp_ho h.hWo h.ho pos0 out kv m)
    hbody
  rw [shp_shW h.hWo, shp_app h.hWo, shp_setC] at e
  exact e

/-- The exact composed cost of `circuitW` (the nesting of its thirteen steps; `seq` adds one). -/
def circuitWCost (q n K L : ℕ) : ℕ :=
  (7 * K + 3) + 1 + ((natBitLength K + 10) * (100 * K + 200) + 1 + ((18 * K + 3) + 1 +
  ((K * (fGateCost q n + 4) + 1) + 1 + ((natBitLength K + 10) * (100 * K + 200) + 1 + ((18 * K + 3) + 1 +
  ((K * (fIntCost n + 4) + 1) + 1 + ((3 * K + 1) + 1 + ((7 * L + 3) + 1 +
  ((natBitLength L + 10) * (100 * L + 200) + 1 + ((18 * L + 3) + 1 + ((L * (51 + 4) + 1) + 1 + (3 * L + 1))))))))))))

theorem circuitW_spec (W o : Fin (ns + 1)) (A : Fin 18 ↪ Fin nr) (σ : WState ns nr) (q : ℕ)
    (h : CirPre cap W o A σ q) :
    WExec cap (circuitW W o A) σ
      (appendO (σ.seth W (circuitEnd (σ.st W) (σ.sh W) q)) o (A 13)
        (marks (Interfaces.circuitWord (readCircuit q ((σ.st W).drop (σ.sh W))).1)))
      (circuitWCost q (σ.st W).length (cK (σ.st W) (σ.sh W)) (cL (σ.st W) (σ.sh W) q)) := by
  set w := σ.st W with hw
  set p := σ.sh W with hp
  obtain ⟨_, hcw⟩ := readCircuit_drop w p q
  have hO := h.capO
  rw [← hw, ← hp, hcw] at hO
  simp only [List.length_append] at hO
  have hKn : cK w p ≤ w.length := fieldLen_le w p
  have hLn : cL w p q ≤ w.length := fieldLen_le w _
  have hc1 := h.cap1
  rw [← hw] at hc1
  have hKb : natBitLength (cK w p) ≤ cK w p + 1 := natBitLength_le_succ _
  have hLb : natBitLength (cL w p q) ≤ cL w p q + 1 := natBitLength_le_succ _
  have e1 := step_count h p [] (by show cK w p ≤ cap; omega)
  have e2 := step_write h (cP1 w p) [] (cK w p) (by simp only [List.length_nil]; omega)
  have e3 := step_dup h (cP1 w p) ([] ++ natWord (cK w p)) (cK w p) (by omega)
  have e4 := step_gates h (cP1 w p) ([] ++ natWord (cK w p)) (cK w p) (cK w p) (by omega)
    (by try rw [← hw]
        simp only [List.length_append, List.length_nil]; omega)
  have e5 := step_write h (cPg w p q)
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p)) (cK w p)
    (by simp only [List.length_append, List.length_nil]; omega)
  have e6 := step_dup h (cPg w p q)
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p) ++ natWord (cK w p)) (cK w p) (by omega)
  have e7 := step_ints h (cPg w p q)
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p) ++ natWord (cK w p)) (cK w p) (cK w p) (by omega)
    (by try rw [← hw]
        simp only [List.length_append, List.length_nil]; omega)
  have e8 := step_clear h (cPc w p q)
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p) ++ natWord (cK w p) ++ emitted (ival w) Interfaces.intWord (intEnd w) (cPg w p q) (cK w p))
    (cK w p) (by omega)
  have e9 := step_count h (cPc w p q)
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p) ++ natWord (cK w p) ++ emitted (ival w) Interfaces.intWord (intEnd w) (cPg w p q) (cK w p))
    (by show cL w p q ≤ cap; omega)
  have e10 := step_write h (cP2 w p q)
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p) ++ natWord (cK w p) ++ emitted (ival w) Interfaces.intWord (intEnd w) (cPg w p q) (cK w p))
    (cL w p q) (by simp only [List.length_append, List.length_nil]; omega)
  have e11 := step_dup h (cP2 w p q)
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p) ++ natWord (cK w p) ++ emitted (ival w) Interfaces.intWord (intEnd w) (cPg w p q) (cK w p) ++
      natWord (cL w p q)) (cL w p q) (by omega)
  have e12 := step_bits h (cP2 w p q)
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p) ++ natWord (cK w p) ++ emitted (ival w) Interfaces.intWord (intEnd w) (cPg w p q) (cK w p) ++
      natWord (cL w p q)) (cL w p q) (cL w p q) (by omega)
    (by try rw [← hw]
        simp only [List.length_append, List.length_nil]; omega)
  have e13 := step_clear h (iter (· + 1) (cP2 w p q) (cL w p q))
    ([] ++ natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
      (cP1 w p) (cK w p) ++ natWord (cK w p) ++ emitted (ival w) Interfaces.intWord (intEnd w) (cPg w p q) (cK w p) ++
      natWord (cL w p q) ++ emitted (fun r => w.getD r false) Interfaces.bitWord (· + 1) (cP2 w p q) (cL w p q))
    (cL w p q) (by omega)
  have chain := WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
    (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12 e13)))))))))))
  rw [shp_init h.hWo (h.hz 14 (by decide) (by decide)) (h.hz 17 (by decide) (by decide))] at chain
  refine WExec.cast cap chain ?_ le_rfl
  rw [shp_final h.hWo _ _ (h.hz 14 (by decide) (by decide)) (h.hz 17 (by decide) (by decide)), iter_succ_eq, hcw]
  simp only [List.nil_append, List.append_assoc]
  rfl

end Steps

end NearCubicGates.Close.Codec

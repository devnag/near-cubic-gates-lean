import Proof.Wire_3_5.PrimTTabWrite

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner

section Scan
variable {ns nr : ℕ} (cap : ℕ)

/-! ## Emitting, seen from every stream -/

theorem emit_st (σ : WState ns nr) (X j : Fin (ns + 1)) (b : Bool) :
    ((σ.sets X (σ.st X ++ [b])).seth X ((σ.st X).length + 1)).st j = if j = X then σ.st X ++ [b] else σ.st j := by
  by_cases h : j = X
  · subst h; simp
  · simp [Function.update_of_ne h, h]

theorem emit_sh (σ : WState ns nr) (X j : Fin (ns + 1)) (b : Bool) :
    ((σ.sets X (σ.st X ++ [b])).seth X ((σ.st X).length + 1)).sh j = if j = X then (σ.st X).length + 1 else σ.sh j := by
  by_cases h : j = X
  · subst h; simp
  · simp [Function.update_of_ne h, h]

variable (Sc : Fin 6 ↪ Fin (ns + 1)) (c : Fin nr)

theorem sc_ne (i j : Fin 6) (h : i ≠ j) : Sc i ≠ Sc j := Sc.injective.ne h

/-! ## The programs -/

/-- Skip a raw `natWord` (`1^k 0` then `k` bits). -/
def rawSkipW (W : Fin (ns + 1)) : WM ns nr :=
  .seq (.whs W (.seq (.fwd W) (.inc c))) (.seq (.fwd W) (.whr c (.seq (.fwd W) (.dec c))))

/-- Skip a framed word. -/
def skipFrameW (W : Fin (ns + 1)) : WM ns nr := .seq (.whs W (.seq (.fwd W) (.fwd W))) (.fwd W)

/-- Copy one framed cell pair to both copies, two ruler cells. -/
def copyPairW : WM ns nr :=
  .seq (.seq (emitW (Sc 1) true) (emitW (Sc 2) true)) (.seq (emitW (Sc 3) true) (.seq (emitW (Sc 3) true)
    (.seq (.fwd (Sc 0)) (.seq (.ifs (Sc 0) (.seq (emitW (Sc 1) true) (emitW (Sc 2) true))
      (.seq (emitW (Sc 1) false) (emitW (Sc 2) false))) (.fwd (Sc 0))))))

/-- Copy one framed word, its end marker, one ruler cell per copied cell; one cell of the gate count. -/
def bottomW : WM ns nr :=
  .seq (emitW (Sc 4) true) (.seq (.whs (Sc 0) (copyPairW Sc)) (.seq (.seq (emitW (Sc 1) false) (emitW (Sc 2) false))
    (.seq (emitW (Sc 3) true) (.fwd (Sc 0)))))

/-- The scan of one native word: the header skipped, every bottom copied. -/
def scanBodyW : WM ns nr := .seq (rawSkipW c (Sc 0)) (.seq (skipFrameW (Sc 0)) (.whs (Sc 0) (bottomW Sc)))

/-- **The scan**: the ruler's sentinel, then one native word. -/
def scanW : WM ns nr := .seq (emitW (Sc 3) false) (scanBodyW Sc c)

/-- **The unary width** from the ruler; the ruler returns to its sentinel. -/
def onesW : WM ns nr :=
  .seq (.fwd (Sc 3)) (.seq (.whs (Sc 3) (.seq (emitW (Sc 5) true) (.fwd (Sc 3)))) (.seq (.bwd (Sc 3))
    (.whs (Sc 3) (.bwd (Sc 3)))))

/-! ## The scan's standing state -/

/-- The copies hold `a`, the ruler `false :: 1^m`, the gate count `1^k`; every output head at its end. -/
def ScanSt (σ : WState ns nr) (a : List Bool) (m k : ℕ) : Prop :=
  σ.st (Sc 1) = a ∧ σ.sh (Sc 1) = a.length ∧ σ.st (Sc 2) = a ∧ σ.sh (Sc 2) = a.length ∧
    σ.st (Sc 3) = false :: List.replicate m true ∧ σ.sh (Sc 3) = m + 1 ∧
    σ.st (Sc 4) = List.replicate k true ∧ σ.sh (Sc 4) = k

theorem rep_snoc (m : ℕ) : List.replicate m true ++ [true] = List.replicate (m + 1) true := by
  rw [List.replicate_succ']

/-! ## Single steps, as facts -/

/-- `τ` agrees with `σ` on stream `j`. -/
def Same (σ τ : WState ns nr) (j : Fin (ns + 1)) : Prop := τ.st j = σ.st j ∧ τ.sh j = σ.sh j

theorem Same.trans' {σ τ ρ : WState ns nr} {j : Fin (ns + 1)} (h1 : Same σ τ j) (h2 : Same τ ρ j) : Same σ ρ j :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem emit_facts (X : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) (hX : σ.sh X = (σ.st X).length) :
    ∃ τ, WExec cap (emitW X b) σ τ 3 ∧ τ.st X = σ.st X ++ [b] ∧ τ.sh X = (τ.st X).length ∧
      (∀ j, j ≠ X → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  refine ⟨_, emitW_spec cap X b σ hX, by simp, by simp, fun j hj => ?_, rfl, rfl⟩
  exact ⟨by simp [Function.update_of_ne hj], by simp [Function.update_of_ne hj]⟩

theorem fwd_facts (X : Fin (ns + 1)) (σ : WState ns nr) :
    ∃ τ, WExec cap (.fwd X) σ τ 1 ∧ τ.st X = σ.st X ∧ τ.sh X = σ.sh X + 1 ∧
      (∀ j, j ≠ X → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  refine ⟨_, WExec.fwd X σ, rfl, by simp, fun j hj => ⟨rfl, by simp [Function.update_of_ne hj]⟩, rfl, rfl⟩

/-- One bit to both copies. -/
theorem emit2_facts (X Y : Fin (ns + 1)) (hXY : X ≠ Y) (b : Bool) (σ : WState ns nr)
    (hX : σ.sh X = (σ.st X).length) (hY : σ.sh Y = (σ.st Y).length) :
    ∃ τ, WExec cap (.seq (emitW X b) (emitW Y b)) σ τ 7 ∧ τ.st X = σ.st X ++ [b] ∧ τ.sh X = (τ.st X).length ∧
      τ.st Y = σ.st Y ++ [b] ∧ τ.sh Y = (τ.st Y).length ∧ (∀ j, j ≠ X → j ≠ Y → Same σ τ j) ∧ τ.val = σ.val ∧
      τ.cell = σ.cell := by
  obtain ⟨τ1, s1, a1, a1h, o1, v1, c1⟩ := emit_facts cap X b σ hX
  obtain ⟨τ, s2, b2, b2h, o2, v2, c2⟩ := emit_facts cap Y b τ1 (by rw [(o1 Y hXY.symm).1, (o1 Y hXY.symm).2, hY])
  refine ⟨τ, WExec.seq s1 s2, by rw [(o2 X hXY).1, a1], by rw [(o2 X hXY).1, (o2 X hXY).2, a1h], by
    rw [b2, (o1 Y hXY.symm).1], b2h, fun j h1 h2 => (o1 j h1).trans' (o2 j h2), v2.trans v1, c2.trans c1⟩

/-- **One cell pair** copied: both copies gain `[true, x]`, the ruler two cells. -/
theorem copyPair_spec (σ : WState ns nr) (a : List Bool) (m k : ℕ) (pre rest : List Bool) (x : Bool)
    (hs : ScanSt Sc σ a m k) (hW : σ.st (Sc 0) = pre ++ (true :: x :: rest)) (hWh : σ.sh (Sc 0) = pre.length) :
    ∃ τ, WExec cap (copyPairW Sc) σ τ 40 ∧ ScanSt Sc τ (a ++ [true, x]) (m + 2) k ∧ τ.st (Sc 0) = σ.st (Sc 0) ∧
      τ.sh (Sc 0) = pre.length + 2 ∧ τ.val = σ.val ∧ τ.cell = σ.cell ∧
      (∀ j, j ≠ Sc 0 → j ≠ Sc 1 → j ≠ Sc 2 → j ≠ Sc 3 → Same σ τ j) := by
  obtain ⟨hA, hAh, hB, hBh, hH, hHh, hG, hGh⟩ := hs
  have d01 := sc_ne Sc 0 1 (by decide); have d02 := sc_ne Sc 0 2 (by decide); have d03 := sc_ne Sc 0 3 (by decide)
  have d12 := sc_ne Sc 1 2 (by decide); have d13 := sc_ne Sc 1 3 (by decide); have d23 := sc_ne Sc 2 3 (by decide)
  have d04 := sc_ne Sc 0 4 (by decide); have d14 := sc_ne Sc 1 4 (by decide); have d24 := sc_ne Sc 2 4 (by decide)
  have d34 := sc_ne Sc 3 4 (by decide)
  obtain ⟨σ2, s12, a2, a2h, b2, b2h, o2, v2, c2⟩ := emit2_facts cap (Sc 1) (Sc 2) d12 true σ (by rw [hAh, hA])
    (by rw [hBh, hB])
  have h3in := o2 (Sc 3) d13.symm d23.symm
  obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap (Sc 3) true σ2 (by rw [h3in.1, h3in.2, hH, hHh]; simp)
  obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap (Sc 3) true σ3 e3h
  obtain ⟨σ5, s5, e5, e5h, o5, v5, c5⟩ := fwd_facts cap (Sc 0) σ4
  have w0 := ((o2 (Sc 0) d01 d02).trans' (o3 (Sc 0) d03)).trans' (o4 (Sc 0) d03)
  have hx : wbit σ5 (Sc 0) = x := by
    simp only [wbit, e5, e5h, w0.1, w0.2, hW, hWh]
    unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (by omega)]; simp
  have A5 : Same σ2 σ5 (Sc 1) := ((o3 (Sc 1) d13).trans' (o4 (Sc 1) d13)).trans' (o5 (Sc 1) d01.symm)
  have B5 : Same σ2 σ5 (Sc 2) := ((o3 (Sc 2) d23).trans' (o4 (Sc 2) d23)).trans' (o5 (Sc 2) d02.symm)
  obtain ⟨σ7, s6, a7, a7h, b7, b7h, o7, v7, c7⟩ : ∃ σ7, WExec cap (.ifs (Sc 0) (.seq (emitW (Sc 1) true)
      (emitW (Sc 2) true)) (.seq (emitW (Sc 1) false) (emitW (Sc 2) false))) σ5 σ7 8 ∧
      σ7.st (Sc 1) = σ5.st (Sc 1) ++ [x] ∧ σ7.sh (Sc 1) = (σ7.st (Sc 1)).length ∧
      σ7.st (Sc 2) = σ5.st (Sc 2) ++ [x] ∧ σ7.sh (Sc 2) = (σ7.st (Sc 2)).length ∧
      (∀ j, j ≠ Sc 1 → j ≠ Sc 2 → Same σ5 σ7 j) ∧ σ7.val = σ5.val ∧ σ7.cell = σ5.cell := by
    have hA5 : σ5.sh (Sc 1) = (σ5.st (Sc 1)).length := by rw [A5.1, A5.2, a2h]
    have hB5 : σ5.sh (Sc 2) = (σ5.st (Sc 2)).length := by rw [B5.1, B5.2, b2h]
    obtain ⟨σ7, s, r⟩ := emit2_facts cap (Sc 1) (Sc 2) d12 x σ5 hA5 hB5
    refine ⟨σ7, ?_, r⟩
    cases x
    · exact WExec.mono (WExec.ifsF hx s) (by omega)
    · exact WExec.mono (WExec.ifsT hx s) (by omega)
  obtain ⟨τ, s7, e8, e8h, o8, v8, c8⟩ := fwd_facts cap (Sc 0) σ7
  have run : WExec cap (copyPairW Sc) σ τ _ :=
    WExec.seq s12 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))
  have H7 : Same σ5 σ7 (Sc 3) := o7 (Sc 3) d13.symm d23.symm
  have G2 : Same σ σ2 (Sc 4) := o2 (Sc 4) d14.symm d24.symm
  have G8 : Same σ2 τ (Sc 4) := ((((o3 (Sc 4) d34.symm).trans' (o4 (Sc 4) d34.symm)).trans' (o5 (Sc 4) d04.symm)).trans'
    (o7 (Sc 4) d14.symm d24.symm)).trans' (o8 (Sc 4) d04.symm)
  refine ⟨τ, WExec.mono run (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(o8 (Sc 1) d01.symm).1, a7, A5.1, a2, hA]; simp
  · rw [(o8 (Sc 1) d01.symm).2, a7h, a7, A5.1, a2, hA]; simp
  · rw [(o8 (Sc 2) d02.symm).1, b7, B5.1, b2, hB]; simp
  · rw [(o8 (Sc 2) d02.symm).2, b7h, b7, B5.1, b2, hB]; simp
  · rw [(o8 (Sc 3) d03.symm).1, H7.1, (o5 (Sc 3) d03.symm).1, e4, e3, h3in.1, hH]
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.replicate_add]; rfl
  · rw [(o8 (Sc 3) d03.symm).2, H7.2, (o5 (Sc 3) d03.symm).2, e4h, e4, e3, h3in.1, hH]; simp; (try omega)
  · rw [G8.1, G2.1, hG]
  · rw [G8.2, G2.2, hGh]
  · rw [e8, (o7 (Sc 0) d01 d02).1, e5, w0.1]
  · rw [e8h, (o7 (Sc 0) d01 d02).2, e5h, w0.2, hWh]
  · rw [v8, v7, v5, v4, v3, v2]
  · rw [c8, c7, c5, c4, c3, c2]
  · intro j h0 h1 h2 h3
    exact (((((o2 j h1 h2).trans' (o3 j h3)).trans' (o4 j h3)).trans' (o5 j h0)).trans' (o7 j h1 h2)).trans' (o8 j h0)

/-! ## One bottom, and all of them -/

theorem copyLoop_spec (rest : List Bool) (k : ℕ) : ∀ (bs a : List Bool) (m : ℕ) (pre : List Bool) (σ : WState ns nr),
    ScanSt Sc σ a m k → σ.st (Sc 0) = pre ++ (frameP bs ++ false :: rest) → σ.sh (Sc 0) = pre.length →
    ∃ τ, WExec cap (.whs (Sc 0) (copyPairW Sc)) σ τ (bs.length * 42 + 1) ∧ ScanSt Sc τ (a ++ frameP bs) (m + 2 * bs.length) k ∧
      τ.st (Sc 0) = σ.st (Sc 0) ∧ τ.sh (Sc 0) = pre.length + 2 * bs.length ∧ τ.val = σ.val ∧ τ.cell = σ.cell ∧
      (∀ j, j ≠ Sc 0 → j ≠ Sc 1 → j ≠ Sc 2 → j ≠ Sc 3 → Same σ τ j)
  | [], a, m, pre, σ, hs, hW, hWh => by
    have hz : wbit σ (Sc 0) = false := by
      simp only [wbit, hW, hWh]; unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), by simpa using hs, rfl, by simp [hWh], rfl, rfl,
      fun j _ _ _ _ => ⟨rfl, rfl⟩⟩
  | b :: bs, a, m, pre, σ, hs, hW, hWh => by
    obtain ⟨τ1, s1, hs1, w1, w1h, v1, c1, o1⟩ := copyPair_spec cap Sc σ a m k pre (frameP bs ++ false :: rest) b hs
      (by rw [hW]; simp) hWh
    obtain ⟨τ, s2, hs2, w2, w2h, v2, c2, o2⟩ := copyLoop_spec rest k bs (a ++ [true, b]) (m + 2) (pre ++ [true, b]) τ1
      hs1 (by rw [w1, hW]; simp) (by rw [w1h]; simp)
    have hw : wbit σ (Sc 0) = true := by
      simp only [wbit, hW, hWh]; unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
    refine ⟨τ, WExec.mono (WExec.whsT hw s1 s2) (by simp; rw [Nat.succ_mul]; omega), ?_, by rw [w2, w1],
      by rw [w2h]; simp; omega, v2.trans v1, c2.trans c1, fun j h0 h1 h2 h3 => (o1 j h0 h1 h2 h3).trans' (o2 j h0 h1 h2 h3)⟩
    have e1 : a ++ [true, b] ++ frameP bs = a ++ frameP (b :: bs) := by simp
    have e2 : m + 2 + 2 * bs.length = m + 2 * (b :: bs).length := by simp; omega
    rw [← e1, ← e2]; exact hs2

/-- **One bottom**: its frame to both copies, one ruler cell per cell, one cell of the gate count. -/
theorem bottom_spec (a : List Bool) (m k : ℕ) (pre rest : List Bool) (bs : List Bool) (σ : WState ns nr)
    (hs : ScanSt Sc σ a m k) (hW : σ.st (Sc 0) = pre ++ (frame bs ++ rest)) (hWh : σ.sh (Sc 0) = pre.length) :
    ∃ τ, WExec cap (bottomW Sc) σ τ (42 * bs.length + 19) ∧
      ScanSt Sc τ (a ++ frame bs) (m + (frame bs).length) (k + 1) ∧ τ.st (Sc 0) = σ.st (Sc 0) ∧
      τ.sh (Sc 0) = pre.length + (frame bs).length ∧ τ.val = σ.val ∧ τ.cell = σ.cell ∧
      (∀ j, j ≠ Sc 0 → j ≠ Sc 1 → j ≠ Sc 2 → j ≠ Sc 3 → j ≠ Sc 4 → Same σ τ j) := by
  obtain ⟨hA, hAh, hB, hBh, hH, hHh, hG, hGh⟩ := hs
  have d01 := sc_ne Sc 0 1 (by decide); have d02 := sc_ne Sc 0 2 (by decide); have d03 := sc_ne Sc 0 3 (by decide)
  have d12 := sc_ne Sc 1 2 (by decide); have d13 := sc_ne Sc 1 3 (by decide); have d23 := sc_ne Sc 2 3 (by decide)
  have d04 := sc_ne Sc 0 4 (by decide); have d14 := sc_ne Sc 1 4 (by decide); have d24 := sc_ne Sc 2 4 (by decide)
  have d34 := sc_ne Sc 3 4 (by decide)
  obtain ⟨σ1, s1, g1, g1h, o1, v1, c1⟩ := emit_facts cap (Sc 4) true σ (by rw [hGh, hG]; simp)
  have hs1 : ScanSt Sc σ1 a m (k + 1) :=
    ⟨by rw [(o1 _ d14).1, hA], by rw [(o1 _ d14).2, hAh], by rw [(o1 _ d24).1, hB], by rw [(o1 _ d24).2, hBh],
      by rw [(o1 _ d34).1, hH], by rw [(o1 _ d34).2, hHh], by rw [g1, hG, rep_snoc], by rw [g1h, g1, hG]; simp⟩
  obtain ⟨σ2, s2, hs2, w2, w2h, v2, c2, o2⟩ := copyLoop_spec cap Sc rest (k + 1) bs a m pre σ1 hs1
    (by rw [(o1 _ d04).1, hW, frame_eq_frameP]; simp) (by rw [(o1 _ d04).2, hWh])
  obtain ⟨hA2, hAh2, hB2, hBh2, hH2, hHh2, hG2, hGh2⟩ := hs2
  obtain ⟨σ3, s3, a3, a3h, b3, b3h, o3, v3, c3⟩ := emit2_facts cap (Sc 1) (Sc 2) d12 false σ2 (by rw [hAh2, hA2])
    (by rw [hBh2, hB2])
  have H3 := o3 (Sc 3) d13.symm d23.symm
  obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap (Sc 3) true σ3 (by rw [H3.1, H3.2, hH2, hHh2]; simp)
  obtain ⟨τ, s5, w5, w5h, o5, v5, c5⟩ := fwd_facts cap (Sc 0) σ4
  have run : WExec cap (bottomW Sc) σ τ _ :=
    WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))
  have hfl : (frame bs).length = 2 * bs.length + 1 := frame_length bs
  have W4 : Same σ2 σ4 (Sc 0) := (o3 (Sc 0) d01 d02).trans' (o4 (Sc 0) d03)
  have G5 : Same σ2 τ (Sc 4) := ((o3 (Sc 4) d14.symm d24.symm).trans' (o4 (Sc 4) d34.symm)).trans' (o5 (Sc 4) d04.symm)
  refine ⟨τ, WExec.mono run (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(o5 _ d01.symm).1, (o4 _ d13).1, a3, hA2, frame_eq_frameP]; simp
  · rw [(o5 _ d01.symm).2, (o4 _ d13).2, a3h, a3, hA2, frame_eq_frameP]; simp
  · rw [(o5 _ d02.symm).1, (o4 _ d23).1, b3, hB2, frame_eq_frameP]; simp
  · rw [(o5 _ d02.symm).2, (o4 _ d23).2, b3h, b3, hB2, frame_eq_frameP]; simp
  · rw [(o5 _ d03.symm).1, e4, H3.1, hH2, hfl]
    simp only [List.cons_append, List.replicate_succ', List.append_assoc]
    rw [show m + (2 * bs.length + 1) = m + 2 * bs.length + 1 by omega, List.replicate_succ']; (try simp)
  · rw [(o5 _ d03.symm).2, e4h, e4, H3.1, hH2, hfl]; simp; (try omega)
  · rw [G5.1, hG2]
  · rw [G5.2, hGh2]
  · rw [w5, W4.1, w2, (o1 _ d04).1]
  · rw [w5h, W4.2, w2h, hfl]; omega
  · rw [v5, v4, v3, v2, v1]
  · rw [c5, c4, c3, c2, c1]
  · intro j h0 h1 h2 h3 h4
    exact ((((o1 j h4).trans' (o2 j h0 h1 h2 h3)).trans' (o3 j h1 h2)).trans' (o4 j h3)).trans' (o5 j h0)

theorem bottomsLoop_spec {n : ℕ} : ∀ (G : List (NormalizedThresholdGate n)) (a : List Bool) (m k : ℕ) (pre : List Bool)
    (σ : WState ns nr), ScanSt Sc σ a m k → σ.st (Sc 0) = pre ++ tabSeg G → σ.sh (Sc 0) = pre.length →
    ∃ τ, WExec cap (.whs (Sc 0) (bottomW Sc)) σ τ (42 * tabH G + 1) ∧
      ScanSt Sc τ (a ++ tabSeg G) (m + tabH G) (k + G.length) ∧ τ.st (Sc 0) = σ.st (Sc 0) ∧ τ.val = σ.val ∧
      τ.cell = σ.cell ∧ (∀ j, j ≠ Sc 0 → j ≠ Sc 1 → j ≠ Sc 2 → j ≠ Sc 3 → j ≠ Sc 4 → Same σ τ j)
  | [], a, m, k, pre, σ, hs, hW, hWh => by
    have hz : wbit σ (Sc 0) = false := by simp [wbit, hW, hWh, tabSeg, readTapeBit]
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by simp), ?_, rfl, rfl, rfl, fun j _ _ _ _ _ => ⟨rfl, rfl⟩⟩
    simpa [tabSeg, tabH] using hs
  | g :: G, a, m, k, pre, σ, hs, hW, hWh => by
    obtain ⟨τ1, s1, hs1, w1, w1h, v1, c1, o1⟩ := bottom_spec cap Sc a m k pre (tabSeg G) (tabGW g) σ hs
      (by rw [hW, tabSeg_cons]) hWh
    obtain ⟨τ, s2, hs2, w2, v2, c2, o2⟩ := bottomsLoop_spec G (a ++ frame (tabGW g)) (m + (frame (tabGW g)).length)
      (k + 1) (pre ++ frame (tabGW g)) τ1 hs1 (by rw [w1, hW, tabSeg_cons]; simp) (by rw [w1h]; simp)
    have hw : wbit σ (Sc 0) = true := by
      simp only [wbit, hW, hWh, tabSeg_cons, readTapeBit]
      have := tabGW_head g (tabSeg G)
      unfold readTapeBit at this
      rw [List.getD_append_right _ _ _ _ (le_refl _)]; simpa using this
    have hfl : (frame (tabGW g)).length = 2 * (tabGW g).length + 1 := frame_length _
    have hH : tabH (g :: G) = (frame (tabGW g)).length + tabH G := by unfold tabH; rw [tabSeg_cons, List.length_append]
    refine ⟨τ, WExec.mono (WExec.whsT hw s1 s2) (by rw [hH, hfl]; omega), ?_, by rw [w2, w1], v2.trans v1,
      c2.trans c1, fun j h0 h1 h2 h3 h4 => (o1 j h0 h1 h2 h3 h4).trans' (o2 j h0 h1 h2 h3 h4)⟩
    have e1 : a ++ frame (tabGW g) ++ tabSeg G = a ++ tabSeg (g :: G) := by rw [tabSeg_cons]; simp
    have e2 : m + (frame (tabGW g)).length + tabH G = m + tabH (g :: G) := by rw [hH]; omega
    have e3 : k + 1 + G.length = k + (g :: G).length := by simp; omega
    rw [← e1, ← e2, ← e3]; exact hs2

/-! ## The header -/

theorem rawCount_spec (W : Fin (ns + 1)) : ∀ (m : ℕ) (σ : WState ns nr),
    (∀ i < m, readTapeBit (σ.st W) (σ.sh W + i) = true) → readTapeBit (σ.st W) (σ.sh W + m) = false →
    σ.val c + m ≤ cap →
    WExec cap (.whs W (.seq (.fwd W) (.inc c))) σ ((σ.seth W (σ.sh W + m)).setv c (σ.val c + m)) (m * 7 + 1)
  | 0, σ, _, hz, _ => by
    have e : (σ.seth W (σ.sh W + 0)).setv c (σ.val c + 0) = σ := by
      simp only [Nat.add_zero, wseth_same]; exact wsetv_same σ c
    rw [e]; exact WExec.whsF (by simpa [wbit] using hz)
  | m + 1, σ, hT, hz, hcap => by
    have s1 := WExec.fwd (cap := cap) W σ
    have s2 := WExec.inc (cap := cap) c (σ.seth W (σ.sh W + 1)) (by simp; omega)
    have ih := rawCount_spec W m ((σ.seth W (σ.sh W + 1)).setv c ((σ.seth W (σ.sh W + 1)).val c + 1))
      (fun i hi => by simp; rw [show σ.sh W + 1 + i = σ.sh W + (i + 1) by omega]; exact hT _ (by omega))
      (by simp; rw [show σ.sh W + 1 + m = σ.sh W + (m + 1) by omega]; exact hz) (by simp; omega)
    have e : (((σ.seth W (σ.sh W + 1)).setv c ((σ.seth W (σ.sh W + 1)).val c + 1)).seth W
        (((σ.seth W (σ.sh W + 1)).setv c ((σ.seth W (σ.sh W + 1)).val c + 1)).sh W + m)).setv c
        (((σ.seth W (σ.sh W + 1)).setv c ((σ.seth W (σ.sh W + 1)).val c + 1)).val c + m) =
        (σ.seth W (σ.sh W + (m + 1))).setv c (σ.val c + (m + 1)) := by
      apply WState.eq <;> simp <;> (try funext j) <;> simp [Function.update_apply] <;> (try split_ifs) <;> omega
    rw [e] at ih
    have hw : wbit σ W = true := by simpa [wbit] using hT 0 (by omega)
    exact WExec.mono (WExec.whsT hw (WExec.seq s1 s2) ih) (by rw [Nat.succ_mul]; omega)

theorem rawSkipLoop_spec (W : Fin (ns + 1)) : ∀ (m : ℕ) (σ : WState ns nr), σ.val c = m → m ≤ cap →
    WExec cap (.whr c (.seq (.fwd W) (.dec c))) σ ((σ.seth W (σ.sh W + m)).setv c 0) (m * 5 + 1)
  | 0, σ, hm, _ => by
    have e : (σ.seth W (σ.sh W + 0)).setv c 0 = σ := by
      simp only [Nat.add_zero, wseth_same]; rw [← hm]; exact wsetv_same σ c
    rw [e]; exact WExec.whrF hm
  | m + 1, σ, hm, hcap => by
    have s1 := WExec.fwd (cap := cap) W σ
    have s2 := WExec.dec (cap := cap) c (σ.seth W (σ.sh W + 1)) (by simp; omega)
    have ih := rawSkipLoop_spec W m ((σ.seth W (σ.sh W + 1)).setv c ((σ.seth W (σ.sh W + 1)).val c - 1))
      (by simp; omega) (by omega)
    have e : (((σ.seth W (σ.sh W + 1)).setv c ((σ.seth W (σ.sh W + 1)).val c - 1)).seth W
        (((σ.seth W (σ.sh W + 1)).setv c ((σ.seth W (σ.sh W + 1)).val c - 1)).sh W + m)).setv c 0 =
        (σ.seth W (σ.sh W + (m + 1))).setv c 0 := by
      apply WState.eq <;> simp <;> (try funext j) <;> simp [Function.update_apply] <;> (try split_ifs) <;> omega
    rw [e] at ih
    exact WExec.mono (WExec.whrT (by omega) (WExec.seq s1 s2) ih) (by rw [Nat.succ_mul]; omega)

theorem natWord_getD' (x i : ℕ) : (natWord x).getD i false = if i < natBitLength x then true
    else if i = natBitLength x then false else (natWord x).getD i false := by
  split_ifs with h1 h2
  · exact natWord_getD_lt x i h1
  · subst h2; exact natWord_getD_k x
  · rfl

/-- **Skip a raw `natWord`**; the count returns to `0`. -/
theorem rawSkip_spec (W : Fin (ns + 1)) (pre rest : List Bool) (x : ℕ) (σ : WState ns nr)
    (hW : σ.st W = pre ++ (natWord x ++ rest)) (hWh : σ.sh W = pre.length) (hc : σ.val c = 0)
    (hk : natBitLength x ≤ cap) :
    WExec cap (rawSkipW c W) σ (σ.seth W (pre.length + (natWord x).length)) (12 * natBitLength x + 5) := by
  set k := natBitLength x with hkd
  have hlen : (natWord x).length = 2 * k + 1 := natWord_length' x
  have rd : ∀ i, readTapeBit (σ.st W) (σ.sh W + i) = (natWord x ++ rest).getD i false := by
    intro i; rw [hW, hWh]; unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (by omega)]; simp
  have s1 := rawCount_spec cap c W k σ
    (fun i hi => by rw [rd, List.getD_append _ _ _ _ (by omega)]; exact natWord_getD_lt x i hi)
    (by rw [rd, List.getD_append _ _ _ _ (by omega)]; exact natWord_getD_k x) (by rw [hc]; omega)
  set σ1 := (σ.seth W (σ.sh W + k)).setv c (σ.val c + k) with hσ1
  have s2 := WExec.fwd (cap := cap) W σ1
  have s3 := rawSkipLoop_spec cap c W k (σ1.seth W (σ1.sh W + 1)) (by simp [hσ1, hc]) hk
  have e : ((σ1.seth W (σ1.sh W + 1)).seth W ((σ1.seth W (σ1.sh W + 1)).sh W + k)).setv c 0 =
      σ.seth W (pre.length + (natWord x).length) := by
    rw [hlen]
    apply WState.eq <;> simp [hσ1] <;> (try funext j) <;> simp [Function.update_apply, hWh, hc] <;> (try split_ifs) <;>
      (try subst_vars) <;> (try omega)
  rw [e] at s3
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega)

theorem skipFrameLoop_spec (W : Fin (ns + 1)) : ∀ (m : ℕ) (σ : WState ns nr),
    (∀ i < m, readTapeBit (σ.st W) (σ.sh W + 2 * i) = true) → readTapeBit (σ.st W) (σ.sh W + 2 * m) = false →
    WExec cap (.whs W (.seq (.fwd W) (.fwd W))) σ (σ.seth W (σ.sh W + 2 * m)) (m * 5 + 1)
  | 0, σ, _, hz => by
    have e : σ.seth W (σ.sh W + 2 * 0) = σ := by simp only [Nat.mul_zero, Nat.add_zero, wseth_same]
    rw [e]; exact WExec.whsF (by simpa [wbit] using hz)
  | m + 1, σ, hT, hz => by
    have s1 := WExec.fwd (cap := cap) W σ
    have s2 : WExec cap (.fwd W) (σ.seth W (σ.sh W + 1)) (σ.seth W (σ.sh W + 1 + 1)) 1 := by
      have := WExec.fwd (cap := cap) W (σ.seth W (σ.sh W + 1)); rw [wseth_seth] at this; simpa using this
    have ih := skipFrameLoop_spec W m (σ.seth W (σ.sh W + 1 + 1))
      (fun i hi => by simp; rw [show σ.sh W + 1 + 1 + 2 * i = σ.sh W + 2 * (i + 1) by omega]; exact hT _ (by omega))
      (by simp; rw [show σ.sh W + 1 + 1 + 2 * m = σ.sh W + 2 * (m + 1) by omega]; exact hz)
    rw [wseth_seth] at ih
    simp only [WState.seth_sh, Function.update_self] at ih
    rw [show σ.sh W + 1 + 1 + 2 * m = σ.sh W + 2 * (m + 1) by omega] at ih
    have hw : wbit σ W = true := by simpa [wbit] using hT 0 (by omega)
    exact WExec.mono (WExec.whsT hw (WExec.seq s1 s2) ih) (by rw [Nat.succ_mul]; omega)

/-- **Skip a framed word.** -/
theorem skipFrame_spec (W : Fin (ns + 1)) (pre rest y : List Bool) (σ : WState ns nr)
    (hW : σ.st W = pre ++ (frame y ++ rest)) (hWh : σ.sh W = pre.length) :
    WExec cap (skipFrameW W) σ (σ.seth W (pre.length + (frame y).length)) (5 * y.length + 3) := by
  have hW' : σ.st W = pre ++ (frameP y ++ (false :: rest)) := by rw [hW, frame_eq_frameP]; simp
  have s1 := skipFrameLoop_spec cap W y.length σ
    (fun i hi => by rw [hW', hWh]; exact rd_marker pre y (false :: rest) i hi)
    (by rw [hW', hWh, rd_shift]; unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (by simp)]; simp)
  have s2 := WExec.fwd (cap := cap) W (σ.seth W (σ.sh W + 2 * y.length))
  rw [wseth_seth] at s2
  simp only [WState.seth_sh, Function.update_self] at s2
  rw [show σ.sh W + 2 * y.length + 1 = pre.length + (frame y).length by rw [hWh, frame_length]; omega] at s2
  exact WExec.mono (WExec.seq s1 s2) (by omega)

/-! ## The scan -/

def scanCost (x : ℕ) (y : List Bool) (h : ℕ) : ℕ := 12 * natBitLength x + 5 * y.length + 42 * h + 12

/-- **The scan of one native word** `natWord x ++ frame y ++ tabSeg G`: both copies gain `tabSeg G`, the ruler
`tabH G` cells, the gate count `|G|` cells; the count register returns to `0`. -/
theorem scanBody_spec {n : ℕ} (x : ℕ) (y : List Bool) (G : List (NormalizedThresholdGate n)) (a : List Bool) (m k : ℕ)
    (σ : WState ns nr) (hs : ScanSt Sc σ a m k) (hW : σ.st (Sc 0) = natWord x ++ (frame y ++ tabSeg G))
    (hWh : σ.sh (Sc 0) = 0) (hc : σ.val c = 0) (hk : natBitLength x ≤ cap) :
    ∃ τ, WExec cap (scanBodyW Sc c) σ τ (scanCost x y (tabH G)) ∧
      ScanSt Sc τ (a ++ tabSeg G) (m + tabH G) (k + G.length) ∧ τ.st (Sc 0) = σ.st (Sc 0) ∧ τ.val c = 0 ∧
      τ.cell = σ.cell ∧ (∀ j, j ≠ Sc 0 → j ≠ Sc 1 → j ≠ Sc 2 → j ≠ Sc 3 → j ≠ Sc 4 → Same σ τ j) ∧
      (∀ q, τ.val q = σ.val q) := by
  have d01 := sc_ne Sc 0 1 (by decide); have d02 := sc_ne Sc 0 2 (by decide); have d03 := sc_ne Sc 0 3 (by decide)
  have d04 := sc_ne Sc 0 4 (by decide)
  have s1 := rawSkip_spec cap c (Sc 0) [] (frame y ++ tabSeg G) x σ (by simpa using hW) (by simpa using hWh) hc hk
  set σ1 := σ.seth (Sc 0) ([].length + (natWord x).length) with hσ1
  have s2 := skipFrame_spec cap (Sc 0) (natWord x) (tabSeg G) y σ1 (by simp [hσ1, hW]) (by simp [hσ1])
  set σ2 := σ1.seth (Sc 0) ((natWord x).length + (frame y).length) with hσ2
  have hs2 : ScanSt Sc σ2 a m k := by
    obtain ⟨hA, hAh, hB, hBh, hH, hHh, hG, hGh⟩ := hs
    exact ⟨by simp [hσ2, hσ1, hA], by simp [hσ2, hσ1, Function.update_of_ne d01.symm, hAh], by simp [hσ2, hσ1, hB],
      by simp [hσ2, hσ1, Function.update_of_ne d02.symm, hBh], by simp [hσ2, hσ1, hH],
      by simp [hσ2, hσ1, Function.update_of_ne d03.symm, hHh], by simp [hσ2, hσ1, hG],
      by simp [hσ2, hσ1, Function.update_of_ne d04.symm, hGh]⟩
  obtain ⟨τ, s3, hs3, w3, v3, c3, o3⟩ := bottomsLoop_spec cap Sc G a m k (natWord x ++ frame y) σ2 hs2
    (by simp [hσ2, hσ1, hW]) (by simp [hσ2, hσ1])
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by unfold scanCost; omega), hs3, by rw [w3]; simp [hσ2, hσ1],
    by rw [v3]; simp [hσ2, hσ1, hc], by rw [c3]; simp [hσ2, hσ1], fun j h0 h1 h2 h3 h4 => ?_, fun q => ?_⟩
  · have := o3 j h0 h1 h2 h3 h4
    exact ⟨by rw [this.1]; simp [hσ2, hσ1], by rw [this.2]; simp [hσ2, hσ1, Function.update_of_ne h0]⟩
  · rw [v3]; simp [hσ2, hσ1]

/-- **The scan from blank outputs.** -/
theorem scan_spec {n : ℕ} (x : ℕ) (y : List Bool) (G : List (NormalizedThresholdGate n)) (σ : WState ns nr)
    (hW : σ.st (Sc 0) = natWord x ++ (frame y ++ tabSeg G)) (hWh : σ.sh (Sc 0) = 0)
    (hA : σ.st (Sc 1) = []) (hAh : σ.sh (Sc 1) = 0) (hB : σ.st (Sc 2) = []) (hBh : σ.sh (Sc 2) = 0)
    (hH : σ.st (Sc 3) = []) (hHh : σ.sh (Sc 3) = 0) (hG : σ.st (Sc 4) = []) (hGh : σ.sh (Sc 4) = 0)
    (hc : σ.val c = 0) (hk : natBitLength x ≤ cap) :
    ∃ τ, WExec cap (scanW Sc c) σ τ (scanCost x y (tabH G) + 4) ∧
      ScanSt Sc τ (tabSeg G) (tabH G) G.length ∧ τ.st (Sc 0) = σ.st (Sc 0) ∧ τ.val = σ.val ∧ τ.cell = σ.cell ∧
      (∀ j, j ≠ Sc 0 → j ≠ Sc 1 → j ≠ Sc 2 → j ≠ Sc 3 → j ≠ Sc 4 → Same σ τ j) := by
  have d03 := sc_ne Sc 0 3 (by decide); have d13 := sc_ne Sc 1 3 (by decide); have d23 := sc_ne Sc 2 3 (by decide)
  have d34 := sc_ne Sc 3 4 (by decide)
  obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (Sc 3) false σ (by rw [hHh, hH]; rfl)
  have hs1 : ScanSt Sc σ1 [] 0 0 :=
    ⟨by rw [(o1 _ d13).1, hA], by rw [(o1 _ d13).2, hAh]; rfl, by rw [(o1 _ d23).1, hB], by rw [(o1 _ d23).2, hBh]; rfl,
      by rw [e1, hH]; rfl, by rw [e1h, e1, hH]; rfl, by rw [(o1 _ d34.symm).1, hG]; rfl, by rw [(o1 _ d34.symm).2, hGh]⟩
  obtain ⟨τ, s2, hs2, w2, c2', cl2, o2, vv2⟩ := scanBody_spec cap Sc c x y G [] 0 0 σ1 hs1
    (by rw [(o1 _ d03).1, hW]) (by rw [(o1 _ d03).2, hWh]) (by rw [v1, hc]) hk
  refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by omega), by simpa using hs2, by rw [w2, (o1 _ d03).1],
    by funext q; rw [vv2, v1], by rw [cl2, c1], fun j h0 h1 h2 h3 h4 => (o1 j h3).trans' (o2 j h0 h1 h2 h3 h4)⟩

/-! ## The unary width -/

theorem onesLoop_spec (O R : Fin (ns + 1)) (hOR : O ≠ R) : ∀ (m : ℕ) (σ : WState ns nr),
    (∀ i < m, readTapeBit (σ.st R) (σ.sh R + i) = true) → readTapeBit (σ.st R) (σ.sh R + m) = false →
    σ.sh O = (σ.st O).length →
    ∃ τ, WExec cap (.whs R (.seq (emitW O true) (.fwd R))) σ τ (m * 7 + 1) ∧
      τ.st O = σ.st O ++ List.replicate m true ∧ τ.sh O = (τ.st O).length ∧ τ.st R = σ.st R ∧
      τ.sh R = σ.sh R + m ∧ (∀ j, j ≠ O → j ≠ R → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, σ, _, hz, hO => ⟨σ, WExec.mono (WExec.whsF (by simpa [wbit] using hz)) (by omega), by simp, hO, rfl, by simp,
      fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | m + 1, σ, hT, hz, hO => by
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap O true σ hO
    obtain ⟨σ2, s2, r2, r2h, o2, v2, c2⟩ := fwd_facts cap R σ1
    have R1 := o1 R hOR.symm
    obtain ⟨τ, s3, eO, eOh, eR, eRh, o3, v3, c3⟩ := onesLoop_spec O R hOR m σ2
      (fun i hi => by rw [r2, r2h, R1.1, R1.2, show σ.sh R + 1 + i = σ.sh R + (i + 1) by omega]; exact hT _ (by omega))
      (by rw [r2, r2h, R1.1, R1.2, show σ.sh R + 1 + m = σ.sh R + (m + 1) by omega]; exact hz)
      (by rw [(o2 O hOR).1, (o2 O hOR).2, e1h])
    have hw : wbit σ R = true := by simpa [wbit] using hT 0 (by omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) (by rw [Nat.succ_mul]; omega), ?_, eOh, ?_, ?_,
      fun j h1 h2 => ((o1 j h1).trans' (o2 j h2)).trans' (o3 j h1 h2), by rw [v3, v2, v1], by rw [c3, c2, c1]⟩
    · rw [eO, (o2 O hOR).1, e1, List.replicate_succ]; simp
    · rw [eR, r2, R1.1]
    · rw [eRh, r2h, R1.2]; omega

/-- **The unary width** `1^h` from the ruler `false :: 1^h`; the ruler's head returns to `0`. -/
theorem onesW_spec (h : ℕ) (σ : WState ns nr) (hR : σ.st (Sc 3) = false :: List.replicate h true)
    (hRh : σ.sh (Sc 3) = 0) (hO : σ.sh (Sc 5) = (σ.st (Sc 5)).length) :
    ∃ τ, WExec cap (onesW Sc) σ τ (10 * h + 7) ∧ τ.st (Sc 5) = σ.st (Sc 5) ++ List.replicate h true ∧
      τ.sh (Sc 5) = (τ.st (Sc 5)).length ∧ τ.st (Sc 3) = σ.st (Sc 3) ∧ τ.sh (Sc 3) = 0 ∧
      (∀ j, j ≠ Sc 5 → j ≠ Sc 3 → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have d53 := sc_ne Sc 5 3 (by decide)
  obtain ⟨σ1, s1, r1, r1h, o1, v1, c1⟩ := fwd_facts cap (Sc 3) σ
  obtain ⟨σ2, s2, eO, eOh, eR, eRh, o2, v2, c2⟩ := onesLoop_spec cap (Sc 5) (Sc 3) d53 h σ1
    (fun i hi => by rw [r1, r1h, hR, hRh, Nat.zero_add, ruler_read]; simp [hi])
    (by rw [r1, r1h, hR, hRh, Nat.zero_add, ruler_read]; simp) (by rw [(o1 _ d53).1, (o1 _ d53).2, hO])
  obtain ⟨σ3, s3, r3, r3h, o3, v3, c3⟩ : ∃ σ3, WExec cap (.bwd (Sc 3)) σ2 σ3 1 ∧ σ3.st (Sc 3) = σ2.st (Sc 3) ∧
      σ3.sh (Sc 3) = σ2.sh (Sc 3) - 1 ∧ (∀ j, j ≠ Sc 3 → Same σ2 σ3 j) ∧ σ3.val = σ2.val ∧ σ3.cell = σ2.cell :=
    ⟨_, WExec.bwd (Sc 3) σ2, rfl, by simp, fun j hj => ⟨rfl, by simp [Function.update_of_ne hj]⟩, rfl, rfl⟩
  have hR3 : σ3.st (Sc 3) = false :: List.replicate h true := by rw [r3, eR, r1, hR]
  have s4 := rewindR_spec cap (Sc 3) h σ3 (by rw [r3h, eRh, r1h, hRh]; omega)
    (fun j h1 h2 => by rw [hR3]; have := ruler_read h (j - 1); rw [show 1 + (j - 1) = j by omega] at this
                       rw [this]; simp; omega)
    (by rw [hR3]; rfl)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]; rw [(o3 _ d53).1, eO, (o1 _ d53).1]
  · simp only [WState.seth_st, WState.seth_sh]; rw [Function.update_of_ne d53, (o3 _ d53).1, (o3 _ d53).2, eOh]
  · simp only [WState.seth_st]; rw [hR3, hR]
  · intro j h1 h2
    exact ⟨by simp only [WState.seth_st]; rw [(o3 j h2).1, (o2 j h1 h2).1, (o1 j h2).1],
      by simp only [WState.seth_sh]; rw [Function.update_of_ne h2, (o3 j h2).2, (o2 j h1 h2).2, (o1 j h2).2]⟩
  · simp only [WState.seth_val]; rw [v3, v2, v1]
  · simp only [WState.seth_cell]; rw [c3, c2, c1]

end Scan

end NearCubicWires.WireExponent3_5.PrimT

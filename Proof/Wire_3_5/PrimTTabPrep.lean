import Proof.Wire_3_5.PrimTTabScan

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

section Prep
variable {ns nr : ℕ} (cap : ℕ) (Sp : Fin 11 ↪ Fin (ns + 1))

theorem sp_ne (i j : Fin 11) (h : i ≠ j) : Sp i ≠ Sp j := Sp.injective.ne h

/-! ## The programs -/

/-- One `false` on each register tape. -/
def regsW : WM ns nr := .seq (emitW (Sp 8) false) (.seq (emitW (Sp 9) false) (emitW (Sp 10) false))

/-- Copy the framed payload: one pair per bit, one unary cell per bit. -/
def payW : WM ns nr :=
  .whs (Sp 0) (.seq (emitW (Sp 3) true) (.seq (.fwd (Sp 0)) (.seq (.ifs (Sp 0) (emitW (Sp 3) true) (emitW (Sp 3) false))
    (.seq (emitW (Sp 4) true) (.fwd (Sp 0))))))

/-- The arity template, with one register cell per arity cell. -/
def arityW : WM ns nr := .whs (Sp 1) (.seq (emitW (Sp 5) true) (.seq (regsW Sp) (.fwd (Sp 1))))

/-- The two copies of `1^L`, with one register cell per cell. -/
def boundW : WM ns nr :=
  .whs (Sp 2) (.seq (emitW (Sp 6) true) (.seq (emitW (Sp 7) true) (.seq (regsW Sp) (.fwd (Sp 2)))))

/-- **The preparation pass.** -/
def prepW : WM ns nr :=
  .seq (.fwd (Sp 0)) (.seq (.whs (Sp 0) (.seq (.fwd (Sp 0)) (.fwd (Sp 0)))) (.seq (.fwd (Sp 0)) (.seq (payW Sp)
    (.seq (emitW (Sp 3) false) (.seq (emitW (Sp 4) true) (.seq (emitW (Sp 5) false) (.seq (arityW Sp)
    (.seq (emitW (Sp 5) false) (.seq (boundW Sp) (regsW Sp))))))))))

/-! ## The register cells -/

/-- The three register tapes hold `r`, heads at their ends. -/
def RegsAt (σ : WState ns nr) (r : List Bool) : Prop :=
  (σ.st (Sp 8) = r ∧ σ.sh (Sp 8) = r.length) ∧ (σ.st (Sp 9) = r ∧ σ.sh (Sp 9) = r.length) ∧
    (σ.st (Sp 10) = r ∧ σ.sh (Sp 10) = r.length)

theorem regsAt_same {σ τ : WState ns nr} {r : List Bool} (h : RegsAt Sp σ r) (h8 : Same σ τ (Sp 8))
    (h9 : Same σ τ (Sp 9)) (h10 : Same σ τ (Sp 10)) : RegsAt Sp τ r :=
  ⟨⟨h8.1.trans h.1.1, h8.2.trans h.1.2⟩, ⟨h9.1.trans h.2.1.1, h9.2.trans h.2.1.2⟩,
    ⟨h10.1.trans h.2.2.1, h10.2.trans h.2.2.2⟩⟩

theorem regsAt_congr {σ : WState ns nr} {r r' : List Bool} (h : RegsAt Sp σ r) (e : r = r') : RegsAt Sp σ r' := e ▸ h

theorem regs_spec (σ : WState ns nr) (r : List Bool) (hr : RegsAt Sp σ r) :
    ∃ τ, WExec cap (regsW Sp) σ τ 11 ∧ RegsAt Sp τ (r ++ [false]) ∧
      (∀ j, j ≠ Sp 8 → j ≠ Sp 9 → j ≠ Sp 10 → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have d89 := sp_ne Sp 8 9 (by decide); have d810 := sp_ne Sp 8 10 (by decide); have d910 := sp_ne Sp 9 10 (by decide)
  obtain ⟨⟨h8, h8h⟩, ⟨h9, h9h⟩, ⟨h10, h10h⟩⟩ := hr
  obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (Sp 8) false σ (by rw [h8h, h8])
  obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap (Sp 9) false σ1
    (by rw [(o1 _ d89.symm).1, (o1 _ d89.symm).2, h9h, h9])
  obtain ⟨τ, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap (Sp 10) false σ2
    (by rw [(o2 _ d910.symm).1, (o2 _ d910.symm).2, (o1 _ d810.symm).1, (o1 _ d810.symm).2, h10h, h10])
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
    fun j h1 h2 h3 => ((o1 j h1).trans' (o2 j h2)).trans' (o3 j h3), by rw [v3, v2, v1], by rw [c3, c2, c1]⟩
  · rw [(o3 _ d810).1, (o2 _ d89).1, e1, h8]
  · rw [(o3 _ d810).2, (o2 _ d89).2, e1h, e1, h8]
  · rw [(o3 _ d910).1, e2, (o1 _ d89.symm).1, h9]
  · rw [(o3 _ d910).2, e2h, e2, (o1 _ d89.symm).1, h9]
  · rw [e3, (o2 _ d910.symm).1, (o1 _ d810.symm).1, h10]
  · rw [e3h, e3, (o2 _ d910.symm).1, (o1 _ d810.symm).1, h10]

/-! ## The payload -/

theorem pay_spec (rest : List Bool) : ∀ (bs : List Bool) (pre f u : List Bool) (σ : WState ns nr),
    σ.st (Sp 0) = pre ++ (frameP bs ++ false :: rest) → σ.sh (Sp 0) = pre.length →
    σ.st (Sp 3) = f → σ.sh (Sp 3) = f.length → σ.st (Sp 4) = u → σ.sh (Sp 4) = u.length →
    ∃ τ, WExec cap (payW Sp) σ τ (bs.length * 20 + 1) ∧ τ.st (Sp 0) = σ.st (Sp 0) ∧
      τ.sh (Sp 0) = pre.length + 2 * bs.length ∧ τ.st (Sp 3) = f ++ frameP bs ∧ τ.sh (Sp 3) = (τ.st (Sp 3)).length ∧
      τ.st (Sp 4) = u ++ List.replicate bs.length true ∧ τ.sh (Sp 4) = (τ.st (Sp 4)).length ∧
      (∀ j, j ≠ Sp 0 → j ≠ Sp 3 → j ≠ Sp 4 → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, f, u, σ, hW, hWh, hF, hFh, hU, hUh => by
    have hz : wbit σ (Sp 0) = false := by
      simp only [wbit, hW, hWh]; unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), rfl, by simp [hWh], by simp [hF], by rw [hFh, hF]; (try simp),
      by simp [hU], by rw [hUh, hU]; (try simp), fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | b :: bs, pre, f, u, σ, hW, hWh, hF, hFh, hU, hUh => by
    have d03 := sp_ne Sp 0 3 (by decide); have d04 := sp_ne Sp 0 4 (by decide); have d34 := sp_ne Sp 3 4 (by decide)
    have hw : wbit σ (Sp 0) = true := by
      simp only [wbit, hW, hWh]; unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (Sp 3) true σ (by rw [hFh, hF])
    obtain ⟨σ2, s2, w2, w2h, o2, v2, c2⟩ := fwd_facts cap (Sp 0) σ1
    have hb : wbit σ2 (Sp 0) = b := by
      simp only [wbit, w2, w2h, (o1 _ d03).1, (o1 _ d03).2, hW, hWh]; unfold readTapeBit
      rw [List.getD_append_right _ _ _ _ (by omega)]; simp
    have F2 : σ2.sh (Sp 3) = (σ2.st (Sp 3)).length := by rw [(o2 _ d03.symm).1, (o2 _ d03.symm).2, e1h]
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ : ∃ σ3, WExec cap (.ifs (Sp 0) (emitW (Sp 3) true) (emitW (Sp 3) false)) σ2 σ3 4 ∧
        σ3.st (Sp 3) = σ2.st (Sp 3) ++ [b] ∧ σ3.sh (Sp 3) = (σ3.st (Sp 3)).length ∧
        (∀ j, j ≠ Sp 3 → Same σ2 σ3 j) ∧ σ3.val = σ2.val ∧ σ3.cell = σ2.cell := by
      obtain ⟨σ3, s, r⟩ := emit_facts cap (Sp 3) b σ2 F2
      refine ⟨σ3, ?_, r⟩
      cases b
      · exact WExec.mono (WExec.ifsF hb s) (by omega)
      · exact WExec.mono (WExec.ifsT hb s) (by omega)
    have U3 : Same σ σ3 (Sp 4) := ((o1 _ d34.symm).trans' (o2 _ d04.symm)).trans' (o3 _ d34.symm)
    obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap (Sp 4) true σ3 (by rw [U3.1, U3.2, hUh, hU])
    obtain ⟨σ5, s5, w5, w5h, o5, v5, c5⟩ := fwd_facts cap (Sp 0) σ4
    have W4 : Same σ2 σ4 (Sp 0) := (o3 _ d03).trans' (o4 _ d04)
    obtain ⟨τ, s6, t0, t0h, t3, t3h, t4, t4h, o6, v6, c6⟩ := pay_spec rest bs (pre ++ [true, b]) (f ++ [true, b])
      (u ++ [true]) σ5 (by rw [w5, W4.1, w2, (o1 _ d03).1, hW]; simp)
      (by rw [w5h, W4.2, w2h, (o1 _ d03).2, hWh]; simp)
      (by rw [(o5 _ d03.symm).1, (o4 _ d34).1, e3, (o2 _ d03.symm).1, e1, hF]; simp)
      (by rw [(o5 _ d03.symm).2, (o4 _ d34).2, e3h, e3, (o2 _ d03.symm).1, e1, hF]; simp)
      (by rw [(o5 _ d04.symm).1, e4, U3.1, hU]) (by rw [(o5 _ d04.symm).2, e4h, e4, U3.1, hU]; (try simp))
    have run : WExec cap (payW Sp) σ τ _ :=
      WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) s6
    refine ⟨τ, WExec.mono run (by simp; rw [Nat.succ_mul]; omega), by rw [t0, w5, W4.1, w2, (o1 _ d03).1],
      by rw [t0h]; simp; omega, by rw [t3]; simp, t3h,
      by rw [t4]; simp only [List.length_cons, List.replicate_succ, List.append_assoc, List.singleton_append], t4h,
      fun j h0 h3 h4 => ((((o1 j h3).trans' (o2 j h0)).trans' (o3 j h3)).trans' (o4 j h4)).trans' ((o5 j h0).trans'
        (o6 j h0 h3 h4)), by rw [v6, v5, v4, v3, v2, v1], by rw [c6, c5, c4, c3, c2, c1]⟩

/-! ## The arity template and the bounds -/

theorem arity_spec : ∀ (m : ℕ) (tm r : List Bool) (σ : WState ns nr),
    (∀ i < m, readTapeBit (σ.st (Sp 1)) (σ.sh (Sp 1) + i) = true) → readTapeBit (σ.st (Sp 1)) (σ.sh (Sp 1) + m) = false →
    σ.st (Sp 5) = tm → σ.sh (Sp 5) = tm.length → RegsAt Sp σ r →
    ∃ τ, WExec cap (arityW Sp) σ τ (m * 20 + 1) ∧ τ.st (Sp 1) = σ.st (Sp 1) ∧ τ.sh (Sp 1) = σ.sh (Sp 1) + m ∧
      τ.st (Sp 5) = tm ++ List.replicate m true ∧ τ.sh (Sp 5) = (τ.st (Sp 5)).length ∧
      RegsAt Sp τ (r ++ List.replicate m false) ∧
      (∀ j, j ≠ Sp 1 → j ≠ Sp 5 → j ≠ Sp 8 → j ≠ Sp 9 → j ≠ Sp 10 → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, tm, r, σ, _, hz, hT, hTh, hR => by
    refine ⟨σ, WExec.mono (WExec.whsF (by simpa [wbit] using hz)) (by simp), rfl, by simp, by simp [hT],
      by rw [hTh, hT]; (try simp), regsAt_congr Sp hR (by simp), fun _ _ _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | m + 1, tm, r, σ, hT1, hz, hT, hTh, hR => by
    have d15 := sp_ne Sp 1 5 (by decide)
    have d18 := sp_ne Sp 1 8 (by decide); have d19 := sp_ne Sp 1 9 (by decide); have d110 := sp_ne Sp 1 10 (by decide)
    have d58 := sp_ne Sp 5 8 (by decide); have d59 := sp_ne Sp 5 9 (by decide); have d510 := sp_ne Sp 5 10 (by decide)
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (Sp 5) true σ (by rw [hTh, hT])
    obtain ⟨σ2, s2, r2, o2, v2, c2⟩ := regs_spec cap Sp σ1 r
      (regsAt_same Sp hR (o1 _ d58.symm) (o1 _ d59.symm) (o1 _ d510.symm))
    obtain ⟨σ3, s3, w3, w3h, o3, v3, c3⟩ := fwd_facts cap (Sp 1) σ2
    have N2 : Same σ σ2 (Sp 1) := (o1 _ d15).trans' (o2 _ d18 d19 d110)
    have T3 : σ3.st (Sp 5) = tm ++ [true] ∧ σ3.sh (Sp 5) = (tm ++ [true]).length := by
      rw [(o3 _ d15.symm).1, (o3 _ d15.symm).2, (o2 _ d58 d59 d510).1, (o2 _ d58 d59 d510).2, e1h, e1, hT]; simp
    obtain ⟨τ, s4, n4, n4h, t4, t4h, r4, o4, v4, c4⟩ := arity_spec m (tm ++ [true]) (r ++ [false]) σ3
      (fun i hi => by
        rw [w3, w3h, N2.1, N2.2, show σ.sh (Sp 1) + 1 + i = σ.sh (Sp 1) + (i + 1) by omega]; exact hT1 _ (by omega))
      (by rw [w3, w3h, N2.1, N2.2, show σ.sh (Sp 1) + 1 + m = σ.sh (Sp 1) + (m + 1) by omega]; exact hz)
      T3.1 T3.2 (regsAt_same Sp r2 (o3 _ d18.symm) (o3 _ d19.symm) (o3 _ d110.symm))
    have hw : wbit σ (Sp 1) = true := by simpa [wbit] using hT1 0 (by omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) s4) (by rw [Nat.succ_mul]; omega),
      by rw [n4, w3, N2.1], by rw [n4h, w3h, N2.2]; omega, by rw [t4]; simp [List.replicate_succ], t4h,
      regsAt_congr Sp r4 (by simp [List.replicate_succ]),
      fun j h1 h5 h8 h9 h10 => (((o1 j h5).trans' (o2 j h8 h9 h10)).trans' (o3 j h1)).trans' (o4 j h1 h5 h8 h9 h10),
      by rw [v4, v3, v2, v1], by rw [c4, c3, c2, c1]⟩

theorem bound_spec : ∀ (m : ℕ) (w r : List Bool) (σ : WState ns nr),
    (∀ i < m, readTapeBit (σ.st (Sp 2)) (σ.sh (Sp 2) + i) = true) → readTapeBit (σ.st (Sp 2)) (σ.sh (Sp 2) + m) = false →
    σ.st (Sp 6) = w → σ.sh (Sp 6) = w.length → σ.st (Sp 7) = w → σ.sh (Sp 7) = w.length → RegsAt Sp σ r →
    ∃ τ, WExec cap (boundW Sp) σ τ (m * 30 + 1) ∧ τ.st (Sp 2) = σ.st (Sp 2) ∧
      τ.st (Sp 6) = w ++ List.replicate m true ∧ τ.sh (Sp 6) = (τ.st (Sp 6)).length ∧
      τ.st (Sp 7) = w ++ List.replicate m true ∧ τ.sh (Sp 7) = (τ.st (Sp 7)).length ∧
      RegsAt Sp τ (r ++ List.replicate m false) ∧
      (∀ j, j ≠ Sp 2 → j ≠ Sp 6 → j ≠ Sp 7 → j ≠ Sp 8 → j ≠ Sp 9 → j ≠ Sp 10 → Same σ τ j) ∧ τ.val = σ.val ∧
      τ.cell = σ.cell
  | 0, w, r, σ, _, hz, h6, h6h, h7, h7h, hR => by
    refine ⟨σ, WExec.mono (WExec.whsF (by simpa [wbit] using hz)) (by simp), rfl, by simp [h6],
      by rw [h6h, h6]; (try simp), by simp [h7], by rw [h7h, h7]; (try simp), regsAt_congr Sp hR (by simp),
      fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | m + 1, w, r, σ, hT1, hz, h6, h6h, h7, h7h, hR => by
    have d26 := sp_ne Sp 2 6 (by decide); have d27 := sp_ne Sp 2 7 (by decide); have d67 := sp_ne Sp 6 7 (by decide)
    have d28 := sp_ne Sp 2 8 (by decide); have d29 := sp_ne Sp 2 9 (by decide); have d210 := sp_ne Sp 2 10 (by decide)
    have d68 := sp_ne Sp 6 8 (by decide); have d69 := sp_ne Sp 6 9 (by decide); have d610 := sp_ne Sp 6 10 (by decide)
    have d78 := sp_ne Sp 7 8 (by decide); have d79 := sp_ne Sp 7 9 (by decide); have d710 := sp_ne Sp 7 10 (by decide)
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (Sp 6) true σ (by rw [h6h, h6])
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap (Sp 7) true σ1
      (by rw [(o1 _ d67.symm).1, (o1 _ d67.symm).2, h7h, h7])
    obtain ⟨σ3, s3, r3, o3, v3, c3⟩ := regs_spec cap Sp σ2 r
      (regsAt_same Sp hR ((o1 _ d68.symm).trans' (o2 _ d78.symm)) ((o1 _ d69.symm).trans' (o2 _ d79.symm))
        ((o1 _ d610.symm).trans' (o2 _ d710.symm)))
    obtain ⟨σ4, s4, w4, w4h, o4, v4, c4⟩ := fwd_facts cap (Sp 2) σ3
    have N3 : Same σ σ3 (Sp 2) := ((o1 _ d26).trans' (o2 _ d27)).trans' (o3 _ d28 d29 d210)
    have W6 : Same σ2 σ4 (Sp 6) := (o3 _ d68 d69 d610).trans' (o4 _ d26.symm)
    have W7 : Same σ2 σ4 (Sp 7) := (o3 _ d78 d79 d710).trans' (o4 _ d27.symm)
    obtain ⟨τ, s5, n5, t6, t6h, t7, t7h, r5, o5, v5, c5⟩ := bound_spec m (w ++ [true]) (r ++ [false]) σ4
      (fun i hi => by
        rw [w4, w4h, N3.1, N3.2, show σ.sh (Sp 2) + 1 + i = σ.sh (Sp 2) + (i + 1) by omega]; exact hT1 _ (by omega))
      (by rw [w4, w4h, N3.1, N3.2, show σ.sh (Sp 2) + 1 + m = σ.sh (Sp 2) + (m + 1) by omega]; exact hz)
      (by rw [W6.1, (o2 _ d67).1, e1, h6]) (by rw [W6.2, (o2 _ d67).2, e1h, e1, h6])
      (by rw [W7.1, e2, (o1 _ d67.symm).1, h7]) (by rw [W7.2, e2h, e2, (o1 _ d67.symm).1, h7])
      (regsAt_same Sp r3 (o4 _ d28.symm) (o4 _ d29.symm) (o4 _ d210.symm))
    have hw : wbit σ (Sp 2) = true := by simpa [wbit] using hT1 0 (by omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) s5)
        (by rw [Nat.succ_mul]; omega), by rw [n5, w4, N3.1],
      by rw [t6]; simp only [List.replicate_succ, List.append_assoc, List.singleton_append], t6h,
      by rw [t7]; simp only [List.replicate_succ, List.append_assoc, List.singleton_append], t7h,
      regsAt_congr Sp r5 (by simp only [List.replicate_succ, List.append_assoc, List.singleton_append]),
      fun j h2 h6 h7 h8 h9 h10 =>
        ((((o1 j h6).trans' (o2 j h7)).trans' (o3 j h8 h9 h10)).trans' (o4 j h2)).trans' (o5 j h2 h6 h7 h8 h9 h10),
      by rw [v5, v4, v3, v2, v1], by rw [c5, c4, c3, c2, c1]⟩

/-! ## The whole preparation -/

def prepCost (k n L : ℕ) : ℕ := 25 * k + 20 * n + 30 * L + 60

/-- **The preparation pass**: from `frame (natWord code)`, `1^n` and `1^L` (all at their starts, the outputs blank),
the decoder's `frame bits` with `bits = binary (natBitLength code) code`, `1^(|bits|+1)`, the template
`UnaryTemplate.tape n`, two copies of `1^L`, and three blank register tapes of `n + L + 1` cells. -/
theorem prepW_spec (code n L : ℕ) (σ : WState ns nr)
    (h0 : σ.st (Sp 0) = frame (natWord code)) (h0h : σ.sh (Sp 0) = 0)
    (h1 : σ.st (Sp 1) = List.replicate n true) (h1h : σ.sh (Sp 1) = 0)
    (h2 : σ.st (Sp 2) = List.replicate L true) (h2h : σ.sh (Sp 2) = 0)
    (hout : ∀ i : Fin 11, 3 ≤ i.val → σ.st (Sp i) = [] ∧ σ.sh (Sp i) = 0) :
    ∃ τ, WExec cap (prepW Sp) σ τ (prepCost (natBitLength code) n L) ∧
      τ.st (Sp 0) = σ.st (Sp 0) ∧ τ.st (Sp 1) = σ.st (Sp 1) ∧ τ.st (Sp 2) = σ.st (Sp 2) ∧
      τ.st (Sp 3) = frame (binary (natBitLength code) code) ∧
      τ.st (Sp 4) = List.replicate (natBitLength code + 1) true ∧ τ.st (Sp 5) = UnaryTemplate.tape n ∧
      τ.st (Sp 6) = List.replicate L true ∧ τ.st (Sp 7) = List.replicate L true ∧
      RegsAt Sp τ (List.replicate (n + L + 1) false) ∧
      (∀ j, (∀ i : Fin 11, j ≠ Sp i) → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  set k := natBitLength code with hk
  have d : ∀ i j : Fin 11, i ≠ j → Sp i ≠ Sp j := fun i j h => sp_ne Sp i j h
  have hlen : (natWord code).length = 2 * k + 1 := natWord_length' code
  -- 1-3: past the unary prefix and the separator
  obtain ⟨σ1, s1, w1, w1h, o1, v1, c1⟩ := fwd_facts cap (Sp 0) σ
  have s2 := skipFrameLoop_spec cap (Sp 0) k σ1
    (fun i hi => by
      rw [w1, w1h, h0, h0h, frame_eq_frameP, show 0 + 1 + 2 * i = 2 * i + 1 by omega,
        readTapeBit_frameP _ _ _ (by omega)]
      exact natWord_getD_lt code i hi)
    (by rw [w1, w1h, h0, h0h, frame_eq_frameP, show 0 + 1 + 2 * k = 2 * k + 1 by omega,
          readTapeBit_frameP _ _ _ (by omega)]
        exact natWord_getD_k code)
  set σ2 := σ1.seth (Sp 0) (σ1.sh (Sp 0) + 2 * k) with hσ2
  obtain ⟨σ3, s3, w3, w3h, o3, v3, c3⟩ := fwd_facts cap (Sp 0) σ2
  -- 4: the payload
  have hT3 : σ3.st (Sp 0) = frameP (List.replicate k true ++ [false]) ++
      (frameP (binary k code) ++ false :: []) := by
    rw [w3, hσ2]; simp only [WState.seth_st]; rw [w1, h0, frame_eq_frameP, frameP_natWord]; simp [hk, frameP_append']
  have hT3h : σ3.sh (Sp 0) = (frameP (List.replicate k true ++ [false])).length := by
    rw [w3h, hσ2]; simp [w1h, h0h]; omega
  have O3 : ∀ i : Fin 11, 3 ≤ i.val → σ3.st (Sp i) = [] ∧ σ3.sh (Sp i) = 0 := by
    intro i hi
    have hne : Sp i ≠ Sp 0 := d i 0 (by intro e; rw [e] at hi; simp at hi)
    have := hout i hi
    refine ⟨?_, ?_⟩
    · rw [(o3 _ hne).1, hσ2]; simp only [WState.seth_st]; rw [(o1 _ hne).1, this.1]
    · rw [(o3 _ hne).2, hσ2]; simp only [WState.seth_sh]; rw [Function.update_of_ne hne, (o1 _ hne).2, this.2]
  obtain ⟨σ4, s4, t0, t0h, t3, t3h, t4, t4h, o4, v4, c4⟩ := pay_spec cap Sp [] (binary k code)
    (frameP (List.replicate k true ++ [false])) [] [] σ3 hT3 hT3h (O3 3 (by decide)).1 (by rw [(O3 3 (by decide)).2]; rfl)
    (O3 4 (by decide)).1 (by rw [(O3 4 (by decide)).2]; rfl)
  -- 5-7: the frame's end, the unary cell, the template's start
  obtain ⟨σ5, s5, e5, e5h, o5, v5, c5⟩ := emit_facts cap (Sp 3) false σ4 t3h
  obtain ⟨σ6, s6, e6, e6h, o6, v6, c6⟩ := emit_facts cap (Sp 4) true σ5
    (by rw [(o5 _ (d 4 3 (by decide))).1, (o5 _ (d 4 3 (by decide))).2, t4h])
  have T5 : Same σ3 σ6 (Sp 5) := ((o4 _ (d 5 0 (by decide)) (d 5 3 (by decide)) (d 5 4 (by decide))).trans'
    (o5 _ (d 5 3 (by decide)))).trans' (o6 _ (d 5 4 (by decide)))
  obtain ⟨σ7, s7, e7, e7h, o7, v7, c7⟩ := emit_facts cap (Sp 5) false σ6
    (by rw [T5.1, T5.2, (O3 5 (by decide)).1, (O3 5 (by decide)).2]; rfl)
  -- 8: the arity cells
  have R7 : ∀ i : Fin 11, 8 ≤ i.val → Same σ3 σ7 (Sp i) := by
    intro i hi
    have n0 : Sp i ≠ Sp 0 := d i 0 (by intro e; rw [e] at hi; simp at hi)
    have n3 : Sp i ≠ Sp 3 := d i 3 (by intro e; rw [e] at hi; simp at hi)
    have n4 : Sp i ≠ Sp 4 := d i 4 (by intro e; rw [e] at hi; simp at hi)
    have n5 : Sp i ≠ Sp 5 := d i 5 (by intro e; rw [e] at hi; simp at hi)
    exact (((o4 _ n0 n3 n4).trans' (o5 _ n3)).trans' (o6 _ n4)).trans' (o7 _ n5)
  have RA7 : RegsAt Sp σ7 [] :=
    ⟨⟨by rw [(R7 8 (by decide)).1, (O3 8 (by decide)).1], by rw [(R7 8 (by decide)).2, (O3 8 (by decide)).2]; rfl⟩,
      ⟨by rw [(R7 9 (by decide)).1, (O3 9 (by decide)).1], by rw [(R7 9 (by decide)).2, (O3 9 (by decide)).2]; rfl⟩,
      ⟨by rw [(R7 10 (by decide)).1, (O3 10 (by decide)).1], by rw [(R7 10 (by decide)).2, (O3 10 (by decide)).2]; rfl⟩⟩
  have N7 : Same σ σ7 (Sp 1) := by
    have n0 := d 1 0 (by decide); have n3 := d 1 3 (by decide); have n4 := d 1 4 (by decide)
    have n5 := d 1 5 (by decide)
    have e12 : Same σ σ2 (Sp 1) := ⟨by rw [hσ2]; simp only [WState.seth_st]; rw [(o1 _ n0).1],
      by rw [hσ2]; simp only [WState.seth_sh]; rw [Function.update_of_ne n0, (o1 _ n0).2]⟩
    exact ((((e12.trans' (o3 _ n0)).trans' (o4 _ n0 n3 n4)).trans' (o5 _ n3)).trans' (o6 _ n4)).trans' (o7 _ n5)
  obtain ⟨σ8, s8, n8, n8h, t8, t8h, r8, o8, v8, c8⟩ := arity_spec cap Sp n [false] [] σ7
    (fun i hi => by rw [N7.1, N7.2, h1, h1h, Nat.zero_add]; unfold readTapeBit
                    rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp)
    (by rw [N7.1, N7.2, h1, h1h, Nat.zero_add]; simp [readTapeBit])
    (by rw [e7, T5.1, (O3 5 (by decide)).1]; rfl) (by rw [e7h, e7, T5.1, (O3 5 (by decide)).1]; rfl) RA7
  -- 9: the template's end
  obtain ⟨σ9, s9, e9, e9h, o9, v9, c9⟩ := emit_facts cap (Sp 5) false σ8 t8h
  -- 10: the bounds
  have Lw9 : Same σ σ9 (Sp 2) := by
    have n0 := d 2 0 (by decide); have n1 := d 2 1 (by decide); have n3 := d 2 3 (by decide)
    have n4 := d 2 4 (by decide); have n5 := d 2 5 (by decide); have n8 := d 2 8 (by decide)
    have n9 := d 2 9 (by decide); have n10 := d 2 10 (by decide)
    have e12 : Same σ σ2 (Sp 2) := ⟨by rw [hσ2]; simp only [WState.seth_st]; rw [(o1 _ n0).1],
      by rw [hσ2]; simp only [WState.seth_sh]; rw [Function.update_of_ne n0, (o1 _ n0).2]⟩
    exact ((((((e12.trans' (o3 _ n0)).trans' (o4 _ n0 n3 n4)).trans' (o5 _ n3)).trans' (o6 _ n4)).trans'
      (o7 _ n5)).trans' (o8 _ n1 n5 n8 n9 n10)).trans' (o9 _ n5)
  have W9 : ∀ i : Fin 11, 6 ≤ i.val → i.val ≤ 7 → σ9.st (Sp i) = [] ∧ σ9.sh (Sp i) = 0 := by
    intro i h6 h7
    have n0 : Sp i ≠ Sp 0 := d i 0 (by intro e; rw [e] at h6; simp at h6)
    have n1 : Sp i ≠ Sp 1 := d i 1 (by intro e; rw [e] at h6; simp at h6)
    have n3 : Sp i ≠ Sp 3 := d i 3 (by intro e; rw [e] at h6; simp at h6)
    have n4 : Sp i ≠ Sp 4 := d i 4 (by intro e; rw [e] at h6; simp at h6)
    have n5 : Sp i ≠ Sp 5 := d i 5 (by intro e; rw [e] at h6; simp at h6)
    have n8 : Sp i ≠ Sp 8 := d i 8 (by intro e; rw [e] at h7; simp at h7)
    have n9 : Sp i ≠ Sp 9 := d i 9 (by intro e; rw [e] at h7; simp at h7)
    have n10 : Sp i ≠ Sp 10 := d i 10 (by intro e; rw [e] at h7; simp at h7)
    have S := (((((o4 _ n0 n3 n4).trans' (o5 _ n3)).trans' (o6 _ n4)).trans' (o7 _ n5)).trans'
      (o8 _ n1 n5 n8 n9 n10)).trans' (o9 _ n5)
    exact ⟨by rw [S.1, (O3 i (by omega)).1], by rw [S.2, (O3 i (by omega)).2]⟩
  obtain ⟨σ10, s10, n10, t6, t6h, t7, t7h, r10, o10, v10, c10⟩ := bound_spec cap Sp L [] (List.replicate n false) σ9
    (fun i hi => by rw [Lw9.1, Lw9.2, h2, h2h, Nat.zero_add]; unfold readTapeBit
                    rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp)
    (by rw [Lw9.1, Lw9.2, h2, h2h, Nat.zero_add]; simp [readTapeBit])
    (W9 6 (by decide) (by decide)).1 (by rw [(W9 6 (by decide) (by decide)).2]; rfl)
    (W9 7 (by decide) (by decide)).1 (by rw [(W9 7 (by decide) (by decide)).2]; rfl)
    (regsAt_same Sp (regsAt_congr Sp r8 (by simp)) (o9 _ (d 8 5 (by decide))) (o9 _ (d 9 5 (by decide)))
      (o9 _ (d 10 5 (by decide))))
  -- 11: the last register cell
  obtain ⟨τ, s11, r11, o11, v11, c11⟩ := regs_spec cap Sp σ10 _ r10
  have run : WExec cap (prepW Sp) σ τ _ :=
    WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 (WExec.seq s7
      (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 s11)))))))))
  have hbl := binary_length k code
  refine ⟨τ, WExec.mono run (by unfold prepCost; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by
    rw [v11, v10, v9, v8, v7, v6, v5, v4, v3, hσ2]; simp [v1], by rw [c11, c10, c9, c8, c7, c6, c5, c4, c3, hσ2]; simp [c1]⟩
  · -- the framed natWord is only read
    have n := fun (i : Fin 11) (h : i ≠ 0) => d 0 i (Ne.symm h)
    rw [(o11 _ (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1,
      (o10 _ (n 2 (by decide)) (n 6 (by decide)) (n 7 (by decide)) (n 8 (by decide)) (n 9 (by decide))
        (n 10 (by decide))).1, (o9 _ (n 5 (by decide))).1,
      (o8 _ (n 1 (by decide)) (n 5 (by decide)) (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1,
      (o7 _ (n 5 (by decide))).1, (o6 _ (n 4 (by decide))).1, (o5 _ (n 3 (by decide))).1, t0, w3, hσ2]
    simp only [WState.seth_st]; rw [w1]
  · have n := fun (i : Fin 11) (h : i ≠ 1) => d 1 i (Ne.symm h)
    rw [(o11 _ (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1,
      (o10 _ (n 2 (by decide)) (n 6 (by decide)) (n 7 (by decide)) (n 8 (by decide)) (n 9 (by decide))
        (n 10 (by decide))).1, (o9 _ (n 5 (by decide))).1, n8, N7.1]
  · have n := fun (i : Fin 11) (h : i ≠ 2) => d 2 i (Ne.symm h)
    rw [(o11 _ (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1, n10, Lw9.1]
  · have n := fun (i : Fin 11) (h : i ≠ 3) => d 3 i (Ne.symm h)
    rw [(o11 _ (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1,
      (o10 _ (n 2 (by decide)) (n 6 (by decide)) (n 7 (by decide)) (n 8 (by decide)) (n 9 (by decide))
        (n 10 (by decide))).1, (o9 _ (n 5 (by decide))).1,
      (o8 _ (n 1 (by decide)) (n 5 (by decide)) (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1,
      (o7 _ (n 5 (by decide))).1, (o6 _ (n 4 (by decide))).1, e5, t3, frame_eq_frameP]
    simp
  · have n := fun (i : Fin 11) (h : i ≠ 4) => d 4 i (Ne.symm h)
    rw [(o11 _ (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1,
      (o10 _ (n 2 (by decide)) (n 6 (by decide)) (n 7 (by decide)) (n 8 (by decide)) (n 9 (by decide))
        (n 10 (by decide))).1, (o9 _ (n 5 (by decide))).1,
      (o8 _ (n 1 (by decide)) (n 5 (by decide)) (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1,
      (o7 _ (n 5 (by decide))).1, e6, (o5 _ (n 3 (by decide))).1, t4, List.replicate_succ']
    simp
  · have n := fun (i : Fin 11) (h : i ≠ 5) => d 5 i (Ne.symm h)
    rw [(o11 _ (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1,
      (o10 _ (n 2 (by decide)) (n 6 (by decide)) (n 7 (by decide)) (n 8 (by decide)) (n 9 (by decide))
        (n 10 (by decide))).1, e9, t8]
    simp [UnaryTemplate.tape]
  · have n := fun (i : Fin 11) (h : i ≠ 6) => d 6 i (Ne.symm h)
    rw [(o11 _ (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1, t6]; simp
  · have n := fun (i : Fin 11) (h : i ≠ 7) => d 7 i (Ne.symm h)
    rw [(o11 _ (n 8 (by decide)) (n 9 (by decide)) (n 10 (by decide))).1, t7]; simp
  · exact regsAt_congr Sp r11 (by rw [List.replicate_add, List.replicate_add]; rfl)
  · intro j hj
    have e12 : Same σ σ2 j := ⟨by rw [hσ2]; simp only [WState.seth_st]; rw [(o1 _ (hj 0)).1],
      by rw [hσ2]; simp only [WState.seth_sh]; rw [Function.update_of_ne (hj 0), (o1 _ (hj 0)).2]⟩
    have a3 := e12.trans' (o3 _ (hj 0))
    have a4 := a3.trans' (o4 _ (hj 0) (hj 3) (hj 4))
    have a5 := a4.trans' (o5 _ (hj 3))
    have a6 := a5.trans' (o6 _ (hj 4))
    have a7 := a6.trans' (o7 _ (hj 5))
    have a8 := a7.trans' (o8 _ (hj 1) (hj 5) (hj 8) (hj 9) (hj 10))
    have a9 := a8.trans' (o9 _ (hj 5))
    have a10 := a9.trans' (o10 _ (hj 2) (hj 6) (hj 7) (hj 8) (hj 9) (hj 10))
    exact a10.trans' (o11 _ (hj 8) (hj 9) (hj 10))

end Prep

end NearCubicWires.WireExponent3_5.PrimT

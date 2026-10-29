import SourceAdapters.RAMACSP.EmbedBridge
import SourceAdapters.RAMACSP.EmbedComplete

/-!
# the embedding theorem (`thm:embedding` Full embedding equivalence, the input-acceptance clause of `def:acsp`)

Paper: `thm:embedding`. The constructed affine instance accepts x̄
exactly when `ET(M,τ,x̄)` is satisfiable.

Consumer (type anchor): the `hE` argument of `affineConstraint_ownReduction_of_ESG` (`RAMACSP/Assembly.lean`),
`∀ irrPoly V, IrreducibleChoice irrPoly → EmbeddingEquivalence V irrPoly (ownCons V irrPoly)`, with
`EmbeddingEquivalence` as defined in `RAMACSP/CheckClauses.lean`:
`RAMTrace.Satisfiable (Field2 irr) M_n mnKind τ x̄ ↔ (ownInst …).Accepts x̄`.

Proof, consumer backward:
- E1 `consPoly_eval` (`EmbedBridge`): the `Accepts` constraint at `α` is `Routing.evaluate` of the emitted sum;
- E2 `ownItems_disjoint` (`EmbedDisjoint`) with `Selectors.eval_emit_iff`: `P = 0` on `H` iff every item's
  equation vanishes where its guard holds;
- ⇐: E4 `holds_of_table` (`EmbedSound`) on the table `A.eval`, with the routing soundness and the direct input
  subspace (`dock_input`);
- ⇒: E5 `table_of_trace` and `machine_vanish` (`EmbedComplete`), the routing completion and one interpolation
  (`Routing.contract`), the routing polynomial (`RoutingPolynomialCorrect`).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.RAMTrace Routing Placement
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Adapters.ShortPCP Polynomial

/-! ## Emitted sums without disjointness; sums over appended lists -/

section Emit

variable {F : Type} [Field F] [CharP F 2] {m : ℕ} {e : Fin m → F} (coords : Coordinates m e)

theorem eval_emit_zero (ts : List (Term m F)) (reads : Vars → F) (v : Fin m → Bool) (h : reads none = cubeEval m e v)
    (hz : ∀ t ∈ ts, patternHolds t.guard v → MvPolynomial.eval reads t.equation = 0) :
    MvPolynomial.eval reads (emit coords ts) = 0 := by
  induction ts with
  | nil => simp [emit]
  | cons t ts ih =>
    rw [Selectors.eval_emit_cons coords t ts reads v h, ih fun u hu => hz u (by simp [hu])]
    split_ifs with hp
    · rw [hz t (by simp) hp, add_zero]
    · rw [add_zero]

omit [CharP F 2] in
theorem emit_append (ts ts' : List (Term m F)) : emit coords (ts ++ ts') = emit coords ts + emit coords ts' := by
  simp [emit, List.map_append, List.sum_append]

end Emit

/-- The reads of `Routing.evaluate` as a named function. -/
def evalReads {F : Type} [Field F] (l : Layout) (e : Fin l.m → F) (A : F → F) (z : F) : Vars → F :=
  fun w => Option.elim w z fun b => A (z + maskEval l.m e b)

theorem evaluate_eq {F : Type} [Field F] (l : Layout) (e : Fin l.m → F) (A : F → F) (z : F) (p : MP F) :
    Routing.evaluate l e A z p = MvPolynomial.eval (evalReads l e A z) p := by
  unfold Routing.evaluate evalReads
  congr 2
  funext w
  cases w <;> rfl

theorem termList_append {F : Type} [Field F] {m : ℕ} (a b : List (Pattern m × Routing.Expr F)) :
    Circuit.termList (a ++ b) = Circuit.termList a ++ Circuit.termList b := by
  simp [Circuit.termList]

theorem termList_routingPairs {F : Type} [Field F] [CharP F 2] (l : Layout) :
    Circuit.termList (routingPairs (F := F) l) = routingTerms l := by
  simp only [Circuit.termList, routingPairs, routingTerms, List.map_map]
  rfl

theorem cast_roundtrip {n m : ℕ} (h : n = m) (f : Fin n → Bool) : (fun b => f (Fin.cast h.symm (Fin.cast h b))) = f := by
  subst h; rfl

/-! ## The instance -/

section Instance

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (r : ClockRequest)

theorem ownRam_w : (ownRam V r).w = 2 ^ wordExp V r.2 := wordW_eq V r.2

theorem ownXbar_NA (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) :
    (ownXbar V r).length / (ownRam V r).w = 2 ^ inRecExp V r := by
  obtain ⟨hpow, -, hw, -, -⟩ := inExp_facts V r hn hnt
  rw [hpow, ownRam_w, Nat.pow_div hw (by norm_num)]
  rfl

variable [Fact (Irreducible (ownIrr V irrPoly (ownCons V irrPoly) r))]
  (hI : Published.Shoup.IrreducibleChoice irrPoly) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2)
include hI

/-- The coordinate expressions are the coordinates (`app:affine-embedding`: `λ_a(Σ u_b e_b) = u_a`). -/
theorem ownLam_eval (A : OwnF V irrPoly r → OwnF V irrPoly r) :
    ∀ j < tau V r.2, ∀ u < 2 ^ (ownLayout V r.2).m,
      Routing.evaluate (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A
        (maskEval (ownLayout V r.2).m (ownBasis V irrPoly (ownCons V irrPoly) r) u)
        ((ownLam V irrPoly r hI) j).poly = if u.testBit j then 1 else 0 := by
  intro j hj u _
  have hjm : j < (ownLayout V r.2).m := by
    have := tau_lt_domExp V r.2; rw [ownLayout_m]; omega
  rw [show ownLam V irrPoly r hI j = lamExpr ((ownCoords V irrPoly r hI).coeff ⟨j, hjm⟩) from dif_pos hjm,
    evaluate_lamExpr]
  exact (ownCoords V irrPoly r hI).on_cube ⟨j, hjm⟩ fun b => u.testBit b.val

include hn hnt

/-- The `Accepts` constraint at every `α ∈ H` is the emitted sum at the cube point. -/
theorem accepts_cons_iff (A : (OwnF V irrPoly r)[X]) :
    (∀ coeff : Fin (ownInstance V irrPoly r).mH → Bool,
      MvPolynomial.eval (Fin.cons ((ownInstance V irrPoly r).hElt coeff) fun i : Fin (ownInstance V irrPoly r).cN =>
        A.eval ((ownInstance V irrPoly r).nbrFn i ((ownInstance V irrPoly r).hElt coeff))) (ownInstance V irrPoly r).consPoly = 0) ↔
    ∀ v : Fin (ownLayout V r.2).m → Bool,
      Routing.evaluate (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A.eval
        (cubeEval _ (ownBasis V irrPoly (ownCons V irrPoly) r) v) (ownEmit V irrPoly r hI) = 0 := by
  have hm := ownInst_mH V irrPoly (ownCons V irrPoly) r
  constructor
  · intro h v
    have := h fun b => v (Fin.cast hm b)
    rw [consPoly_eval V irrPoly r hI hn hnt, hElt_eq_cubeEval] at this
    exact this
  · intro h coeff
    rw [consPoly_eval V irrPoly r hI hn hnt]
    have e2 := hElt_eq_cubeEval V irrPoly (ownCons V irrPoly) r (fun b' => coeff (Fin.cast hm.symm b'))
    beta_reduce at e2
    rw [cast_roundtrip hm coeff] at e2
    rw [e2]
    exact h _

/-- E1 + E2: a polynomial satisfying the `Accepts` constraint makes every emitted item's equation vanish where its
guard holds. -/
theorem sem_of_accepts (A : (OwnF V irrPoly r)[X])
    (hP : ∀ coeff : Fin (ownInstance V irrPoly r).mH → Bool,
      MvPolynomial.eval (Fin.cons ((ownInstance V irrPoly r).hElt coeff) fun i : Fin (ownInstance V irrPoly r).cN =>
        A.eval ((ownInstance V irrPoly r).nbrFn i ((ownInstance V irrPoly r).hElt coeff))) (ownInstance V irrPoly r).consPoly = 0) :
    ∀ v, ∀ t ∈ ownItems V r (ownLam V irrPoly r hI), patternHolds t.1 v →
      Routing.evaluate (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A.eval
        (cubeEval _ (ownBasis V irrPoly (ownCons V irrPoly) r) v) t.2.poly = 0 := by
  intro v t ht hg
  have h1 := (accepts_cons_iff V irrPoly r hI hn hnt A).mp hP v
  rw [evaluate_eq] at h1 ⊢
  exact (Selectors.eval_emit_iff (ownCoords V irrPoly r hI) (Circuit.termList (ownItems V r (ownLam V irrPoly r hI)))
    (ownItems_disjoint V r hn hnt (ownLam V irrPoly r hI)) (evalReads _ _ A.eval _) v rfl).mp h1
    ⟨t.1, t.2.poly⟩ (List.mem_map_of_mem ht) hg

omit hn hnt in
/-- The routing items then give the routing equations (`RoutingPolynomialCorrect`). -/
theorem localRouting_of_sem (A : OwnF V irrPoly r → OwnF V irrPoly r)
    (hS : ∀ v, ∀ t ∈ ownItems V r (ownLam V irrPoly r hI), patternHolds t.1 v →
      Routing.evaluate (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A
        (cubeEval _ (ownBasis V irrPoly (ownCons V irrPoly) r) v) t.2.poly = 0) :
    LocalRouting (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A := by
  refine (Routing.contract.polynomial (ownLayout V r.2) _ (ownBasis_independent V irrPoly (ownCons V irrPoly) r hI)
    (ownCoords V irrPoly r hI) A).mp fun z hz => ?_
  obtain ⟨v, rfl⟩ := hz
  rw [evaluate_eq]
  refine (Selectors.eval_emit_iff (ownCoords V irrPoly r hI) (routingTerms (ownLayout V r.2))
    (routingTerms_disjoint _) (evalReads _ _ A _) v rfl).mpr fun t ht hg => ?_
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp ht
  have := hS v (it.guard _, it.expr _) (List.mem_append_left _ (List.mem_map_of_mem hit)) hg
  rw [evaluate_eq] at this
  exact this

omit [Fact (Irreducible (ownIrr V irrPoly (ownCons V irrPoly) r))] hI in
theorem xbar_index (c0 b : ℕ) (hc0 : c0 < 2 ^ inRecExp V r) (hb : b < 2 ^ wordExp V r.2) :
    c0 * 2 ^ wordExp V r.2 + b < (ownXbar V r).length ∧ (c0 * 2 ^ wordExp V r.2 + b) / 2 ^ wordExp V r.2 = c0 ∧
      (c0 * 2 ^ wordExp V r.2 + b) % 2 ^ wordExp V r.2 = b := by
  obtain ⟨hpow, -, hw, -, -⟩ := inExp_facts V r hn hnt
  have hpos := Nat.two_pow_pos (wordExp V r.2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hpow]
    have e : 2 ^ inExp V r = 2 ^ inRecExp V r * 2 ^ wordExp V r.2 := by
      rw [← pow_add]; unfold inRecExp; congr 1; omega
    rw [e]
    have : (c0 + 1) * 2 ^ wordExp V r.2 ≤ 2 ^ inRecExp V r * 2 ^ wordExp V r.2 := Nat.mul_le_mul_right _ hc0
    rw [Nat.add_mul, one_mul] at this
    omega
  · rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hb, add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

omit [Fact (Irreducible (ownIrr V irrPoly (ownCons V irrPoly) r))] hI hn hnt in
theorem recCell_va_col (b : ℕ) : (recCell (.va, b)).col (wordExp V r.2) = b := by
  simp [recCell, Cell.col, RecField.tag]

omit hI hn hnt in
theorem hElt_in_label (i : ℕ) (A : OwnF V irrPoly r → OwnF V irrPoly r) (c0 b : ℕ) (hc : i / 2 ^ wordExp V r.2 = c0)
    (hb : i % 2 ^ wordExp V r.2 = b) :
    A (label (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) (2 ^ tau V r.2 + i / 2 ^ wordExp V r.2) 0
      (i % 2 ^ wordExp V r.2) 0 0) =
    cellAt (ownBasis V irrPoly (ownCons V irrPoly) r) (wordExp V r.2) A (2 ^ tau V r.2 + c0) 0 (recCell (.va, b)) := by
  rw [hc, hb]
  unfold cellAt
  rw [recCell_va_col]
  rfl

/-- **The embedding theorem at one clock request** (`thm:embedding` Full embedding equivalence). -/
theorem embedding_at :
    RAMTrace.Satisfiable (Field2 (ownIrr V irrPoly (ownCons V irrPoly) r)) (ownRam V r) RAMTrace.mnKind
        (timeExp (clockConst V) r.2) (padInput (clockConst V) r.2 r.1.2) ↔
      (ownInst V irrPoly (ownCons V irrPoly) r).Accepts (ownXbar V r) := by
  have c := ownCtx V r hn hnt
  have hInd := ownBasis_independent V irrPoly (ownCons V irrPoly) r hI
  have hNA := ownXbar_NA V r hn hnt
  obtain ⟨hpow, -, hw, hlt, h2⟩ := inExp_facts V r hn hnt
  have hwpos := Nat.two_pow_pos (wordExp V r.2)
  constructor
  · -- ⇒ (E5): route the trace's records, fill the machine values, interpolate
    rintro ⟨tr, hH⟩
    have hH' : Holds (ownRam V r) RAMTrace.mnKind (tau V r.2) (ownXbar V r) tr := hH
    obtain ⟨A', hLR, hsrc, hdst, htime, hsort⟩ := table_of_trace _ hInd c RAMTrace.mnKind (ownXbar V r) tr hH'
    obtain ⟨A, hdeg, hAA'⟩ := Routing.contract.interpolation (ownLayout V r.2).m _ hInd A'
    have hMV := machine_vanish _ c A' tr RAMTrace.mnKind (ownLam V irrPoly r hI) hsrc hdst htime hsort hH' hNA
      (ownLam_eval V irrPoly r hI A')
    have hB5 : ∀ c0 < 2 ^ inRecExp V r, ∀ b < (ownRam V r).w,
        tr.src (2 ^ tau V r.2 + c0) .va b = if (ownXbar V r).getD (c0 * (ownRam V r).w + b) false then 1 else 0 := by
      have h := hH'
      unfold Holds at h
      dsimp only at h
      rw [hNA] at h
      intro c0 hc0 b hb
      exact (h.2.2.2.2.2.2.2.2.2.2.2.2.1 c0 hc0).2.2.2.2.2.2 b hb
    refine ⟨?_, A, ?_, ?_, ?_⟩
    · rw [ownInst_m]; exact hpow
    · rw [ownInst_mH]
      exact hdeg
    · refine (accepts_cons_iff V irrPoly r hI hn hnt A).mpr ?_
      intro v
      have hz : InH _ (ownBasis V irrPoly (ownCons V irrPoly) r) (cubeEval _ (ownBasis V irrPoly (ownCons V irrPoly) r) v) :=
        ⟨v, rfl⟩
      rw [evaluate_eq]
      have hreads : evalReads (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A.eval
          (cubeEval _ (ownBasis V irrPoly (ownCons V irrPoly) r) v) =
          evalReads (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A'
            (cubeEval _ (ownBasis V irrPoly (ownCons V irrPoly) r) v) := by
        funext w
        cases w with
        | none => rfl
        | some b => exact hAA' _ (LayoutFacts.inH_translate _ _ b _ hz)
      rw [hreads]
      show MvPolynomial.eval _ (Routing.emit (ownCoords V irrPoly r hI)
        (Circuit.termList (routingPairs (ownLayout V r.2) ++ machineItems (ownLayout V r.2) (wordExp V r.2)
          (regCount V) (codeLen V) (ownRam V r) RAMTrace.mnKind (tau V r.2) (inRecExp V r)
          (ownLam V irrPoly r hI)))) = 0
      rw [termList_append, emit_append, termList_routingPairs, map_add]
      have hr := (Routing.contract.polynomial _ _ hInd (ownCoords V irrPoly r hI) A').mpr hLR _ hz
      rw [evaluate_eq] at hr
      rw [hr, zero_add]
      refine eval_emit_zero (ownCoords V irrPoly r hI) _ _ v rfl fun t ht hg => ?_
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp ht
      have := hMV v it hit hg
      rw [evaluate_eq] at this
      exact this
    · intro i hi
      rw [dock_input V irrPoly (ownCons V irrPoly) r hI Routing.affineRouting hn hnt i hi,
        hAA' _ (LayoutFacts.label_mem _ _ _ _ _ _ _)]
      have hb : i % 2 ^ wordExp V r.2 < 2 ^ wordExp V r.2 := Nat.mod_lt _ hwpos
      have hi' : i < 2 ^ inRecExp V r * 2 ^ wordExp V r.2 := by
        rw [← pow_add, show inRecExp V r + wordExp V r.2 = inExp V r by unfold inRecExp; omega, ← hpow]; exact hi
      have hc0 : i / 2 ^ wordExp V r.2 < 2 ^ inRecExp V r := (Nat.div_lt_iff_lt_mul hwpos).mpr hi'
      have hτ := tau_lt_wordW V r.2 (by omega)
      have hx : 2 ^ tau V r.2 + i / 2 ^ wordExp V r.2 < 2 ^ (tau V r.2 + 1) := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) c.ha; rw [pow_succ]; omega
      have key := hElt_in_label V irrPoly r i A' (i / 2 ^ wordExp V r.2) (i % 2 ^ wordExp V r.2) rfl rfl
      have hsv := hsrc _ hx (.va, i % 2 ^ wordExp V r.2)
        (show i % 2 ^ wordExp V r.2 < (ownRam V r).w by rw [ownRam_w]; exact hb)
      have hbv := hB5 _ hc0 (i % 2 ^ wordExp V r.2) (by rw [ownRam_w]; exact hb)
      rw [ownRam_w, Nat.mul_comm, Nat.div_add_mod, List.getD_eq_getElem _ _ hi] at hbv
      exact key.trans (hsv.trans hbv)
  · -- ⇐ (E4): the table `A` read as an event trace
    rintro ⟨-, A, -, hP, hin⟩
    have hS := sem_of_accepts V irrPoly r hI hn hnt A hP
    have hR := localRouting_of_sem V irrPoly r hI A.eval hS
    have hM : ∀ v, ∀ t ∈ machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r)
        RAMTrace.mnKind (tau V r.2) (inRecExp V r) (ownLam V irrPoly r hI), patternHolds t.1 v →
        Routing.evaluate (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A.eval
          (cubeEval _ (ownBasis V irrPoly (ownCons V irrPoly) r) v) t.2.poly = 0 :=
      fun v t ht hg => hS v t (List.mem_append_right _ ht) hg
    have hva : ∀ c0 < 2 ^ inRecExp V r, ∀ b < (ownRam V r).w,
        cellAt (ownBasis V irrPoly (ownCons V irrPoly) r) (wordExp V r.2) A.eval (2 ^ tau V r.2 + c0) 0
          (recCell (.va, b)) = if (ownXbar V r).getD (c0 * (ownRam V r).w + b) false then 1 else 0 := by
      intro c0 hc0 b hb
      rw [ownRam_w] at hb ⊢
      obtain ⟨hi, hdiv, hmod⟩ := xbar_index V r hn hnt c0 b hc0 hb
      have h0 := hin _ hi
      rw [dock_input V irrPoly (ownCons V irrPoly) r hI Routing.affineRouting hn hnt _ hi] at h0
      have key := hElt_in_label V irrPoly r _ A.eval c0 b hdiv hmod
      rw [List.getD_eq_getElem _ _ hi]
      exact key.symm.trans h0
    exact ⟨_, holds_of_table _ hInd c RAMTrace.mnKind (ownLam V irrPoly r hI) A.eval hM hR (ownXbar V r) hNA
      (ownLam_eval V irrPoly r hI A.eval) hva⟩

end Instance

/-- **the embedding theorem** (`thm:embedding` Full embedding equivalence; the input-acceptance clause of `def:acsp`, the interpolation argument in `thm:embedding`),
for the emitted constraint circuit `ownCons` — exactly the `hE` argument of `affineConstraint_ownReduction_of_ESG`. -/
theorem embeddingEquivalence : ∀ (irrPoly : ℕ → (ZMod 2)[X]) (V : Verifier),
    Published.Shoup.IrreducibleChoice irrPoly → EmbeddingEquivalence V irrPoly (ownCons V irrPoly) := by
  intro irrPoly V hI r hn hnt _
  exact embedding_at V irrPoly r hI hn hnt

end NearCubicGates.Adapters.RAMACSP

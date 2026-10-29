import SourceAdapters.Compile.OraclePrintParse

/-!
# The printer builds the node records: input gates, vectors, oracle gates, rounds, verdict

proof of `thm:short-pcp-ours`, Step 4 ("Convert this computation into a circuit in the standard way"): the circuit is the input gates, the
initial formulas, `fuel` rounds (the query address bits, one oracle gate on them, the transition formulas reading the
answer) and the verdict. This module realizes the plan `planPS` of `OraclePrintPlan` in the cell language on the
token machine representation `Rep` (node records in `NS`, wire map in `WM`):
* `inputsP`: the input gates `.input i`, wire map `[0, …, ell)`;
* `copyW`: the outputs of a vector (store `W2`) become the wire map;
* `oracleP`: the oracle gate record `[5, 0, 0] ++ addresses`, its index written at wire-map entry `clockBits`;
* `roundP`/`roundsP`: one/`fuel` clock rounds (`roundPS`);
* `verdictP`: the verdict template, its output wire popped to `OUTR`.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource
open NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Compile (OracleCompilationRequest)
open NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicGates.Adapters.Compile.OracleExpressions (wireStream vectorStream)

set_option autoImplicit false

/-! ## Token counts and node counts (pure) -/

section Counts

variable {n arity : ℕ}

theorem PS.step_cnt_ge (w : List ℕ) (S : PS n arity) (t : Tok) : S.cnt ≤ (S.step w t).cnt := by
  cases t <;> simp [PS.step, PS.emit]

theorem PS.run_cnt_ge (w : List ℕ) (l : List Tok) : ∀ S : PS n arity, S.cnt ≤ (S.run w l).cnt := by
  induction l with
  | nil => intro S; simp
  | cons t l ih => intro S; exact (PS.step_cnt_ge w S t).trans (ih _)

theorem PS.vec_cnt_ge (w : List ℕ) (tf : ℕ → List Tok) (k : ℕ) : ∀ S : PS n arity, S.cnt ≤ (PS.vec w tf k S).1.cnt := by
  induction k with
  | zero => intro S; simp [PS.vec]
  | succ k ih =>
      intro S
      rw [PS.vec_succ]
      exact (ih S).trans (PS.run_cnt_ge w (tf k) _)

theorem postR_length_le {width : ℕ} (ρ : Fin width → ℕ) (e : BoolExpr width) :
    ∀ (base : ℕ) (wire : Fin width → ℕ),
      (postR ρ e).length ≤ 2 * (wireStream (n := n) (arity := arity) base wire e).1.length + 1 := by
  induction e with
  | const b => intro base wire; simp [postR, wireStream]
  | input i => intro base wire; simp [postR, wireStream]
  | not c ih => intro base wire; have := ih base wire; simp [postR, wireStream]; omega
  | and l r ihl ihr =>
      intro base wire
      have h1 := ihl base wire
      have h2 := ihr (base + (wireStream (n := n) (arity := arity) base wire l).1.length) wire
      simp [postR, wireStream]; omega
  | or l r ihl ihr =>
      intro base wire
      have h1 := ihl base wire
      have h2 := ihr (base + (wireStream (n := n) (arity := arity) base wire l).1.length) wire
      simp [postR, wireStream]; omega

/-- **The tokens of a vector are at most twice its nodes plus its count.** -/
theorem vec_tokens_le {width : ℕ} (ρ : Fin width → ℕ) (wire : Fin width → ℕ) (count : ℕ) :
    ∀ (exprs : Fin count → BoolExpr width) (tf : ℕ → List Tok) (base : ℕ),
      (∀ j : Fin count, tf j.val = postR ρ (exprs j)) →
      ((List.range count).flatMap tf).length ≤
        2 * (vectorStream (n := n) (arity := arity) base wire count exprs).1.length + count := by
  induction count with
  | zero => intro exprs tf base _; simp
  | succ k ih =>
      intro exprs tf base h
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.length_append]
      have h0 : tf 0 = postR ρ (exprs 0) := h 0
      have e1 := postR_length_le (n := n) (arity := arity) ρ (exprs 0) base wire
      have e2 := ih (fun i => exprs i.succ) (fun i => tf (i + 1))
        (base + (wireStream (n := n) (arity := arity) base wire (exprs 0)).1.length) (fun j => h j.succ)
      simp only [vectorStream, List.length_append]
      rw [h0]
      have : ((List.range k).flatMap (fun i => tf (Nat.succ i))).length =
          ((List.range k).flatMap (fun i => tf (i + 1))).length := rfl
      omega

end Counts

/-! ## The input gates -/

variable {C : Ctx}

/-- `.input i` for `i < ell`, appending `i` to the wire map. -/
def inputsP : St VV MM :=
  .seq (.op (.zero IR)) (.loop (.lt IR ELR) (.seq (rec3 v1 IR vZ) (.seq (.op (.wrM WM IR))
    (.seq (.op (.inc CNT)) (.seq (.op (.inc WL)) (.op (.inc IR)))))))

def InT (y : ℕ) : Prop := y = 24 ∨ y = 101 ∨ y = 103

theorem keep_set_in {T : ℕ → Prop} {R M : ℕ → Prop} {a b : DS VV MM} (h : Keep T R M a b) (x : Fin VV) (v : ℕ)
    (hx : T x.val) : Keep T R M a (b.set x v) := h.trans (Keep.set b x v hx)

theorem inputsP_spec (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) (a : DS VV MM)
    (h : Rep [] (reqD r) (⟨0, [], []⟩ : PS r.ell r.ell) a) (hg : Gl p r a) (hW : r.ell + 1 < 2 ^ C.Wd) :
    Hs C inputsP a (15 * r.ell + 4) (fun b => Rep (List.range r.ell) (reqD r) (initPS r.ell) b ∧ Gl p r b ∧
      b.rc W2 = a.rc W2) := by
  obtain ⟨⟨hc, hcnt, hns, hnsc, hwm, hwl, hwc, hdsr, hdl, hdc⟩, hs1, hs2, hs3⟩ := h
  refine Hs.mono (t := 1 + (r.ell * (13 + 2) + 2) + 1) (Hs.seq (hs_zero C IR a) (fun b hb => ?_)) (by omega)
    (fun x hx => hx)
  subst hb
  let I : ℕ → DS VV MM → Prop := fun k x => x.ram NS = (List.range k).flatMap (fun j => [1, j, 0]) ∧
    x.rc NS = 3 * k ∧ x.env CNT = k ∧ x.ram WM = List.range k ∧ x.rc WM = k ∧ x.env WL = k ∧ x.env IR = k ∧
    Keep InT (fun m => m = 0 ∨ m = 2) (fun m => m = 0 ∨ m = 2) a x
  have hI0 : I 0 (a.set IR 0) := by
    refine ⟨by rw [DS.set_ram, hns]; rfl, by rw [DS.set_rc, hnsc, hns]; rfl, by
      rw [DS.set_env_ne _ _ (by decide), hcnt], by rw [DS.set_ram, hwm]; rfl, by
      rw [DS.set_rc]; simp at hwc; omega, by rw [DS.set_env_ne _ _ (by decide), hwl]; rfl,
      DS.set_env_self _ _ _, Keep.set _ _ _ (Or.inl rfl)⟩
  have hstep : ∀ k < r.ell, ∀ x, I k x → Cnd.eval x (.lt IR ELR) = true ∧
      Hs C (.seq (rec3 v1 IR vZ) (.seq (.op (.wrM WM IR)) (.seq (.op (.inc CNT)) (.seq (.op (.inc WL))
        (.op (.inc IR)))))) x 13 (I (k + 1)) := by
    intro k hk x ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩
    have hcx : Cst x := x8.cst (by unfold InT; omega) hc
    have hEx : x.env ELR = r.ell := by rw [x8.env ELR (by unfold InT; simp), hg.ell]
    refine ⟨by simp [Cnd.eval, x7, hEx, hk], ?_⟩
    have hnl : x.rc NS = (x.ram NS).length := by rw [x2, x1]; simp; omega
    refine Hs.mono (t := 5 + (1 + (1 + (1 + 1 + 1) + 1) + 1) + 1)
      (Hs.seq (rec3_spec (C := C) v1 IR vZ x hnl) (fun y ⟨y1, y2, y3⟩ => ?_)) le_rfl (fun t ht => ht)
    have hyW : y.rc WM ≤ (y.ram WM).length := by
      rw [y3.rc WM (by simp), y3.ram WM (by simp), x5, x4]; simp
    refine Hs.seq (hs_wrM C WM IR y hyW) (fun z hz => ?_)
    subst hz
    have hz1 : (y.put WM (y.env IR)).env CNT = k := by
      show y.env CNT = k
      rw [y3.env CNT (fun h => h), x3]
    refine Hs.mono (t := 1 + 3 + 1) (Hs.seq (hs_inc C CNT _ (by rw [hz1]; omega)) (fun z2 hz2 => ?_)) le_rfl
      (fun t ht => ht)
    subst hz2
    have hz2 : ((y.put WM (y.env IR)).set CNT ((y.put WM (y.env IR)).env CNT + 1)).env WL = k := by
      rw [DS.set_env_ne _ _ (by decide)]
      show y.env WL = k
      rw [y3.env WL (fun h => h), x6]
    refine Hs.mono (t := 1 + 1 + 1) (Hs.seq (hs_inc C WL _ (by rw [hz2]; omega)) (fun z3 hz3 => ?_)) le_rfl
      (fun t ht => ht)
    subst hz3
    set z := ((y.put WM (y.env IR)).set CNT ((y.put WM (y.env IR)).env CNT + 1)).set WL
      (((y.put WM (y.env IR)).set CNT ((y.put WM (y.env IR)).env CNT + 1)).env WL + 1) with hzdef
    have hzI : z.env IR = k := by
      rw [hzdef, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]
      show y.env IR = k
      rw [y3.env IR (fun h => h), x7]
    refine Hs.mono (hs_inc C IR z (by rw [hzI]; omega)) le_rfl ?_
    rintro t rfl
    have hyIR : y.env IR = k := by rw [y3.env IR (fun h => h), x7]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (y.put WM (y.env IR)).ram NS = _
      simp only [DS.put]
      rw [Function.update_of_ne (by decide), y1, x1, List.range_succ, List.flatMap_append]
      simp [hcx.one, hcx.z, x7]
    · show (y.put WM (y.env IR)).rc NS = _
      simp only [DS.put]
      rw [Function.update_of_ne (by decide), y2, y1, x1]
      simp; omega
    · rw [DS.set_env_ne _ _ (by decide), hzdef, DS.set_env_ne _ _ (by decide), DS.set_env_self, hz1]
    · show (y.put WM (y.env IR)).ram WM = _
      simp only [DS.put, Function.update_self]
      rw [y3.rc WM (by simp), y3.ram WM (by simp), x5, x4, hyIR, List.range_succ]
      unfold putAt; simp
    · show (y.put WM (y.env IR)).rc WM = _
      simp only [DS.put, Function.update_self]
      rw [y3.rc WM (by simp), x5]
    · rw [DS.set_env_ne _ _ (by decide), hzdef, DS.set_env_self, hz2]
    · rw [DS.set_env_self, hzI]
    · have k1 : Keep InT (fun m => m = 0 ∨ m = 2) (fun m => m = 0 ∨ m = 2) x y :=
        y3.mono (fun _ h => h.elim) (fun m hm => Or.inl hm) (fun m hm => Or.inl hm)
      have k2 : Keep InT (fun m => m = 0 ∨ m = 2) (fun m => m = 0 ∨ m = 2) y (y.put WM (y.env IR)) :=
        (keep_put y WM _).mono (fun _ h => h.elim) (fun m hm => Or.inr hm) (fun m hm => Or.inr hm)
      exact keep_set_in (keep_set_in (keep_set_in (x8.trans (k1.trans k2)) CNT _ (Or.inr (Or.inl rfl))) WL _
        (Or.inr (Or.inr rfl))) IR _ (Or.inl rfl)
  have hstop : ∀ x, I r.ell x → Cnd.eval x (.lt IR ELR) = false := by
    intro x ⟨_, _, _, _, _, _, x7, x8⟩
    have hEx : x.env ELR = r.ell := by rw [x8.env ELR (by unfold InT; simp), hg.ell]
    simp [Cnd.eval, x7, hEx]
  refine Hs.mono (Hs.loopN (show Cnd.wf (Cnd.lt IR ELR) from (by decide : IR ≠ ELR)) I r.ell 13 hstep hstop _ hI0)
    le_rfl ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, _, b8⟩
  have hnr : (initPS r.ell).nodes.flatMap nodeRec = (List.range r.ell).flatMap (fun j => [1, j, 0]) :=
    flatMap_ofFn r.ell _ nodeRec _ (fun i => rfl)
  refine ⟨⟨⟨b8.cst (by unfold InT; omega) hc, b3, by rw [b1, hnr], by rw [b2, b1]; simp; omega, b4,
    by rw [b6]; simp, by rw [b5]; simp, by rw [b8.ram DSt (by simp), hdsr], by rw [b8.env DL (by unfold InT; simp), hdl],
    by rw [b8.rc DSt (by simp)]; exact hdc⟩, by rw [b8.env HR (by unfold InT; simp), hs1]; rfl,
    by rw [b8.rc STK (by simp), hs2]; rfl, by rfl⟩, ⟨fun j hj => ?_, ?_, ?_, ?_, ?_⟩, b8.rc W2 (by simp)⟩
  · rw [b8.env (Sl j) (by rw [Sl_val hj]; unfold InT; omega), hg.slots j hj]
  · rw [b8.env ELR (by unfold InT; simp), hg.ell]
  · rw [b8.env FUR (by unfold InT; simp), hg.fuel]
  · rw [b8.env CBR (by unfold InT; simp), hg.cb]
  · rw [b8.out, hg.out]

end NearCubicGates.Adapters.Compile.OraclePrint

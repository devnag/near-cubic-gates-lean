import SourceAdapters.Compile.CNFInterpH

/-!
# The request's token run is in range

proof of `lem:multitape-refuter` (every clause of the free-input Tseitin 3-CNF is one of the formula's clauses) and proof of `lem:multitape-refuter` (the
native balanced code of the whole formula is written, so it fits the cell width). `runP_spec` needs `RunOK`: every
token payload is below the step bound and every clause code emitted on the way fits the width. Both follow from
global facts:

* payloads: every token of `requestToks r` has payload `≤ windowBits + n + 1` (`requestToks_pay`);
* clause codes: the nodes of every prefix run are a prefix of the final nodes (`RS.run_nodes`), so their clauses are
  clauses of `requestFormula r` (`requestFormula_rcl`), and every element of a balanced list code is at most the code
  (`le_encodeBalancedList`), hence below `2^Wd` once `sourceSATCode (requestFormula r)` is (`runOK_piece`).

Also the general cell fact `ex_ram_len`: a run of cost `n` grows each store by at most `n` records (used to bound
the generated token counts by the generators' costs).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
  NearCubicWires.FinitePredicateCircuit NearCubicWires.CanonicalBinary NearCubicWires.RepairSource
set_option autoImplicit false

/-! ## Store growth -/

theorem ex_ram_len {C : Ctx} {s : St VV MM} {a b : DS VV MM} {n : ℕ} (h : Ex C s a b n) (m : Fin MM) :
    (b.ram m).length ≤ (a.ram m).length + n := by
  induction h with
  | op ho =>
      cases ho with
      | wrM m' x a hrc =>
          simp only [DS.put]
          by_cases hm : m = m'
          · subst hm; rw [Function.update_self, putAt_length _ _ _ hrc]; omega
          · rw [Function.update_of_ne hm]; omega
      | srtM m' a h0 =>
          simp only [DS.srt]
          by_cases hm : m = m'
          · subst hm; rw [Function.update_self, List.length_insertionSort]; omega
          · rw [Function.update_of_ne hm]; omega
      | rdM m' x a h => simp [DS.adv, DS.set]
      | rwM m' a => simp [DS.rew]
      | kcall s a h1 h2 => simp [DS.called]
      | _ => simp [DS.set]
  | seq _ _ ih1 ih2 => omega
  | iteT _ _ _ ih => omega
  | iteF _ _ _ ih => omega
  | loopF _ _ => omega
  | loopT _ _ _ _ ih1 ih2 => omega
  | mono _ hle ih => omega

/-- A run within cost `t` grows store `m` by at most `t` records. -/
theorem Hs.ramLen {C : Ctx} {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM → Prop} (h : Hs C s a t R)
    (m : Fin MM) : Hs C s a t (fun b => R b ∧ (b.ram m).length ≤ (a.ram m).length + t) := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  exact ⟨b, n, he, hn, hb, (ex_ram_len he m).trans (by omega)⟩

/-- Tokens appended within cost `t` number at most `t`. -/
theorem Ext.len_le {a b : DS VV MM} {toks : List RTok} {t : ℕ} (hE : Ext a b toks)
    (hl : (b.ram sTT).length ≤ (a.ram sTT).length + t) : toks.length ≤ t := by
  rw [hE.tt, List.length_append, List.length_map] at hl
  omega

/-! ## Run composition -/

theorem RunOK_append (C : Ctx) (n : ℕ) : ∀ (l1 l2 : List RTok) (k : ℕ) (S : RS),
    RunOK C n k S (l1 ++ l2) ↔ RunOK C n k S l1 ∧ RunOK C n (k + l1.length) (S.run l1) l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 k S; simp [RunOK]
  | cons t ts ih =>
      intro l2 k S
      simp only [List.cons_append, RunOK, ih, RS.run_cons, List.length_cons]
      rw [show k + 1 + ts.length = k + (ts.length + 1) by omega]
      tauto

theorem RS.step_nodes (S : RS) (t : RTok) : ∃ l, (S.step t).nodes = S.nodes ++ l := by
  cases t <;> simp [RS.step, RS.push]

theorem RS.run_nodes : ∀ (toks : List RTok) (S : RS), ∃ l, (S.run toks).nodes = S.nodes ++ l := by
  intro toks
  induction toks with
  | nil => intro S; exact ⟨[], by simp⟩
  | cons t ts ih =>
      intro S
      obtain ⟨l1, h1⟩ := RS.step_nodes S t
      obtain ⟨l2, h2⟩ := ih (S.step t)
      exact ⟨l1 ++ l2, by rw [RS.run_cons, h2, h1, List.append_assoc]⟩

theorem RS.step_len (S : RS) (h : S.nodes.length = S.idx) (t : RTok) :
    (S.step t).nodes.length = (S.step t).idx := by
  cases t <;> simp [RS.step, RS.push, h]

theorem RS.run_len : ∀ (toks : List RTok) (S : RS), S.nodes.length = S.idx →
    (S.run toks).nodes.length = (S.run toks).idx := by
  intro toks
  induction toks with
  | nil => intro S h; exact h
  | cons t ts ih => intro S h; exact ih _ (RS.step_len S h t)

theorem rclFrom_append (n start : ℕ) (l : List RNode) : ∀ l' : List RNode,
    rclFrom n start (l ++ l') = rclFrom n start l ++ rclFrom n (start + l.length) l' := by
  intro l'
  induction l' using List.reverseRecOn with
  | nil => simp [rclFrom_nil]
  | append_singleton l' x ih =>
      rw [← List.append_assoc, rclFrom_concat, ih, rclFrom_concat, List.length_append, List.append_assoc,
        Nat.add_assoc]

theorem clauseOK_of (C : Ctx) (n : ℕ) (S : RS) (t : RTok) (hS : S.nodes.length = S.idx)
    (h : ∀ c ∈ (rclFrom n 0 (S.step t).nodes).map Encodable.encode, c < 2 ^ C.Wd) : ClauseOK C n S t := by
  have key : ∀ x : RNode, (S.step t).nodes = S.nodes ++ [x] →
      ∀ c ∈ (rcl n S.idx x).map Encodable.encode, c < 2 ^ C.Wd := by
    intro x hx c hc
    apply h
    rw [hx, rclFrom_concat, List.map_append, List.mem_append, Nat.zero_add, hS]
    exact Or.inr hc
  cases t with
  | cst b => exact key _ rfl
  | inp j => exact key _ rfl
  | neg => exact key _ rfl
  | conj => exact key _ rfl
  | disj => exact key _ rfl
  | wir k => trivial
  | save => trivial
  | swap => trivial

/-- **A run is in range** when its payloads are bounded and the clauses of its final nodes fit. -/
theorem runOK_of (C : Ctx) (n : ℕ) : ∀ (toks : List RTok) (k : ℕ) (S : RS), S.nodes.length = S.idx →
    (∀ t ∈ toks, tpay t ≤ k) →
    (∀ c ∈ (rclFrom n 0 (S.run toks).nodes).map Encodable.encode, c < 2 ^ C.Wd) → RunOK C n k S toks := by
  intro toks
  induction toks with
  | nil => intro _ _ _ _ _; trivial
  | cons t ts ih =>
      intro k S hS hp hc
      refine ⟨⟨hp t (by simp), clauseOK_of C n S t hS (fun c hc' => hc c ?_)⟩,
        ih (k + 1) _ (RS.step_len S hS t) (fun u hu => le_trans (hp u (by simp [hu])) (by omega)) hc⟩
      obtain ⟨l, hl⟩ := RS.run_nodes ts (S.step t)
      rw [RS.run_cons, hl, rclFrom_append, List.map_append, List.mem_append]
      exact Or.inl hc'

/-! ## Balanced codes dominate their elements -/

theorem le_encodeBalancedList : ∀ (l : List ℕ), ∀ x ∈ l, x ≤ encodeBalancedList l := by
  intro l
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | h len ih =>
      match l with
      | [] => intro x hx; simp at hx
      | [v] =>
          intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          rw [encodeBalancedList]
          exact Nat.right_le_pair _ _
      | first :: second :: rest =>
          intro x hx
          rw [encodeBalancedList]
          have hl : (first :: second :: rest).length = rest.length + 2 := by simp
          set h := ((first :: second :: rest).length + 1) / 2 with hh
          have hx' : x ∈ (first :: second :: rest).take h ∨ x ∈ (first :: second :: rest).drop h := by
            rw [← List.mem_append, List.take_append_drop]; exact hx
          have p1 := Nat.left_le_pair (encodeBalancedList ((first :: second :: rest).take h))
            (encodeBalancedList ((first :: second :: rest).drop h))
          have p2 := Nat.right_le_pair (encodeBalancedList ((first :: second :: rest).take h))
            (encodeBalancedList ((first :: second :: rest).drop h))
          have p3 := Nat.right_le_pair 2 (Nat.pair (encodeBalancedList ((first :: second :: rest).take h))
            (encodeBalancedList ((first :: second :: rest).drop h)))
          rcases hx' with hx' | hx'
          · have := ih ((first :: second :: rest).take h).length (by simp; omega) _ rfl x hx'
            omega
          · have := ih ((first :: second :: rest).drop h).length (by simp; omega) _ rfl x hx'
            omega

/-! ## Payload bounds -/

theorem postW_pay {w : ℕ} (e : BoolExpr w) : ∀ t ∈ postW e, tpay t ≤ w + 1 := by
  induction e with
  | const b => intro t ht; simp [postW] at ht; subst ht; cases b <;> simp [tpay]
  | input i => intro t ht; simp [postW] at ht; subst ht; simp [tpay]; omega
  | not c ih => intro t ht; simp [postW] at ht; rcases ht with h | h; exact ih t h; subst h; simp [tpay]
  | and l r ihl ihr =>
      intro t ht; simp [postW] at ht
      rcases ht with h | h | h
      · exact ihl t h
      · exact ihr t h
      · subst h; simp [tpay]
  | or l r ihl ihr =>
      intro t ht; simp [postW] at ht
      rcases ht with h | h | h
      · exact ihl t h
      · exact ihr t h
      · subst h; simp [tpay]

theorem postE_pay {w : ℕ} (e : BoolExpr w) : ∀ t ∈ postE e, tpay t ≤ w + 1 := by
  induction e with
  | const b => intro t ht; simp [postE] at ht; subst ht; cases b <;> simp [tpay]
  | input i => intro t ht; simp [postE] at ht; subst ht; simp [tpay]; omega
  | not c ih => intro t ht; simp [postE] at ht; rcases ht with h | h; exact ih t h; subst h; simp [tpay]
  | and l r ihl ihr =>
      intro t ht; simp [postE] at ht
      rcases ht with h | h | h
      · exact ihl t h
      · exact ihr t h
      · subst h; simp [tpay]
  | or l r ihl ihr =>
      intro t ht; simp [postE] at ht
      rcases ht with h | h | h
      · exact ihl t h
      · exact ihr t h
      · subst h; simp [tpay]

theorem vecW_pay {w : ℕ} (count : ℕ) (exprs : Fin count → BoolExpr w) : ∀ t ∈ vecW count exprs, tpay t ≤ w + 1 := by
  intro t ht
  simp only [vecW, List.mem_flatten, List.mem_ofFn] at ht
  obtain ⟨l, ⟨j, rfl⟩, hl⟩ := ht
  rw [List.mem_append] at hl
  rcases hl with h | h
  · exact postW_pay _ t h
  · simp at h; subst h; simp [tpay]

theorem vecE_pay {w : ℕ} (count : ℕ) (exprs : Fin count → BoolExpr w) : ∀ t ∈ vecE count exprs, tpay t ≤ w + 1 := by
  intro t ht
  simp only [vecE, List.mem_flatten, List.mem_ofFn] at ht
  obtain ⟨l, ⟨j, rfl⟩, hl⟩ := ht
  rw [List.mem_append] at hl
  rcases hl with h | h
  · exact postE_pay _ t h
  · simp at h; subst h; simp [tpay]

/-- Every token payload of the request stream is at most `windowBits + n + 1`. -/
theorem requestToks_pay (r : CNFCompilationRequest) : ∀ t ∈ requestToks r,
    tpay t ≤ windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1) + r.witnessLength + 1 := by
  intro t ht
  simp only [requestToks, List.mem_append, List.mem_singleton] at ht
  rcases ht with ((((h | h) | h) | h) | h) | h
  · have := vecE_pay _ _ t h; omega
  · subst h; simp [tpay]
  · simp only [List.mem_flatten, List.mem_replicate] at h
    obtain ⟨l, ⟨_, rfl⟩, hl⟩ := h
    simp only [roundToks, List.mem_append, List.mem_singleton] at hl
    rcases hl with h | h
    · have := vecW_pay _ _ t h; omega
    · subst h; simp [tpay]
  · have := postW_pay _ t h; omega
  · have := postE_pay _ t h; omega
  · subst h; simp [tpay]

/-! ## The request's pieces -/

/-- The clause codes of the nodes of any prefix run are below the width once the whole formula's code is. -/
theorem prefix_codes (C : Ctx) (r : CNFCompilationRequest) (pre rest : List RTok) (hsplit : requestToks r = pre ++ rest)
    (hcode : RecoveryOracle.sourceSATCode (requestFormula r) < 2 ^ C.Wd) :
    ∀ c ∈ (rclFrom r.witnessLength 0 (RS.init.run pre).nodes).map Encodable.encode, c < 2 ^ C.Wd := by
  intro c hc
  have hall : ∀ c ∈ (requestFormula r).map Encodable.encode, c < 2 ^ C.Wd :=
    fun c hc => lt_of_le_of_lt (le_encodeBalancedList _ c hc) hcode
  apply hall
  obtain ⟨l, hl⟩ := RS.run_nodes rest (RS.init.run pre)
  rw [requestFormula_rcl, hsplit, RS.run_append, hl, rclFrom_append]
  simp only [List.map_append, List.mem_append] at hc ⊢
  tauto

/-- **A piece of the request stream is in range** (proof of `lem:multitape-refuter`). -/
theorem runOK_piece (C : Ctx) (r : CNFCompilationRequest) (pre piece rest : List RTok)
    (hsplit : requestToks r = pre ++ piece ++ rest) (k : ℕ)
    (hk : windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel + 1) + r.witnessLength + 1 ≤ k)
    (hcode : RecoveryOracle.sourceSATCode (requestFormula r) < 2 ^ C.Wd) :
    RunOK C r.witnessLength k (RS.init.run pre) piece := by
  refine runOK_of C r.witnessLength piece k _ (RS.run_len pre RS.init rfl) (fun t ht => le_trans
    (requestToks_pay r t (by rw [hsplit]; simp [ht])) hk) ?_
  rw [← RS.run_append]
  exact prefix_codes C r (pre ++ piece) rest hsplit hcode

end NearCubicGates.Adapters.Compile

import SourceAdapters.Routing.TermsMachineExpression
import SourceAdapters.Routing.TermsMachineBoundsRequest

/-! The construction in `lem:generator`: expression capacities at the actual paid request allocation. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open Joins ACSP RAMACSP ShortPCP.Machines.FL CoordinateMachine Circuit Circuit.Encoding

/-- The allocation also pays for one more than rawN stack entries. -/
theorem prepared_expression_stack_power (word : List Bool) :
    2 ^ (Bounds.wordWidth word.length * (word.length+1)) ≤
      (globOf (preparedInput word)).cap := by
  let G := globOf (preparedInput word)
  have hk : Bounds.arithmeticBound word.length+3 ≤ G.K := (Bounds.prepared_large word).1
  have hexp : Bounds.wordWidth word.length*(word.length+1) < G.K := by
    unfold Bounds.wordWidth Bounds.arithmeticBound at *
    nlinarith
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hexp
  have hc := cap_add G
  change 2 ^ (Bounds.wordWidth word.length * (word.length+1)) ≤ G.cap
  omega

/-- Every expression capacity follows from the request itself. -/
theorem prepared_expression_bounds (p : TermsReq) (h : TermsOk p) :
    Expression.Bounds (globOf (preparedInput (termsInput p h))) p.l
      (Bounds.wordWidth (termsInput p h).length) (10*((termsInput p h).length+1))
      (termsInput p h).length (max (Bounds.arithmeticBound (termsInput p h).length) (2^p.f)) := by
  let N := (termsInput p h).length
  let G := globOf (preparedInput (termsInput p h))
  let M := Bounds.arithmeticBound N
  have hl := Bounds.prepared_lookup_bounds p h
  have hn := Bounds.prepared_numeric_bounds p h
  have hr := Bounds.raw_le_arithmetic N
  have hM : 5 ≤ M := by dsimp [M, Bounds.arithmeticBound]; nlinarith
  have htwice : 2*Bounds.wordWidth N ≤ M := by
    dsimp [M, Bounds.wordWidth, Bounds.arithmeticBound]
    nlinarith
  have hgate : 10*(N+1) ≤ M := by dsimp [M, Bounds.arithmeticBound]; nlinarith
  have hbank : (globalBank p.l).length+1 ≤ M := by
    have hs := (Bounds.request_size p h).2.2.2.1
    dsimp [M, N] at *
    omega
  have hdispatch : Expression.DispatchBounds G p.l (Bounds.wordWidth N) :=
    ⟨hM.trans hn.1, hl.2.2.2, htwice.trans hn.1, Bounds.bank_words p h,
      hl.1, hl.2.1, hl.2.2.1, hn.2.2.2⟩
  refine ⟨hdispatch, (Bounds.index_lt_width p h _ le_rfl).le,
    hgate.trans (Nat.le_max_left _ _), hbank.trans (Nat.le_max_left _ _),
    (show 3 ≤ M by omega).trans (Nat.le_max_left _ _), hn.2.1 _ le_rfl,
    prepared_expression_stack_power (termsInput p h), ?_⟩
  exact (show N+1 ≤ M by dsimp [M]; omega).trans hn.1

/-- Any listed expression has at most rawN gates. -/
theorem expression_gateCount_le (p : TermsReq) (h : TermsOk p)
    (item : Pattern p.l.m × Expr (Field2 p.irr)) (hi : item ∈ p.items) :
    gateCount item.2 ≤ (termsInput p h).length := by
  have hm : (exprToks (termsMask p h) item.2).length+1 ∈
      p.items.map (fun i => (exprToks (termsMask p h) i.2).length+1) :=
    List.mem_map.mpr ⟨item, hi, rfl⟩
  have hs := List.single_le_sum (fun x _ => Nat.zero_le x) _ hm
  have hb := (Bounds.request_size p h).2.2.2.2.2
  rw [Bounds.tokens_length] at hs
  omega

theorem expression_constants_le (p : TermsReq) (h : TermsOk p) (c : Field2 p.irr) :
    termsMask p h c ≤ max (Bounds.arithmeticBound (termsInput p h).length) (2^p.f) :=
  (Bounds.mask_lt p h c).le.trans (Nat.le_max_right _ _)

/-- A current prefix bounded by the full circuit has the common gate-index limit. -/
theorem expression_counter_le (p : TermsReq) (h : TermsOk p) (next count : ℕ)
    (hc : next+count ≤ (termsCircuit p h).length) :
    next+count ≤ 10*((termsInput p h).length+1) := hc.trans (Bounds.circuit_length_le p h)

/-- Additional numerical room for the surrounding item's two accumulator gates. -/
theorem expression_item_arithmetic (p : TermsReq) (h : TermsOk p) :
    let N := (termsInput p h).length
    let B := max (Bounds.arithmeticBound N) (2^p.f)
    10*(N+1)+2*p.l.m+3 ≤ B ∧ 4*p.l.m+p.l.m*(3*p.l.m+1) ≤ B ∧ 4 ≤ B ∧
      B ≤ (globOf (preparedInput (termsInput p h))).cap := by
  intro N B
  have hs := Bounds.request_size p h
  have hm : p.l.m ≤ N := hs.2.1
  have hmm : p.l.m*p.l.m ≤ N := hs.2.2.1
  have h1 : 10*(N+1)+2*p.l.m+3 ≤ Bounds.arithmeticBound N := by
    unfold Bounds.arithmeticBound
    nlinarith
  have h2 : 4*p.l.m+p.l.m*(3*p.l.m+1) ≤ Bounds.arithmeticBound N := by
    unfold Bounds.arithmeticBound
    nlinarith
  have h4 : 4 ≤ Bounds.arithmeticBound N := by unfold Bounds.arithmeticBound; nlinarith
  exact ⟨h1.trans (Nat.le_max_left _ _), h2.trans (Nat.le_max_left _ _),
    h4.trans (Nat.le_max_left _ _), (Bounds.prepared_numeric_bounds p h).2.2.1 _ le_rfl⟩

/-- The complete expression printer with all request-global capacities discharged. -/
theorem expressionRequest_spec (p : TermsReq) (h : TermsOk p) (s : FS)
    (item : Pattern p.l.m × Expr (Field2 p.irr)) (hi : item ∈ p.items) (pos : ℕ)
    (hnext : s.env 24+gateCount item.2 ≤ 10*((termsInput p h).length+1))
    (hat : At (s.env 10) pos (exprWord (termsMask p h) item.2)) (h14 : s.env 14 = pos)
    (hend : pos+(exprWord (termsMask p h) item.2).length ≤ (termsInput p h).length)
    (h23 : s.env 23 = packW (Bounds.wordWidth (termsInput p h).length) (globalBank p.l))
    (h26 : s.env 26 = (globalBank p.l).length)
    (h30 : s.env 30 = Bounds.wordWidth (termsInput p h).length) :
    let G := globOf (preparedInput (termsInput p h))
    let u := evalS G Expression.program s
    Appends Expression.writes s u
      (Prefix.words (s.env 31) ((expressionGates p.l (s.env 24) item.2).map (codeGate (termsMask p h)))) ∧
      u.env 14 = pos+(exprWord (termsMask p h) item.2).length ∧
      u.env 24 = s.env 24+gateCount item.2 ∧ u.env 28 = s.env 24+gateCount item.2-1 ∧
      u.env 29 = 1 ∧ u.env 40 = 0 :=
  Expression.program_spec_of_constants _ s p.l (termsMask p h) item.2
    (Bounds.wordWidth (termsInput p h).length) (10*((termsInput p h).length+1))
    (termsInput p h).length (max (Bounds.arithmeticBound (termsInput p h).length) (2^p.f))
    pos (termsInput p h).length (prepared_expression_bounds p h) (prepared_BdOk (termsInput p h))
    hnext (expression_gateCount_le p h item hi) (expression_constants_le p h)
    hat h14 hend h23 h26 h30

/-- The same specialization using the natural full-circuit prefix bound. -/
theorem expressionRequest_spec_of_circuit (p : TermsReq) (h : TermsOk p) (s : FS)
    (item : Pattern p.l.m × Expr (Field2 p.irr)) (hi : item ∈ p.items) (pos : ℕ)
    (hnext : s.env 24+gateCount item.2 ≤ (termsCircuit p h).length)
    (hat : At (s.env 10) pos (exprWord (termsMask p h) item.2)) (h14 : s.env 14 = pos)
    (hend : pos+(exprWord (termsMask p h) item.2).length ≤ (termsInput p h).length)
    (h23 : s.env 23 = packW (Bounds.wordWidth (termsInput p h).length) (globalBank p.l))
    (h26 : s.env 26 = (globalBank p.l).length)
    (h30 : s.env 30 = Bounds.wordWidth (termsInput p h).length) :
    let G := globOf (preparedInput (termsInput p h))
    let u := evalS G Expression.program s
    Appends Expression.writes s u
      (Prefix.words (s.env 31) ((expressionGates p.l (s.env 24) item.2).map (codeGate (termsMask p h)))) ∧
      u.env 14 = pos+(exprWord (termsMask p h) item.2).length ∧
      u.env 24 = s.env 24+gateCount item.2 ∧ u.env 28 = s.env 24+gateCount item.2-1 ∧
      u.env 29 = 1 ∧ u.env 40 = 0 :=
  expressionRequest_spec p h s item hi pos (expression_counter_le p h _ _ hnext)
    hat h14 hend h23 h26 h30

end NearCubicGates.Adapters.Routing.TermsMachine

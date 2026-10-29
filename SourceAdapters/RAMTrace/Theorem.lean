import SourceAdapters.RAMTrace.Completeness
import SourceAdapters.RAMTrace.Catalog

/-!
# `thm:trace` over a ring of characteristic two

`app:event-trace` `def:event-trace` asks for an assignment of bits; (G) makes every slot of the slot catalog of `def:event-trace` a bit, and the
equations have coefficients in `{0, 1}` and read only such slots (`timeEq_reads_active`, `sortEq_reads_active`), so
`ET(M, τ, x̄)` holds over any ring of characteristic two iff it holds over bits (`satisfiable_iff_bits`). With
`holdsB_sound` (⇒) and `bhram_complete` (⇐) this is `thm:trace` (`event_trace_iff`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr

/-- An assignment with every value mapped. -/
def Trace.map {α β : Type} (g : α → β) (a : Trace α) : Trace β where
  src x f k := g (a.src x f k)
  dst x f k := g (a.dst x f k)
  time i s := g (a.time i s)
  sort j s := g (a.sort j s)

theorem Trace.timeRead_map {α β : Type} (g : α → β) (a : Trace α) (i : ℕ) :
    (a.map g).timeRead i = fun v => g (a.timeRead i v) := by
  funext v; rcases v with s | ⟨f, k⟩ <;> rfl

theorem Trace.sortRead_map {α β : Type} (g : α → β) (a : Trace α) (j : ℕ) :
    (a.map g).sortRead j = fun v => g (a.sortRead j v) := by
  funext v; rcases v with s | ⟨f, k⟩ <;> rfl

theorem eSet_reads_active (M : Ram) (τ : ℕ) (Q : Instr M.w M.k M.ops → Bool) :
    ∀ v ∈ (eSet M Q).vars, v.Active (dims M τ) := by
  show AllVars (TVar.Active (dims M τ)) (eSet M Q)
  apply allVars_sumCode
  intro p I _ hp
  split_ifs
  · simp only [tv, allVars_var]; show p < M.code.length; simpa using hp
  · simp

section Transfer

variable {F : Type} [CommRing F] [CharP F 2] (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ) (xbar : List Bool)

/-- Bits give a solution over `F`. -/
theorem holds_of_holdsB (b : Trace Bool) (hb : HoldsB M kind τ xbar b) :
    Holds M kind τ xbar (b.map (boolF (F := F))) := by
  obtain ⟨hT, hB1, hB2, hout, hacc, hS, hsen, hB4, hB5, hdum, π, hπ⟩ := hb
  have ev : ∀ {ι : Type} (v : ι → Bool) (e : Expr ι), e.eval (fun i => boolF (F := F) (v i)) = boolF (e.evalB v) :=
    fun v e => eval_boolF v e
  refine ⟨fun _ _ _ _ => isBit_boolF _, fun _ _ _ _ => isBit_boolF _, fun _ _ _ _ => isBit_boolF _,
    fun _ _ _ _ => isBit_boolF _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨π, fun x s hs => ?_⟩⟩
  · intro i hi q hq
    rw [Trace.timeRead_map, ev, hT i hi q hq]; rfl
  · intro c hc
    rw [Trace.timeRead_map]; simp only; rw [hB1 c hc]; rfl
  · intro i hi c hc
    rw [Trace.timeRead_map]; simp only; rw [hB2 i hi c hc]; rfl
  · intro i hi
    rw [Trace.timeRead_map, ev, hout i hi]; rfl
  · rw [Trace.timeRead_map, ev, hacc]; rfl
  · intro j hj q hq
    rw [Trace.sortRead_map, ev, hS j hj q hq]; rfl
  · intro f k hk
    show boolF (b.sort 0 (.prev f k)) = sentinel f
    rw [hsen f k hk]
    cases f <;> simp [boolF, sentinel]
  · intro j hj f k hk
    show boolF (b.sort (j + 1) (.prev f k)) = boolF (b.dst j f k)
    rw [hB4 j hj f k hk]
  · intro c hc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB5 c hc
    refine ⟨?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun k hk => ?_⟩
    · show boolF _ = 1; rw [h1]; rfl
    · show boolF _ = 1; rw [h2]; rfl
    · show boolF _ = 0; rw [h3]; rfl
    · show boolF _ = 0; rw [h4]; rfl
    · show boolF _ = 0; rw [h5 j hj]; rfl
    · show boolF _ = _; rw [h6 j hj]; rfl
    · show boolF _ = _; rw [h7 k hk]; rfl
  · intro x h1 h2 s hs
    show boolF _ = 0; rw [hdum x h1 h2 s hs]; rfl
  · show boolF _ = boolF _; rw [hπ x s hs]

open Classical in
/-- A solution over `F` reads off as bits. -/
theorem holdsB_of_holds (hw : 1 ≤ M.w) (a : Trace F) (ha : Holds M kind τ xbar a) :
    HoldsB M kind τ xbar (a.map fun z => decide (z = 1)) := by
  obtain ⟨g1, g2, g3, g4, hT, hB1, hB2, hout, hacc, hS, hsen, hB4, hB5, hdum, π, hπ⟩ := ha
  have hT1 : ∀ i, i < 2 ^ τ → i < 2 ^ (τ + 1) := fun i hi => by rw [pow_succ]; omega
  have hbitT : ∀ i < 2 ^ τ, ∀ v : TVar, v.Active (dims M τ) → IsBit (a.timeRead i v) := by
    intro i hi v hv
    rcases v with s | ⟨f, k⟩
    · exact g3 i hi s hv
    · exact g1 i (hT1 i hi) (f, k) hv
  have hbitS : ∀ j < 2 ^ (τ + 1), ∀ v : SVar, v.Active (dims M τ) → IsBit (a.sortRead j v) := by
    intro j hj v hv
    rcases v with s | ⟨f, k⟩
    · exact g4 j hj s hv
    · exact g2 j hj (f, k) hv
  have zero_ne : decide ((0 : F) = 1) = false := by simp [(one_ne_zero_char2 (F := F)).symm]
  have one_eq : decide ((1 : F) = 1) = true := by simp
  have ev0 : ∀ {ι : Type} (val : ι → F) (e : Expr ι), (∀ v ∈ e.vars, IsBit (val v)) → e.eval val = 0 →
      e.evalB (fun v => decide (val v = 1)) = false := by
    intro ι val e hbits h0
    rw [eval_of_bits val e hbits, boolF_eq_zero] at h0
    exact h0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨π, fun x s hs => ?_⟩⟩
  · intro i hi q hq
    rw [Trace.timeRead_map]
    exact ev0 _ _ (fun v hv => hbitT i hi v (timeEq_reads_active M kind τ hw q hq v hv)) (hT i hi q hq)
  · intro c hc
    rw [Trace.timeRead_map]; simp only; rw [hB1 c hc]; exact zero_ne
  · intro i hi c hc
    rw [Trace.timeRead_map]; simp only; rw [hB2 i hi c hc]; rfl
  · intro i hi
    rw [Trace.timeRead_map]
    exact ev0 _ _ (fun v hv => hbitT i (by omega) v (eSet_reads_active M τ _ v hv)) (hout i hi)
  · rw [Trace.timeRead_map]
    have hT0 : 2 ^ τ - 1 < 2 ^ τ := by have := Nat.one_le_two_pow (n := τ); omega
    apply ev0 _ _ _ hacc
    intro v hv
    simp only [accE, Expr.vars, List.mem_append, List.not_mem_nil, or_false] at hv
    exact hbitT _ hT0 v (eSet_reads_active M τ _ v hv)
  · intro j hj q hq
    rw [Trace.sortRead_map]
    exact ev0 _ _ (fun v hv => hbitS j hj v (sortEq_reads_active (dims M τ) hw q hq v hv)) (hS j hj q hq)
  · intro f k hk
    show decide (a.sort 0 (.prev f k) = 1) = decide (f = .act)
    rw [hsen f k hk]
    cases f <;> simp [sentinel, (one_ne_zero_char2 (F := F)).symm]
  · intro j hj f k hk
    show decide (a.sort (j + 1) (.prev f k) = 1) = decide (a.dst j f k = 1)
    rw [hB4 j hj f k hk]
  · intro c hc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB5 c hc
    refine ⟨?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun k hk => ?_⟩
    · show decide (_ = 1) = true; rw [h1]; exact one_eq
    · show decide (_ = 1) = true; rw [h2]; exact one_eq
    · show decide (_ = 1) = false; rw [h3]; exact zero_ne
    · show decide (_ = 1) = false; rw [h4]; exact zero_ne
    · show decide (_ = 1) = false; rw [h5 j hj]; exact zero_ne
    · show decide (_ = 1) = _; rw [h6 j hj]; cases c.testBit j <;> simp [zero_ne]
    · show decide (_ = 1) = _; rw [h7 k hk]; cases xbar.getD (c * M.w + k) false <;> simp [zero_ne]
  · intro x h1 h2 s hs
    show decide (_ = 1) = false; rw [hdum x h1 h2 s hs]; exact zero_ne
  · show decide (_ = 1) = decide (_ = 1); rw [hπ x s hs]

/-- `ET(M, τ, x̄)` is satisfiable over `F` iff it is satisfiable by bits. -/
theorem satisfiable_iff_bits (hw : 1 ≤ M.w) :
    Satisfiable F M kind τ xbar ↔ ∃ b : Trace Bool, HoldsB M kind τ xbar b := by
  constructor
  · rintro ⟨a, ha⟩
    classical
    exact ⟨_, holdsB_of_holds M kind τ xbar hw a ha⟩
  · rintro ⟨b, hb⟩
    exact ⟨_, holds_of_holdsB M kind τ xbar b hb⟩

/-- **`thm:trace` (event trace ⟺ bounded halting).** -/
theorem event_trace_iff (halu : ∀ op, M.alu op = (kind op).fn) (hw2 : M.w = 2 ^ Nat.log 2 M.w) (hτ : 1 ≤ τ)
    (hωτ : Nat.log 2 M.w ≤ τ) (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ) :
    Satisfiable F M kind τ xbar ↔ M.BHRAM xbar τ τ := by
  have hw : 1 ≤ M.w := by rw [hw2]; exact Nat.one_le_two_pow
  rw [satisfiable_iff_bits M kind τ xbar hw]
  constructor
  · rintro ⟨b, hb⟩
    exact holdsB_sound M kind τ xbar b halu hw2 hτ hωτ hτw hlen hb
  · intro h
    exact bhram_complete M kind τ xbar halu hw2 hωτ hτw hlen h

end Transfer

end NearCubicGates.Adapters.RAMTrace

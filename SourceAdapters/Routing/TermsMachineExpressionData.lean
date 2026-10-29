import SourceAdapters.Routing.TermsMachineTokens
import SourceAdapters.Routing.TermsMachinePrefixData
import SourceAdapters.Routing.TermsMachineTokenRead

/-! Typed postfix traces and their exact ordered gate lists. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Expression

open Joins ACSP Circuit Circuit.Encoding

def popCount : TermTok → ℕ
  | .const _ | .read _ => 0
  | .add | .mul => 2
  | .square => 1

def emittedGate (l : Layout) (st : List ℕ) : TermTok → ArithGate ℕ
  | .const c => .const c
  | .read v => .input (readIndex l v)
  | .add => .add (st.getD 1 0) (st.getD 0 0)
  | .mul => .mul (st.getD 1 0) (st.getD 0 0)
  | .square => .mul (st.getD 0 0) (st.getD 0 0)

theorem tokenStep_eq (l : Layout) (s : TokenState) (t : TermTok)
    (h : popCount t ≤ s.stack.length) :
    tokenStep l s t = ⟨s.next+1, s.next :: s.stack.drop (popCount t),
      s.gates ++ [emittedGate l s.stack t]⟩ := by
  cases t with
  | const c => rfl
  | read v => rfl
  | add =>
      cases hs : s.stack with
      | nil => simp [hs, popCount] at h
      | cons b tail =>
          cases tail with
          | nil => simp [hs, popCount] at h
          | cons a rest => simp [tokenStep, hs, tokenPush, popCount, emittedGate]
  | mul =>
      cases hs : s.stack with
      | nil => simp [hs, popCount] at h
      | cons b tail =>
          cases tail with
          | nil => simp [hs, popCount] at h
          | cons a rest => simp [tokenStep, hs, tokenPush, popCount, emittedGate]
  | square =>
      cases hs : s.stack with
      | nil => simp [hs, popCount] at h
      | cons a rest => simp [tokenStep, hs, tokenPush, popCount, emittedGate]

/-- Each token has the operands it removes. -/
def Valid (l : Layout) : List TermTok → TokenState → Prop
  | [], _ => True
  | t :: ts, s => popCount t ≤ s.stack.length ∧ Valid l ts (tokenStep l s t)

theorem valid_append (l : Layout) (as bs : List TermTok) (s : TokenState) :
    Valid l (as ++ bs) s ↔ Valid l as s ∧ Valid l bs (runTokens l as s) := by
  induction as generalizing s with
  | nil => simp [Valid, runTokens]
  | cons t ts ih => simp [Valid, runTokens, ih, and_assoc]

theorem valid_expression {F : Type} (l : Layout) (mk : F → ℕ) (e : Expr F)
    (n : ℕ) (st : List ℕ) (gs : List (ArithGate ℕ)) :
    Valid l (exprToks mk e) ⟨n, st, gs⟩ := by
  induction e generalizing n st gs with
  | const c => simp [exprToks, Valid, popCount]
  | read v => simp [exprToks, Valid, popCount]
  | add a b ha hb =>
      rw [exprToks, valid_append, valid_append, runTokens_append,
        runTokens_expression, runTokens_expression]
      exact ⟨⟨ha _ _ _, hb _ _ _⟩, by simp [Valid, popCount]⟩
  | mul a b ha hb =>
      rw [exprToks, valid_append, valid_append, runTokens_append,
        runTokens_expression, runTokens_expression]
      exact ⟨⟨ha _ _ _, hb _ _ _⟩, by simp [Valid, popCount]⟩
  | square a ha =>
      rw [exprToks, valid_append, runTokens_expression]
      exact ⟨ha _ _ _, by simp [Valid, popCount]⟩

def trace (l : Layout) : List TermTok → ℕ → List ℕ → TokenState
  | [], n, st => ⟨n, st, []⟩
  | t :: ts, n, st =>
      let u := tokenStep l ⟨n, st, []⟩ t
      let v := trace l ts u.next u.stack
      ⟨v.next, v.stack, u.gates ++ v.gates⟩

theorem tokenStep_prefix (l : Layout) (t : TermTok) (n : ℕ) (st : List ℕ)
    (gs : List (ArithGate ℕ)) :
    tokenStep l ⟨n, st, gs⟩ t =
      let u := tokenStep l ⟨n, st, []⟩ t
      ⟨u.next, u.stack, gs ++ u.gates⟩ := by
  cases t <;> cases st with
  | nil => simp [tokenStep, tokenPush]
  | cons a st => cases st <;> simp [tokenStep, tokenPush]

theorem runTokens_trace (l : Layout) (ts : List TermTok) (n : ℕ) (st : List ℕ)
    (gs : List (ArithGate ℕ)) :
    runTokens l ts ⟨n, st, gs⟩ =
      ⟨(trace l ts n st).next, (trace l ts n st).stack, gs ++ (trace l ts n st).gates⟩ := by
  induction ts generalizing n st gs with
  | nil => simp [trace, runTokens]
  | cons t ts ih =>
      change runTokens l ts (tokenStep l ⟨n, st, gs⟩ t) = _
      rw [tokenStep_prefix, ih]
      simp only [trace, List.append_assoc]

theorem trace_expression {F : Type} (l : Layout) (mk : F → ℕ) (e : Expr F)
    (n : ℕ) (st : List ℕ) :
    trace l (exprToks mk e) n st =
      ⟨n+gateCount e, (n+gateCount e-1)::st, expressionGates l n (mapExpression mk e)⟩ := by
  have h := runTokens_expression l mk e n st []
  rw [runTokens_trace] at h
  cases ht : trace l (exprToks mk e) n st
  simpa only [ht, List.nil_append] using h

theorem valid_irrel_gates (l : Layout) (ts : List TermTok) (n : ℕ) (st : List ℕ)
    (as bs : List (ArithGate ℕ)) : Valid l ts ⟨n, st, as⟩ ↔ Valid l ts ⟨n, st, bs⟩ := by
  induction ts generalizing n st as bs with
  | nil => rfl
  | cons t ts ih =>
      simp only [Valid]
      rw [tokenStep_prefix l t n st as, tokenStep_prefix l t n st bs]
      exact and_congr_right (fun _ => ih _ _ _ _)

theorem trace_cons (l : Layout) (t : TermTok) (ts : List TermTok) (n : ℕ) (st : List ℕ)
    (h : popCount t ≤ st.length) :
    trace l (t::ts) n st =
      let v := trace l ts (n+1) (n::st.drop (popCount t))
      ⟨v.next, v.stack, emittedGate l st t :: v.gates⟩ := by
  simp only [trace, tokenStep_eq l ⟨n, st, []⟩ t h, List.nil_append, List.singleton_append]

theorem exprToks_length {F : Type} (mk : F → ℕ) (e : Expr F) :
    (exprToks mk e).length = gateCount e := by
  induction e with
  | const c => rfl
  | read v => rfl
  | add a b ha hb => simp [exprToks, gateCount, ha, hb, Nat.add_assoc]
  | mul a b ha hb => simp [exprToks, gateCount, ha, hb, Nat.add_assoc]
  | square a ha => simp [exprToks, gateCount, ha]

theorem expression_code {F : Type} (l : Layout) (mk : F → ℕ) (e : Expr F) (n : ℕ) :
    (expressionGates l n (mapExpression mk e)).map (codeGate id) =
      (expressionGates l n e).map (codeGate mk) := by
  rw [expressionGates_map, List.map_map]
  congr 1
  funext g
  cases g <;> rfl

end NearCubicGates.Adapters.Routing.TermsMachine.Expression

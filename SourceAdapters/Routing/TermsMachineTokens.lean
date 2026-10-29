import SourceAdapters.Joins.TermsCircuit
import SourceAdapters.Routing.CircuitEncodingExpr

/-!
# Postfix expression compilation

The construction in `lem:generator`: the ordinary constraint printer processes the supplied expression
tokens in postorder. The stack contains absolute gate indices. These equations
identify that execution with the original circuit compiler, including square's
repeated reference and reads absent from the supplied bank.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.Joins
open Circuit Circuit.Encoding

structure TokenState where
  next : ℕ
  stack : List ℕ
  gates : List (ArithGate ℕ)

def tokenPush (s : TokenState) (rest : List ℕ) (g : ArithGate ℕ) : TokenState :=
  ⟨s.next + 1, s.next :: rest, s.gates ++ [g]⟩

def tokenStep (l : Layout) (s : TokenState) : TermTok → TokenState
  | .const c => tokenPush s s.stack (.const c)
  | .read v => tokenPush s s.stack (.input (readIndex l v))
  | .add => match s.stack with
    | b :: a :: rest => tokenPush s rest (.add a b)
    | _ => s
  | .mul => match s.stack with
    | b :: a :: rest => tokenPush s rest (.mul a b)
    | _ => s
  | .square => match s.stack with
    | a :: rest => tokenPush s rest (.mul a a)
    | _ => s

def runTokens (l : Layout) (ts : List TermTok) (s : TokenState) : TokenState :=
  ts.foldl (tokenStep l) s

theorem runTokens_append (l : Layout) (as bs : List TermTok) (s : TokenState) :
    runTokens l (as ++ bs) s = runTokens l bs (runTokens l as s) := by
  exact List.foldl_append

theorem runTokens_expression {F : Type} (l : Layout) (mk : F → ℕ) (e : Expr F)
    (n : ℕ) (st : List ℕ) (gs : List (ArithGate ℕ)) :
    runTokens l (exprToks mk e) ⟨n, st, gs⟩ =
      ⟨n + gateCount e, (n + gateCount e - 1) :: st,
        gs ++ expressionGates l n (mapExpression mk e)⟩ := by
  induction e generalizing n st gs with
  | const c => simp [runTokens, exprToks, tokenStep, tokenPush, gateCount,
      mapExpression, expressionGates]
  | read v => simp [runTokens, exprToks, tokenStep, tokenPush, gateCount,
      mapExpression, expressionGates]
  | add a b ha hb =>
      simp only [exprToks, runTokens_append, ha, hb]
      simp [runTokens, tokenStep, tokenPush, gateCount, mapExpression,
        expressionGates, gateCount_mapExpression, List.append_assoc, Nat.add_assoc]
      omega
  | mul a b ha hb =>
      simp only [exprToks, runTokens_append, ha, hb]
      simp [runTokens, tokenStep, tokenPush, gateCount, mapExpression,
        expressionGates, gateCount_mapExpression, List.append_assoc, Nat.add_assoc]
      omega
  | square a ha =>
      simp only [exprToks, runTokens_append, ha]
      simp [runTokens, tokenStep, tokenPush, gateCount, mapExpression,
        expressionGates, gateCount_mapExpression, List.append_assoc, Nat.add_assoc]

end NearCubicGates.Adapters.Routing.TermsMachine

import SourceAdapters.Compile.OracleNodeStream

/-!
# Postfix tokens and uniform expression templates of the oracle circuit printer

proof of `thm:short-pcp-ours`: the algorithm `A` computes the oracle circuit `C^O_x` "in the standard way" in polynomial time; proof of `cor:short-pcp-clock` make the clock an input, so one printer serves every data word, seed length and clock. The circuit of
`OracleExpressions.requestCircuit p r` is a sequence of compiled Boolean expressions whose shapes depend on the run
time numbers `requestWidth r`, `r.fuel`, `r.ell` and the data bits. This module is the pure part of the printer:

* `Tok`, `PS.step`: a postfix token stack machine that emits genuine MW20 `OracleNode`s (constant, NOT, AND, OR) and
  pushes wire references; `run_postR`: the tokens `postR ρ e` of an expression emit exactly `wireStream` (`OracleNodeStream.lean`), with the wire map read through `ρ`;
* `Tm`, `U`, `U.toks`: index terms and expression templates (constants, data bits, wire references, NOT/AND/OR,
  counted conjunction/disjunction chains, branching, local bindings) whose token streams are those of whole
  expression families; a template is fixed once the oracle program is fixed, its numbers are read at run time.

-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.FinitePredicateCircuit
open NearCubicGates.Adapters.Compile.OracleExpressions (wireStream)
open NearCubicGates.Adapters.Compile (anyExpression allExpression)

set_option autoImplicit false

/-! ## The token machine -/

/-- Postfix tokens: a constant node, a wire reference, and the three gates. -/
inductive Tok where
  | cst (b : Bool)
  | wir (k : ℕ)
  | neg
  | conj
  | disj
  deriving DecidableEq

/-- The printer's state: the index of the next node, the stack of wire indices (top first), and the nodes
emitted so far. -/
structure PS (n arity : ℕ) where
  cnt : ℕ
  stk : List ℕ
  nodes : List (OracleNode n arity)

variable {n arity : ℕ}

/-- Emit `x` at index `cnt` and push that index on `stk`. -/
def PS.emit (S : PS n arity) (stk : List ℕ) (x : OracleNode n arity) : PS n arity :=
  ⟨S.cnt + 1, S.cnt :: stk, S.nodes ++ [x]⟩

/-- One token, with the wire map `w`. Popping an empty stack yields `0` (the cell program does the same). -/
def PS.step (w : List ℕ) (S : PS n arity) : Tok → PS n arity
  | .cst b => S.emit S.stk (.const b)
  | .wir k => ⟨S.cnt, w.getD k 0 :: S.stk, S.nodes⟩
  | .neg => S.emit S.stk.tail (.not (S.stk.headD 0))
  | .conj => S.emit S.stk.tail.tail (.and (S.stk.tail.headD 0) (S.stk.headD 0))
  | .disj => S.emit S.stk.tail.tail (.or (S.stk.tail.headD 0) (S.stk.headD 0))

/-- A token list. -/
def PS.run (w : List ℕ) (S : PS n arity) (l : List Tok) : PS n arity := l.foldl (PS.step w) S

@[simp] theorem PS.run_nil (w : List ℕ) (S : PS n arity) : S.run w [] = S := rfl
@[simp] theorem PS.run_cons (w : List ℕ) (S : PS n arity) (t : Tok) (l : List Tok) :
    S.run w (t :: l) = (S.step w t).run w l := rfl
theorem PS.run_append (w : List ℕ) (S : PS n arity) (a b : List Tok) :
    S.run w (a ++ b) = (S.run w a).run w b := List.foldl_append

/-- Postfix tokens of an expression whose input `i` is the wire-map entry `ρ i`. -/
def postR {width : ℕ} (ρ : Fin width → ℕ) : BoolExpr width → List Tok
  | .const b => [.cst b]
  | .input i => [.wir (ρ i)]
  | .not c => postR ρ c ++ [.neg]
  | .and l r => postR ρ l ++ postR ρ r ++ [.conj]
  | .or l r => postR ρ l ++ postR ρ r ++ [.disj]

/-- **The tokens of an expression emit exactly its compiled nodes** (`wireStream`, proof of `thm:short-pcp-ours`) and
push its output wire. -/
theorem run_postR {width : ℕ} (w : List ℕ) (ρ : Fin width → ℕ) (e : BoolExpr width) :
    ∀ S : PS n arity, S.run w (postR ρ e) =
      ⟨S.cnt + (wireStream (n := n) (arity := arity) S.cnt (fun i => w.getD (ρ i) 0) e).1.length,
        (wireStream (n := n) (arity := arity) S.cnt (fun i => w.getD (ρ i) 0) e).2 :: S.stk,
        S.nodes ++ (wireStream (n := n) (arity := arity) S.cnt (fun i => w.getD (ρ i) 0) e).1⟩ := by
  induction e with
  | const b => intro S; rfl
  | input i => intro S; simp [postR, wireStream, PS.step]
  | not c ih =>
      intro S
      rw [postR, PS.run_append, ih]
      simp [PS.step, PS.emit, wireStream, Nat.add_assoc]
  | and l r ihl ihr =>
      intro S
      rw [postR, PS.run_append, PS.run_append, ihl, ihr]
      simp [PS.step, PS.emit, wireStream, Nat.add_assoc]
  | or l r ihl ihr =>
      intro S
      rw [postR, PS.run_append, PS.run_append, ihl, ihr]
      simp [PS.step, PS.emit, wireStream, Nat.add_assoc]

/-- Renaming the inputs of an expression is renaming its wire references. -/
theorem postR_rename {width width' : ℕ} (σ : Fin width' → ℕ) (ρ : Fin width → Fin width') (e : BoolExpr width) :
    postR σ (Compile.renameExpression ρ e) = postR (fun i => σ (ρ i)) e := by
  induction e with
  | const b => rfl
  | input i => rfl
  | not c ih => simp [Compile.renameExpression, postR, ih]
  | and l r ihl ihr => simp [Compile.renameExpression, postR, ihl, ihr]
  | or l r ihl ihr => simp [Compile.renameExpression, postR, ihl, ihr]

theorem postR_congr {width : ℕ} (ρ σ : Fin width → ℕ) (h : ∀ i, ρ i = σ i) (e : BoolExpr width) :
    postR ρ e = postR σ e := by
  rw [show ρ = σ from funext h]

/-- A disjunction chain: the members, `false`, then one OR per member. -/
theorem postR_any {width : ℕ} (ρ : Fin width → ℕ) (l : List (BoolExpr width)) :
    postR ρ (anyExpression l) = l.flatMap (postR ρ) ++ [.cst false] ++ List.replicate l.length .disj := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      simp only [anyExpression, postR, ih, List.flatMap_cons, List.length_cons, List.replicate_succ',
        List.append_assoc]

/-- A conjunction chain: the members, `true`, then one AND per member. -/
theorem postR_all {width : ℕ} (ρ : Fin width → ℕ) (l : List (BoolExpr width)) :
    postR ρ (allExpression l) = l.flatMap (postR ρ) ++ [.cst true] ++ List.replicate l.length .conj := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      simp only [allExpression, postR, ih, List.flatMap_cons, List.length_cons, List.replicate_succ',
        List.append_assoc]

/-- `List.ofFn` members as a `range` loop. -/
theorem flatMap_ofFn {α β : Type} (k : ℕ) :
    ∀ (F : Fin k → α) (g : α → List β) (f : ℕ → List β), (∀ i : Fin k, g (F i) = f i.val) →
      (List.ofFn F).flatMap g = (List.range k).flatMap f := by
  induction k with
  | zero => intro F g f _; rfl
  | succ k ih =>
      intro F g f h
      rw [List.ofFn_succ', List.concat_eq_append, List.flatMap_append, List.range_succ, List.flatMap_append,
        ih (fun i => F i.castSucc) g f (fun i => h i.castSucc)]
      simp [h (Fin.last k)]

/-! ## Index terms and templates -/

/-- Index terms over the bound numbers `env` (de Bruijn levels: `v j` is the `j`-th binding). -/
inductive Tm where
  | v (j : ℕ)
  | k (c : ℕ)
  | add (a b : Tm)
  | sub (a b : Tm)
  | mul (a b : Tm)
  | div (a b : Tm)
  | md (a b : Tm)
  | lt (a b : Tm)
  | eq (a b : Tm)
  | ite (c a b : Tm)

/-- Values (truncated subtraction; `x / 0 = 0`, `x % 0 = x`; tests are `0`/`1`; `ite` tests for nonzero). -/
def Tm.eval (env : List ℕ) : Tm → ℕ
  | .v j => env.getD j 0
  | .k c => c
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .div a b => a.eval env / b.eval env
  | .md a b => a.eval env % b.eval env
  | .lt a b => if a.eval env < b.eval env then 1 else 0
  | .eq a b => if a.eval env = b.eval env then 1 else 0
  | .ite c a b => if c.eval env = 0 then b.eval env else a.eval env

/-- Expression templates. `bigAnd n body fin` is `body 0 ∧ (body 1 ∧ … ∧ (body (n-1) ∧ fin))`, the body bound to the
member index at the next level, `fin` bound to `n` there; `bigOr` likewise. -/
inductive U where
  | cst (c : Tm)
  | dat (t : Tm)
  | inp (t : Tm)
  | not (u : U)
  | and (u v : U)
  | or (u v : U)
  | bigAnd (n : Tm) (body fin : U)
  | bigOr (n : Tm) (body fin : U)
  | ite (c : Tm) (u v : U)
  | lett (t : Tm) (body : U)

/-- **The tokens of a template**, given the data bits `D` and the bound numbers `env`. -/
def U.toks (D : List Bool) : List ℕ → U → List Tok
  | env, .cst c => [.cst (c.eval env != 0)]
  | env, .dat t => [.cst (D.getD (t.eval env) false)]
  | env, .inp t => [.wir (t.eval env)]
  | env, .not u => u.toks D env ++ [.neg]
  | env, .and u v => u.toks D env ++ v.toks D env ++ [.conj]
  | env, .or u v => u.toks D env ++ v.toks D env ++ [.disj]
  | env, .bigAnd n body fin =>
      (List.range (n.eval env)).flatMap (fun i => body.toks D (env ++ [i])) ++
        fin.toks D (env ++ [n.eval env]) ++ List.replicate (n.eval env) .conj
  | env, .bigOr n body fin =>
      (List.range (n.eval env)).flatMap (fun i => body.toks D (env ++ [i])) ++
        fin.toks D (env ++ [n.eval env]) ++ List.replicate (n.eval env) .disj
  | env, .ite c u v => if c.eval env = 0 then v.toks D env else u.toks D env
  | env, .lett t body => body.toks D (env ++ [t.eval env])

theorem U.toks_ne_nil (D : List Bool) (u : U) : ∀ env, u.toks D env ≠ [] := by
  induction u with
  | cst c => intro env; simp [U.toks]
  | dat t => intro env; simp [U.toks]
  | inp t => intro env; simp [U.toks]
  | not u _ => intro env; simp [U.toks]
  | and u v _ _ => intro env; simp [U.toks]
  | or u v _ _ => intro env; simp [U.toks]
  | bigAnd n body fin _ ihf => intro env; simp [U.toks, ihf]
  | bigOr n body fin _ ihf => intro env; simp [U.toks, ihf]
  | ite c u v ihu ihv => intro env; simp only [U.toks]; split <;> simp [ihu, ihv]
  | lett t body ih => intro env; exact ih _

/-- A Boolean constant as a test term. -/
def Tm.ofBool (b : Bool) : Tm := .k b.toNat

@[simp] theorem Tm.ofBool_eval (b : Bool) (env : List ℕ) : ((Tm.ofBool b).eval env != 0) = b := by
  cases b <;> rfl

/-- Constant-valued templates. -/
def U.ofBool (b : Bool) : U := .cst (Tm.ofBool b)

@[simp] theorem U.ofBool_toks (D : List Bool) (env : List ℕ) (b : Bool) :
    (U.ofBool b).toks D env = [.cst b] := by
  simp [U.ofBool, U.toks]

/-- A fixed finite disjunction chain of templates (`anyExpression` of a fixed list). -/
def U.orList : List U → U
  | [] => .ofBool false
  | u :: l => .or u (U.orList l)

theorem U.orList_toks (D : List Bool) (env : List ℕ) (l : List U) :
    (U.orList l).toks D env = l.flatMap (fun u => u.toks D env) ++ [.cst false] ++ List.replicate l.length .disj := by
  induction l with
  | nil => simp [U.orList]
  | cons u l ih =>
      simp only [U.orList, U.toks, ih, List.flatMap_cons, List.length_cons, List.replicate_succ',
        List.append_assoc]

/-- A fixed finite conjunction chain of templates. -/
def U.andList : List U → U
  | [] => .ofBool true
  | u :: l => .and u (U.andList l)

theorem U.andList_toks (D : List Bool) (env : List ℕ) (l : List U) :
    (U.andList l).toks D env = l.flatMap (fun u => u.toks D env) ++ [.cst true] ++ List.replicate l.length .conj := by
  induction l with
  | nil => simp [U.andList]
  | cons u l ih =>
      simp only [U.andList, U.toks, ih, List.flatMap_cons, List.length_cons, List.replicate_succ',
        List.append_assoc]

/-- A disjunction chain over `List.ofFn` is a `bigOr` loop. -/
theorem postR_anyOfFn {width k : ℕ} (ρ : Fin width → ℕ) (F : Fin k → BoolExpr width) (D : List Bool)
    (env : List ℕ) (n : Tm) (body fin : U) (hn : n.eval env = k)
    (hb : ∀ i : Fin k, postR ρ (F i) = body.toks D (env ++ [i.val]))
    (hf : fin.toks D (env ++ [k]) = [.cst false]) :
    postR ρ (anyExpression (List.ofFn F)) = (U.bigOr n body fin).toks D env := by
  rw [postR_any, U.toks, hn, hf, List.length_ofFn,
    flatMap_ofFn k F (postR ρ) (fun i => body.toks D (env ++ [i])) hb]

/-- A conjunction chain over `List.ofFn` is a `bigAnd` loop. -/
theorem postR_allOfFn {width k : ℕ} (ρ : Fin width → ℕ) (F : Fin k → BoolExpr width) (D : List Bool)
    (env : List ℕ) (n : Tm) (body fin : U) (hn : n.eval env = k)
    (hb : ∀ i : Fin k, postR ρ (F i) = body.toks D (env ++ [i.val]))
    (hf : fin.toks D (env ++ [k]) = [.cst true]) :
    postR ρ (allExpression (List.ofFn F)) = (U.bigAnd n body fin).toks D env := by
  rw [postR_all, U.toks, hn, hf, List.length_ofFn,
    flatMap_ofFn k F (postR ρ) (fun i => body.toks D (env ++ [i])) hb]

/-- A disjunction chain over a fixed `List.ofFn` is an `orList`. -/
theorem postR_anyOfFn_list {width k : ℕ} (ρ : Fin width → ℕ) (F : Fin k → BoolExpr width) (D : List Bool)
    (env : List ℕ) (G : Fin k → U) (hb : ∀ i : Fin k, postR ρ (F i) = (G i).toks D env) :
    postR ρ (anyExpression (List.ofFn F)) = (U.orList (List.ofFn G)).toks D env := by
  rw [postR_any, U.orList_toks, List.length_ofFn, List.length_ofFn,
    flatMap_ofFn k F (postR ρ) (fun i => if h : i < k then (G ⟨i, h⟩).toks D env else []) (fun i => by
      simp [hb i]),
    flatMap_ofFn k G (fun u => u.toks D env) (fun i => if h : i < k then (G ⟨i, h⟩).toks D env else []) (fun i => by
      simp)]

end NearCubicGates.Adapters.Compile.OraclePrint

import SourceAdapters.Routing.CircuitPrefixFormula
import SourceAdapters.ACSP.Encoding

/-! The construction in `lem:generator`: the numerical coordinate-prefix gate list and its raw words. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open ACSP Joins

/-- Replace only field constants by their numerical encodings. -/
def codeGate {F : Type} (encode : F → ℕ) : ArithGate F → CodeGate
  | .input i => .input i
  | .const c => .const (encode c)
  | .add a b => .add a b
  | .mul a b => .mul a b

namespace Prefix

/-- The raw gate words, or the empty word in count mode. -/
def words (mode : ℕ) (gs : List CodeGate) : List Bool :=
  if mode = 0 then [] else gs.flatMap gateWord

@[simp] theorem words_nil (mode : ℕ) : words mode [] = [] := by simp [words]

@[simp] theorem words_append (mode : ℕ) (as bs : List CodeGate) :
    words mode (as ++ bs) = words mode as ++ words mode bs := by
  by_cases h : mode = 0 <;> simp [words, h]

/-- Three gates for coefficient r of row a. -/
def termGates (m s b a r : ℕ) (cs : List ℕ) : List CodeGate :=
  [.const (cs.getD (a*m+r) 0), .mul (b+1+3*r) (s+r), .add (b+3*r) (b+2+3*r)]

def terms (m s b a k : ℕ) (cs : List ℕ) : List CodeGate :=
  (List.range k).flatMap fun r => termGates m s b a r cs

def rowGates (m s b a : ℕ) (cs : List ℕ) : List CodeGate :=
  [.const 0] ++ terms m s b a m cs

def rows (m s k : ℕ) (cs : List ℕ) : List CodeGate :=
  (List.range k).flatMap fun a => rowGates m s (s+m+a*(3*m+1)) a cs

def squares (s k : ℕ) : List CodeGate :=
  (List.range k).map fun r => .mul (s+r) (s+r)

def gates (m s : ℕ) (cs : List ℕ) : List CodeGate :=
  [.input 0] ++ squares s (m-1) ++ rows m s m cs

@[simp] theorem termGates_length (m s b a r : ℕ) (cs : List ℕ) :
    (termGates m s b a r cs).length = 3 := rfl

@[simp] theorem terms_length (m s b a k : ℕ) (cs : List ℕ) :
    (terms m s b a k cs).length = 3*k := by
  simp [terms, List.length_flatMap, Nat.mul_comm]

@[simp] theorem rowGates_length (m s b a : ℕ) (cs : List ℕ) :
    (rowGates m s b a cs).length = 3*m+1 := by simp [rowGates, Nat.add_comm]

@[simp] theorem rows_length (m s k : ℕ) (cs : List ℕ) :
    (rows m s k cs).length = k*(3*m+1) := by simp [rows, List.length_flatMap]

@[simp] theorem squares_length (s k : ℕ) : (squares s k).length = k := by simp [squares]

theorem gates_length (m s : ℕ) (cs : List ℕ) (hm : 1 ≤ m) :
    (gates m s cs).length = 3*m*m+2*m := by
  simp only [gates, List.length_append, List.length_singleton, squares_length, rows_length]
  have h : 1+(m-1)=m := by omega
  rw [h]
  ring

@[simp] theorem terms_succ (m s b a k : ℕ) (cs : List ℕ) :
    terms m s b a (k+1) cs = terms m s b a k cs ++ termGates m s b a k cs := by
  simp [terms, List.range_succ]

@[simp] theorem rows_succ (m s k : ℕ) (cs : List ℕ) :
    rows m s (k+1) cs = rows m s k cs ++ rowGates m s (s+m+k*(3*m+1)) k cs := by
  simp [rows, List.range_succ]

@[simp] theorem squares_succ (s k : ℕ) :
    squares s (k+1) = squares s k ++ [.mul (s+k) (s+k)] := by
  simp [squares, List.range_succ]

theorem finRange_val (m : ℕ) : (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

theorem row_code {F : Type} [Field F] {m : ℕ} (encode : F → ℕ)
    (hzero : encode 0 = 0) (coeff : Fin m → F) (s b a : ℕ) (cs : List ℕ)
    (hc : ∀ r : Fin m, cs.getD (a*m+r.val) 0 = encode (coeff r)) :
    (Circuit.PrefixFormula.rowGates coeff s b).map (codeGate encode) = rowGates m s b a cs := by
  rw [Circuit.PrefixFormula.rowGates, rowGates, terms, ← finRange_val m]
  simp only [List.map_append, List.map_cons, List.map_nil, codeGate, hzero,
    List.map_flatMap, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro r _
  simp only [termGates, hc]

theorem gates_code {F : Type} [Field F] (l : Layout) {e : Fin l.m → F}
    (coords : Coordinates l.m e) (encode : F → ℕ) (hzero : encode 0 = 0)
    (s : ℕ) (cs : List ℕ)
    (hc : ∀ a r : Fin l.m, cs.getD (a.val*l.m+r.val) 0 = encode (coords.coeff a r)) :
    (Circuit.PrefixFormula.prefixGates l coords s).map (codeGate encode) = gates l.m s cs := by
  simp only [Circuit.PrefixFormula.prefixGates, gates, List.map_append,
    List.map_cons, List.map_nil, codeGate]
  congr 1
  · simp [Circuit.PrefixFormula.squareGates, squares, codeGate, List.map_map]
  · rw [rows, ← finRange_val l.m]
    simp only [List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr
    intro a _
    exact row_code encode hzero (coords.coeff a) s _ a.val cs (hc a)

end Prefix
end NearCubicGates.Adapters.Routing.TermsMachine

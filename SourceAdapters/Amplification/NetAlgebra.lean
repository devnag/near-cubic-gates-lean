import NineInputs
import Mathlib

/-!
# A02 infrastructure: multi-output Boolean nets and their composition, with exact node counts

`app:sources`, "Full-range amplification interface": the reconstruction yields "an exact circuit for the original `n`-input function with at most
`A(n/δ)^a s' + n + 2` nodes. The polynomial reconstruction overhead includes fixing the decoder's randomness and
conversion to our fan-in-two basis." STV's proof of Theorem 24 obtains the circuit by "expressing `M_j^B` as a
circuit"; this module is the circuit side of that sentence, in the target basis (`BooleanNode`: constants, inputs,
NOT, fan-in-two AND/OR), counting every node.

* `Net α β`: a node list over inputs indexed by `α` with outputs indexed by `β` (children are absolute indices;
  a child that is not earlier reads `false`, exactly as `BooleanCircuit.values` reads a missing entry).
* `Real s F`: some net with at most `s` nodes computes `F : (α → Bool) → β → Bool`.
* Closure: `Real.bind` (the second net reads the original inputs and the first net's outputs; sizes add),
  `Real.comp`, `Real.par`, `Real.reindex`, `Real.mapIn` (free relabelings), `Real.leaves` (constants and inputs),
  `Real.pi` (one net per output), `Real.shannon` (every `a`-ary function with `8·2^a` nodes),
  `Real.local` (every output a function of `a` chosen inputs), `Real.iterate`, `Real.foldList`.
* `hasCircuitOfSize_of_real`: a single-output net on `Fin n` gives `HasCircuitOfSize` with the same size (the
  nodes are made well formed without changing any value).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma39

/-! ## Gates and their values -/

/-- A gate whose inputs are indexed by `α`; children are absolute node indices. -/
inductive Gate (α : Type) where
  | const (b : Bool)
  | input (a : α)
  | not (c : ℕ)
  | and (l r : ℕ)
  | or (l r : ℕ)

namespace Gate

variable {α γ : Type}

/-- The value of a gate given the input and the values of the earlier nodes. -/
def eval (x : α → Bool) (P : List Bool) : Gate α → Bool
  | const b => b
  | input a => x a
  | not c => !(P[c]?.getD false)
  | and l r => P[l]?.getD false && P[r]?.getD false
  | or l r => P[l]?.getD false || P[r]?.getD false

/-- A gate of a copied net: children move by `off`, input `a` becomes the gate `inp a`. -/
def shift (off : ℕ) (inp : γ → Gate α) : Gate γ → Gate α
  | const b => const b
  | input a => inp a
  | not c => not (c + off)
  | and l r => and (l + off) (r + off)
  | or l r => or (l + off) (r + off)

theorem eval_shift (off : ℕ) (inp : γ → Gate α) (x : α → Bool) (y : γ → Bool) (P Q : List Bool)
    (hP : P.length = off) (hinp : ∀ a (R : List Bool), (∀ i < off, R[i]? = P[i]?) → (inp a).eval x R = y a)
    (g : Gate γ) : (g.shift off inp).eval x (P ++ Q) = g.eval y Q := by
  have hr : ∀ c, (P ++ Q)[c + off]? = Q[c]? := by
    intro c
    rw [List.getElem?_append_right (by omega)]
    congr 1
    omega
  cases g with
  | const b => rfl
  | input a =>
      exact hinp a _ (fun i hi => List.getElem?_append_left (by omega))
  | not c => simp only [shift, eval, hr]
  | and l r => simp only [shift, eval, hr]
  | or l r => simp only [shift, eval, hr]

end Gate

/-- The values of the nodes `L` appended after the values `P`. -/
def vals {α : Type} (x : α → Bool) : List (Gate α) → List Bool → List Bool
  | [], P => P
  | g :: L, P => vals x L (P ++ [g.eval x P])

theorem length_vals {α : Type} (x : α → Bool) :
    ∀ (L : List (Gate α)) (P : List Bool), (vals x L P).length = P.length + L.length
  | [], P => by simp [vals]
  | g :: L, P => by
      rw [vals, length_vals x L]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem vals_append {α : Type} (x : α → Bool) :
    ∀ (L1 L2 : List (Gate α)) (P : List Bool), vals x (L1 ++ L2) P = vals x L2 (vals x L1 P)
  | [], L2, P => rfl
  | g :: L1, L2, P => by
      rw [List.cons_append, vals, vals, vals_append x L1 L2]

theorem vals_prefix {α : Type} (x : α → Bool) :
    ∀ (L : List (Gate α)) (P : List Bool), ∃ V, vals x L P = P ++ V
  | [], P => ⟨[], by simp [vals]⟩
  | g :: L, P => by
      obtain ⟨V, hV⟩ := vals_prefix x L (P ++ [g.eval x P])
      exact ⟨[g.eval x P] ++ V, by rw [vals, hV, List.append_assoc]⟩

theorem vals_shift {α γ : Type} (off : ℕ) (inp : γ → Gate α) (x : α → Bool) (y : γ → Bool) (P : List Bool)
    (hP : P.length = off) (hinp : ∀ a (R : List Bool), (∀ i < off, R[i]? = P[i]?) → (inp a).eval x R = y a) :
    ∀ (L : List (Gate γ)) (Q : List Bool), vals x (L.map (Gate.shift off inp)) (P ++ Q) = P ++ vals y L Q
  | [], Q => rfl
  | g :: L, Q => by
      rw [List.map_cons, vals, vals, Gate.eval_shift off inp x y P Q hP hinp, List.append_assoc]
      exact vals_shift off inp x y P hP hinp L _

/-! ## Nets -/

/-- A multi-output net: nodes over inputs `α`, an output node for every `b : β`. -/
structure Net (α β : Type) where
  nodes : List (Gate α)
  out : β → ℕ
  out_lt : ∀ b, out b < nodes.length

namespace Net

variable {α β γ δ : Type}

/-- The output values of the net on input `x`. -/
def eval (N : Net α β) (x : α → Bool) (b : β) : Bool :=
  (vals x N.nodes [])[N.out b]?.getD false

/-- The second net reads the original inputs (`inl`) and the outputs of the first (`inr`). -/
def bind (N1 : Net α β) (N2 : Net (α ⊕ β) γ) : Net α γ where
  nodes := N1.nodes ++ N2.nodes.map
    (Gate.shift N1.nodes.length (Sum.elim Gate.input (fun b => Gate.or (N1.out b) (N1.out b))))
  out c := N1.nodes.length + N2.out c
  out_lt c := by
    have := N2.out_lt c
    simp only [List.length_append, List.length_map]
    omega

theorem eval_bind (N1 : Net α β) (N2 : Net (α ⊕ β) γ) (x : α → Bool) :
    (N1.bind N2).eval x = N2.eval (Sum.elim x (N1.eval x)) := by
  funext c
  have hv := vals_shift N1.nodes.length (Sum.elim Gate.input (fun b => Gate.or (N1.out b) (N1.out b))) x
    (Sum.elim x (N1.eval x)) (vals x N1.nodes []) (by rw [length_vals]; simp) (by
      intro a R hR
      cases a with
      | inl a => rfl
      | inr b =>
          have h1 := hR (N1.out b) (N1.out_lt b)
          simp only [Sum.elim_inr, Gate.eval, Bool.or_self, h1]
          rfl) N2.nodes []
  simp only [List.append_nil] at hv
  simp only [eval, bind]
  rw [vals_append, hv]
  rw [List.getElem?_append_right (by rw [length_vals]; simp)]
  congr 2
  rw [length_vals]
  simp

/-- Two nets side by side on the same inputs. -/
def par (N1 : Net α β) (N2 : Net α γ) : Net α (β ⊕ γ) where
  nodes := N1.nodes ++ N2.nodes.map (Gate.shift N1.nodes.length Gate.input)
  out := Sum.elim N1.out (fun c => N1.nodes.length + N2.out c)
  out_lt b := by
    cases b with
    | inl b => have := N1.out_lt b; simp only [Sum.elim_inl, List.length_append]; omega
    | inr c => have := N2.out_lt c; simp only [Sum.elim_inr, List.length_append, List.length_map]; omega

theorem eval_par (N1 : Net α β) (N2 : Net α γ) (x : α → Bool) :
    (N1.par N2).eval x = Sum.elim (N1.eval x) (N2.eval x) := by
  funext b
  have hv := vals_shift N1.nodes.length Gate.input x x (vals x N1.nodes []) (by rw [length_vals]; simp)
    (fun a R _ => rfl) N2.nodes []
  simp only [List.append_nil] at hv
  simp only [eval, par]
  rw [vals_append, hv]
  cases b with
  | inl b =>
      simp only [Sum.elim_inl]
      rw [List.getElem?_append_left (by rw [length_vals]; simpa using N1.out_lt b)]
      rfl
  | inr c =>
      simp only [Sum.elim_inr]
      rw [List.getElem?_append_right (by rw [length_vals]; simp)]
      congr 2
      rw [length_vals]
      simp

/-- Relabel the outputs. -/
def reindex (N : Net α β) (e : γ → β) : Net α γ where
  nodes := N.nodes
  out := N.out ∘ e
  out_lt c := N.out_lt (e c)

theorem eval_reindex (N : Net α β) (e : γ → β) (x : α → Bool) : (N.reindex e).eval x = N.eval x ∘ e := rfl

/-- Relabel the inputs. -/
def mapIn (N : Net γ β) (e : γ → α) : Net α β where
  nodes := N.nodes.map (Gate.shift 0 (fun a => Gate.input (e a)))
  out := N.out
  out_lt b := by simpa using N.out_lt b

theorem eval_mapIn (N : Net γ β) (e : γ → α) (x : α → Bool) : (N.mapIn e).eval x = N.eval (x ∘ e) := by
  funext b
  have hv := vals_shift 0 (fun a => Gate.input (e a)) x (x ∘ e) [] rfl (fun a R _ => rfl) N.nodes []
  simp only [List.nil_append] at hv
  simp only [eval, mapIn, hv]

end Net

/-! ## Realizable functions -/

/-- `F` is computed by a net with at most `s` nodes. -/
def Real {α β : Type} (s : ℕ) (F : (α → Bool) → β → Bool) : Prop :=
  ∃ N : Net α β, N.nodes.length ≤ s ∧ ∀ x, N.eval x = F x

namespace Real

variable {α β γ δ : Type}

theorem mono {s s' : ℕ} {F : (α → Bool) → β → Bool} (h : Real s F) (hs : s ≤ s') : Real s' F := by
  obtain ⟨N, hN, hF⟩ := h
  exact ⟨N, hN.trans hs, hF⟩

theorem congr {s : ℕ} {F G : (α → Bool) → β → Bool} (h : Real s F) (hFG : ∀ x b, F x b = G x b) : Real s G := by
  obtain ⟨N, hN, hF⟩ := h
  exact ⟨N, hN, fun x => by rw [hF]; funext b; exact hFG x b⟩

theorem bind {s1 s2 : ℕ} {F : (α → Bool) → β → Bool} {G : (α ⊕ β → Bool) → γ → Bool}
    (h1 : Real s1 F) (h2 : Real s2 G) : Real (s1 + s2) (fun x => G (Sum.elim x (F x))) := by
  obtain ⟨N1, hN1, hF⟩ := h1
  obtain ⟨N2, hN2, hG⟩ := h2
  refine ⟨N1.bind N2, ?_, fun x => ?_⟩
  · simp only [Net.bind, List.length_append, List.length_map]; omega
  · rw [Net.eval_bind, hG, hF]

theorem par {s1 s2 : ℕ} {F : (α → Bool) → β → Bool} {G : (α → Bool) → γ → Bool}
    (h1 : Real s1 F) (h2 : Real s2 G) : Real (s1 + s2) (fun x => Sum.elim (F x) (G x)) := by
  obtain ⟨N1, hN1, hF⟩ := h1
  obtain ⟨N2, hN2, hG⟩ := h2
  refine ⟨N1.par N2, ?_, fun x => ?_⟩
  · simp only [Net.par, List.length_append, List.length_map]; omega
  · rw [Net.eval_par, hF, hG]

theorem reindex {s : ℕ} {F : (α → Bool) → β → Bool} (h : Real s F) (e : γ → β) : Real s (fun x => F x ∘ e) := by
  obtain ⟨N, hN, hF⟩ := h
  exact ⟨N.reindex e, hN, fun x => by rw [Net.eval_reindex, hF]⟩

theorem mapIn {s : ℕ} {G : (γ → Bool) → β → Bool} (h : Real s G) (e : γ → α) : Real s (fun x => G (x ∘ e)) := by
  obtain ⟨N, hN, hG⟩ := h
  exact ⟨N.mapIn e, by simpa [Net.mapIn] using hN, fun x => by rw [Net.eval_mapIn, hG]⟩

theorem comp {s1 s2 : ℕ} {F : (α → Bool) → β → Bool} {G : (β → Bool) → γ → Bool}
    (h1 : Real s1 F) (h2 : Real s2 G) : Real (s1 + s2) (fun x => G (F x)) :=
  (bind h1 (mapIn h2 Sum.inr)).congr fun _ _ => rfl

/-- A leaf: a constant (`inl`) or an input (`inr`). -/
def leafEval {α : Type} (x : α → Bool) : Bool ⊕ α → Bool := Sum.elim id x

/-- The gate of a leaf. -/
def leafGate {α : Type} : Bool ⊕ α → Gate α := Sum.elim Gate.const Gate.input

theorem vals_leaves (x : α → Bool) :
    ∀ (L : List (Bool ⊕ α)) (P : List Bool), vals x (L.map leafGate) P = P ++ L.map (leafEval x)
  | [], P => by simp [vals]
  | w :: L, P => by
      rw [List.map_cons, vals, vals_leaves x L, List.map_cons, List.append_assoc]
      cases w <;> rfl

/-- Constants and inputs: `k` nodes. -/
theorem leaves {k : ℕ} (w : Fin k → Bool ⊕ α) : Real k (fun x j => leafEval x (w j)) := by
  refine ⟨⟨(List.ofFn w).map leafGate, fun j => j.val, fun j => by simp⟩, by simp, fun x => ?_⟩
  funext j
  simp only [Net.eval]
  rw [vals_leaves, List.nil_append, List.getElem?_map, List.getElem?_ofFn]
  simp

/-- The empty family of outputs. -/
theorem empty (F : (α → Bool) → Fin 0 → Bool) : Real 0 F :=
  ⟨⟨[], fun j => j.elim0, fun j => j.elim0⟩, le_rfl, fun _ => funext fun j => j.elim0⟩

/-- One net per output, over `Fin k`. -/
theorem piFin {s : ℕ} : ∀ (k : ℕ) (F : (α → Bool) → Fin k → Bool),
    (∀ j, Real s (fun x (_ : Unit) => F x j)) → Real (k * s) F
  | 0, F, _ => (empty F).mono (by simp)
  | k + 1, F, h => by
      have h1 := piFin k (fun x j => F x j.castSucc) (fun j => h j.castSucc)
      have h2 := par h1 (h (Fin.last k))
      have h3 := h2.reindex (fun j : Fin (k + 1) => if hj : j.val < k then Sum.inl ⟨j.val, hj⟩ else Sum.inr ())
      refine (h3.mono (by ring_nf; omega)).congr fun x j => ?_
      simp only [Function.comp_apply]
      by_cases hj : j.val < k
      · rw [dif_pos hj]; rfl
      · rw [dif_neg hj]
        have : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
        subst this; rfl

/-- One net per output, over any finite type. -/
theorem pi [Fintype β] {s : ℕ} (F : (α → Bool) → β → Bool) (h : ∀ b, Real s (fun x (_ : Unit) => F x b)) :
    Real (Fintype.card β * s) F := by
  classical
  let e := Fintype.equivFin β
  have h1 := piFin (Fintype.card β) (fun x j => F x (e.symm j)) (fun j => h (e.symm j))
  exact (h1.reindex e).congr fun x b => by simp

/-- The multiplexer `x_last ? y1 : y0` as a net: 7 nodes. -/
def muxNet : Net (Bool ⊕ Bool ⊕ Bool) Unit where
  nodes := [.input (.inl true), .input (.inr (.inl true)), .input (.inr (.inr true)), .not 0, .and 0 1,
    .and 3 2, .or 4 5]
  out _ := 6
  out_lt _ := by simp

theorem muxNet_eval (z : Bool ⊕ Bool ⊕ Bool → Bool) :
    muxNet.eval z () = if z (.inl true) then z (.inr (.inl true)) else z (.inr (.inr true)) := by
  simp only [Net.eval, muxNet, vals, Gate.eval]
  cases z (.inl true) <;> cases z (.inr (.inl true)) <;> cases z (.inr (.inr true)) <;> rfl

/-- Shannon expansion in nets, exact count `8·2^a − 7`. -/
theorem shannon' : ∀ (a : ℕ) (g : (Fin a → Bool) → Bool), Real (8 * 2 ^ a - 7) (fun x (_ : Unit) => g x)
  | 0, g => by
      have h := leaves (α := Fin 0) (fun _ : Fin 1 => Sum.inl (g Fin.elim0))
      refine ((h.reindex (fun _ : Unit => (0 : Fin 1))).mono (by norm_num)).congr fun x _ => ?_
      simp only [Function.comp_apply, leafEval, Sum.elim_inl, id]
      congr 1; funext i; exact i.elim0
  | a + 1, g => by
      have h1 := (shannon' a (fun y => g (Fin.snoc y true))).mapIn (Fin.castSucc : Fin a → Fin (a + 1))
      have h0 := (shannon' a (fun y => g (Fin.snoc y false))).mapIn (Fin.castSucc : Fin a → Fin (a + 1))
      have hp := par h1 h0
      have hm : Real 7 (fun (z : Fin (a + 1) ⊕ (Unit ⊕ Unit) → Bool) (_ : Unit) =>
          if z (.inl (Fin.last a)) then z (.inr (.inl ())) else z (.inr (.inr ()))) := by
        refine ⟨muxNet.mapIn (Sum.elim (fun _ => Sum.inl (Fin.last a))
          (Sum.elim (fun _ => Sum.inr (Sum.inl ())) (fun _ => Sum.inr (Sum.inr ())))), by simp [Net.mapIn, muxNet],
          fun z => ?_⟩
        funext u
        rw [Net.eval_mapIn, muxNet_eval]
        rfl
      have hb := bind hp hm
      refine (hb.mono (by have := Nat.one_le_two_pow (n := a); rw [pow_succ]; omega)).congr fun x _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      have hx : x = Fin.snoc (fun i : Fin a => x i.castSucc) (x (Fin.last a)) := by
        funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      cases hl : x (Fin.last a)
      · simp only [Bool.false_eq_true, if_false]
        conv_rhs => rw [hx, hl]
        rfl
      · simp only [if_true]
        conv_rhs => rw [hx, hl]
        rfl

/-- **Shannon expansion** in nets: every `a`-ary function with at most `8·2^a` nodes. -/
theorem shannon (a : ℕ) (g : (Fin a → Bool) → Bool) : Real (8 * 2 ^ a) (fun x (_ : Unit) => g x) :=
  (shannon' a g).mono (Nat.sub_le _ _)

/-- **Local functions**: every output is a function of `a` chosen inputs. -/
theorem «local» [Fintype β] (a : ℕ) (σ : β → Fin a → α) (g : β → (Fin a → Bool) → Bool) :
    Real (Fintype.card β * (a + 8 * 2 ^ a)) (fun x b => g b (fun i => x (σ b i))) := by
  refine pi _ fun b => ?_
  have h1 := leaves (fun i : Fin a => (Sum.inr (σ b i) : Bool ⊕ α))
  exact (comp h1 (shannon a (g b))).congr fun x _ => rfl

/-- `T` applications of `F` after `I`. -/
theorem iterate {s0 s : ℕ} {I : (α → Bool) → γ → Bool} {F : (γ → Bool) → γ → Bool} (h0 : Real s0 I)
    (h : Real s F) : ∀ T : ℕ, Real (s0 + T * s) (fun x => F^[T] (I x))
  | 0 => h0.mono (by simp)
  | T + 1 => by
      refine ((comp (iterate h0 h T) h).mono (by ring_nf; omega)).congr fun x b => ?_
      rw [Function.iterate_succ_apply']

/-- A left fold over a list of steps, each reading the original input and the current state. -/
theorem foldList {ι σ : Type} {c0 c : ℕ} (step : ι → (σ → Bool) → (α → Bool) → σ → Bool) :
    ∀ (l : List ι) (I : (α → Bool) → σ → Bool), Real c0 I →
      (∀ i ∈ l, Real c (fun (z : α ⊕ σ → Bool) => step i (z ∘ Sum.inr) (z ∘ Sum.inl))) →
      Real (c0 + l.length * c) (fun x => l.foldl (fun s i => step i s x) (I x))
  | [], I, h0, _ => h0.mono (by simp)
  | i :: l, I, h0, h => by
      have h1 := bind h0 (h i (by simp))
      have h2 := foldList step l (fun x => step i (I x) x) h1 (fun j hj => h j (by simp [hj]))
      exact (h2.mono (by simp only [List.length_cons]; ring_nf; omega)).congr fun x b => rfl

end Real

/-! ## Back to `BooleanCircuit` -/

/-- A well-formed node with the same value: a child that is not earlier is read as `false`. -/
def toNode {n : ℕ} (i : ℕ) : Gate (Fin n) → BooleanNode n
  | .const b => .const b
  | .input a => .input a
  | .not c => if c < i then .not c else .const true
  | .and l r => if l < i ∧ r < i then .and l r else .const false
  | .or l r =>
      if l < i ∧ r < i then .or l r else if l < i then .or l l else if r < i then .or r r else .const false

/-- The nodes `L` converted, the first at index `i`. -/
def toNodes {n : ℕ} : ℕ → List (Gate (Fin n)) → List (BooleanNode n)
  | _, [] => []
  | i, g :: L => toNode i g :: toNodes (i + 1) L

theorem length_toNodes {n : ℕ} : ∀ (i : ℕ) (L : List (Gate (Fin n))), (toNodes i L).length = L.length
  | _, [] => rfl
  | i, _ :: L => by simp [toNodes, length_toNodes (i + 1) L]

theorem toNode_wf {n : ℕ} (i : ℕ) (g : Gate (Fin n)) : (toNode i g).WellFormedAt i := by
  cases g with
  | const b => trivial
  | input a => trivial
  | not c => simp only [toNode]; split_ifs with h <;> simp_all [BooleanNode.WellFormedAt]
  | and l r => simp only [toNode]; split_ifs with h <;> simp_all [BooleanNode.WellFormedAt]
  | or l r => simp only [toNode]; split_ifs with h h' h'' <;> simp_all [BooleanNode.WellFormedAt]

theorem toNodes_getElem {n : ℕ} : ∀ (i : ℕ) (L : List (Gate (Fin n))) (j : ℕ) (hj : j < (toNodes i L).length),
    ∃ g, (toNodes i L)[j] = toNode (i + j) g
  | _, [], j, hj => by simp [toNodes] at hj
  | i, g :: L, 0, _ => ⟨g, by simp [toNodes]⟩
  | i, g :: L, j + 1, hj => by
      obtain ⟨g', hg'⟩ := toNodes_getElem (i + 1) L j (by simp [toNodes] at hj; simpa [length_toNodes] using hj)
      exact ⟨g', by simp only [toNodes, List.getElem_cons_succ]; rw [hg']; congr 1; omega⟩

theorem toNode_eval {n : ℕ} (x : BitInput n) (P : Array Bool) (g : Gate (Fin n)) :
    (toNode P.size g).eval x P = g.eval x P.toList := by
  have hn : ∀ c, P.size ≤ c → P[c]? = none := fun c hc => Array.getElem?_eq_none hc
  cases g with
  | const b => rfl
  | input a => rfl
  | not c =>
      simp only [toNode]
      split_ifs with h
      · simp [BooleanNode.eval, Gate.eval]
      · simp [BooleanNode.eval, Gate.eval, hn c (by omega)]
  | and l r =>
      simp only [toNode]
      split_ifs with h
      · simp [BooleanNode.eval, Gate.eval]
      · by_cases hl : l < P.size
        · have hr' : ¬ r < P.size := fun hr' => h ⟨hl, hr'⟩
          simp [BooleanNode.eval, Gate.eval, hn r (by omega)]
        · simp [BooleanNode.eval, Gate.eval, hn l (by omega)]
  | or l r =>
      simp only [toNode]
      split_ifs with h h' h''
      · simp [BooleanNode.eval, Gate.eval]
      · simp [BooleanNode.eval, Gate.eval, hn r (by omega)]
      · simp [BooleanNode.eval, Gate.eval, hn l (by omega)]
      · simp [BooleanNode.eval, Gate.eval, hn l (by omega), hn r (by omega)]

theorem foldl_toNodes {n : ℕ} (x : BitInput n) :
    ∀ (L : List (Gate (Fin n))) (P : Array Bool),
      ((toNodes P.size L).foldl (fun prior node => prior.push (node.eval x prior)) P).toList =
        vals x L P.toList
  | [], P => by simp [toNodes, vals]
  | g :: L, P => by
      simp only [toNodes, List.foldl_cons, vals]
      have h := foldl_toNodes x L (P.push ((toNode P.size g).eval x P))
      simp only [Array.size_push] at h
      rw [h, Array.toList_push, toNode_eval]

/-- **Back to the target model**: a single-output net with at most `s` nodes gives a circuit of size `≤ s`. -/
theorem hasCircuitOfSize_of_real {n s : ℕ} {F : (Fin n → Bool) → Unit → Bool} (h : Real s F) :
    HasCircuitOfSize (fun x => F x ()) s := by
  obtain ⟨N, hN, hF⟩ := h
  refine ⟨⟨toNodes 0 N.nodes, ⟨N.out (), by rw [length_toNodes]; exact N.out_lt ()⟩, fun j => ?_⟩, ?_, fun x => ?_⟩
  · obtain ⟨g, hg⟩ := toNodes_getElem 0 N.nodes j.val j.isLt
    rw [List.get_eq_getElem, hg, zero_add]
    exact toNode_wf _ g
  · simpa [BooleanCircuit.size, length_toNodes] using hN
  · show _ = F x ()
    rw [← hF x]
    simp only [BooleanCircuit.eval, BooleanCircuit.values, Net.eval]
    have h := foldl_toNodes x N.nodes #[]
    simp only [Array.size_empty] at h
    rw [← h]
    simp

/-! ## From `BooleanCircuit` -/

/-- A target node as a gate. -/
def ofNode {n : ℕ} : BooleanNode n → Gate (Fin n)
  | .const b => .const b
  | .input a => .input a
  | .not c => .not c
  | .and l r => .and l r
  | .or l r => .or l r

theorem ofNode_eval {n : ℕ} (x : BitInput n) (P : Array Bool) (g : BooleanNode n) :
    (ofNode g).eval x P.toList = g.eval x P := by
  cases g <;> simp [ofNode, Gate.eval, BooleanNode.eval]

theorem foldl_ofNode {n : ℕ} (x : BitInput n) :
    ∀ (L : List (BooleanNode n)) (P : Array Bool),
      (L.foldl (fun prior node => prior.push (node.eval x prior)) P).toList = vals x (L.map ofNode) P.toList
  | [], P => by simp [vals]
  | g :: L, P => by
      simp only [List.foldl_cons, List.map_cons, vals]
      rw [foldl_ofNode x L, Array.toList_push, ofNode_eval]

/-- **A target circuit is a net** with the same number of nodes. -/
theorem Real.ofCircuit {n : ℕ} (C : BooleanCircuit n) : Real C.size (fun x (_ : Unit) => C.eval x) := by
  refine ⟨⟨C.nodes.map ofNode, fun _ => C.output.val, fun _ => by simp⟩, by simp [BooleanCircuit.size], fun x => ?_⟩
  funext u
  simp only [Net.eval, BooleanCircuit.eval, BooleanCircuit.values]
  have h := foldl_ofNode x C.nodes #[]
  rw [← h, Array.getElem?_toList]

end NearCubicGates.Adapters.Amplification

import Proof.Gates.Outer.Interface

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires NearCubicWires.Bindings.MW20

variable {q ℓ : ℕ}

/-- The answer to an oracle query `a ∈ {0,1}^ℓ` is `B_pf(a 0^{q−ℓ})` (paper §11.4, `O_{B_pf}`). -/
def padQuery (a : BitInput ℓ) : BitInput q := fun j => if h : j.val < ℓ then a ⟨j.val, h⟩ else false

/-- `C`'s input: the first `ℓ` of the `q` inputs (`false` beyond `q`). -/
def truncInput (r : BitInput q) : BitInput ℓ := fun i => if h : i.val < q then r ⟨i.val, h⟩ else false

/-- A reference into the copied circuit: the image of `C`'s node `c`, or the zero wire `0`. -/
def ref (map : List ℕ) (c : ℕ) : ℕ := map.getD c 0

/-- A reference inside the copy of `B` started at `off`: node `c < t` of `B` sits at `off + c`; others read the zero
wire. -/
def copyRef (off t c : ℕ) : ℕ := if c < t then off + c else 0

/-- Node `t` of `B`, copied at offset `off`, its inputs wired to `wires`. -/
def copyNode (off : ℕ) (wires : List ℕ) (t : ℕ) : BooleanNode q → BooleanNode q
  | .const b => .const b
  | .input j => if j.val < wires.length then .or (wires.getD j.val 0) (wires.getD j.val 0) else .const false
  | .not c => .not (copyRef off t c)
  | .and l r => .and (copyRef off t l) (copyRef off t r)
  | .or l r => .or (copyRef off t l) (copyRef off t r)

/-- The nodes of `B` from position `t` on, copied at offset `off`. -/
def copyNodesFrom (off : ℕ) (wires : List ℕ) : ℕ → List (BooleanNode q) → List (BooleanNode q)
  | _, [] => []
  | t, nd :: rest => copyNode off wires t nd :: copyNodesFrom off wires (t + 1) rest

/-- One node of `C`: append its image (one node, or a copy of `B` for an oracle gate) and record where it is.
General form (shared with the stage-2 formula of the `E^NP` recovery): `C`'s input `i` becomes the node `inMap i`, and the copy of `B`
at an oracle gate reads the gate's argument wires followed by the fixed wires `extra`. -/
def substStepG (B : BooleanCircuit q) (inMap : Fin ℓ → BooleanNode q) (extra : List ℕ)
    (acc : List (BooleanNode q) × List ℕ) (nd : OracleNode ℓ ℓ) : List (BooleanNode q) × List ℕ :=
  match nd with
  | .const b => (acc.1 ++ [.const b], acc.2 ++ [acc.1.length])
  | .input i => (acc.1 ++ [inMap i], acc.2 ++ [acc.1.length])
  | .not c => (acc.1 ++ [.not (ref acc.2 c)], acc.2 ++ [acc.1.length])
  | .and l r => (acc.1 ++ [.and (ref acc.2 l) (ref acc.2 r)], acc.2 ++ [acc.1.length])
  | .or l r => (acc.1 ++ [.or (ref acc.2 l) (ref acc.2 r)], acc.2 ++ [acc.1.length])
  | .oracle args =>
      (acc.1 ++ copyNodesFrom acc.1.length ((List.ofFn fun j => ref acc.2 (args j)) ++ extra) 0 B.nodes,
        acc.2 ++ [acc.1.length + B.output.val])

/-- `D_B`'s input map: `C`'s input `i` is `D`'s input `i` (`false` beyond `q`). -/
def inputMapD (i : Fin ℓ) : BooleanNode q := if h : i.val < q then .input ⟨i.val, h⟩ else .const false

/-- The step of `D_B`: identity input map, no extra wires. -/
def substStep (B : BooleanCircuit q) : List (BooleanNode q) × List ℕ → OracleNode ℓ ℓ → List (BooleanNode q) × List ℕ :=
  substStepG B inputMapD []

/-- General build from a start prefix (shared with the `E^NP` recovery). -/
def substBuildG (start : List (BooleanNode q)) (inMap : Fin ℓ → BooleanNode q) (extra : List ℕ)
    (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) : List (BooleanNode q) × List ℕ :=
  C.nodes.foldl (substStepG B inMap extra) (start, [])

/-- All of `C`, starting from the zero wire. -/
def substBuild (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) : List (BooleanNode q) × List ℕ :=
  substBuildG [.const false] inputMapD [] C B

/-- The nodes of `D`: the image of `C`, then the negation of `C`'s output. -/
def substNodes (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) : List (BooleanNode q) :=
  (substBuild C B).1 ++ [.not (ref (substBuild C B).2 C.output.val)]

/-! ## Well-formedness -/

/-- Every node refers only to earlier nodes, every recorded image is a node, and node `0` exists. -/
def BuildOK (acc : List (BooleanNode q) × List ℕ) : Prop :=
  1 ≤ acc.1.length ∧ (∀ p (h : p < acc.1.length), (acc.1[p]'h).WellFormedAt p) ∧ ∀ x ∈ acc.2, x < acc.1.length

theorem ref_lt {map : List ℕ} {len : ℕ} (hmap : ∀ x ∈ map, x < len) (hlen : 1 ≤ len) (c : ℕ) :
    ref map c < len := by
  unfold ref
  rw [List.getD_eq_getElem?_getD]
  cases h : map[c]? with
  | none => simp only [Option.getD_none]; omega
  | some x => simpa using hmap x (List.mem_of_getElem? h)

theorem copyNodesFrom_length (off : ℕ) (wires : List ℕ) :
    ∀ (t : ℕ) (bs : List (BooleanNode q)), (copyNodesFrom off wires t bs).length = bs.length
  | _, [] => rfl
  | t, _ :: rest => by simp [copyNodesFrom, copyNodesFrom_length off wires (t + 1) rest]

theorem copyNodesFrom_getElem? (off : ℕ) (wires : List ℕ) :
    ∀ (t : ℕ) (bs : List (BooleanNode q)) (u : ℕ),
      (copyNodesFrom off wires t bs)[u]? = (bs[u]?).map (copyNode off wires (t + u))
  | _, [], u => by simp [copyNodesFrom]
  | t, nd :: rest, 0 => by simp [copyNodesFrom]
  | t, nd :: rest, u + 1 => by
      simp only [copyNodesFrom, List.getElem?_cons_succ]
      rw [copyNodesFrom_getElem? off wires (t + 1) rest u]
      congr 2
      omega

theorem copyNodesFrom_getElem (off : ℕ) (wires : List ℕ) (t : ℕ) (bs : List (BooleanNode q)) (u : ℕ)
    (h : u < (copyNodesFrom off wires t bs).length) :
    (copyNodesFrom off wires t bs)[u]'h =
      copyNode off wires (t + u) (bs[u]'(by rwa [copyNodesFrom_length] at h)) := by
  have h1 := copyNodesFrom_getElem? off wires t bs u
  rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem (by rwa [copyNodesFrom_length] at h)] at h1
  simpa using h1

theorem copyNode_wellFormed (off : ℕ) (wires : List ℕ) (t : ℕ) (nd : BooleanNode q)
    (hoff : 1 ≤ off) (hwires : ∀ x ∈ wires, x < off) :
    (copyNode off wires t nd).WellFormedAt (off + t) := by
  have hc : ∀ c, copyRef off t c < off + t := by
    intro c
    unfold copyRef
    split <;> omega
  cases nd with
  | const b => trivial
  | input j =>
      show (if j.val < wires.length then BooleanNode.or (wires.getD j.val 0) (wires.getD j.val 0)
        else BooleanNode.const false).WellFormedAt (off + t)
      by_cases hj : j.val < wires.length
      · rw [if_pos hj]
        have hw : wires.getD j.val 0 < off := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
          exact hwires _ (List.getElem_mem hj)
        exact ⟨by omega, by omega⟩
      · rw [if_neg hj]
        trivial
  | not c => exact hc c
  | and l r => exact ⟨hc l, hc r⟩
  | or l r => exact ⟨hc l, hc r⟩

theorem substStepG_ok (B : BooleanCircuit q) (inMap : Fin ℓ → BooleanNode q) (extra : List ℕ)
    (hin : ∀ i p, (inMap i).WellFormedAt p) (acc : List (BooleanNode q) × List ℕ) (nd : OracleNode ℓ ℓ)
    (h : BuildOK acc) (hextra : ∀ x ∈ extra, x < acc.1.length) : BuildOK (substStepG B inMap extra acc nd) := by
  obtain ⟨h1, hwf, hmap⟩ := h
  have hr := ref_lt hmap h1
  -- a single appended node
  have single : ∀ (node : BooleanNode q), node.WellFormedAt acc.1.length →
      BuildOK (acc.1 ++ [node], acc.2 ++ [acc.1.length]) := by
    intro node hnode
    refine ⟨by simp, ?_, ?_⟩
    · intro p hp
      simp only [List.length_append, List.length_singleton] at hp
      by_cases hlt : p < acc.1.length
      · rw [List.getElem_append_left hlt]
        exact hwf p hlt
      · have hp' : p = acc.1.length := by omega
        subst hp'
        simpa using hnode
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      simp only [List.length_append, List.length_singleton]
      rcases hx with hx | hx
      · have := hmap x hx
        omega
      · omega
  cases nd with
  | const b => exact single _ trivial
  | input i => exact single _ (hin i _)
  | not c => exact single _ (hr c)
  | and l r => exact single _ ⟨hr l, hr r⟩
  | or l r => exact single _ ⟨hr l, hr r⟩
  | oracle args =>
      have hwires : ∀ x ∈ ((List.ofFn fun j => ref acc.2 (args j)) ++ extra), x < acc.1.length := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rw [List.mem_ofFn] at hx
          obtain ⟨j, rfl⟩ := hx
          exact hr _
        · exact hextra x hx
      have hlenB := copyNodesFrom_length acc.1.length ((List.ofFn fun j => ref acc.2 (args j)) ++ extra) 0 B.nodes
      show BuildOK (acc.1 ++ copyNodesFrom acc.1.length ((List.ofFn fun j => ref acc.2 (args j)) ++ extra) 0 B.nodes,
        acc.2 ++ [acc.1.length + B.output.val])
      refine ⟨by simp only [List.length_append]; omega, ?_, ?_⟩
      · intro p hp
        simp only [List.length_append] at hp
        by_cases hlt : p < acc.1.length
        · rw [List.getElem_append_left hlt]
          exact hwf p hlt
        · rw [List.getElem_append_right (by omega)]
          rw [copyNodesFrom_getElem]
          have := copyNode_wellFormed acc.1.length ((List.ofFn fun j => ref acc.2 (args j)) ++ extra)
            (0 + (p - acc.1.length)) (B.nodes[p - acc.1.length]'(by omega)) h1 hwires
          rwa [show acc.1.length + (0 + (p - acc.1.length)) = p by omega] at this
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        simp only [List.length_append]
        rcases hx with hx | hx
        · have := hmap x hx
          omega
        · have := B.output.isLt
          omega

theorem substBuildG_ok (start : List (BooleanNode q)) (inMap : Fin ℓ → BooleanNode q) (extra : List ℕ)
    (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) (hin : ∀ i p, (inMap i).WellFormedAt p)
    (hstart : BuildOK (start, [])) (hextra : ∀ x ∈ extra, x < start.length) :
    BuildOK (substBuildG start inMap extra C B) := by
  unfold substBuildG
  have hmono : ∀ (acc : List (BooleanNode q) × List ℕ) nd, acc.1.length ≤ (substStepG B inMap extra acc nd).1.length := by
    intro acc nd
    cases nd <;> simp [substStepG]
  have key : ∀ (nodes : List (OracleNode ℓ ℓ)) (acc : List (BooleanNode q) × List ℕ), BuildOK acc →
      start.length ≤ acc.1.length → BuildOK (nodes.foldl (substStepG B inMap extra) acc) := by
    intro nodes
    induction nodes with
    | nil => intro acc h _; simpa using h
    | cons nd rest ih =>
        intro acc h hlen
        simp only [List.foldl_cons]
        exact ih _ (substStepG_ok B inMap extra hin acc nd h (fun x hx => by have := hextra x hx; omega))
          (le_trans hlen (hmono acc nd))
  exact key C.nodes (start, []) hstart le_rfl

theorem inputMapD_wellFormed (i : Fin ℓ) (p : ℕ) : (inputMapD (q := q) i).WellFormedAt p := by
  unfold inputMapD
  split <;> trivial

theorem substBuild_ok (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) : BuildOK (substBuild C B) := by
  apply substBuildG_ok _ _ _ C B inputMapD_wellFormed
  · refine ⟨by simp, ?_, by simp⟩
    intro p hp
    simp only [List.length_singleton] at hp
    have : p = 0 := by omega
    subst this
    trivial
  · simp

theorem substNodes_length_pos (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) : 0 < (substNodes C B).length := by
  simp [substNodes]

/-- `D` before padding: the explicit circuit `¬C^{B(·,0)}` on `q` inputs. -/
def substCircuit (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) : BooleanCircuit q where
  nodes := substNodes C B
  output := ⟨(substBuild C B).1.length, by simp [substNodes]⟩
  wellFormed := by
    intro index
    obtain ⟨h1, hwf, hmap⟩ := substBuild_ok C B
    rw [List.get_eq_getElem]
    unfold substNodes
    by_cases hlt : index.val < (substBuild C B).1.length
    · rw [List.getElem_append_left hlt]
      exact hwf _ hlt
    · have hidx : index.val = (substBuild C B).1.length := by
        have := index.isLt
        simp only [substNodes, List.length_append, List.length_singleton] at this
        omega
      rw [List.getElem_append_right (by omega)]
      simp only [hidx, Nat.sub_self, List.getElem_cons_zero]
      exact ref_lt hmap h1 _

theorem substCircuit_size (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) :
    (substCircuit C B).size = (substBuild C B).1.length + 1 := by
  simp [substCircuit, BooleanCircuit.size, substNodes]

end NearCubicGates.Close.Outer

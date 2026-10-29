import Proof.Gates.Worker.Intervals

/-!
# The counter calls of a guess and useful witnesses — `eq:gadget-upper`, `eq:gadget-upper-complete`, `sec:gadget-machine`

Each term of a gadget makes at most one counter call (`callOf`, the call `intervalOf` reads). If every call's
witness is useful (radius at most `ω`), every term interval has radius at most `ω`, which is the hypothesis of
`upper_le` (eq:gadget-upper-complete). Every call is admitted and within the weight caps of thm:pair-uniform when the
guessed circuits are well formed and within the weight budget, and the radius and budget satisfy the stated bounds.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates NearCubicGates.FiniteAverages NearCubicGates.Gadget

theorem empty_wellFormed (n B : ℕ) : (NCircuit.empty n).WellFormed B := by
  refine ⟨rfl, by simp [NCircuit.empty], by simp [NCircuit.empty, NCircuit.topWeight], by simp [NCircuit.empty]⟩

@[simp] theorem empty_topWeight (n : ℕ) : (NCircuit.empty n).topWeight = 0 := rfl

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N))

/-- The counter call `intervalOf` makes on an operand list, if any. -/
noncomputable def callOf (ω : ℚ) (ops : List (Bool × Atom)) : Option Call :=
  match ops.map Prod.snd with
  | [.aux j] => some (G.singleCall ω j ∅)
  | [.sys u, .aux j] => some (G.singleCall ω j (G.sysSupport P x u))
  | [.aux j, .sys u] => some (G.singleCall ω j (G.sysSupport P x u))
  | [.aux i, .aux j] => if i = j then none else some (G.pairCall ω i j)
  | _ => none

theorem flip_radius (fl : Bool) (X : ℚ × ℚ) : ((if fl = true then (1 - X.1, X.2) else X) : ℚ × ℚ).2 = X.2 := by
  cases fl <;> rfl

/-- Useful witnesses give radius at most `ω` on every one- or two-operand term. -/
theorem intervalOf_radius {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (hω : 0 ≤ ω) (w : List Bool)
    (ops : List (Bool × Atom)) (hlen : ops.length = 1 ∨ ops.length = 2)
    (hw : ∀ c, G.callOf P x ω ops = some c → (ctr.value c w).2 ≤ ω) :
    (G.intervalOf P x ctr ω w ops).2 ≤ ω := by
  classical
  have hlen' : (ops.map Prod.snd).length = 1 ∨ (ops.map Prod.snd).length = 2 := by simpa using hlen
  unfold intervalOf
  unfold callOf at hw
  dsimp only at hw ⊢
  generalize ops.foldl (fun f o => xor f o.1) false = fl
  generalize ops.map Prod.snd = as at hw hlen' ⊢
  rcases as with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, rest⟩⟩⟩
  · simp at hlen'
  · cases a₁ with
    | sys u => dsimp only; split_ifs <;> exact hω
    | aux j => dsimp only at hw ⊢; split_ifs <;> exact hw _ rfl
  · cases a₁ with
    | sys u =>
      cases a₂ with
      | sys v => dsimp only; split_ifs <;> exact hω
      | aux j => dsimp only at hw ⊢; split_ifs <;> exact hw _ rfl
    | aux i =>
      cases a₂ with
      | sys u => dsimp only at hw ⊢; split_ifs <;> exact hw _ rfl
      | aux j =>
        dsimp only at hw ⊢
        by_cases hij : i = j
        · rw [if_pos hij]; split_ifs <;> exact hω
        · rw [if_neg hij]; rw [if_neg hij] at hw; split_ifs <;> exact hw _ rfl
  · simp at hlen'

theorem operands_length (a : ℕ) (t : Fin 10) : (G.operands P x a t).length = 1 ∨ (G.operands P x a t).length = 2 := by
  unfold operands
  fin_cases t <;> simp

/-- The atoms of every term of a gadget `a < M` name a proof coordinate or that gadget's helper. -/
theorem operands_aux_lt (a : ℕ) (ha : a < gadgets s g N) (t : Fin 10) (o : Bool × Atom) (ho : o ∈ G.operands P x a t)
    (j : ℕ) (hj : o.2 = .aux j) : j < G.auxCount P x := by
  have hlit : ∀ i : Fin 3, ∀ j, (G.literalParts P x (G.clause P x a i)).2 = .aux j →
      j < (pcpp s P g x G.oracle).proofBits := by
    intro i j hj
    have key : ∀ v : Fin (G.Arity P x), G.atomOf P x v = .aux j → j < (pcpp s P g x G.oracle).proofBits := by
      intro v hv
      unfold atomOf at hv
      split_ifs at hv with hlt
      cases hv
      have := v.isLt
      simp only [Arity] at this
      omega
    cases hc : G.clause P x a i with
    | positive v => rw [hc] at hj; exact key v hj
    | negative v => rw [hc] at hj; exact key v hj
  have hhelp : ∀ j, (G.helper P x a) = .aux j → j < G.auxCount P x := by
    intro j hj
    unfold helper at hj
    cases hj
    unfold auxCount
    omega
  have hform : (∃ i : Fin 3, o = G.literalParts P x (G.clause P x a i)) ∨ o = (false, G.helper P x a) := by
    unfold operands at ho
    fin_cases t
    · simp at ho; exact Or.inr ho
    · simp at ho; exact Or.inl ⟨0, ho⟩
    · simp at ho; exact Or.inl ⟨1, ho⟩
    · simp at ho; exact Or.inl ⟨2, ho⟩
    · simp at ho; rcases ho with h | h; exacts [Or.inl ⟨0, h⟩, Or.inl ⟨1, h⟩]
    · simp at ho; rcases ho with h | h; exacts [Or.inl ⟨0, h⟩, Or.inl ⟨2, h⟩]
    · simp at ho; rcases ho with h | h; exacts [Or.inl ⟨1, h⟩, Or.inl ⟨2, h⟩]
    · simp at ho; rcases ho with h | h; exacts [Or.inl ⟨0, h⟩, Or.inr h]
    · simp at ho; rcases ho with h | h; exacts [Or.inl ⟨1, h⟩, Or.inr h]
    · simp at ho; rcases ho with h | h; exacts [Or.inl ⟨2, h⟩, Or.inr h]
  rcases hform with ⟨i, rfl⟩ | rfl
  · have := hlit i j hj
    unfold auxCount
    omega
  · exact hhelp j hj

/-- Every call has arity `q` and radius `ω`. -/
theorem callOf_n_radius (ω : ℚ) (ops : List (Bool × Atom)) (c : Call) (hc : G.callOf P x ω ops = some c) :
    c.n = width s g N ∧ c.radius = ω := by
  classical
  unfold callOf at hc
  generalize ops.map Prod.snd = as at hc
  rcases as with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, rest⟩⟩⟩
  · simp at hc
  · cases a₁ <;> simp at hc
    subst hc; unfold singleCall; split_ifs <;> exact ⟨rfl, rfl⟩
  · cases a₁ <;> cases a₂ <;> simp at hc
    all_goals first
      | (subst hc; unfold singleCall; split_ifs <;> exact ⟨rfl, rfl⟩)
      | (obtain ⟨-, rfl⟩ := hc; exact ⟨rfl, rfl⟩)
  · cases a₁ <;> cases a₂ <;> simp at hc

end Guess

end NearCubicGates.Close.Worker

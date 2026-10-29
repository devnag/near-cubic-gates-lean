import SourceAdapters.Routing.TermsMachineTokenProgramSpec

/-! Uniform numerical capacities for every postfix stack and emitted field. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Expression

open NearCubicWires
open ShortPCP.Machines.FL Joins ACSP

/-- E bounds references, D bounds stack depth, and B bounds printed numbers. -/
structure Bounds (G : Glob) (l : Layout) (w E D B : ℕ) : Prop extends DispatchBounds G l w where
  gate_width : E ≤ 2^w
  gate_B : E ≤ B
  bank_B : (globalBank l).length+1 ≤ B
  tag_B : 3 ≤ B
  bits : Small G B
  stack_power : 2^(w*(D+1)) ≤ G.cap
  stack_depth : D+1 ≤ G.cap

def ConstantBound (B : ℕ) : TermTok → Prop
  | .const c => c ≤ B
  | _ => True

theorem Small.mono {G : Glob} {a b : ℕ} (h : Small G b) (hab : a ≤ b) : Small G a := by
  have hlog : natBitLength a ≤ natBitLength b := Nat.add_le_add_right (Nat.log_mono_right hab) 1
  exact (Nat.add_le_add_right hlog 2).trans h

theorem getD_le (st : List ℕ) (B k : ℕ) (h : ∀ a ∈ st, a ≤ B) : st.getD k 0 ≤ B := by
  by_cases hk : k < st.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

theorem readIndex_le (l : Layout) (v : Vars) : readIndex l v ≤ (globalBank l).length+1 := by
  cases v with
  | none => simp [readIndex]
  | some b => have := List.idxOf_le_length (l := globalBank l) (a := b); simp only [readIndex]; omega

variable {G : Glob} {l : Layout} {w E D B : ℕ}

theorem Bounds.gateFits (h : Bounds G l w E D B) (st : List ℕ) (t : TermTok)
    (hs : ∀ a ∈ st, a < E) (ht : ConstantBound B t) : GateFits G (emittedGate l st t) := by
  have h0 := h.bits.mono (Nat.zero_le B)
  have h1 := h.bits.mono (show 1 ≤ B by have := h.tag_B; omega)
  have h2 := h.bits.mono (show 2 ≤ B by have := h.tag_B; omega)
  have h3 := h.bits.mono h.tag_B
  have hg (k : ℕ) := h.bits.mono (getD_le st B k (fun a ha => (hs a ha).le.trans h.gate_B))
  cases t with
  | const c => exact ⟨h1, h.bits.mono ht, h0⟩
  | read v => exact ⟨h0, h.bits.mono ((readIndex_le l v).trans h.bank_B), h0⟩
  | add => exact ⟨h2, hg 1, hg 0⟩
  | mul => exact ⟨h3, hg 1, hg 0⟩
  | square => exact ⟨h3, hg 0, hg 0⟩

theorem Bounds.push_cap (h : Bounds G l w E D B) (n : ℕ) (st : List ℕ) (k : ℕ)
    (hn : n < E) (hs : ∀ a ∈ st, a < E) (hd : st.length ≤ D) :
    packW w (n :: st.drop k) ≤ G.cap := by
  have hp := packW_lt w (n :: st.drop k) (by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hn.trans_le h.gate_width
    · exact (hs a (List.mem_of_mem_drop ha)).trans_le h.gate_width)
  have hlen : (n :: st.drop k).length ≤ D+1 := by simp; omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_left w hlen)
  exact hp.le.trans (hpow.trans h.stack_power)

theorem constants_expression {F : Type} (mk : F → ℕ) (e : Expr F) (B : ℕ)
    (h : ∀ c, mk c ≤ B) : ∀ t ∈ exprToks mk e, ConstantBound B t := by
  induction e with
  | const c => simpa [exprToks, ConstantBound] using h c
  | read v => simp [exprToks, ConstantBound]
  | add a b ha hb =>
      intro t ht
      simp only [exprToks, List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | ht) | rfl
      · exact ha t ht
      · exact hb t ht
      · trivial
  | mul a b ha hb =>
      intro t ht
      simp only [exprToks, List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | ht) | rfl
      · exact ha t ht
      · exact hb t ht
      · trivial
  | square a ha =>
      intro t ht
      simp only [exprToks, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact ha t ht
      · trivial

end NearCubicGates.Adapters.Routing.TermsMachine.Expression

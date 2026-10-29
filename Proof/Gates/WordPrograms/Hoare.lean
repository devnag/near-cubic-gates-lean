import Proof.Gates.WordPrograms.RecLoopSum

/-! # Specs as postconditions: `Runs` and frame lemmas

The paper's machine model (`sec:prelim`, "Machine model"): every algorithm of the counter is a multitape
machine; arithmetic and table
work cost "fixed polynomial factors". The tabulator machines (PolyTab, CellTables) are long compositions of `WMX` programs, so
their specs are stated as postconditions: **`Runs cap P σ c Q`** says that the ONE compiled machine of `P` goes from
the encoding of `σ` to the encoding of a state satisfying `Q` within `c` steps (`WXExec`). The combinators
`Runs.seq`, `Runs.ifr`, `Runs.ifs`, `Runs.mono` compose such specs; `Runs.exec` recovers the `WXExec` fact (and so
the machine's `Step` and `run`, by `WXExec.step`/`WXExec.run`).

Frames are `SameExcept σ τ S Rg` (every stream outside `S` and every register outside `Rg` unchanged, cell
unchanged); `SameExcept.numOn`, `SameExcept.st`, `SameExcept.sh`, `SameExcept.val` transport facts through a frame,
`SameExcept.weaken` enlarges it, `SameExcept.comp` composes two frames. -/

set_option autoImplicit false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

/-! ## Runs -/

/-- `P` runs from `σ` within `c` steps to a state satisfying `Q`. -/
def Runs (cap : ℕ) (P : WMX ns nr) (σ : WState ns nr) (c : ℕ) (Q : WState ns nr → Prop) : Prop :=
  ∃ τ, WXExec cap P σ τ c ∧ Q τ

section Runs
variable {cap : ℕ}

theorem Runs.of {P : WMX ns nr} {σ τ : WState ns nr} {c : ℕ} {Q : WState ns nr → Prop}
    (h : WXExec cap P σ τ c) (hq : Q τ) : Runs cap P σ c Q := ⟨τ, h, hq⟩

theorem Runs.mono {P : WMX ns nr} {σ : WState ns nr} {c c' : ℕ} {Q Q' : WState ns nr → Prop}
    (h : Runs cap P σ c Q) (hc : c ≤ c') (hq : ∀ τ, Q τ → Q' τ) : Runs cap P σ c' Q' := by
  obtain ⟨τ, h1, h2⟩ := h
  exact ⟨τ, WXExec.mono h1 hc, hq τ h2⟩

theorem Runs.post {P : WMX ns nr} {σ : WState ns nr} {c : ℕ} {Q Q' : WState ns nr → Prop}
    (h : Runs cap P σ c Q) (hq : ∀ τ, Q τ → Q' τ) : Runs cap P σ c Q' := h.mono le_rfl hq

theorem Runs.cost {P : WMX ns nr} {σ : WState ns nr} {c c' : ℕ} {Q : WState ns nr → Prop}
    (h : Runs cap P σ c Q) (hc : c ≤ c') : Runs cap P σ c' Q := h.mono hc (fun _ h => h)

theorem Runs.seq {P P' : WMX ns nr} {σ : WState ns nr} {c1 c2 : ℕ} {Q1 Q2 : WState ns nr → Prop}
    (h1 : Runs cap P σ c1 Q1) (h2 : ∀ τ, Q1 τ → Runs cap P' τ c2 Q2) : Runs cap (.seq P P') σ (c1 + 1 + c2) Q2 := by
  obtain ⟨τ, e1, q1⟩ := h1
  obtain ⟨ρ, e2, q2⟩ := h2 τ q1
  exact ⟨ρ, WXExec.seq e1 e2, q2⟩

/-- Sequencing after a deterministic first step. -/
theorem Runs.seqE {P P' : WMX ns nr} {σ τ : WState ns nr} {c1 c2 : ℕ} {Q : WState ns nr → Prop}
    (h1 : WXExec cap P σ τ c1) (h2 : Runs cap P' τ c2 Q) : Runs cap (.seq P P') σ (c1 + 1 + c2) Q := by
  obtain ⟨ρ, e2, q2⟩ := h2
  exact ⟨ρ, WXExec.seq h1 e2, q2⟩

theorem Runs.seq' {P P' : WMX ns nr} {σ : WState ns nr} {c1 c2 c : ℕ} {Q1 Q2 : WState ns nr → Prop}
    (h1 : Runs cap P σ c1 Q1) (h2 : ∀ τ, Q1 τ → Runs cap P' τ c2 Q2) (hc : c1 + 1 + c2 ≤ c) :
    Runs cap (.seq P P') σ c Q2 := (Runs.seq h1 h2).cost hc

theorem Runs.ifrT {r : Fin nr} {P P' : WMX ns nr} {σ : WState ns nr} {c : ℕ} {Q : WState ns nr → Prop}
    (hv : σ.val r ≠ 0) (h : Runs cap P σ c Q) : Runs cap (.ifr r P P') σ (c + 1) Q := by
  obtain ⟨τ, e, q⟩ := h
  exact ⟨τ, WXExec.ifrT hv e, q⟩

theorem Runs.ifrF {r : Fin nr} {P P' : WMX ns nr} {σ : WState ns nr} {c : ℕ} {Q : WState ns nr → Prop}
    (hv : σ.val r = 0) (h : Runs cap P' σ c Q) : Runs cap (.ifr r P P') σ (c + 1) Q := by
  obtain ⟨τ, e, q⟩ := h
  exact ⟨τ, WXExec.ifrF hv e, q⟩

theorem Runs.ifsT {i : Fin (ns + 1)} {P P' : WMX ns nr} {σ : WState ns nr} {c : ℕ} {Q : WState ns nr → Prop}
    (hv : wbit σ i = true) (h : Runs cap P σ c Q) : Runs cap (.ifs i P P') σ (c + 1) Q := by
  obtain ⟨τ, e, q⟩ := h
  exact ⟨τ, WXExec.ifsT hv e, q⟩

theorem Runs.ifsF {i : Fin (ns + 1)} {P P' : WMX ns nr} {σ : WState ns nr} {c : ℕ} {Q : WState ns nr → Prop}
    (hv : wbit σ i = false) (h : Runs cap P' σ c Q) : Runs cap (.ifs i P P') σ (c + 1) Q := by
  obtain ⟨τ, e, q⟩ := h
  exact ⟨τ, WXExec.ifsF hv e, q⟩

/-- A two-way register branch with one cost for both arms. -/
theorem Runs.ifr {r : Fin nr} {P P' : WMX ns nr} {σ : WState ns nr} {c : ℕ} {Q : WState ns nr → Prop}
    (hT : σ.val r ≠ 0 → Runs cap P σ c Q) (hF : σ.val r = 0 → Runs cap P' σ c Q) :
    Runs cap (.ifr r P P') σ (c + 1) Q := by
  by_cases h : σ.val r = 0
  · exact Runs.ifrF h (hF h)
  · exact Runs.ifrT h (hT h)

theorem Runs.ifs {i : Fin (ns + 1)} {P P' : WMX ns nr} {σ : WState ns nr} {c : ℕ} {Q : WState ns nr → Prop}
    (hT : wbit σ i = true → Runs cap P σ c Q) (hF : wbit σ i = false → Runs cap P' σ c Q) :
    Runs cap (.ifs i P P') σ (c + 1) Q := by
  cases h : wbit σ i
  · exact Runs.ifsF h (hF h)
  · exact Runs.ifsT h (hT h)

/-- A register loop, by induction on a measure that the body decreases. -/
theorem Runs.whr {r : Fin nr} {P : WMX ns nr} (Inv : ℕ → WState ns nr → Prop) (c : ℕ) (Q : WState ns nr → Prop)
    (hexit : ∀ σ, Inv 0 σ → σ.val r = 0 ∧ Q σ)
    (hbody : ∀ k σ, Inv (k + 1) σ → σ.val r ≠ 0 ∧ Runs cap P σ c (Inv k)) :
    ∀ k σ, Inv k σ → Runs cap (.whr r P) σ (k * (c + 2) + 1) Q := by
  intro k
  induction k with
  | zero =>
    intro σ h
    obtain ⟨h0, hq⟩ := hexit σ h
    exact ⟨σ, WXExec.mono (WXExec.whrF h0) (by omega), hq⟩
  | succ k ih =>
    intro σ h
    obtain ⟨hv, τ, e1, q1⟩ := hbody k σ h
    obtain ⟨ρ, e2, q2⟩ := ih τ q1
    exact ⟨ρ, WXExec.mono (WXExec.whrT hv e1 e2) (by ring_nf; omega), q2⟩

/-- A stream loop, by induction on a measure that the body decreases. -/
theorem Runs.whs {i : Fin (ns + 1)} {P : WMX ns nr} (Inv : ℕ → WState ns nr → Prop) (c : ℕ)
    (Q : WState ns nr → Prop) (hexit : ∀ σ, Inv 0 σ → wbit σ i = false ∧ Q σ)
    (hbody : ∀ k σ, Inv (k + 1) σ → wbit σ i = true ∧ Runs cap P σ c (Inv k)) :
    ∀ k σ, Inv k σ → Runs cap (.whs i P) σ (k * (c + 2) + 1) Q := by
  intro k
  induction k with
  | zero =>
    intro σ h
    obtain ⟨h0, hq⟩ := hexit σ h
    exact ⟨σ, WXExec.mono (WXExec.whsF h0) (by omega), hq⟩
  | succ k ih =>
    intro σ h
    obtain ⟨hv, τ, e1, q1⟩ := hbody k σ h
    obtain ⟨ρ, e2, q2⟩ := ih τ q1
    exact ⟨ρ, WXExec.mono (WXExec.whsT hv e1 e2) (by ring_nf; omega), q2⟩

/-- A counted loop: `K` holds `n` at entry; pass `k` runs the body with `K = n − k − 1`. -/
theorem Runs.count {K : Fin nr} {body : WMX ns nr} (c n : ℕ) (Inv : ℕ → WState ns nr → Prop) (hcap : n ≤ cap)
    (hstep : ∀ k < n, ∀ σ, Inv k σ → σ.val K = n - k →
      Runs cap body (σ.setv K (n - k - 1)) c (fun τ => Inv (k + 1) τ ∧ τ.val K = n - k - 1)) :
    ∀ σ, Inv 0 σ → σ.val K = n →
      Runs cap (.whr K (.seq (WMX.dec K) body)) σ (n * (c + 4) + 1) (fun τ => Inv n τ ∧ τ.val K = 0) := by
  have key : ∀ m j σ, j + m = n → Inv j σ → σ.val K = n - j →
      Runs cap (.whr K (.seq (WMX.dec K) body)) σ (m * (c + 4) + 1) (fun τ => Inv n τ ∧ τ.val K = 0) := by
    intro m
    induction m with
    | zero =>
      intro j σ hj hI hK
      rw [Nat.add_zero] at hj; subst hj
      exact ⟨σ, WXExec.mono (WXExec.whrF (by omega)) (by omega), hI, by omega⟩
    | succ m ih =>
      intro j σ hj hI hK
      have hd := WXExec.dec cap K σ (by omega)
      obtain ⟨τ, e1, q1, hK1⟩ := hstep j (by omega) σ hI hK
      have e : σ.setv K (σ.val K - 1) = σ.setv K (n - j - 1) := by rw [hK]
      rw [e] at hd
      obtain ⟨ρ, e2, q2⟩ := ih (j + 1) τ (by omega) q1 (by omega)
      exact ⟨ρ, WXExec.mono (WXExec.whrT (by omega) (WXExec.seq hd e1) e2) (by ring_nf; omega), q2⟩
  intro σ hI hK
  exact key n 0 σ (by omega) hI (by omega)

def repK (K K2 : Fin nr) (body : WMX ns nr) : WMX ns nr :=
  .seq (.whr K (.seq (WMX.dec K) (.seq (WMX.inc K2) body))) (.wm (WM.move K2 K))

/-- **The repeat loop.** `Inv` must not depend on the two counters; the body keeps them. -/
theorem Runs.rep {K K2 : Fin nr} {body : WMX ns nr} (hKK : K ≠ K2) (c n : ℕ) (Inv : ℕ → WState ns nr → Prop)
    (hcap : 2 * n ≤ cap) (hInvK : ∀ k σ v, Inv k σ → Inv k (σ.setv K v))
    (hInvK2 : ∀ k σ v, Inv k σ → Inv k (σ.setv K2 v))
    (hstep : ∀ k < n, ∀ σ, Inv k σ →
      Runs cap body σ c (fun τ => Inv (k + 1) τ ∧ τ.val K = σ.val K ∧ τ.val K2 = σ.val K2)) :
    ∀ σ, Inv 0 σ → σ.val K = n → σ.val K2 = 0 →
      Runs cap (repK K K2 body) σ (n * (c + 8) + 7 * n + 3) (fun τ => Inv n τ ∧ τ.val K = n ∧ τ.val K2 = 0) := by
  intro σ hI hK hK2
  let Inv' : ℕ → WState ns nr → Prop := fun k τ => Inv k τ ∧ τ.val K2 = k
  have hl := Runs.count (cap := cap) (K := K) (body := .seq (WMX.inc K2) body) (c + 4) n Inv' (by omega)
    (by
      intro k hk τ hτ hKτ
      have hi := WXExec.inc cap K2 (τ.setv K (n - k - 1)) (by simp [Function.update_of_ne (Ne.symm hKK), hτ.2]; omega)
      obtain ⟨ρ, e, q, hKρ, hK2ρ⟩ := hstep k hk _ (hInvK2 k _ _ (hInvK k τ _ hτ.1))
      refine ⟨ρ, WXExec.mono (WXExec.seq hi e) (by omega), ⟨q, ?_⟩, ?_⟩
      · rw [hK2ρ]; simp [Function.update_of_ne (Ne.symm hKK), hτ.2]
      · rw [hKρ]; simp [Function.update_of_ne hKK]) σ ⟨hI, hK2⟩ hK
  obtain ⟨τ, e1, ⟨hIτ, hK2τ⟩, hKτ⟩ := hl
  have hm := WXExec.wm (wmove_spec (cap := cap) K2 K (Ne.symm hKK) n τ hK2τ (by omega) (by omega))
  refine ⟨_, WXExec.mono (WXExec.seq e1 hm) (by ring_nf; omega), ?_, ?_, ?_⟩
  · exact hInvK n _ _ (hInvK2 n _ _ hIτ)
  · simp [hKτ, hK2τ]
  · simp [Function.update_of_ne (Ne.symm hKK)]

/-- **The repeat loop with exact states.** `st k` is the state after `k` passes (its counters as at the start); the
body takes `st k` to `st (k + 1)` whatever the two counters hold. -/
theorem Runs.repE {K K2 : Fin nr} {body : WMX ns nr} (hKK : K ≠ K2) (c n : ℕ) (st : ℕ → WState ns nr)
    (hcap : 2 * n ≤ cap) (hK : ∀ k, (st k).val K = (st 0).val K) (hK2 : ∀ k, (st k).val K2 = (st 0).val K2)
    (hstep : ∀ k < n, ∀ v1 v2 : ℕ,
      WXExec cap body (((st k).setv K v1).setv K2 v2) (((st (k + 1)).setv K v1).setv K2 v2) c)
    (h0K : (st 0).val K = n) (h0K2 : (st 0).val K2 = 0) :
    WXExec cap (repK K K2 body) (st 0) (st n) (n * (c + 8) + 7 * n + 3) := by
  let Inv : ℕ → WState ns nr → Prop := fun k τ => ∃ v1 v2 : ℕ, τ = ((st k).setv K v1).setv K2 v2
  have hsv : ∀ (τ : WState ns nr) (r : Fin nr), τ.setv r (τ.val r) = τ := fun τ r => wsetv_same τ r
  obtain ⟨τ, e, ⟨v1, v2, hτ⟩, hKτ, hK2τ⟩ := Runs.rep (cap := cap) (body := body) hKK c n Inv hcap
    (by
      rintro k τ v ⟨v1, v2, rfl⟩
      refine ⟨v, v2, ?_⟩
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all)
    (by
      rintro k τ v ⟨v1, v2, rfl⟩
      refine ⟨v1, v, ?_⟩
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all)
    (by
      rintro k hk τ ⟨v1, v2, rfl⟩
      refine ⟨_, hstep k hk v1 v2, ⟨v1, v2, rfl⟩, ?_, ?_⟩
      · simp [Function.update_of_ne hKK]
      · simp)
    (st 0) ⟨(st 0).val K, (st 0).val K2, by rw [hsv, hsv]⟩ h0K h0K2
  have e2 : τ = st n := by
    rw [hτ]
    have h1 : v1 = (st n).val K := by
      have := hKτ; rw [hτ] at this; simp [Function.update_of_ne hKK] at this; rw [hK n, h0K]; exact this
    have h2 : v2 = (st n).val K2 := by
      have := hK2τ; rw [hτ] at this; simp at this; rw [hK2 n, h0K2]; exact this
    rw [h1, h2, hsv, hsv]
  rw [e2] at e
  exact e

end Runs

/-! ## Frames -/

section Frames
variable {σ τ ρ : WState ns nr} {S S' : List (Fin (ns + 1))} {Rg Rg' : List (Fin nr)}

theorem SameExcept.st (h : SameExcept σ τ S Rg) {x : Fin (ns + 1)} (hx : x ∉ S) : τ.st x = σ.st x := (h.1 x hx).1

theorem SameExcept.sh (h : SameExcept σ τ S Rg) {x : Fin (ns + 1)} (hx : x ∉ S) : τ.sh x = σ.sh x := (h.1 x hx).2

theorem SameExcept.val (h : SameExcept σ τ S Rg) {r : Fin nr} (hr : r ∉ Rg) : τ.val r = σ.val r := h.2.1 r hr

theorem SameExcept.cell (h : SameExcept σ τ S Rg) : τ.cell = σ.cell := h.2.2

theorem SameExcept.numOn (h : SameExcept σ τ S Rg) {X : Fin (ns + 1)} (hX : X ∉ S) {W v : ℕ}
    (hn : NumOn σ X W v) : NumOn τ X W v := ⟨by rw [h.st hX, hn.1], by rw [h.sh hX, hn.2]⟩

theorem SameExcept.weaken (h : SameExcept σ τ S Rg) (hS : ∀ x ∈ S, x ∈ S') (hR : ∀ r ∈ Rg, r ∈ Rg') :
    SameExcept σ τ S' Rg' :=
  ⟨fun x hx => h.1 x (fun m => hx (hS x m)), fun r hr => h.2.1 r (fun m => hr (hR r m)), h.2.2⟩

theorem SameExcept.comp (h1 : SameExcept σ τ S Rg) (h2 : SameExcept τ ρ S Rg) : SameExcept σ ρ S Rg :=
  SameExcept.trans h1 h2

/-- Composition of two frames into their union. -/
theorem SameExcept.comp' (h1 : SameExcept σ τ S Rg) (h2 : SameExcept τ ρ S' Rg') :
    SameExcept σ ρ (S ++ S') (Rg ++ Rg') :=
  SameExcept.trans (h1.weaken (fun _ hx => List.mem_append_left _ hx) (fun _ hr => List.mem_append_left _ hr))
    (h2.weaken (fun _ hx => List.mem_append_right _ hx) (fun _ hr => List.mem_append_right _ hr))

theorem sameExcept_sets (σ : WState ns nr) {X : Fin (ns + 1)} (hX : X ∈ S) (l : List Bool) :
    SameExcept σ (σ.sets X l) S Rg :=
  ⟨fun y hy => by
    have hne : y ≠ X := fun e => hy (e ▸ hX)
    simp [Function.update_of_ne hne], fun _ _ => rfl, rfl⟩

theorem sameExcept_seth (σ : WState ns nr) {X : Fin (ns + 1)} (hX : X ∈ S) (n : ℕ) :
    SameExcept σ (σ.seth X n) S Rg :=
  ⟨fun y hy => by
    have hne : y ≠ X := fun e => hy (e ▸ hX)
    simp [Function.update_of_ne hne], fun _ _ => rfl, rfl⟩

theorem sameExcept_setv (σ : WState ns nr) {r : Fin nr} (hr : r ∈ Rg) (v : ℕ) : SameExcept σ (σ.setv r v) S Rg :=
  ⟨fun y _ => by simp, fun q hq => by
    have hne : q ≠ r := fun e => hq (e ▸ hr)
    simp [Function.update_of_ne hne], rfl⟩

/-- A register set back to its old value is no change. -/
theorem sameExcept_setv_same (σ : WState ns nr) (r : Fin nr) : SameExcept σ (σ.setv r (σ.val r)) S Rg := by
  rw [wsetv_same σ r]; exact SameExcept.refl σ S Rg

end Frames

end NearCubicGates.Close.WordPrograms

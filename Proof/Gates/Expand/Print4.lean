import Proof.Gates.Expand.Print3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

section Steps
variable {PB : Fin 14 ↪ Fin (ns + 1)} {PG : Fin 5 ↪ Fin nr} {PR : Fin 4 ↪ Fin nr} {O : Fin (ns + 1)} {OP : Fin nr}
  {cap Wb : ℕ} {σ0 : WState ns nr}

theorem RS.emit {τ τ' : WState ns nr} {w : Fin 14 → ℕ} {u u' : List Bool} {f g : ℕ}
    (h : RS PB PG O OP Wb σ0 τ w u f g) (hl : PLay PB PG PR O OP) (he : Emitted O OP τ τ' u') :
    RS PB PG O OP Wb σ0 τ' w (u ++ u') f g := by
  obtain ⟨hw, hO, hOh, hOP, hf, hg, s⟩ := h
  obtain ⟨fr, hO', hOh', hOP'⟩ := he
  refine ⟨hw.frame' fr (fun i => by simp [hl.bo i]), by rw [hO', hO, List.append_assoc],
    by rw [hOh', hOh]; simp; ring, by rw [hOP', hOP]; simp; ring, by rw [fr.val (by simp [hl.go 0]), hf],
    by rw [fr.val (by simp [hl.go 4]), hg], s.trans (se_sub fr (by simp [bl]) (by simp))⟩

theorem rDecF (hl : PLay PB PG PR O OP) {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ}
    (h : RS PB PG O OP Wb σ0 τ w u 1 g) (hc : 1 ≤ cap) :
    Runs cap (WMX.dec (PG 0)) τ 1 (fun τ' => RS PB PG O OP Wb σ0 τ' w u 0 g) :=
  Runs.of (WXExec.dec cap (PG 0) τ (by rw [h.2.2.2.2.1]; exact hc))
    (h.regs hl (sameExcept_setv τ (by simp) _) (by simp [h.2.2.2.2.1])
      (by simp [Function.update_of_ne (pgN (show (4 : Fin 5) ≠ 0 by decide)), h.2.2.2.2.2.1]))

theorem rIncG (hl : PLay PB PG PR O OP) {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {f g : ℕ}
    (h : RS PB PG O OP Wb σ0 τ w u f g) (hc : g < cap) :
    Runs cap (WMX.inc (PG 4)) τ 3 (fun τ' => RS PB PG O OP Wb σ0 τ' w u f (g + 1)) :=
  Runs.of (WXExec.inc cap (PG 4) τ (by rw [h.2.2.2.2.2.1]; exact hc))
    (h.regs hl (sameExcept_setv τ (by simp) _)
      (by simp [Function.update_of_ne (pgN (show (0 : Fin 5) ≠ 4 by decide)), h.2.2.2.2.1])
      (by simp [h.2.2.2.2.2.1]))

theorem rDecG (hl : PLay PB PG PR O OP) {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {f g : ℕ}
    (h : RS PB PG O OP Wb σ0 τ w u f g) (hc : g ≤ cap) :
    Runs cap (WMX.dec (PG 4)) τ 1 (fun τ' => RS PB PG O OP Wb σ0 τ' w u f (g - 1)) :=
  Runs.of (WXExec.dec cap (PG 4) τ (by rw [h.2.2.2.2.2.1]; exact hc))
    (h.regs hl (sameExcept_setv τ (by simp) _)
      (by simp [Function.update_of_ne (pgN (show (0 : Fin 5) ≠ 4 by decide)), h.2.2.2.2.1])
      (by simp [h.2.2.2.2.2.1]))

variable (z : Regs0 PG PR σ0) (hl : PLay PB PG PR O OP)
include z hl

theorem rCopy {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ} (a b : Fin 14) (hab : a ≠ b)
    (ha : PB a ∈ bl PB O) (h : RS PB PG O OP Wb σ0 τ w u 0 g) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.copy (PB a) (PB b) (PG 0) (PG 1)) τ (41 * Wb + 3)
      (fun τ' => RS PB PG O OP Wb σ0 τ' (Function.update w a (w b)) u 0 g) :=
  (mCopy cap Wb a b hab (pgN (by decide)) h.1 h.2.2.2.2.1 (h.r0 hl z).1 hcap).post
    (fun _ ⟨hw, fr⟩ => h.op hl a ha hw fr)

theorem rAnd {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ} (a b : Fin 14) (hab : a ≠ b)
    (ha : PB a ∈ bl PB O) (h : RS PB PG O OP Wb σ0 τ w u 0 g) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (andX (PB a) (PB b) (PG 0) (PG 1)) τ (41 * Wb + 3)
      (fun τ' => RS PB PG O OP Wb σ0 τ' (Function.update w a (w a &&& w b)) u 0 g) :=
  (mAnd cap Wb a b hab (pgN (by decide)) h.1 h.2.2.2.2.1 (h.r0 hl z).1 hcap).post
    (fun _ ⟨hw, fr⟩ => h.op hl a ha hw fr)

theorem rSub {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ} (a b : Fin 14) (hab : a ≠ b)
    (ha : PB a ∈ bl PB O) (h : RS PB PG O OP Wb σ0 τ w u 0 g) (hba : w b ≤ w a) (hlt : w a < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.sub (PB a) (PB b) (PG 0) (PG 1)) τ (41 * Wb + 9)
      (fun τ' => RS PB PG O OP Wb σ0 τ' (Function.update w a (w a - w b)) u 0 g) :=
  (mSub cap Wb a b hab (pgN (by decide)) h.1 h.2.2.2.2.1 (h.r0 hl z).1 hba hlt hcap).post
    (fun _ ⟨hw, fr⟩ => h.op hl a ha hw fr)

theorem rInc {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ} (a b : Fin 14) (hab : a ≠ b)
    (ha : PB a ∈ bl PB O) (h : RS PB PG O OP Wb σ0 τ w u 0 g) (hlt : w a + 1 < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.inc (PB a) (PB b) (PG 0) (PG 1)) τ (41 * Wb + 7)
      (fun τ' => RS PB PG O OP Wb σ0 τ' (Function.update w a (w a + 1)) u 0 g) :=
  (mInc cap Wb a b hab (pgN (by decide)) h.1 h.2.2.2.2.1 (h.r0 hl z).1 hlt hcap).post
    (fun _ ⟨hw, fr⟩ => h.op hl a ha hw fr)

theorem rZero {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ} (a b : Fin 14) (hab : a ≠ b)
    (ha : PB a ∈ bl PB O) (h : RS PB PG O OP Wb σ0 τ w u 0 g) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.zero (PB a) (PB b) (PG 0) (PG 1)) τ (41 * Wb + 3)
      (fun τ' => RS PB PG O OP Wb σ0 τ' (Function.update w a 0) u 0 g) :=
  (mZero cap Wb a b hab (pgN (by decide)) h.1 h.2.2.2.2.1 (h.r0 hl z).1 hcap).post
    (fun _ ⟨hw, fr⟩ => h.op hl a ha hw fr)

theorem rHalf {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {f g : ℕ} (a : Fin 14)
    (ha : PB a ∈ bl PB O) (h : RS PB PG O OP Wb σ0 τ w u f g) (hlt : w a < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.half (PB a) (PG 1)) τ (34 * Wb + 3)
      (fun τ' => RS PB PG O OP Wb σ0 τ' (Function.update w a (w a / 2)) u f g) :=
  ⟨_, BinW.half_spec cap Wb τ (w a) (h.1 a) (h.r0 hl z).1 hlt (by omega),
    h.op hl a ha (h.1.upd a (sameExcept_sets (S := [PB a]) (Rg := []) τ (by simp) _) _
      (BinW.numOn_sets_self τ (PB a) Wb _ (h.1 a).2)) (sameExcept_sets (S := [PB a]) (Rg := []) τ (by simp) _)⟩

theorem rLt {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ} (a b : Fin 14) (hab : a ≠ b)
    (h : RS PB PG O OP Wb σ0 τ w u 0 g) (ha : w a < 2 ^ Wb) (hb : w b < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.lt (PB a) (PB b) (PG 0) (PG 1)) τ (41 * Wb + 3)
      (fun τ' => RS PB PG O OP Wb σ0 τ' w u (decide (w a < w b)).toNat g) :=
  (mLt cap Wb a b hab (pgN (by decide)) h.1 h.2.2.2.2.1 (h.r0 hl z).1 ha hb hcap).post
    (fun _ ⟨_, hF, fr⟩ => h.regs hl (se_sub fr (by simp) (by simp)) hF
      (by rw [fr.val (by simp [pgN (show (4 : Fin 5) ≠ 0 by decide)]), h.2.2.2.2.2.1]))

theorem rDivmod {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ} (a b q m x : Fin 14)
    (hd : [a, b, q, m, x].Nodup) (hq : PB q ∈ bl PB O) (hm : PB m ∈ bl PB O) (hx : PB x ∈ bl PB O)
    (h : RS PB PG O OP Wb σ0 τ w u 0 g) (ha : w a < 2 ^ Wb) (hb : 0 < w b) (h2b : 2 * w b ≤ 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.divmod (PB a) (PB b) (PB q) (PB m) (PB x) (PG 0) (PG 1) (PG 2) (PG 3)) τ (BinW.divCost Wb)
      (fun τ' => RS PB PG O OP Wb σ0 τ'
        (Function.update (Function.update (Function.update w q (w a / w b)) m (w a % w b)) x 0) u 0 g) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨_, haq, ham, hax⟩, ⟨hbq, hbm, hbx⟩, ⟨hqm, hqx⟩, hmx⟩ := hd
  have r0 := h.r0 hl z
  refine (fDivmod cap Wb (sN haq) (sN ham) (sN hax) (sN hbq) (sN hbm) (sN hbx) (sN hqm) (sN hqx) (sN hmx.1)
    (pgN (by decide)) (pgN (by decide)) (pgN (by decide)) (pgN (by decide)) (h.1 a) (h.1 b) (h.1 q) (h.1 m) (h.1 x)
    h.2.2.2.2.1 r0.1 r0.2.1 r0.2.2.1 ha hb h2b hcap).post (fun τ' ⟨hQ, hM, hX, fr⟩ => ?_)
  obtain ⟨_, hO, hOh, hOP, hf, hg, s⟩ := h
  have hn : ∀ i, i ≠ q → i ≠ m → i ≠ x → PB i ∉ [PB q, PB m, PB x] := by
    intro i h1 h2 h3; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨sN h1, sN h2, sN h3⟩
  have hO' : O ∉ [PB q, PB m, PB x] := by simp [(hl.bo q).symm, (hl.bo m).symm, (hl.bo x).symm]
  refine ⟨fun i => ?_, by rw [fr.st hO', hO], by rw [fr.sh hO', hOh], by rw [fr.val (by simp), hOP],
    by rw [fr.val (by simp), hf], by rw [fr.val (by simp), hg], s.trans (se_sub fr ?_ (by simp))⟩
  · by_cases ex : i = x
    · subst ex; simpa using hX
    · by_cases em : i = m
      · subst em; simpa [ex] using hM
      · by_cases eq : i = q
        · subst eq; simpa [ex, em] using hQ
        · simp only [Function.update_of_ne ex, Function.update_of_ne em, Function.update_of_ne eq]
          exact fr.numOn (hn i eq em ex) (by have := s; exact (show NumOn τ (PB i) Wb (w i) from by
            simpa using (show MV PB Wb w τ from by assumption) i))
  · intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> assumption

theorem rNatW {τ : WState ns nr} {w : Fin 14 → ℕ} {u : List Bool} {g : ℕ} (a : Fin 14)
    (h : RS PB PG O OP Wb σ0 τ w u 0 g) (hO0 : σ0.sh O = (σ0.st O).length) (hv : w a < 2 ^ Wb) (hW : 1 ≤ Wb)
    (hcap : 2 * Wb + 2 ≤ cap) (hcO : σ0.val OP + u.length + 2 * Wb + 2 ≤ cap) :
    Runs cap (natW (PB a) O OP PR) τ (natWCost Wb)
      (fun τ' => RS PB PG O OP Wb σ0 τ' w (u ++ natWord (w a)) 0 g) := by
  have hτO : τ.sh O = (τ.st O).length := by rw [h.2.2.1, h.2.1, List.length_append, hO0]
  exact (natW_spec (cap := cap) hl.po (hl.bo a) τ Wb (w a) (h.1 a) hv hW (h.r0 hl z).2.2.2 hτO hcap
    (by rw [h.2.2.2.1]; omega)).post (fun _ he => h.emit hl he)

end Steps

end NearCubicGates.Close.Expand

import Proof.Wire_3_5.UnionMachineRoundParse

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm

local notation "sO" => (0 : Fin 3)
local notation "sR" => (1 : Fin 3)
local notation "sD" => (2 : Fin 3)
local notation "rF" => (0 : Fin 14)
local notation "rRC" => (1 : Fin 14)
local notation "rQ" => (2 : Fin 14)
local notation "rT" => (3 : Fin 14)
local notation "rSG" => (4 : Fin 14)
local notation "rK" => (8 : Fin 14)
local notation "rPC" => (9 : Fin 14)
local notation "rMP" => (10 : Fin 14)
local notation "rMN" => (11 : Fin 14)

/-! ## Two more pass facts -/

/-- The final state of a pass does not depend on what it writes. -/
theorem mapS_snd (out out' nxt : Bool → Bool → Bool → Bool) :
    ∀ (as bs : List Bool) (c : Bool), (mapS out nxt as bs c).2 = (mapS out' nxt as bs c).2
  | [], _, _ => by cases ‹List Bool› <;> rfl
  | _ :: _, [], _ => rfl
  | a :: as, b :: bs, c => by simp only [mapS]; exact mapS_snd out out' nxt as bs _

/-- The shift pass's carry out is the overflow bit of `2x + c`. -/
theorem mapS_shl_carry : ∀ (w x : ℕ) (bs : List Bool) (c : Bool), bs.length = w → x < 2 ^ w →
    (mapS shOut shNxt (binary w x) bs c).2 = decide (2 ^ w ≤ 2 * x + c.toNat)
  | 0, x, [], c, _, hx => by
    have : x = 0 := by simpa using hx
    subst this
    show c = _
    cases c <;> simp
  | w + 1, x, b :: bs, c, h, hx => by
    simp only [binary_succ, mapS, shOut, shNxt]
    have hx2 : x / 2 < 2 ^ w := by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hx; omega
    rw [mapS_shl_carry w (x / 2) bs _ (by simpa using h) hx2]
    have hc := Bool.toNat_le c
    have hm := Nat.mod_two_eq_zero_or_one x
    rw [pow_succ]
    rcases hm with hm | hm <;> simp [hm] <;> omega
  | 0, _, _ :: _, _, h, _ => by simp at h
  | _ + 1, _, [], _, h, _ => by simp at h

/-! ## The loop with an invariant -/

section LoopInv
variable {ns nr : ℕ} (cap : ℕ)

/-- **The counted loop with an invariant**: per-round existential body specs. -/
theorem wloopE (K : Fin nr) (body : WM ns nr) (c n : ℕ) (Inv : ℕ → WState ns nr → Prop) (hcap : n ≤ cap)
    (hstep : ∀ k < n, ∀ σ, Inv k σ → σ.val K = n - k →
      ∃ τ, WExec cap body (σ.setv K (n - k - 1)) τ c ∧ Inv (k + 1) τ ∧ τ.val K = n - k - 1) :
    ∀ σ, Inv 0 σ → σ.val K = n →
      ∃ τ, WExec cap (.whr K (.seq (.dec K) body)) σ τ (n * (c + 4) + 1) ∧ Inv n τ ∧ τ.val K = 0 := by
  have key : ∀ m j σ, j + m = n → Inv j σ → σ.val K = n - j →
      ∃ τ, WExec cap (.whr K (.seq (.dec K) body)) σ τ (m * (c + 4) + 1) ∧ Inv n τ ∧ τ.val K = 0 := by
    intro m
    induction m with
    | zero =>
      intro j σ hj hI hK
      rw [Nat.add_zero] at hj; subst hj
      exact ⟨σ, WExec.mono (WExec.whrF (by omega)) (by omega), hI, by omega⟩
    | succ m ih =>
      intro j σ hj hI hK
      have h1 := WExec.dec (cap := cap) K σ (by omega)
      rw [hK] at h1
      obtain ⟨τ, hτ, hI', hK'⟩ := hstep j (by omega) σ hI hK
      obtain ⟨ρ, hρ, hIρ, hKρ⟩ := ih (j + 1) τ (by omega) hI' (by omega)
      exact ⟨ρ, WExec.mono (WExec.whrT (by omega) (WExec.seq h1 hτ) hρ) (by nlinarith), hIρ, hKρ⟩
  intro σ hI hK
  exact key n 0 σ (by omega) hI (by omega)

end LoopInv

/-! ## Programs that never touch the result cell -/

section Cell
variable {ns nr : ℕ}

/-- The program has no `setc`. -/
def cellFree : WM ns nr → Bool
  | .setc _ => false
  | .seq P Q => cellFree P && cellFree Q
  | .ifr _ P Q => cellFree P && cellFree Q
  | .ifs _ P Q => cellFree P && cellFree Q
  | .whr _ P => cellFree P
  | .whs _ P => cellFree P
  | _ => true

theorem cellFree_cell (cap : ℕ) {P : WM ns nr} (hP : cellFree P = true) {σ τ : WState ns nr} {n : ℕ}
    (h : WExec cap P σ τ n) : τ.cell = σ.cell := by
  induction h with
  | skip => rfl
  | inc => rfl
  | dec => rfl
  | fwd => rfl
  | bwd => rfl
  | wr => rfl
  | setc => simp [cellFree] at hP
  | seq _ _ ih1 ih2 =>
    simp only [cellFree, Bool.and_eq_true] at hP
    exact (ih2 hP.2).trans (ih1 hP.1)
  | ifrT _ _ ih => simp only [cellFree, Bool.and_eq_true] at hP; exact ih hP.1
  | ifrF _ _ ih => simp only [cellFree, Bool.and_eq_true] at hP; exact ih hP.2
  | ifsT _ _ ih => simp only [cellFree, Bool.and_eq_true] at hP; exact ih hP.1
  | ifsF _ _ ih => simp only [cellFree, Bool.and_eq_true] at hP; exact ih hP.2
  | whrF => rfl
  | whrT _ _ _ ih1 ih2 => exact (ih2 hP).trans (ih1 hP)
  | whsF => rfl
  | whsT _ _ _ ih1 ih2 => exact (ih2 hP).trans (ih1 hP)
  | mono _ _ ih => exact ih hP

end Cell

/-! ## The division state -/

/-- The division's state: remainder `r` and denominator on streams `1`, `2` (width `w`, heads `0`), quotient `Q`,
flags and counters clear, `PC = p`, `SG = sg`, the outputs `MP = MN = 0`. -/
def DivSt (w den p sg r q : ℕ) (σ : RS) : Prop :=
  σ.st sR = frameP (binary w r) ++ [false] ∧ σ.sh sR = 0 ∧ σ.st sD = frameP (binary w den) ++ [false] ∧
  σ.sh sD = 0 ∧ σ.val rF = 0 ∧ σ.val rRC = 0 ∧ σ.val rQ = q ∧ σ.val rT = 0 ∧ σ.val rPC = p ∧ σ.val rSG = sg ∧
  σ.val rMP = 0 ∧ σ.val rMN = 0

variable (cap : ℕ)

/-! ## One conditional subtraction -/

/-- Compare, then subtract once if the denominator fits (one `intStep`). -/
def condSub : WM 2 14 :=
  .seq (setFlag rF true) <| .seq (mapPass keepA geN sR sD rF rRC) <|
    .ifr rF (.seq (.inc rQ) (.seq (mapPass subO geN sR sD rF rRC) (setFlag rF false))) .skip

theorem condSub_spec (w den p sg r q : ℕ) (σ : RS) (hσ : DivSt w den p sg r q σ) (hr : r < 2 ^ w)
    (hd : den < 2 ^ w) (hcap : 2 * w + q + 2 ≤ cap) :
    ∃ τ, WExec cap condSub σ τ (w * 90 + 30) ∧
      DivSt w den p sg (intStep den (r, q)).1 (intStep den (r, q)).2 τ ∧ τ.val rK = σ.val rK := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hσ
  have hc1 : 1 ≤ cap := by omega
  have e1 := setFlag_spec cap rF true false σ (by simp [h5]) hc1
  set σ1 := σ.setv rF (true.toNat) with hσ1
  have e2 := mapPass_spec cap keepA geN sR sD rF rRC (by decide) (by decide) hc1 (binary w r) (binary w den) []
    [false] true σ1 (by simp) (by simp [σ1, h1]) (by simp [σ1, h2]) (by simp [σ1, h3]) (by simp [σ1, h4])
    (by simp [σ1]) (by simp [σ1, Function.update_apply, h6]) (by simp; omega)
  rw [mapS_keepA geN _ _ _ (by simp), mapS_ge, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hd, binary_length] at e2
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e2
  set σ2 := (σ1.sets sR (frameP (binary w r) ++ [false])).setv rF (decide (den ≤ r)).toNat with hσ2
  by_cases hle : den ≤ r
  · -- subtract
    have hF2 : σ2.val rF ≠ 0 := by simp [σ2, hle]
    have e3 := WExec.inc (cap := cap) rQ σ2 (by simp [σ2, σ1, Function.update_apply, h7]; omega)
    set σ3 := σ2.setv rQ (σ2.val rQ + 1) with hσ3
    have e4 := mapPass_spec cap subO geN sR sD rF rRC (by decide) (by decide) hc1 (binary w r) (binary w den) []
      [false] true σ3 (by simp) (by simp [σ3, σ2]) (by simp [σ3, σ2, σ1, h2]) (by simp [σ3, σ2, σ1, h3])
      (by simp [σ3, σ2, σ1, h4]) (by simp [σ3, σ2, Function.update_apply, hle])
      (by simp [σ3, σ2, σ1, Function.update_apply, h6]) (by simp; omega)
    rw [mapS_sub w r den hle hr, mapS_snd subO keepA, mapS_ge, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hd,
      binary_length] at e4
    simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero, hle, decide_true] at e4
    set σ4 := (σ3.sets sR (frameP (binary w (r - den)) ++ [false])).setv rF (true.toNat) with hσ4
    have e5 := setFlag_spec cap rF false true σ4 (by simp [σ4]) hc1
    refine ⟨σ4.setv rF (false.toNat), WExec.mono (e1.seq (e2.seq (WExec.ifrT hF2 (e3.seq (e4.seq e5))))) ?_, ?_, ?_⟩
    · omega
    · simp only [intStep, hle, if_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [σ4, σ3, σ2, σ1, Function.update_apply, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12]
    · simp [σ4, σ3, σ2, σ1, Function.update_apply]
  · -- keep
    have hF2 : σ2.val rF = 0 := by simp [σ2, hle]
    refine ⟨σ2, WExec.mono (e1.seq (e2.seq (WExec.ifrF hF2 (WExec.skip σ2)))) ?_, ?_, ?_⟩
    · omega
    · simp only [intStep, hle, if_false]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [σ2, σ1, Function.update_apply, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12, hle]
    · simp [σ2, σ1, Function.update_apply]

/-! ## Doubling the quotient, shifting the remainder -/

/-- `Q := 2Q` through `T`. -/
def dblQ : WM 2 14 := .seq (WM.move rQ rT) (.whr rT (.seq (.dec rT) (.seq (.inc rQ) (.inc rQ))))

theorem dblQ_spec (w den p sg r q : ℕ) (σ : RS) (hσ : DivSt w den p sg r q σ) (hcap : 2 * q ≤ cap) :
    ∃ τ, WExec cap dblQ σ τ (18 * q + 3) ∧ DivSt w den p sg r (2 * q) τ ∧ τ.val rK = σ.val rK := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hσ
  have e1 := wmove_spec cap rQ rT (by decide) q σ h7 (by omega) (by omega)
  let S : ℕ → RS := fun k => (σ.setv rQ (2 * k)).setv rT (q - k)
  have hS0 : S 0 = (σ.setv rQ 0).setv rT (σ.val rT + σ.val rQ) := by
    simp only [S]; rw [h8, h7]; simp
  have e2 := wloop cap rT (.seq (.inc rQ) (.inc rQ)) 7 q S (fun k _ => by simp [S]) (by omega)
    (fun k hk => by
      have a1 := WExec.inc (cap := cap) rQ ((S k).setv rT (q - k - 1)) (by simp [S, Function.update_apply]; omega)
      have a2 := WExec.inc (cap := cap) rQ (((S k).setv rT (q - k - 1)).setv rQ
        (((S k).setv rT (q - k - 1)).val rQ + 1)) (by simp [S, Function.update_apply]; omega)
      refine WExec.cast cap (a1.seq a2) ?_ (by omega)
      simp only [S]
      refine WState.eq rfl rfl ?_ rfl
      funext x
      simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all <;> omega)
  rw [← hS0] at e1
  refine ⟨S q, WExec.mono (e1.seq e2) (by omega), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [S, Function.update_apply, h1, h2, h3, h4, h5, h6, h9, h10, h11, h12]
  · simp [S, Function.update_apply]

/-- `r := 2r` (the flag `0` shifted in). -/
def shiftP : WM 2 14 := mapPass shOut shNxt sR sD rF rRC

theorem shiftP_spec (w den p sg r q : ℕ) (σ : RS) (hσ : DivSt w den p sg r q σ) (hr : 2 * r < 2 ^ w)
    (hcap : 2 * w + 2 ≤ cap) :
    ∃ τ, WExec cap shiftP σ τ (w * 41 + 3) ∧ DivSt w den p sg (2 * r) q τ ∧ τ.val rK = σ.val rK := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hσ
  have e := mapPass_spec cap shOut shNxt sR sD rF rRC (by decide) (by decide) (by omega) (binary w r) (binary w den)
    [] [false] false σ (by simp) (by simp [h1]) h2 (by simp [h3]) h4 (by simp [h5]) h6 (by simp; omega)
  rw [mapS_shl w r _ false (by simp), mapS_shl_carry w r _ false (by simp) (by omega), binary_length] at e
  simp only [Bool.toNat_false, Nat.add_zero] at e
  have e' : WExec cap shiftP σ ((σ.sets sR (frameP (binary w (2 * r)) ++ [false])).setv rF 0) (w * 41 + 3) :=
    WExec.cast cap e (by congr 1; simp only [Bool.toNat_eq_zero, decide_eq_false_iff_not, not_le]; omega) le_rfl
  refine ⟨_, e', ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Function.update_apply, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12]
  · simp [Function.update_apply]

/-- One fractional round: shift, double `Q`, conditional subtraction (one `fracStep`). -/
def fracBody : WM 2 14 := .seq shiftP (.seq dblQ condSub)

theorem fracBody_spec (w den p sg r q : ℕ) (σ : RS) (hσ : DivSt w den p sg r q σ) (hr : r < den)
    (hd : 4 * den ≤ 2 ^ w) (hcap : 2 * w + 2 * q + 4 ≤ cap) :
    ∃ τ, WExec cap fracBody σ τ (w * 131 + 18 * q + 38) ∧
      DivSt w den p sg (fracStep den (r, q)).1 (fracStep den (r, q)).2 τ ∧ τ.val rK = σ.val rK := by
  obtain ⟨τ1, e1, hτ1, hK1⟩ := shiftP_spec cap w den p sg r q σ hσ (by omega) (by omega)
  obtain ⟨τ2, e2, hτ2, hK2⟩ := dblQ_spec cap w den p sg (2 * r) q τ1 hτ1 (by omega)
  obtain ⟨τ3, e3, hτ3, hK3⟩ := condSub_spec cap w den p sg (2 * r) (2 * q) τ2 hτ2 (by omega) (by omega) (by omega)
  have hfs : intStep den (2 * r, 2 * q) = fracStep den (r, q) := by
    unfold intStep fracStep; split_ifs <;> simp
  rw [hfs] at hτ3
  exact ⟨τ3, WExec.mono (e1.seq (e2.seq e3)) (by omega), hτ3, by rw [hK3, hK2, hK1]⟩

/-! ## The integer part and the fraction -/

/-- The integer part: three conditional subtractions. -/
def intP : WM 2 14 := .seq condSub (.seq condSub condSub)

theorem intP_spec (w den p sg r : ℕ) (σ : RS) (hσ : DivSt w den p sg r 0 σ) (hr : r < 2 ^ w)
    (hd : den < 2 ^ w) (hcap : 2 * w + 5 ≤ cap) :
    ∃ τ, WExec cap intP σ τ (w * 270 + 92) ∧
      DivSt w den p sg ((intStep den)^[3] (r, 0)).1 ((intStep den)^[3] (r, 0)).2 τ ∧ τ.val rK = σ.val rK := by
  have hle : ∀ rq : ℕ × ℕ, (intStep den rq).1 ≤ rq.1 ∧ (intStep den rq).2 ≤ rq.2 + 1 := by
    intro rq; unfold intStep; split_ifs <;> simp <;> omega
  obtain ⟨τ1, e1, hτ1, hK1⟩ := condSub_spec cap w den p sg r 0 σ hσ hr hd (by omega)
  have b1 := hle (r, 0)
  obtain ⟨τ2, e2, hτ2, hK2⟩ := condSub_spec cap w den p sg _ _ τ1 hτ1 (by omega) hd (by simp at b1; omega)
  have b2 := hle ((intStep den (r, 0)).1, (intStep den (r, 0)).2)
  obtain ⟨τ3, e3, hτ3, hK3⟩ := condSub_spec cap w den p sg _ _ τ2 hτ2 (by omega) hd (by simp at b1; omega)
  refine ⟨τ3, WExec.mono (e1.seq (e2.seq e3)) (by omega), ?_, by rw [hK3, hK2, hK1]⟩
  simpa [Function.iterate_succ, Function.comp] using hτ3

/-- The fraction: `p` fractional rounds, counted from `PC` in `K`. -/
def fracP : WM 2 14 := .seq (copyU rPC rK) (.whr rK (.seq (.dec rK) fracBody))

theorem divRef_q_lt (num den k : ℕ) (hd : 0 < den) (h : num < 4 * den) : (divRef num den k).2 < 4 * 2 ^ k := by
  obtain ⟨h1, _⟩ := divRef_inv num den hd h k
  by_contra hc
  have hc' := Nat.le_of_not_lt hc
  have h3 : 4 * 2 ^ k * den ≤ (divRef num den k).2 * den := Nat.mul_le_mul_right _ hc'
  have h2 : num * 2 ^ k < 4 * den * 2 ^ k := Nat.mul_lt_mul_of_pos_right h (by positivity)
  have e : 4 * den * 2 ^ k = 4 * 2 ^ k * den := by ring
  omega

theorem fracP_spec (w num den p sg : ℕ) (σ : RS) (hσ : DivSt w den p sg (num % den) (num / den) σ)
    (hK : σ.val rK = 0) (hd0 : 0 < den) (hn : num < 4 * den) (hd : 4 * den ≤ 2 ^ w)
    (hcap : 2 * w + 8 * 2 ^ p + 10 ≤ cap) :
    ∃ τ, WExec cap fracP σ τ (20 * p + 3 + 1 + (p * (w * 131 + 72 * 2 ^ p + 38 + 4) + 1)) ∧
      DivSt w den p sg (divRef num den p).1 (divRef num den p).2 τ := by
  have hp2 : p < 2 ^ p := Nat.lt_two_pow_self
  have h8 : σ.val rT = 0 := hσ.2.2.2.2.2.2.2.1
  have h9 : σ.val rPC = p := hσ.2.2.2.2.2.2.2.2.1
  have e1 := copyU_spec cap rPC rK (by decide) (by decide) (by decide) σ h8 (by rw [hK, h9]; omega)
    (by rw [h9]; omega)
  rw [hK, h9, Nat.zero_add] at e1
  have hσ1 : DivSt w den p sg (divRef num den 0).1 (divRef num den 0).2 (σ.setv rK p) := by
    have e : divRef num den 0 = (num % den, num / den) := by
      simp [divRef, intStep3 num den hd0 hn]
    rw [e]
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := hσ
    exact ⟨by simpa using g1, by simpa using g2, by simpa using g3, by simpa using g4, by simpa using g5,
      by simpa using g6, by simpa using g7, by simpa using g8, by simpa using g9, by simpa using g10,
      by simpa using g11, by simpa using g12⟩
  obtain ⟨τ, e2, hτ, _⟩ := wloopE cap rK fracBody (w * 131 + 72 * 2 ^ p + 38) p
    (fun k σ => DivSt w den p sg (divRef num den k).1 (divRef num den k).2 σ) (by omega)
    (fun k hk σ hI hKσ => by
      have hI' : DivSt w den p sg (divRef num den k).1 (divRef num den k).2 (σ.setv rK (p - k - 1)) := by
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := hI
        exact ⟨by simpa using g1, by simpa using g2, by simpa using g3, by simpa using g4, by simpa using g5,
          by simpa using g6, by simpa using g7, by simpa using g8, by simpa using g9, by simpa using g10,
          by simpa using g11, by simpa using g12⟩
      have hq := divRef_q_lt num den k hd0 hn
      have hk2 : 2 ^ k ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hk.le
      obtain ⟨_, hrlt⟩ := divRef_inv num den hd0 hn k
      obtain ⟨τ, e, hτ, hKτ⟩ := fracBody_spec cap w den p sg _ _ _ hI' hrlt hd (by omega)
      refine ⟨τ, WExec.mono e (by nlinarith), ?_, by simpa using hKτ⟩
      have e2 : divRef num den (k + 1) = fracStep den (divRef num den k) := by
        simp only [divRef, Function.iterate_succ_apply']
      rw [e2]
      exact hτ) (σ.setv rK p) hσ1 (by simp)
  exact ⟨τ, WExec.mono (e1.seq e2) (by omega), hτ⟩

/-! ## The sign -/

/-- `MP := Q` (nonnegative), or `MN := Q + [r ≠ 0]` (negative). -/
def signP : WM 2 14 :=
  .ifr rSG (.seq (mapPass keepA anyN sR sD rF rRC) (.seq (WM.move rQ rMN) (.ifr rF (.inc rMN) .skip)))
    (WM.move rQ rMP)

theorem signP_spec (w den p : ℕ) (sg : Bool) (r q : ℕ) (σ : RS) (hσ : DivSt w den p sg.toNat r q σ)
    (hr : r < 2 ^ w) (hcap : 2 * w + q + 2 ≤ cap) :
    ∃ τ, WExec cap signP σ τ (w * 41 + 7 * q + 16) ∧
      ((τ.val rMP : ℤ) - τ.val rMN = floorVal sg (r, q)) ∧ τ.val rPC = p ∧ τ.cell = σ.cell := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hσ
  cases sg
  · have e := wmove_spec cap rQ rMP (by decide) q σ h7 (by omega) (by omega)
    refine ⟨_, WExec.mono (WExec.ifrF (by simpa using h10) e) (by omega), ?_, ?_, ?_⟩
    · simp [Function.update_apply, h7, h11, h12, floorVal]
    · simp [Function.update_apply, h9]
    · rfl
  · have e1 := mapPass_spec cap keepA anyN sR sD rF rRC (by decide) (by decide) (by omega) (binary w r)
      (binary w den) [] [false] false σ (by simp) (by simp [h1]) h2 (by simp [h3]) h4 (by simp [h5]) h6
      (by simp; omega)
    rw [mapS_keepA anyN _ _ _ (by simp), mapS_any w r _ false (by simp), Nat.mod_eq_of_lt hr, binary_length] at e1
    simp only [Bool.false_or] at e1
    set σ1 := (σ.sets sR (frameP (binary w r) ++ [false])).setv rF (decide (r ≠ 0)).toNat with hσ1
    have e2 := wmove_spec cap rQ rMN (by decide) q σ1 (by simp [σ1, Function.update_apply, h7])
      (by simp [σ1, Function.update_apply, h7]; omega) (by simp [σ1, Function.update_apply, h7, h12]; omega)
    set σ2 := (σ1.setv rQ 0).setv rMN (σ1.val rMN + σ1.val rQ) with hσ2
    by_cases hr0 : r = 0
    · have hF : σ2.val rF = 0 := by simp [σ2, σ1, Function.update_apply, hr0]
      refine ⟨σ2, WExec.mono (WExec.ifrT (by simp [h10]) (e1.seq (e2.seq (WExec.ifrF hF (WExec.skip σ2)))))
        (by omega), ?_, ?_, ?_⟩
      · simp [σ2, σ1, Function.update_apply, h7, h11, h12, floorVal, hr0]
      · simp [σ2, σ1, Function.update_apply, h9]
      · rfl
    · have hF : σ2.val rF ≠ 0 := by simp [σ2, σ1, Function.update_apply, hr0]
      have e3 := WExec.inc (cap := cap) rMN σ2 (by simp [σ2, σ1, Function.update_apply, h7, h12]; omega)
      refine ⟨_, WExec.mono (WExec.ifrT (by simp [h10]) (e1.seq (e2.seq (WExec.ifrT hF e3)))) (by omega),
        ?_, ?_, ?_⟩
      · simp [σ2, σ1, Function.update_apply, h7, h11, h12, floorVal, hr0]
      · simp [σ2, σ1, Function.update_apply, h9]
      · rfl

/-! ## The rounding program -/

/-- **The rounding program**: read the answer, divide, sign. -/
def roundP : WM 2 14 := .seq parseP (.seq intP (.seq fracP signP))

/-- The rounding program's step bound. -/
def roundCost (b p : ℕ) : ℕ := 250 * (b + 2) + (p + 4) * (400 * (b + 2) + 100 * 2 ^ p + 200)

theorem round_spec (v : ℚ) (p : ℕ) (c : Bool) (hv : v.num.natAbs < 4 * v.den)
    (hcap : 4 * lb v + 8 * 2 ^ p + 20 ≤ cap) :
    ∃ τ, WExec cap roundP (parseIn v p c) τ (roundCost (lb v) p) ∧
      ((τ.val rMP : ℤ) - τ.val rMN = ⌊v * 2 ^ p⌋) ∧ τ.val rPC = p ∧ τ.cell = c := by
  have hd0 : 0 < v.den := v.den_pos
  have hdw : 4 * v.den ≤ 2 ^ (lb v + 2) := by
    have := natBitLength_lt v.den
    rw [pow_add]; unfold lb at *; omega
  have hnw : v.num.natAbs < 2 ^ (lb v + 2) := by omega
  have hdw' : v.den < 2 ^ (lb v + 2) := by omega
  have e0 := parse_spec cap v p c hv (by omega)
  have hP : DivSt (lb v + 2) v.den p (sgn v).toNat v.num.natAbs 0 (parseOut v p c) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [parseOut, st3]
  obtain ⟨τ1, e1, hτ1, hK1⟩ := intP_spec cap (lb v + 2) v.den p _ _ _ hP hnw hdw' (by omega)
  rw [intStep3 _ _ hd0 hv] at hτ1
  obtain ⟨τ2, e2, hτ2⟩ := fracP_spec cap (lb v + 2) v.num.natAbs v.den p _ τ1 hτ1
    (by rw [hK1]; simp [parseOut, st3]) hd0 hv hdw (by omega)
  have hq := divRef_q_lt v.num.natAbs v.den p hd0 hv
  obtain ⟨_, hrlt⟩ := divRef_inv v.num.natAbs v.den hd0 hv p
  obtain ⟨τ3, e3, hval, hpc, hcell⟩ := signP_spec cap (lb v + 2) v.den p (sgn v) _ _ τ2 hτ2 (by omega) (by omega)
  refine ⟨τ3, WExec.mono (e0.seq (e1.seq (e2.seq e3))) ?_, ?_, hpc, ?_⟩
  · unfold roundCost; nlinarith
  · rw [hval, floorVal_eq v p hv]
  · rw [hcell]
    exact (cellFree_cell cap (by decide) e2).trans ((cellFree_cell cap (by decide) e1).trans
      (by simp [parseOut, st3]))

end NearCubicWires.WireExponent3_5.UnionMachine.Round

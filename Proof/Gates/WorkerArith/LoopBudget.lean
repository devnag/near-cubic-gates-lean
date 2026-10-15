import Proof.Gates.WorkerArith.HotFuel
import Proof.Gates.WorkerArith.TermD
import Proof.Gates.TermLoop.Gadget4

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup NearCubicGates.Close.TermLoop NearCubicGates.Close.Codec
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd)
open NearCubicGates.Close.WorkerArith (bud1 bud2 TermFit)

noncomputable section

theorem budget_split {B1 B2 : ℕ} (ctr : Counter B1 B2) :
    ∃ onset K e : ℕ, ∀ (c : Call) (w : List Bool), onset ≤ c.n →
      ctr.budget c w ≤ hotCall c.n + K * ((callWord c).length + 1) ^ e := by
  obtain ⟨o1, hf⟩ := ctr.fast
  obtain ⟨K, e, hr⟩ := ctr.rest
  refine ⟨max o1 1, K, e, fun c w hn => ?_⟩
  by_cases hA : c.Admitted B1 B2
  · have h := hf c (le_trans (le_max_left _ _) hn) hA w
    have hpos : 0 < c.n ^ NearCubicGates.Target.mu c.n := Nat.pow_pos (by have := le_max_right o1 1; omega)
    have : ctr.budget c w ≤ hotCall c.n := (Nat.le_div_iff_mul_le hpos).2 h
    omega
  · have := hr c w hA; omega

/-- What the loop's operand descriptors satisfy (`lit_idx`, `helpOpd`). -/
structure OpdOK (q Rn N Z : ℕ) (o : Opd) : Prop where
  le : o.idx ≤ Z
  sys : o.sys = true → o.idx < q + Rn
  aux : o.sys = false → o.idx < N

section Bud
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) {q : ℕ} (Cs : ℕ → NCircuit q) (rows : ℕ → List ℕ) (Rn N : ℕ) (ω : ℚ)
  (w : List Bool) (cap Z Bc V : ℕ) (hT : TermFit cap Cs N rows Rn ω w Z Bc V) (onset K e : ℕ)
  (hb : ∀ (c : Call) (w : List Bool), onset ≤ c.n → ctr.budget c w ≤ hotCall c.n + K * ((callWord c).length + 1) ^ e)
  (hq : onset ≤ q)
include hT hb hq

omit hb hq in
theorem sysList_le (o : Opd) (ho : OpdOK q Rn N Z o) (hs : o.sys = true) :
    (listWord natWord (sysList q rows o.idx)).length ≤ 2 * Z + 10 := by
  unfold sysList
  split_ifs with h
  · exact listWord_single_le _ _ ho.le
  · have := hT.rowZ (o.idx - q) (by have := ho.sys hs; omega); omega

theorem one_le (j : ℕ) (hj : j < N) (ps : List ℕ) (hp : (listWord natWord ps).length ≤ 2 * Z + 10) :
    ctr.budget (oneCallOf Cs j ps ω) w ≤ hotCall q + K * (10 * Z + 41) ^ e := by
  have h1 := hb (oneCallOf Cs j ps ω) w hq
  have h2 := callWord_one_le Cs j ps ω Z hT.qZ (hT.cwZ j hj) hp hT.ωZ
  have h3 : ((callWord (oneCallOf Cs j ps ω)).length + 1) ^ e ≤ (10 * Z + 41) ^ e := Nat.pow_le_pow_left (by omega) e
  exact h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h3) _)

theorem pair_le (i j : ℕ) (hi : i < N) (hj : j < N) :
    ctr.budget (pairCallOf Cs i j ω) w ≤ hotCall q + K * (10 * Z + 41) ^ e := by
  have h1 := hb (pairCallOf Cs i j ω) w hq
  have h2 := callWord_pair_le Cs i j ω Z hT.qZ (hT.cwZ i hi) (hT.cwZ j hj) hT.ωZ
  have h3 : ((callWord (pairCallOf Cs i j ω)).length + 1) ^ e ≤ (10 * Z + 41) ^ e := Nat.pow_le_pow_left (by omega) e
  exact h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h3) _)

theorem bud1_le (o : Opd) (ho : OpdOK q Rn N Z o) : bud1 ctr Cs ω w o ≤ hotCall q + K * (10 * Z + 41) ^ e := by
  unfold bud1
  split_ifs with h
  · omega
  · exact one_le ctr Cs rows Rn N ω w cap Z Bc V hT onset K e hb hq o.idx (ho.aux (by simpa using h)) []
      (by rw [listWord_nil_len]; omega)

theorem bud2_le (o1 o2 : Opd) (h1 : OpdOK q Rn N Z o1) (h2 : OpdOK q Rn N Z o2) :
    bud2 ctr Cs rows ω w o1 o2 ≤ hotCall q + K * (10 * Z + 41) ^ e := by
  unfold bud2
  rcases ho1 : o1.sys <;> rcases ho2 : o2.sys
  · simp only
    split_ifs
    · omega
    · exact pair_le ctr Cs rows Rn N ω w cap Z Bc V hT onset K e hb hq _ _ (h1.aux ho1) (h2.aux ho2)
  · exact one_le ctr Cs rows Rn N ω w cap Z Bc V hT onset K e hb hq _ (h1.aux ho1) _
      (sysList_le Cs rows Rn N ω w cap Z Bc V hT o2 h2 ho2)
  · exact one_le ctr Cs rows Rn N ω w cap Z Bc V hT onset K e hb hq _ (h2.aux ho2) _
      (sysList_le Cs rows Rn N ω w cap Z Bc V hT o1 h1 ho1)
  · simp only; omega

end Bud

/-! ## The loop's descriptors and budgets -/

section Loop
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

theorem litOpd_ok (Z i : ℕ) (hidx : sysCount s P g x B + auxN s P g x B ≤ Z) (k : Fin 3) :
    OpdOK (width s g N) (P.code.length (width s g N)) (auxN s P g x B) Z (litOpd s P g x B i k) := by
  obtain ⟨a, b, c⟩ := lit_idx (P := P) x B Z i hidx k
  exact ⟨a, b, c⟩

theorem helpOpd_ok (Z i : ℕ) (hidx : sysCount s P g x B + auxN s P g x B ≤ Z) (hi : i < gadgets s g N) :
    OpdOK (width s g N) (P.code.length (width s g N)) (auxN s P g x B) Z (helpOpd s P g x B i) := by
  have h := (lit_bounds (P := P) x B i 0).2.2
  refine ⟨?_, fun h' => by simp [helpOpd] at h', fun _ => ?_⟩
  · show (pcpp s P g x B).proofBits + i ≤ Z
    omega
  · show (pcpp s P g x B).proofBits + i < auxN s P g x B
    omega

/-- **The per-term budget split.** -/
theorem termBud_le (cap Z Bc V : ℕ) (onset K e : ℕ)
    (hb : ∀ (c : Call) (w : List Bool), onset ≤ c.n → ctr.budget c w ≤ hotCall c.n + K * ((callWord c).length + 1) ^ e)
    (hq : onset ≤ width s g N) (hidx : sysCount s P g x B + auxN s P g x B ≤ Z) (i : ℕ) (hi : i < gadgets s g N)
    (t : Fin 10)
    (hT : TermFit cap (circs s g N bits pad) (auxN s P g x B) (suppRows P (width s g N))
      (P.code.length (width s g N)) ω (termField s P g x bits pad B i t) Z Bc V) :
    termBud s P g x bits pad B ctr ω i t ≤ hotCall (width s g N) + K * (10 * Z + 41) ^ e := by
  have l := litOpd_ok x B Z i hidx
  have h := helpOpd_ok x B Z i hidx hi
  have b1 := fun o (ho : OpdOK _ _ _ Z o) =>
    bud1_le ctr (circs s g N bits pad) (suppRows P (width s g N)) (P.code.length (width s g N)) (auxN s P g x B) ω
      (termField s P g x bits pad B i t) cap Z Bc V hT onset K e hb hq o ho
  have b2 := fun o1 o2 (h1 : OpdOK _ _ _ Z o1) (h2 : OpdOK _ _ _ Z o2) =>
    bud2_le ctr (circs s g N bits pad) (suppRows P (width s g N)) (P.code.length (width s g N)) (auxN s P g x B) ω
      (termField s P g x bits pad B i t) cap Z Bc V hT onset K e hb hq o1 o2 h1 h2
  unfold termBud
  fin_cases t
  · exact b1 _ h
  · exact b1 _ (l 0)
  · exact b1 _ (l 1)
  · exact b1 _ (l 2)
  · exact b2 _ _ (l 0) (l 1)
  · exact b2 _ _ (l 0) (l 2)
  · exact b2 _ _ (l 1) (l 2)
  · exact b2 _ _ (l 0) h
  · exact b2 _ _ (l 1) h
  · exact b2 _ _ (l 2) h

/-- **The loop's counter budget.** -/
theorem loopBud_le (cap Z Bc V : ℕ) (onset K e : ℕ)
    (hb : ∀ (c : Call) (w : List Bool), onset ≤ c.n → ctr.budget c w ≤ hotCall c.n + K * ((callWord c).length + 1) ^ e)
    (hq : onset ≤ width s g N) (hL : LoopFit (P := P) ctr ω x bits pad B cap Z Bc V) :
    loopBud s P g x bits pad B ctr ω ≤ 10 * gadgets s g N * (hotCall (width s g N) + K * (10 * Z + 41) ^ e) := by
  unfold loopBud gadgetBud
  calc ∑ a ∈ Finset.range (gadgets s g N), ∑ t : Fin 10, termBud s P g x bits pad B ctr ω a t
      ≤ ∑ _a ∈ Finset.range (gadgets s g N), ∑ _t : Fin 10, (hotCall (width s g N) + K * (10 * Z + 41) ^ e) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun t _ =>
          termBud_le x bits pad B ctr ω cap Z Bc V onset K e hb hq hL.idxZ a (Finset.mem_range.1 ha) t
            (hL.fit a (Finset.mem_range.1 ha) t)
    _ = 10 * gadgets s g N * (hotCall (width s g N) + K * (10 * Z + 41) ^ e) := by
        simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

theorem loopBud_split (cap Z Bc V : ℕ) (onset K e : ℕ)
    (hb : ∀ (c : Call) (w : List Bool), onset ≤ c.n → ctr.budget c w ≤ hotCall c.n + K * ((callWord c).length + 1) ^ e)
    (hq : onset ≤ width s g N) (hL : LoopFit (P := P) ctr ω x bits pad B cap Z Bc V) (tc : ℕ) :
    (300 * tc + 6000) * loopBud s P g x bits pad B ctr ω ≤
      hotOf s g tc N + (300 * tc + 6000) * (10 * gadgets s g N * (K * (10 * Z + 41) ^ e)) := by
  have h := Nat.mul_le_mul_left (300 * tc + 6000) (loopBud_le x bits pad B ctr ω cap Z Bc V onset K e hb hq hL)
  unfold hotOf
  calc _ ≤ _ := h
    _ = _ := by ring

end Loop

end

end NearCubicGates.Close.WorkerArith.WorkerBounds

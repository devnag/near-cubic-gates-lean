import Proof.Gates.Expand.PassDW

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
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp)
open NearCubicGates.Close.Interfaces.Formats

variable {ns nr : ℕ}

section Progs
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

/-- `a := (m − a) mod m` through `C` (`U 4`). -/
def negm (a : Fin 10) : WMX ns nr :=
  .seq (BinW.copy (U 4) (U 7) (R 2) (R 3)) (.seq (BinW.sub (U 4) (U a) (R 2) (R 3))
    (.seq (BinW.inc (U 4) (U 8) (R 2) (R 3)) (.seq (andX (U 4) (U 7) (R 2) (R 3)) (BinW.copy (U a) (U 4) (R 2) (R 3)))))

def negmCost (Wb : ℕ) : ℕ := (41 * Wb + 3) + 1 + ((41 * Wb + 9) + 1 + ((41 * Wb + 7) + 1 + ((41 * Wb + 3) + 1 +
  (41 * Wb + 3))))

end Progs

section Neg
variable {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr} {σ0 σ : WState ns nr} {Wb hd e : ℕ}
  {inp : List Bool} {v : Fin 10 → ℕ} (cap : ℕ)

theorem negmV (W : ℕ) (a : Fin 10) (ha : Scr a) (ha4 : a ≠ 4)
    (h : Post U R σ0 Wb inp hd e v σ) (hv7 : v 7 = 2 ^ W - 1) (hva : v a < 2 ^ W)
    (hmW : 2 ^ W < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (negm U R a) σ (negmCost Wb)
      (Post U R σ0 Wb inp hd e (Function.update (Function.update v 4 ((2 ^ W - v a) % 2 ^ W)) a
        ((2 ^ W - v a) % 2 ^ W))) := by
  have hm : 1 ≤ 2 ^ W := Nat.one_le_two_pow
  refine Runs.seq (opCopy cap 4 7 (by decide) (by decide) (by decide) h hcap) (fun τ1 h1 => ?_)
  rw [hv7] at h1
  have hv7' : v 7 = 2 ^ W - 1 := hv7
  refine Runs.seq (opSub cap 4 a (by decide) ha.ne0 (Ne.symm ha4) h1
    (by rw [Function.update_of_ne ha4, Function.update_self]; omega)
    (by rw [Function.update_self]; omega) hcap) (fun τ2 h2 => ?_)
  simp only [Function.update_self, Function.update_of_ne ha4, Function.update_idem] at h2
  refine Runs.seq (opInc cap 4 8 (by decide) (by decide) (by decide) h2
    (by rw [Function.update_self]; omega) hcap) (fun τ3 h3 => ?_)
  simp only [Function.update_self, Function.update_idem] at h3
  rw [show 2 ^ W - 1 - v a + 1 = 2 ^ W - v a by omega] at h3
  refine Runs.seq (opAnd cap 4 7 (by decide) (by decide) (by decide) h3 hcap) (fun τ4 h4 => ?_)
  simp only [Function.update_self, Function.update_of_ne (by decide : (7 : Fin 10) ≠ 4), Function.update_idem,
    hv7', Nat.and_two_pow_sub_one_eq_mod] at h4
  refine (opCopy cap a 4 ha (by decide) ha4 h4 hcap).post (fun τ5 h5 => ?_)
  simp only [Function.update_of_ne (Ne.symm ha4), Function.update_self] at h5
  exact h5

end Neg

section Progs2
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

def vAdd : WMX ns nr :=
  .seq (pop2 U R) (.seq (BinW.add (U 2) (U 3) (R 2) (R 3)) (.seq (andX (U 2) (U 7) (R 2) (R 3)) (push U R)))
def vSub : WMX ns nr :=
  .seq (pop2 U R) (.seq (negm U R 3) (.seq (BinW.add (U 2) (U 3) (R 2) (R 3))
    (.seq (andX (U 2) (U 7) (R 2) (R 3)) (push U R))))
def vNeg : WMX ns nr := .seq (pop U R) (.seq (negm U R 2) (push U R))
def mulm : WMX ns nr :=
  .seq (BinW.mul (U 2) (U 3) (U 4) (U 5) (R 2) (R 3) (R 4))
    (.seq (andX (U 4) (U 7) (R 2) (R 3)) (BinW.copy (U 2) (U 4) (R 2) (R 3)))
def vMul : WMX ns nr := .seq (pop2 U R) (.seq (mulm U R) (push U R))
def vPow : WMX ns nr :=
  .seq (readNat1 U R) (.seq (pop U R) (.seq (BinW.copy (U 3) (U 2) (R 2) (R 3))
    (.seq (BinW.copy (U 2) (U 8) (R 2) (R 3)) (.seq (.whr (R 1) (.seq (WMX.dec (R 1)) (mulm U R))) (push U R)))))
def vVar : WMX ns nr :=
  .seq (readNat1 U R) (.seq (BinW.copy (U 2) (U 9) (R 2) (R 3))
    (.seq (.whr (R 1) (.seq (WMX.dec (R 1)) (BinW.half (U 2) (R 3)))) (.seq (andX (U 2) (U 8) (R 2) (R 3)) (push U R))))
def vConst : WMX ns nr :=
  .seq (readNat1 U R) (.seq (.ifr (R 1)
      (.seq (WMX.dec (R 1)) (.seq (readBin U R 2 3) (.seq (andX (U 2) (U 7) (R 2) (R 3)) (negm U R 2))))
      (.seq (readBin U R 2 3) (andX (U 2) (U 7) (R 2) (R 3))))
    (push U R))

/-- The value pass's token programs, by tag. -/
def valH : List (WMX ns nr) := [vConst U R, vVar U R, vAdd U R, vNeg U R, vSub U R, vMul U R, vPow U R]

end Progs2

section VSpecs
variable {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr}

/-- The value pass's constants. -/
structure VOK (Wb W : ℕ) : Prop where
  w1 : 1 ≤ W
  wb : W ≤ Wb

def vAddCost (Wb : ℕ) : ℕ := pop2Cost Wb + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + pushCost Wb))

theorem vAdd_spec (cap Wb W t : ℕ) (hW : VOK Wb W) (hcap : 2 * Wb + 1 ≤ cap) :
    HSpec U R cap Wb (2 ^ W) (2 ^ W - 1) t (valAlg W t) (vAdd U R) .add (vAddCost Wb) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm : 2 ≤ 2 ^ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW.w1
  obtain ⟨hmm, h2m, hmW, hsl⟩ := depth_facts xs hm hdep
  refine Runs.seq (pop2V cap (Post.refl hv) (2 ^ W) xs hv1 hv6 hm hxs hdep hcap)
    (fun τ ⟨v2, h2, h21, h22, h23, h2o⟩ => ?_)
  obtain ⟨k6, k7, k8, k9⟩ := keep4 h2o
  have hx : xs.tail.headD 0 < 2 ^ W := Alg.headD_lt (by omega) _ (Alg.tail_lt xs hxs)
  have hy : xs.headD 0 < 2 ^ W := Alg.headD_lt (by omega) _ hxs
  refine Runs.seq (opAdd cap 2 3 (by decide) (by decide) (by decide) h2 (by rw [h22, h23]; omega) hcap)
    (fun ρ h3 => ?_)
  refine Runs.seq (opAnd cap 2 7 (by decide) (by decide) (by decide) h3 hcap) (fun ρ' h4 => ?_)
  simp only [Function.update_self, Function.update_of_ne (by decide : (7 : Fin 10) ≠ 2), Function.update_idem, k7,
    hv7, Nat.and_two_pow_sub_one_eq_mod, h22, h23] at h4
  have hz : (xs.tail.headD 0 + xs.headD 0) % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by omega)
  refine (finishV (k := 2 ^ W - 1) (t := t) cap h4 ((xs.tail.headD 0 + xs.headD 0) % 2 ^ W) xs.tail.tail
    (by simp [h21]) (by simp) (by simp [k6, hv6]) (by simp [k7, hv7]) (by simp [k8, hv8]) (by simp [k9, hv9])
    (hsl _ (by simp; omega) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt _ (Alg.tail_lt xs hxs) y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  simpa [payload, Alg.step, valAlg] using hω.1

theorem two_le_pow {W : ℕ} (h : 1 ≤ W) : 2 ≤ 2 ^ W :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h

def vSubCost (Wb : ℕ) : ℕ :=
  pop2Cost Wb + 1 + (negmCost Wb + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + pushCost Wb)))

theorem vSub_spec (cap Wb W t : ℕ) (hW : VOK Wb W) (hcap : 2 * Wb + 1 ≤ cap) :
    HSpec U R cap Wb (2 ^ W) (2 ^ W - 1) t (valAlg W t) (vSub U R) .sub (vSubCost Wb) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm := two_le_pow hW.w1
  obtain ⟨hmm, h2m, hmW, hsl⟩ := depth_facts xs hm hdep
  refine Runs.seq (pop2V cap (Post.refl hv) (2 ^ W) xs hv1 hv6 hm hxs hdep hcap)
    (fun τ ⟨v2, h2, h21, h22, h23, h2o⟩ => ?_)
  obtain ⟨k6, k7, k8, k9⟩ := keep4 h2o
  have hx : xs.tail.headD 0 < 2 ^ W := Alg.headD_lt (by omega) _ (Alg.tail_lt xs hxs)
  have hy : xs.headD 0 < 2 ^ W := Alg.headD_lt (by omega) _ hxs
  refine Runs.seq (negmV cap W 3 (by decide) (by decide) h2 (by rw [k7, hv7]) (by rw [h23]; exact hy) hmW hcap)
    (fun τ3 h3 => ?_)
  set ny := (2 ^ W - xs.headD 0) % 2 ^ W with hny
  rw [h23] at h3
  have hny_lt : ny < 2 ^ W := Nat.mod_lt _ (by omega)
  refine Runs.seq (opAdd cap 2 3 (by decide) (by decide) (by decide) h3 (by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h22, Function.update_self]; omega)
    hcap) (fun ρ h4 => ?_)
  refine Runs.seq (opAnd cap 2 7 (by decide) (by decide) (by decide) h4 hcap) (fun ρ' h5 => ?_)
  simp only [Function.update_self, Function.update_of_ne (by decide : (7 : Fin 10) ≠ 2),
    Function.update_of_ne (by decide : (7 : Fin 10) ≠ 3), Function.update_of_ne (by decide : (7 : Fin 10) ≠ 4),
    Function.update_of_ne (by decide : (2 : Fin 10) ≠ 3), Function.update_of_ne (by decide : (2 : Fin 10) ≠ 4),
    Function.update_idem, k7, hv7, Nat.and_two_pow_sub_one_eq_mod, h22] at h5
  have hz : (xs.tail.headD 0 + ny) % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by omega)
  refine (finishV (k := 2 ^ W - 1) (t := t) cap h5 ((xs.tail.headD 0 + ny) % 2 ^ W) xs.tail.tail
    (by simp [h21]) (by simp [hny]) (by simp [k6, hv6]) (by simp [k7, hv7]) (by simp [k8, hv8]) (by simp [k9, hv9])
    (hsl _ (by simp; omega) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt _ (Alg.tail_lt xs hxs) y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have e : (valAlg W t).step xs .sub = (xs.tail.headD 0 + ny) % 2 ^ W :: xs.tail.tail := by
    show (xs.tail.headD 0 + (2 ^ W - xs.headD 0)) % 2 ^ W :: _ = _
    rw [hny, Nat.add_mod_mod]
  rw [e]; simpa [payload] using hω.1

def vNegCost (Wb : ℕ) : ℕ := popCost Wb + 1 + (negmCost Wb + 1 + pushCost Wb)

theorem vNeg_spec (cap Wb W t : ℕ) (hW : VOK Wb W) (hcap : 2 * Wb + 1 ≤ cap) :
    HSpec U R cap Wb (2 ^ W) (2 ^ W - 1) t (valAlg W t) (vNeg U R) .neg (vNegCost Wb) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm := two_le_pow hW.w1
  obtain ⟨hmm, h2m, hmW, hsl⟩ := depth_facts xs hm hdep
  refine Runs.seq (pop1V cap (Post.refl hv) (2 ^ W) xs hv1 hv6 hm hxs hdep hcap)
    (fun τ ⟨v2, h2, h21, h22, h2o⟩ => ?_)
  have k6 : v2 6 = 2 ^ W := by rw [h2o 6 (by decide) (by decide) (by decide) (by decide), hv6]
  have k7 : v2 7 = 2 ^ W - 1 := by rw [h2o 7 (by decide) (by decide) (by decide) (by decide), hv7]
  have k8 : v2 8 = 1 := by rw [h2o 8 (by decide) (by decide) (by decide) (by decide), hv8]
  have k9 : v2 9 = t := by rw [h2o 9 (by decide) (by decide) (by decide) (by decide), hv9]
  have hx : xs.headD 0 < 2 ^ W := Alg.headD_lt (by omega) _ hxs
  refine Runs.seq (negmV cap W 2 (by decide) (by decide) h2 k7 (by rw [h22]; exact hx) hmW hcap)
    (fun τ3 h3 => ?_)
  rw [h22] at h3
  have hz : (2 ^ W - xs.headD 0) % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by omega)
  refine (finishV (k := 2 ^ W - 1) (t := t) cap h3 ((2 ^ W - xs.headD 0) % 2 ^ W) xs.tail
    (by simp [h21]) (by simp) (by simp [k6]) (by simp [k7]) (by simp [k8]) (by simp [k9])
    (hsl _ (by simp) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt xs hxs y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  simpa [payload, Alg.step, valAlg] using hω.1

def mulmCost (Wb : ℕ) : ℕ := mulCost Wb + 1 + ((41 * Wb + 3) + 1 + (41 * Wb + 3))

/-- `A := A·B mod 2^W` (`C`, `X` scratch). -/
theorem mulmV (cap W : ℕ) {σ0 σ : WState ns nr} {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ}
    (h : Post U R σ0 Wb inp hd e v σ) (hv7 : v 7 = 2 ^ W - 1) (ha : v 2 < 2 ^ W) (hb : v 3 < 2 ^ W)
    (hmm : 2 ^ W * 2 ^ W ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (mulm U R) σ (mulmCost Wb) (fun τ => ∃ v', Post U R σ0 Wb inp hd e v' τ ∧ v' 2 = v 2 * v 3 % 2 ^ W ∧
      ∀ i : Fin 10, i ≠ 2 → i ≠ 4 → i ≠ 5 → v' i = v i) := by
  have hab : v 2 * v 3 < 2 ^ Wb := lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) hmm
  have hbW : v 3 < 2 ^ Wb := lt_of_lt_of_le hb (le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos W)) hmm)
  refine Runs.seq (opMul cap 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) h hab hbW hcap) (fun τ1 h1 => ?_)
  refine Runs.seq (opAnd cap 4 7 (by decide) (by decide) (by decide) h1 hcap) (fun τ2 h2 => ?_)
  refine (opCopy cap 2 4 (by decide) (by decide) (by decide) h2 hcap).post (fun τ3 h3 => ⟨_, h3, ?_, ?_⟩)
  · simp [hv7, Nat.and_two_pow_sub_one_eq_mod]
  · intro i i2 i4 i5; simp [i2, i4, i5]

def vMulCost (Wb : ℕ) : ℕ := pop2Cost Wb + 1 + (mulmCost Wb + 1 + pushCost Wb)

theorem vMul_spec (cap Wb W t : ℕ) (hW : VOK Wb W) (hcap : 2 * Wb + 1 ≤ cap) :
    HSpec U R cap Wb (2 ^ W) (2 ^ W - 1) t (valAlg W t) (vMul U R) .mul (vMulCost Wb) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm := two_le_pow hW.w1
  obtain ⟨hmm, h2m, hmW, hsl⟩ := depth_facts xs hm hdep
  refine Runs.seq (pop2V cap (Post.refl hv) (2 ^ W) xs hv1 hv6 hm hxs hdep hcap)
    (fun τ ⟨v2, h2, h21, h22, h23, h2o⟩ => ?_)
  obtain ⟨k6, k7, k8, k9⟩ := keep4 h2o
  have hx : xs.tail.headD 0 < 2 ^ W := Alg.headD_lt (by omega) _ (Alg.tail_lt xs hxs)
  have hy : xs.headD 0 < 2 ^ W := Alg.headD_lt (by omega) _ hxs
  refine Runs.seq (mulmV cap W h2 (by rw [k7, hv7]) (by rw [h22]; exact hx) (by rw [h23]; exact hy) hmm hcap)
    (fun ρ ⟨v3, h3, h32, h3o⟩ => ?_)
  rw [h22, h23] at h32
  have hz : xs.tail.headD 0 * xs.headD 0 % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by omega)
  refine (finishV (k := 2 ^ W - 1) (t := t) cap h3 (xs.tail.headD 0 * xs.headD 0 % 2 ^ W) xs.tail.tail
    (by rw [h3o 1 (by decide) (by decide) (by decide), h21]) h32
    (by rw [h3o 6 (by decide) (by decide) (by decide), k6, hv6])
    (by rw [h3o 7 (by decide) (by decide) (by decide), k7, hv7])
    (by rw [h3o 8 (by decide) (by decide) (by decide), k8, hv8])
    (by rw [h3o 9 (by decide) (by decide) (by decide), k9, hv9])
    (hsl _ (by simp; omega) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt _ (Alg.tail_lt xs hxs) y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  simpa [payload, Alg.step, valAlg] using hω.1

/-- A counted loop on `R 1` with a value invariant (the input head does not move). -/
theorem loopVP (cap : ℕ) {σ0 σ : WState ns nr} {Wb hd : ℕ} {inp : List Bool} (body : WMX ns nr) (n c : ℕ)
    (P : ℕ → (Fin 10 → ℕ) → Prop) (h0 : ∃ v, Post U R σ0 Wb inp hd n v σ ∧ P 0 v)
    (hstep : ∀ j < n, ∀ τ v, Post U R σ0 Wb inp hd (n - j - 1) v τ → P j v →
      Runs cap body τ c (fun ρ => ∃ v', Post U R σ0 Wb inp hd (n - j - 1) v' ρ ∧ P (j + 1) v'))
    (hcap : n ≤ cap) :
    Runs cap (.whr (R 1) (.seq (WMX.dec (R 1)) body)) σ (n * (c + 4) + 1)
      (fun ρ => ∃ v', Post U R σ0 Wb inp hd 0 v' ρ ∧ P n v') := by
  obtain ⟨v0, hv0, hp0⟩ := h0
  have key := Runs.count (cap := cap) (K := R 1) (body := body) c n
    (fun j τ => ∃ v, Post U R σ0 Wb inp hd (n - j) v τ ∧ P j v) hcap
    (fun j hj τ ⟨v, hτ, hp⟩ _ => (hstep j hj _ v (hτ.setv1 (n - j - 1)) hp).post (fun ρ ⟨v', hρ, hp'⟩ =>
      ⟨⟨v', by rw [show n - (j + 1) = n - j - 1 by omega]; exact hρ, hp'⟩, hρ.1.r1⟩))
    σ ⟨v0, by simpa using hv0, hp0⟩ hv0.1.r1
  exact key.post (fun τ ⟨⟨v', hτ, hp⟩, _⟩ => ⟨v', by simpa using hτ, hp⟩)

def vPowCost (Wb e : ℕ) : ℕ :=
  (natBitLength e + 2) * (40 * 2 ^ natBitLength e + 40) + 1 + (popCost Wb + 1 + ((41 * Wb + 3) + 1 +
    ((41 * Wb + 3) + 1 + ((e * (mulmCost Wb + 4) + 1) + 1 + pushCost Wb))))

theorem vPow_spec (cap Wb W t e : ℕ) (hW : VOK Wb W) (hcap : 2 * Wb + 1 ≤ cap)
    (hcape : 2 ^ (natBitLength e + 1) ≤ cap) :
    HSpec U R cap Wb (2 ^ W) (2 ^ W - 1) t (valAlg W t) (vPow U R) (.pow e) (vPowCost Wb e) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm := two_le_pow hW.w1
  obtain ⟨hmm, h2m, hmW, hsl⟩ := depth_facts xs hm hdep
  have hx : xs.headD 0 < 2 ^ W := Alg.headD_lt (by omega) _ hxs
  set x := xs.headD 0 with hxd
  have hen : e ≤ cap := by
    have h1 : e < 2 ^ natBitLength e := lt_two_pow_natBitLength e
    have h2 : 2 ^ natBitLength e ≤ 2 ^ (natBitLength e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Runs.seq (readNatV cap (Post.refl hv) e pre rest rfl rfl hcape) (fun τ1 h1 => ?_)
  refine Runs.seq (pop1V cap h1 (2 ^ W) xs hv1 hv6 hm hxs hdep hcap) (fun τ2 ⟨v2, h2, h21, h22, h2o⟩ => ?_)
  have k6 : v2 6 = 2 ^ W := by rw [h2o 6 (by decide) (by decide) (by decide) (by decide), hv6]
  have k7 : v2 7 = 2 ^ W - 1 := by rw [h2o 7 (by decide) (by decide) (by decide) (by decide), hv7]
  have k8 : v2 8 = 1 := by rw [h2o 8 (by decide) (by decide) (by decide) (by decide), hv8]
  have k9 : v2 9 = t := by rw [h2o 9 (by decide) (by decide) (by decide) (by decide), hv9]
  refine Runs.seq (opCopy cap 3 2 (by decide) (by decide) (by decide) h2 hcap) (fun τ3 h3 => ?_)
  refine Runs.seq (opCopy cap 2 8 (by decide) (by decide) (by decide) h3 hcap) (fun τ4 h4 => ?_)
  let P : ℕ → (Fin 10 → ℕ) → Prop := fun j w => w 2 = x ^ j % 2 ^ W ∧ w 3 = x ∧ w 1 = senc (2 ^ W) xs.tail ∧
    w 6 = 2 ^ W ∧ w 7 = 2 ^ W - 1 ∧ w 8 = 1 ∧ w 9 = t
  refine Runs.seq (loopVP cap (mulm U R) e (mulmCost Wb) P ⟨_, h4, ?_⟩ ?_ hen) (fun τ5 ⟨v5, h5, hp5⟩ => ?_)
  · have hW1 := hW.w1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_self, Function.update_of_ne (by decide), k8, pow_zero,
        Nat.one_mod_two_pow (by omega)]
    · rw [Function.update_of_ne (by decide), Function.update_self, h22]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h21]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), k6]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), k7]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), k8]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), k9]
  · intro j _ τ w hτ ⟨p2, p3, p1, p6, p7, p8, p9⟩
    refine (mulmV cap W hτ p7 (by rw [p2]; exact Nat.mod_lt _ (by omega)) (by rw [p3]; exact hx) hmm hcap).post
      (fun ρ ⟨w', hρ, hw2, hwo⟩ => ⟨w', hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [hw2, p2, p3, pow_succ, Nat.mod_mul_mod]
    · rw [hwo 3 (by decide) (by decide) (by decide), p3]
    · rw [hwo 1 (by decide) (by decide) (by decide), p1]
    · rw [hwo 6 (by decide) (by decide) (by decide), p6]
    · rw [hwo 7 (by decide) (by decide) (by decide), p7]
    · rw [hwo 8 (by decide) (by decide) (by decide), p8]
    · rw [hwo 9 (by decide) (by decide) (by decide), p9]
  obtain ⟨p2, _, p1, p6, p7, p8, p9⟩ := hp5
  have hz : x ^ e % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by omega)
  refine (finishV (k := 2 ^ W - 1) (t := t) cap h5 (x ^ e % 2 ^ W) xs.tail p1 p2 p6 p7 p8 p9
    (hsl _ (by simp) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt xs hxs y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have e2 : (valAlg W t).step xs (.pow e) = x ^ e % 2 ^ W :: xs.tail := rfl
  rw [e2]
  simp only [payload]
  exact hω.1

def vVarCost (Wb j : ℕ) : ℕ :=
  (natBitLength j + 2) * (40 * 2 ^ natBitLength j + 40) + 1 + ((41 * Wb + 3) + 1 +
    ((j * ((34 * Wb + 3) + 4) + 1) + 1 + ((41 * Wb + 3) + 1 + pushCost Wb)))

theorem testBit_val (t j W : ℕ) (hW : 1 ≤ W) :
    t / 2 ^ j % 2 = if t.testBit j then 1 % 2 ^ W else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.one_mod_two_pow (by omega)]
  rcases Nat.mod_two_eq_zero_or_one (t / 2 ^ j) with h | h <;> simp [h]

theorem vVar_spec (cap Wb W t j : ℕ) (hW : VOK Wb W) (ht : t < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapj : 2 ^ (natBitLength j + 1) ≤ cap) :
    HSpec U R cap Wb (2 ^ W) (2 ^ W - 1) t (valAlg W t) (vVar U R) (.var j) (vVarCost Wb j) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm := two_le_pow hW.w1
  obtain ⟨hmm, h2m, hmW, hsl⟩ := depth_facts xs hm hdep
  have hjn : j ≤ cap := by
    have h1 : j < 2 ^ natBitLength j := lt_two_pow_natBitLength j
    have h2 : 2 ^ natBitLength j ≤ 2 ^ (natBitLength j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Runs.seq (readNatV cap (Post.refl hv) j pre rest rfl rfl hcapj) (fun τ1 h1 => ?_)
  refine Runs.seq (opCopy cap 2 9 (by decide) (by decide) (by decide) h1 hcap) (fun τ2 h2 => ?_)
  let P : ℕ → (Fin 10 → ℕ) → Prop := fun i w => w 2 = t / 2 ^ i ∧ w 1 = senc (2 ^ W) xs ∧
    w 6 = 2 ^ W ∧ w 7 = 2 ^ W - 1 ∧ w 8 = 1 ∧ w 9 = t
  refine Runs.seq (loopVP cap (BinW.half (U 2) (R 3)) j (34 * Wb + 3) P ⟨_, h2, ?_⟩ ?_ hjn)
    (fun τ3 ⟨v3, h3, hp3⟩ => ?_)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_self, hv9]; simp
    · rw [Function.update_of_ne (by decide), hv1]
    · rw [Function.update_of_ne (by decide), hv6]
    · rw [Function.update_of_ne (by decide), hv7]
    · rw [Function.update_of_ne (by decide), hv8]
    · rw [Function.update_of_ne (by decide), hv9]
  · intro i _ τ w hτ ⟨p2, p1, p6, p7, p8, p9⟩
    have hlt : w 2 < 2 ^ Wb := by rw [p2]; exact lt_of_le_of_lt (Nat.div_le_self _ _) ht
    refine (opHalf cap 2 (by decide) hτ hlt hcap).post (fun ρ hρ => ⟨_, hρ, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [Function.update_self, p2, Nat.div_div_eq_div_mul, pow_succ]
    · rw [Function.update_of_ne (by decide), p1]
    · rw [Function.update_of_ne (by decide), p6]
    · rw [Function.update_of_ne (by decide), p7]
    · rw [Function.update_of_ne (by decide), p8]
    · rw [Function.update_of_ne (by decide), p9]
  obtain ⟨p2, p1, p6, p7, p8, p9⟩ := hp3
  refine Runs.seq (opAnd cap 2 8 (by decide) (by decide) (by decide) h3 hcap) (fun τ4 h4 => ?_)
  rw [p2, p8, Nat.and_one_is_mod] at h4
  have hz : t / 2 ^ j % 2 < 2 ^ W := lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) hm
  refine (finishV (k := 2 ^ W - 1) (t := t) cap h4 (t / 2 ^ j % 2) xs
    (by rw [Function.update_of_ne (by decide), p1]) (by rw [Function.update_self])
    (by rw [Function.update_of_ne (by decide), p6]) (by rw [Function.update_of_ne (by decide), p7])
    (by rw [Function.update_of_ne (by decide), p8]) (by rw [Function.update_of_ne (by decide), p9])
    (hsl _ (by simp) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact hxs y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have e2 : (valAlg W t).step xs (.var j) = t / 2 ^ j % 2 :: xs := by
    show (if t.testBit j then 1 % 2 ^ W else 0) :: xs = _
    rw [testBit_val t j W hW.w1]
  rw [e2]
  simp only [payload]
  exact hω.1

theorem toNat_emod_neg (a : ℤ) (W : ℕ) (ha : a < 0) :
    (a % (2 ^ W : ℤ)).toNat = (2 ^ W - a.natAbs % 2 ^ W) % 2 ^ W := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨a.natAbs, by omega⟩
  rw [Int.natAbs_neg, Int.natAbs_natCast]
  have hle : n % 2 ^ W ≤ 2 ^ W := (Nat.mod_lt _ (Nat.two_pow_pos W)).le
  have key : (((2 ^ W - n % 2 ^ W) % 2 ^ W : ℕ) : ℤ) = (-(n : ℤ)) % 2 ^ W := by
    rw [Int.natCast_mod, Nat.cast_sub hle]
    push_cast
    have h0 : ((2 : ℤ) ^ W) ≡ 0 [ZMOD 2 ^ W] := by unfold Int.ModEq; simp
    have h2 : ((n : ℤ) % 2 ^ W) ≡ (n : ℤ) [ZMOD 2 ^ W] := Int.mod_modEq _ _
    have h3 := h0.sub h2
    rw [zero_sub] at h3
    exact h3
  rw [← key, Int.toNat_natCast]

theorem toNat_emod_nonneg (a : ℤ) (W : ℕ) (ha : 0 ≤ a) : (a % (2 ^ W : ℤ)).toNat = a.natAbs % 2 ^ W := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n : ℤ) := ⟨a.natAbs, by omega⟩
  rw [Int.natAbs_natCast, show ((2 : ℤ) ^ W) = ((2 ^ W : ℕ) : ℤ) by push_cast; rfl, ← Int.natCast_mod,
    Int.toNat_natCast]

def vConstCost (Wb : ℕ) (a : ℤ) : ℕ :=
  (natBitLength (if a < 0 then 1 else 0) + 2) * (40 * 2 ^ natBitLength (if a < 0 then 1 else 0) + 40) + 1 +
    (((1 + 1 + (readBinCost Wb (natBitLength a.natAbs) + 1 + ((41 * Wb + 3) + 1 + negmCost Wb))) + 1) + 1 +
      pushCost Wb)

theorem vConst_spec (cap Wb W t : ℕ) (a : ℤ) (hW : VOK Wb W) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapa : natBitLength a.natAbs + 4 ≤ cap) :
    HSpec U R cap Wb (2 ^ W) (2 ^ W - 1) t (valAlg W t) (vConst U R) (.const a) (vConstCost Wb a) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm := two_le_pow hW.w1
  obtain ⟨hmm, h2m, hmW, hsl⟩ := depth_facts xs hm hdep
  have hW1 : 1 ≤ Wb := le_trans hW.w1 hW.wb
  set s : ℕ := if a < 0 then 1 else 0 with hs
  have hs1 : natBitLength s ≤ 1 := by rw [hs]; split_ifs <;> decide
  have hinp : pre ++ enc true (payload (.const a)) ++ rest =
      pre ++ enc true (natWord s) ++ (enc true (natWord a.natAbs) ++ rest) := by
    simp only [payload, Interfaces.intWord, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append, List.append_assoc, hs]
  have hpow : 2 ^ (natBitLength s + 1) ≤ cap := by
    have : 2 ^ (natBitLength s + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Runs.seq (readNatV cap (Post.refl hv) s pre _ hinp rfl hpow) (fun τ1 h1 => ?_)
  set pre' := pre ++ enc true (natWord s) with hpre'
  have hlen' : pre'.length = pre.length + 2 * (natWord s).length := by
    rw [hpre', List.length_append, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length]; rfl
  have hinp' : pre ++ enc true (payload (.const a)) ++ rest = pre' ++ enc true (natWord a.natAbs) ++ rest := by
    rw [hinp, hpre']; simp only [List.append_assoc]
  have hmod : a.natAbs % 2 ^ Wb % 2 ^ W = a.natAbs % 2 ^ W :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hW.wb)
  -- the branch on the sign
  let Q : WState ns nr → Prop := fun ρ => ∃ w, Post U R σ Wb (pre ++ enc true (payload (.const a)) ++ rest)
    (pre'.length + 2 * (natWord a.natAbs).length) 0 w ρ ∧ w 2 = (a % (2 ^ W : ℤ)).toNat ∧
    w 1 = senc (2 ^ W) xs ∧ w 6 = 2 ^ W ∧ w 7 = 2 ^ W - 1 ∧ w 8 = 1 ∧ w 9 = t
  have hbr : Runs cap (.ifr (R 1)
      (.seq (WMX.dec (R 1)) (.seq (readBin U R 2 3) (.seq (andX (U 2) (U 7) (R 2) (R 3)) (negm U R 2))))
      (.seq (readBin U R 2 3) (andX (U 2) (U 7) (R 2) (R 3)))) τ1
      ((1 + 1 + (readBinCost Wb (natBitLength a.natAbs) + 1 + ((41 * Wb + 3) + 1 + negmCost Wb))) + 1) Q := by
    refine Runs.ifr (fun hne => ?_) (fun h0 => ?_)
    · -- negative constant
      have hsv : s = 1 := by rw [h1.1.r1] at hne; rw [hs] at hne ⊢; split_ifs at hne ⊢ <;> simp_all
      have han : a < 0 := by by_contra hc; rw [hs, if_neg hc] at hsv; exact absurd hsv (by decide)
      have hval : τ1.val (R 1) - 1 = 0 := by rw [h1.1.r1, hsv]
      have hd := WXExec.dec cap (R 1) τ1 (by rw [h1.1.r1]; omega)
      rw [hval] at hd
      refine Runs.seqE hd ?_
      refine Runs.seq (readBinV cap 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (h1.setv1 0)
        hv8 hW1 a.natAbs pre' rest hinp' hlen'.symm (by omega) hcap) (fun ρ1 g1 => ?_)
      set X := a.natAbs % 2 ^ Wb
      set Y := 2 ^ natBitLength a.natAbs % 2 ^ Wb
      have e2a : Function.update (Function.update v 2 X) 3 Y 2 = X := by simp
      have e7 : Function.update (Function.update v 2 X) 3 Y 7 = 2 ^ W - 1 := by simp [hv7]
      refine Runs.seq (opAnd cap 2 7 (by decide) (by decide) (by decide) g1 hcap) (fun ρ2 g2 => ?_)
      rw [e2a, e7, Nat.and_two_pow_sub_one_eq_mod, hmod] at g2
      refine (negmV cap W 2 (by decide) (by decide) g2 (by simp [hv7])
        (by rw [Function.update_self]; exact Nat.mod_lt _ (Nat.two_pow_pos W)) hmW hcap).post
        (fun ρ3 g3 => ⟨_, g3, ?_, ?_, ?_, ?_, ?_, ?_⟩)
      · rw [Function.update_self, Function.update_self, toNat_emod_neg a W han]
      · simp [hv1]
      · simp [hv6]
      · simp [hv7]
      · simp [hv8]
      · simp [hv9]
    · -- nonnegative constant
      have hsv : s = 0 := by rw [h1.1.r1] at h0; exact h0
      have han : 0 ≤ a := by by_contra hc; rw [hs, if_pos (by omega)] at hsv; exact absurd hsv (by decide)
      have h1z : Post U R σ Wb (pre ++ enc true (payload (.const a)) ++ rest) (pre.length + 2 * (natWord s).length)
          0 v τ1 := by rw [← hsv]; exact h1
      set X := a.natAbs % 2 ^ Wb
      set Y := 2 ^ natBitLength a.natAbs % 2 ^ Wb
      have e2a : Function.update (Function.update v 2 X) 3 Y 2 = X := by simp
      have e7 : Function.update (Function.update v 2 X) 3 Y 7 = 2 ^ W - 1 := by simp [hv7]
      have hr : Runs cap (.seq (readBin U R 2 3) (andX (U 2) (U 7) (R 2) (R 3))) τ1
          (readBinCost Wb (natBitLength a.natAbs) + 1 + (41 * Wb + 3)) Q := by
        refine Runs.seq (readBinV cap 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) h1z hv8 hW1
          a.natAbs pre' rest hinp' hlen'.symm (by omega) hcap) (fun ρ1 g1 => ?_)
        refine (opAnd cap 2 7 (by decide) (by decide) (by decide) g1 hcap).post
          (fun ρ2 g2 => ⟨_, g2, ?_, ?_, ?_, ?_, ?_, ?_⟩)
        · rw [Function.update_self, e2a, e7, Nat.and_two_pow_sub_one_eq_mod, hmod, toNat_emod_nonneg a W han]
        · simp [hv1]
        · simp [hv6]
        · simp [hv7]
        · simp [hv8]
        · simp [hv9]
      exact hr.cost (by omega)
  refine Runs.seq hbr (fun τ2 ⟨w, h2, q2, q1, q6, q7, q8, q9⟩ => ?_)
  have hz : (a % (2 ^ W : ℤ)).toNat < 2 ^ W := (valAlg_closed W t).c a
  refine (finishV (k := 2 ^ W - 1) (t := t) cap h2 _ xs q1 q2 q6 q7 q8 q9
    (hsl _ (by simp) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact hxs y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have hl : pre'.length + 2 * (natWord a.natAbs).length = pre.length + 2 * (payload (.const a)).length := by
    rw [hlen']; simp only [payload, Interfaces.intWord, List.length_append, hs]; ring
  rw [hl] at hω
  exact hω.1

end VSpecs

end NearCubicGates.Close.Expand

import Proof.Gates.Expand.Ops2

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

theorem senc_headD (m : ℕ) (xs : List ℕ) : senc m xs = senc m (xs.headD 0 :: xs.tail) := by
  cases xs with
  | nil => simp [senc]
  | cons x xs => rfl

/-- Numeric facts from the stack bound of `HSpec`. -/
theorem depth_facts {m Wb : ℕ} (xs : List ℕ) (hm : 2 ≤ m)
    (hdep : m ^ (xs.length + 2) ≤ 2 ^ Wb) :
    m * m ≤ 2 ^ Wb ∧ 2 * m ≤ 2 ^ Wb ∧ m < 2 ^ Wb ∧
      ∀ ys : List ℕ, ys.length ≤ xs.length + 1 → (∀ y ∈ ys, y < m) → senc m ys < 2 ^ Wb := by
  have h1 : m * m ≤ 2 ^ Wb := by
    refine le_trans ?_ hdep
    rw [← pow_two]; exact Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨h1, by nlinarith, by nlinarith, fun ys hys hy => ?_⟩
  refine lt_of_lt_of_le (senc_lt m ys hy) (le_trans (Nat.pow_le_pow_right (by omega) ?_) hdep)
  omega

section Steps
variable {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr} {σ0 σ : WState ns nr} {Wb hd e : ℕ}
  {inp : List Bool} {v : Fin 10 → ℕ} (cap : ℕ)

/-- Pop one argument into `A` (`0` if the stack is empty). -/
theorem pop1V (h : Post U R σ0 Wb inp hd e v σ) (m : ℕ) (xs : List ℕ) (hv1 : v 1 = senc m xs) (hv6 : v 6 = m)
    (hm : 2 ≤ m) (hxs : ∀ x ∈ xs, x < m) (hdep : m ^ (xs.length + 2) ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (pop U R) σ (popCost Wb) (fun τ => ∃ v', Post U R σ0 Wb inp hd e v' τ ∧ v' 1 = senc m xs.tail ∧
      v' 2 = xs.headD 0 ∧ ∀ i : Fin 10, i ≠ 1 → i ≠ 2 → i ≠ 4 → i ≠ 5 → v' i = v i) := by
  obtain ⟨_, h2m, _, hs⟩ := depth_facts xs hm hdep
  have hx : xs.headD 0 < m := Alg.headD_lt (by omega) xs hxs
  exact popV cap h m _ _ (by rw [hv1, senc_headD]) hv6 hx
    (by rw [← senc_headD]; exact hs xs (by omega) hxs) h2m hcap

/-- Pop two arguments: `A := second`, `B := top`. -/
def pop2 (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WMX ns nr :=
  .seq (pop U R) (.seq (BinW.copy (U 3) (U 2) (R 2) (R 3)) (pop U R))

def pop2Cost (Wb : ℕ) : ℕ := popCost Wb + 1 + ((41 * Wb + 3) + 1 + popCost Wb)

theorem pop2V (h : Post U R σ0 Wb inp hd e v σ) (m : ℕ) (xs : List ℕ) (hv1 : v 1 = senc m xs) (hv6 : v 6 = m)
    (hm : 2 ≤ m) (hxs : ∀ x ∈ xs, x < m) (hdep : m ^ (xs.length + 2) ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (pop2 U R) σ (pop2Cost Wb) (fun τ => ∃ v', Post U R σ0 Wb inp hd e v' τ ∧
      v' 1 = senc m xs.tail.tail ∧ v' 2 = xs.tail.headD 0 ∧ v' 3 = xs.headD 0 ∧
      ∀ i : Fin 10, i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → v' i = v i) := by
  refine Runs.seq (pop1V cap h m xs hv1 hv6 hm hxs hdep hcap) (fun τ ⟨v1, h1, h11, h12, h1o⟩ => ?_)
  refine Runs.seq (opCopy cap 3 2 (by decide) (by decide) (by decide) h1 hcap) (fun ρ h2 => ?_)
  have hxs' : ∀ x ∈ xs.tail, x < m := Alg.tail_lt xs hxs
  have hdep' : m ^ (xs.tail.length + 2) ≤ 2 ^ Wb :=
    le_trans (Nat.pow_le_pow_right (by omega) (by simp)) hdep
  refine (pop1V cap h2 m xs.tail (by simp [h11]) (by simp [h1o 6 (by decide) (by decide) (by decide) (by decide), hv6])
    hm hxs' hdep' hcap).post (fun ω ⟨v3, h3, h31, h32, h3o⟩ => ⟨v3, h3, h31, h32, ?_, ?_⟩)
  · rw [h3o 3 (by decide) (by decide) (by decide) (by decide)]; simp [h12]
  · intro i i1 i2 i3 i4 i5
    rw [h3o i i1 i2 i4 i5]; simp [Function.update_of_ne i3, h1o i i1 i2 i4 i5]

/-- Push the result in `A`: the evaluator is at rest with the new stack. -/
theorem finishV {m k t : ℕ} (h : Post U R σ0 Wb inp hd 0 v σ) (z : ℕ) (r : List ℕ) (hv1 : v 1 = senc m r)
    (hv2 : v 2 = z) (hv6 : v 6 = m) (hv7 : v 7 = k) (hv8 : v 8 = 1) (hv9 : v 9 = t)
    (hs : senc m (z :: r) < 2 ^ Wb) (hm : m < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (push U R) σ (pushCost Wb) (fun τ => EvAt U R Wb m k t inp hd (z :: r) τ ∧
      SameExcept σ0 τ (evS U) (evR R)) := by
  refine (pushV cap h m z r hv1 hv6 hv2 hs hm hcap).post (fun τ ⟨v', h', h'1, h'o⟩ => ⟨?_, h'.2⟩)
  exact h'.1.toAt h'1 (by rw [h'o 6 (by decide) (by decide) (by decide), hv6])
    (by rw [h'o 7 (by decide) (by decide) (by decide), hv7]) (by rw [h'o 8 (by decide) (by decide) (by decide), hv8])
    (by rw [h'o 9 (by decide) (by decide) (by decide), hv9])

end Steps

/-! ## The programs -/

section Progs
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

/-- `A := min A K`. -/
def sat : WMX ns nr := cmov U R 7 2 2 7

def dConst : WMX ns nr :=
  .seq (.wm (Codec.skipInt true (U 0) (R 7) (R 8))) (.seq (BinW.zero (U 2) (U 8) (R 2) (R 3)) (push U R))
def dVar : WMX ns nr :=
  .seq (.wm (Codec.skipNat true (U 0) (R 7) (R 8)))
    (.seq (BinW.copy (U 2) (U 8) (R 2) (R 3)) (.seq (sat U R) (push U R)))
def dMax : WMX ns nr := .seq (pop2 U R) (.seq (cmov U R 2 3 2 3) (push U R))
def wMax : WMX ns nr :=
  .seq (pop2 U R) (.seq (cmov U R 2 3 2 3) (.seq (BinW.inc (U 2) (U 8) (R 2) (R 3)) (.seq (sat U R) (push U R))))
def dMul : WMX ns nr :=
  .seq (pop2 U R) (.seq (BinW.add (U 2) (U 3) (R 2) (R 3)) (.seq (sat U R) (push U R)))
def dPow : WMX ns nr :=
  .seq (readNat1 U R) (.seq (pop U R) (.seq (BinW.copy (U 3) (U 2) (R 2) (R 3))
    (.seq (BinW.zero (U 2) (U 8) (R 2) (R 3))
      (.seq (.whr (R 1) (.seq (WMX.dec (R 1)) (.seq (BinW.add (U 2) (U 3) (R 2) (R 3)) (sat U R)))) (push U R)))))
def wConst : WMX ns nr :=
  .seq (.wm (Codec.skipNat true (U 0) (R 7) (R 8))) (.seq (readSize U R 2 3) (.seq (sat U R) (push U R)))

/-- The degree pass's token programs, by tag. -/
def degH : List (WMX ns nr) := [dConst U R, dVar U R, dMax U R, WMX.skip, dMax U R, dMul U R, dPow U R]
/-- The weight pass's token programs, by tag. -/
def wtH : List (WMX ns nr) := [wConst U R, dVar U R, wMax U R, WMX.skip, wMax U R, dMul U R, dPow U R]

end Progs

end NearCubicGates.Close.Expand

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp)
open NearCubicGates.Close.Interfaces.Formats

variable {ns nr : ℕ}

theorem HSpec.mono {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr} {cap Wb m k t : ℕ} {A : Alg} {P : WMX ns nr}
    {tok : Tok} {c c' : ℕ} (h : HSpec U R cap Wb m k t A P tok c) (hc : c ≤ c') : HSpec U R cap Wb m k t A P tok c' :=
  fun σ pre rest xs hxs hdep hE => (h σ pre rest xs hxs hdep hE).cost hc

theorem ite_lt_max (x y : ℕ) : (if x < y then y else x) = max x y := by split_ifs <;> omega

section Specs
variable {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr}

theorem cmov_at {v : Fin 10 → ℕ} (a b x y i : Fin 10) :
    (if v a < v b then Function.update v x (v y) else v) i = if i = x ∧ v a < v b then v y else v i := by
  by_cases h : v a < v b
  · by_cases hi : i = x
    · subst hi; simp [h]
    · simp [h, hi]
  · simp [h]

/-- `sat` as a value step: `A := min A K` when `U 7` holds `K`. -/
theorem satV (cap : ℕ) {σ0 σ : WState ns nr} {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ}
    (h : Post U R σ0 Wb inp hd e v σ) (hA : v 2 < 2 ^ Wb) (hK : v 7 < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (sat U R) σ (cmovCost Wb) (Post U R σ0 Wb inp hd e (Function.update v 2 (min (v 2) (v 7)))) := by
  refine (opCmov cap 7 2 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h hK hA hcap).post
    (fun τ hτ => ?_)
  have e : (if v 7 < v 2 then Function.update v 2 (v 7) else v) = Function.update v 2 (min (v 2) (v 7)) := by
    by_cases hc : v 7 < v 2
    · rw [if_pos hc, min_eq_right hc.le]
    · rw [if_neg hc, min_eq_left (by omega)]; exact (Function.update_eq_self 2 v).symm
  rw [e] at hτ; exact hτ

def dMaxCost (Wb : ℕ) : ℕ := pop2Cost Wb + 1 + (cmovCost Wb + 1 + pushCost Wb)

theorem dMax_spec (cap Wb K t : ℕ) (A : Alg) (hA : ∀ x y, A.add x y = max x y ∧ A.sub x y = max x y)
    (hK : 1 ≤ K) (hcap : 2 * Wb + 1 ≤ cap) (tok : Tok) (htok : tok = .add ∨ tok = .sub) :
    HSpec U R cap Wb (K + 1) K t A (dMax U R) tok (dMaxCost Wb) := by
  intro σ pre rest xs hxs hdep hE
  have hpay : payload tok = [] := by rcases htok with rfl | rfl <;> rfl
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm : 2 ≤ K + 1 := by omega
  obtain ⟨_, _, hmW, hsl⟩ := depth_facts xs hm hdep
  refine Runs.seq (pop2V cap (Post.refl hv) (K + 1) xs hv1 hv6 hm hxs hdep hcap)
    (fun τ ⟨v2, h2, h21, h22, h23, h2o⟩ => ?_)
  have hx : xs.tail.headD 0 < K + 1 := Alg.headD_lt (by omega) _ (Alg.tail_lt xs hxs)
  have hy : xs.headD 0 < K + 1 := Alg.headD_lt (by omega) _ hxs
  refine Runs.seq (opCmov cap 2 3 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2
    (by rw [h22]; omega) (by rw [h23]; omega) hcap) (fun ρ h3 => ?_)
  have hz : max (xs.tail.headD 0) (xs.headD 0) < K + 1 := max_lt hx hy
  refine (finishV (k := K) (t := t) cap h3 (max (xs.tail.headD 0) (xs.headD 0)) xs.tail.tail ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by omega) hcap).post
    (fun ω hω => ⟨?_, hω.2⟩)
  · rw [cmov_at]; simp [h21]
  · rw [cmov_at]; simp [h22, h23, ite_lt_max]
  · rw [cmov_at]; simp [h2o 6 (by decide) (by decide) (by decide) (by decide) (by decide), hv6]
  · rw [cmov_at]; simp [h2o 7 (by decide) (by decide) (by decide) (by decide) (by decide), hv7]
  · rw [cmov_at]; simp [h2o 8 (by decide) (by decide) (by decide) (by decide) (by decide), hv8]
  · rw [cmov_at]; simp [h2o 9 (by decide) (by decide) (by decide) (by decide) (by decide), hv9]
  · exact hsl _ (by simp; omega) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt _ (Alg.tail_lt xs hxs) y hy')
  · have hω1 := hω.1
    rw [hpay] at hω1 ⊢
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    have e : A.step xs tok = max (xs.tail.headD 0) (xs.headD 0) :: xs.tail.tail := by
      rcases htok with rfl | rfl
      · show A.add _ _ :: _ = _; rw [(hA _ _).1]
      · show A.sub _ _ :: _ = _; rw [(hA _ _).2]
    rw [e]
    exact hω1

theorem min_add_min (a x K : ℕ) : min (min a K + x) K = min (a + x) K := by
  rcases le_total a K with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]; omega

/-- Common frame facts after a chain of scratch steps. -/
theorem keep4 {v w : Fin 10 → ℕ} (h : ∀ i : Fin 10, i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → w i = v i) :
    w 6 = v 6 ∧ w 7 = v 7 ∧ w 8 = v 8 ∧ w 9 = v 9 :=
  ⟨h 6 (by decide) (by decide) (by decide) (by decide) (by decide), h 7 (by decide) (by decide) (by decide)
    (by decide) (by decide), h 8 (by decide) (by decide) (by decide) (by decide) (by decide),
    h 9 (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem neg_spec (cap Wb m k t : ℕ) (A : Alg) (hA : ∀ x, A.neg x = x) :
    HSpec U R cap Wb m k t A WMX.skip .neg 0 := by
  intro σ pre rest xs _ _ hE
  refine ⟨σ, WXExec.skip cap σ, ⟨⟨hE.ev, hE.inp, by simpa [payload] using hE.hd, ?_⟩, SameExcept.refl σ _ _⟩⟩
  show NumOn σ (U 1) Wb (senc m (A.neg (xs.headD 0) :: xs.tail))
  rw [hA, ← senc_headD]; exact hE.stk

def dConstCost (Wb : ℕ) (a : ℤ) : ℕ := Codec.skipIntCost a + 1 + ((41 * Wb + 3) + 1 + pushCost Wb)

theorem dConst_spec (cap Wb K t : ℕ) (A : Alg) (a : ℤ) (hA : A.c a = 0) (hK : 1 ≤ K)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapa : natBitLength a.natAbs + 2 ≤ cap) :
    HSpec U R cap Wb (K + 1) K t A (dConst U R) (.const a) (dConstCost Wb a) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  obtain ⟨_, _, hmW, hsl⟩ := depth_facts xs (by omega : 2 ≤ K + 1) hdep
  refine Runs.seq (skipIntV cap (Post.refl hv) a pre rest rfl rfl hcapa) (fun τ h1 => ?_)
  refine Runs.seq (opZero cap 2 8 (by decide) (by decide) (by decide) h1 hcap) (fun ρ h2 => ?_)
  refine (finishV (k := K) (t := t) cap h2 0 xs (by simp [hv1]) (by simp) (by simp [hv6]) (by simp [hv7])
    (by simp [hv8]) (by simp [hv9]) (hsl _ (by simp) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · omega
      · exact hxs y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have e : A.step xs (.const a) = 0 :: xs := by show A.c a :: xs = _; rw [hA]
  rw [e]; simpa [payload] using hω.1

def dVarCost (Wb j : ℕ) : ℕ := (20 * natBitLength j + 20) + 1 + ((41 * Wb + 3) + 1 + (cmovCost Wb + 1 + pushCost Wb))

theorem dVar_spec (cap Wb K t : ℕ) (A : Alg) (j : ℕ) (hA : A.v j = min 1 K) (hK : 1 ≤ K)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapj : natBitLength j + 1 ≤ cap) :
    HSpec U R cap Wb (K + 1) K t A (dVar U R) (.var j) (dVarCost Wb j) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  obtain ⟨_, _, hmW, hsl⟩ := depth_facts xs (by omega : 2 ≤ K + 1) hdep
  refine Runs.seq (skipNatV cap (Post.refl hv) j pre rest rfl rfl hcapj) (fun τ h1 => ?_)
  refine Runs.seq (opCopy cap 2 8 (by decide) (by decide) (by decide) h1 hcap) (fun ρ h2 => ?_)
  refine Runs.seq (satV cap h2 (by rw [Function.update_self, hv8]; omega)
    (by rw [Function.update_of_ne (by decide), hv7]; omega) hcap) (fun ρ' h3 => ?_)
  refine (finishV (k := K) (t := t) cap h3 (min 1 K) xs (by simp [hv1]) (by simp [hv8, hv7]) (by simp [hv6])
    (by simp [hv7]) (by simp [hv8]) (by simp [hv9]) (hsl _ (by simp) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · omega
      · exact hxs y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have e : A.step xs (.var j) = min 1 K :: xs := by show A.v j :: xs = _; rw [hA]
  rw [e]; simpa [payload] using hω.1

def dMulCost (Wb : ℕ) : ℕ := pop2Cost Wb + 1 + ((41 * Wb + 3) + 1 + (cmovCost Wb + 1 + pushCost Wb))

theorem dMul_spec (cap Wb K t : ℕ) (A : Alg) (hA : ∀ x y, A.mul x y = min (x + y) K) (hK : 1 ≤ K)
    (hcap : 2 * Wb + 1 ≤ cap) :
    HSpec U R cap Wb (K + 1) K t A (dMul U R) .mul (dMulCost Wb) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm : 2 ≤ K + 1 := by omega
  obtain ⟨hmm, _, hmW, hsl⟩ := depth_facts xs hm hdep
  refine Runs.seq (pop2V cap (Post.refl hv) (K + 1) xs hv1 hv6 hm hxs hdep hcap)
    (fun τ ⟨v2, h2, h21, h22, h23, h2o⟩ => ?_)
  obtain ⟨k6, k7, k8, k9⟩ := keep4 h2o
  have hx : xs.tail.headD 0 < K + 1 := Alg.headD_lt (by omega) _ (Alg.tail_lt xs hxs)
  have hy : xs.headD 0 < K + 1 := Alg.headD_lt (by omega) _ hxs
  have h2K : 2 * K < 2 ^ Wb := by nlinarith
  refine Runs.seq (opAdd cap 2 3 (by decide) (by decide) (by decide) h2 (by rw [h22, h23]; omega) hcap)
    (fun ρ h3 => ?_)
  refine Runs.seq (satV cap h3 (by simp only [Function.update_self]; rw [h22, h23]; omega)
    (by rw [Function.update_of_ne (by decide), k7, hv7]; omega) hcap) (fun ρ' h4 => ?_)
  have hz : min (xs.tail.headD 0 + xs.headD 0) K < K + 1 := by omega
  refine (finishV (k := K) (t := t) cap h4 (min (xs.tail.headD 0 + xs.headD 0) K) xs.tail.tail (by simp [h21])
    (by simp [h22, h23, k7, hv7]) (by simp [k6, hv6]) (by simp [k7, hv7]) (by simp [k8, hv8]) (by simp [k9, hv9])
    (hsl _ (by simp; omega) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt _ (Alg.tail_lt xs hxs) y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have e : A.step xs .mul = min (xs.tail.headD 0 + xs.headD 0) K :: xs.tail.tail := by
    show A.mul _ _ :: _ = _; rw [hA]
  rw [e]; simpa [payload] using hω.1

def wMaxCost (Wb : ℕ) : ℕ :=
  pop2Cost Wb + 1 + (cmovCost Wb + 1 + ((41 * Wb + 7) + 1 + (cmovCost Wb + 1 + pushCost Wb)))

theorem wMax_spec (cap Wb K t : ℕ) (A : Alg)
    (hA : ∀ x y, A.add x y = min (max x y + 1) K ∧ A.sub x y = min (max x y + 1) K)
    (hK : 1 ≤ K) (hcap : 2 * Wb + 1 ≤ cap) (tok : Tok) (htok : tok = .add ∨ tok = .sub) :
    HSpec U R cap Wb (K + 1) K t A (wMax U R) tok (wMaxCost Wb) := by
  intro σ pre rest xs hxs hdep hE
  have hpay : payload tok = [] := by rcases htok with rfl | rfl <;> rfl
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm : 2 ≤ K + 1 := by omega
  obtain ⟨hmm, _, hmW, hsl⟩ := depth_facts xs hm hdep
  refine Runs.seq (pop2V cap (Post.refl hv) (K + 1) xs hv1 hv6 hm hxs hdep hcap)
    (fun τ ⟨v2, h2, h21, h22, h23, h2o⟩ => ?_)
  obtain ⟨k6, k7, k8, k9⟩ := keep4 h2o
  have hx : xs.tail.headD 0 < K + 1 := Alg.headD_lt (by omega) _ (Alg.tail_lt xs hxs)
  have hy : xs.headD 0 < K + 1 := Alg.headD_lt (by omega) _ hxs
  refine Runs.seq (opCmov cap 2 3 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2
    (by rw [h22]; omega) (by rw [h23]; omega) hcap) (fun ρ h3 => ?_)
  set z := max (xs.tail.headD 0) (xs.headD 0) with hzd
  have hc2 : (if v2 2 < v2 3 then Function.update v2 2 (v2 3) else v2) 2 = z := by
    rw [cmov_at]
    by_cases hlt : v2 2 < v2 3
    · rw [if_pos ⟨rfl, hlt⟩, h23, hzd]; rw [h22, h23] at hlt; omega
    · rw [if_neg (fun hh => hlt hh.2), h22, hzd]; rw [h22, h23] at hlt; omega
  have hco : ∀ i : Fin 10, i ≠ 2 → (if v2 2 < v2 3 then Function.update v2 2 (v2 3) else v2) i = v2 i := by
    intro i hi; rw [cmov_at]; simp [hi]
  have hzK : z ≤ K := by omega
  refine Runs.seq (opInc cap 2 8 (by decide) (by decide) (by decide) h3
    (by rw [hc2]; omega) hcap) (fun ρ' h4 => ?_)
  refine Runs.seq (satV cap h4 (by rw [Function.update_self, hc2]; omega)
    (by rw [Function.update_of_ne (by decide), hco 7 (by decide), k7, hv7]; omega) hcap) (fun ρ'' h5 => ?_)
  have hz : min (z + 1) K < K + 1 := by omega
  refine (finishV (k := K) (t := t) cap h5 (min (z + 1) K) xs.tail.tail
    (by simp [hco 1 (by decide), h21]) (by simp [hc2, hco 8 (by decide), hco 7 (by decide), k8, hv8, k7, hv7])
    (by simp [hco 6 (by decide), k6, hv6]) (by simp [hco 7 (by decide), k7, hv7])
    (by simp [hco 8 (by decide), k8, hv8]) (by simp [hco 9 (by decide), k9, hv9])
    (hsl _ (by simp; omega) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt _ (Alg.tail_lt xs hxs) y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have hω1 := hω.1
  rw [hpay] at hω1 ⊢
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
  have e : A.step xs tok = min (z + 1) K :: xs.tail.tail := by
    rcases htok with rfl | rfl
    · show A.add _ _ :: _ = _; rw [(hA _ _).1]
    · show A.sub _ _ :: _ = _; rw [(hA _ _).2]
  rw [e]; exact hω1

def powBodyCost (Wb : ℕ) : ℕ := (41 * Wb + 3) + 1 + cmovCost Wb

def dPowCost (Wb e : ℕ) : ℕ :=
  (natBitLength e + 2) * (40 * 2 ^ natBitLength e + 40) + 1 + (popCost Wb + 1 + ((41 * Wb + 3) + 1 +
    ((41 * Wb + 3) + 1 + ((e * (powBodyCost Wb + 4) + 1) + 1 + pushCost Wb))))

theorem dPow_spec (cap Wb K t : ℕ) (A : Alg) (e : ℕ) (hA : ∀ x, A.pow x e = min (e * x) K) (hK : 1 ≤ K)
    (hcap : 2 * Wb + 1 ≤ cap) (hcape : 2 ^ (natBitLength e + 1) ≤ cap) :
    HSpec U R cap Wb (K + 1) K t A (dPow U R) (.pow e) (dPowCost Wb e) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  have hm : 2 ≤ K + 1 := by omega
  obtain ⟨hmm, _, hmW, hsl⟩ := depth_facts xs hm hdep
  have h2K : 2 * K < 2 ^ Wb := by nlinarith
  have hx : xs.headD 0 < K + 1 := Alg.headD_lt (by omega) _ hxs
  set x := xs.headD 0 with hxd
  have hen : e ≤ cap := by
    have h1 : e < 2 ^ natBitLength e := lt_two_pow_natBitLength e
    have h2 : 2 ^ natBitLength e ≤ 2 ^ (natBitLength e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Runs.seq (readNatV cap (Post.refl hv) e pre rest rfl rfl hcape) (fun τ1 h1 => ?_)
  refine Runs.seq (pop1V cap h1 (K + 1) xs hv1 hv6 hm hxs hdep hcap) (fun τ2 ⟨v2, h2, h21, h22, h2o⟩ => ?_)
  have k6 : v2 6 = K + 1 := by rw [h2o 6 (by decide) (by decide) (by decide) (by decide), hv6]
  have k7 : v2 7 = K := by rw [h2o 7 (by decide) (by decide) (by decide) (by decide), hv7]
  have k8 : v2 8 = 1 := by rw [h2o 8 (by decide) (by decide) (by decide) (by decide), hv8]
  have k9 : v2 9 = t := by rw [h2o 9 (by decide) (by decide) (by decide) (by decide), hv9]
  refine Runs.seq (opCopy cap 3 2 (by decide) (by decide) (by decide) h2 hcap) (fun τ3 h3 => ?_)
  refine Runs.seq (opZero cap 2 8 (by decide) (by decide) (by decide) h3 hcap) (fun τ4 h4 => ?_)
  set v4 := Function.update (Function.update v2 3 (v2 2)) 2 0 with hv4
  let vs : ℕ → Fin 10 → ℕ := fun j => Function.update v4 2 (min (j * x) K)
  have hvs0 : v4 = vs 0 := by
    simp only [vs, zero_mul, Nat.zero_min]; rw [hv4, Function.update_idem]
  have hvs3 : ∀ j, vs j 3 = x := by
    intro j; simp only [vs]
    rw [Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), Function.update_self, h22]
  have hvs7 : ∀ j, vs j 7 = K := by intro j; simp [vs, hv4, k7]
  rw [hvs0] at h4
  set hd1 := pre.length + 2 * (natWord e).length
  refine Runs.seq (loopV cap _ e (powBodyCost Wb) (fun _ => hd1) vs h4 ?_ hen) (fun τ5 h5 => ?_)
  · intro j _ τ hτ
    have hvj : vs j 2 = min (j * x) K := by simp [vs]
    refine Runs.seq (opAdd cap 2 3 (by decide) (by decide) (by decide) hτ (by rw [hvj, hvs3]; omega) hcap)
      (fun ρ hρ => ?_)
    refine (satV cap hρ (by rw [Function.update_self, hvj, hvs3]; omega)
      (by rw [Function.update_of_ne (by decide), hvs7]; omega) hcap).post (fun ω hω => ?_)
    have e1 : Function.update (Function.update (vs j) 2 (vs j 2 + vs j 3))
        2 (min (Function.update (vs j) 2 (vs j 2 + vs j 3) 2) (Function.update (vs j) 2 (vs j 2 + vs j 3) 7)) =
        vs (j + 1) := by
      rw [Function.update_idem, Function.update_self, Function.update_of_ne (by decide), hvj, hvs3, hvs7,
        min_add_min]
      simp only [vs, Function.update_idem]
      congr 2; ring
    rw [e1] at hω; exact hω
  have hz : min (e * x) K < K + 1 := by omega
  refine (finishV (k := K) (t := t) cap h5 (min (e * x) K) xs.tail
    (by simp [vs, hv4, h21]) (by simp [vs]) (by simp [vs, hv4, k6]) (by simp [vs, hv4, k7])
    (by simp [vs, hv4, k8]) (by simp [vs, hv4, k9])
    (hsl _ (by simp) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact Alg.tail_lt xs hxs y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have e2 : A.step xs (.pow e) = min (e * x) K :: xs.tail := by show A.pow _ e :: _ = _; rw [hA]
  rw [e2]
  simp only [payload]
  exact hω.1

def wConstCost (Wb : ℕ) (a : ℤ) : ℕ :=
  (20 * natBitLength (if a < 0 then 1 else 0) + 20) + 1 + (readSizeCost Wb (natBitLength a.natAbs) + 1 +
    (cmovCost Wb + 1 + pushCost Wb))

theorem wConst_spec (cap Wb K t : ℕ) (A : Alg) (a : ℤ) (hA : A.c a = min (Nat.size a.natAbs) K) (hK : 1 ≤ K)
    (hW : 1 ≤ Wb) (hcap : 2 * Wb + 1 ≤ cap) (hcapa : natBitLength a.natAbs + 2 ≤ cap)
    (hbits : natBitLength a.natAbs < 2 ^ Wb) :
    HSpec U R cap Wb (K + 1) K t A (wConst U R) (.const a) (wConstCost Wb a) := by
  intro σ pre rest xs hxs hdep hE
  obtain ⟨v, hv, hv1, hv6, hv7, hv8, hv9⟩ := hE.toV
  obtain ⟨_, _, hmW, hsl⟩ := depth_facts xs (by omega : 2 ≤ K + 1) hdep
  set s : ℕ := if a < 0 then 1 else 0 with hs
  have hinp : pre ++ enc true (payload (.const a)) ++ rest =
      pre ++ enc true (natWord s) ++ (enc true (natWord a.natAbs) ++ rest) := by
    simp only [payload, Interfaces.intWord, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append, List.append_assoc, hs]
  have hs1 : natBitLength s + 1 ≤ cap := by
    have : natBitLength s ≤ 1 := by rw [hs]; split_ifs <;> decide
    omega
  refine Runs.seq (skipNatV cap (Post.refl hv) s pre _ hinp rfl hs1) (fun τ1 h1 => ?_)
  set pre' := pre ++ enc true (natWord s) with hpre'
  have hlen' : pre'.length = pre.length + 2 * (natWord s).length := by
    rw [hpre', List.length_append, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length]; rfl
  refine Runs.seq (readSizeV cap 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) h1 hv8 a.natAbs
    pre' rest (by rw [hinp, hpre']; simp only [List.append_assoc]) hlen'.symm hbits hW (by omega) hcap)
    (fun τ2 h2 => ?_)
  refine Runs.seq (satV cap h2 (by
      rw [Function.update_of_ne (by decide), Function.update_self]
      have := size_le_natBitLength a.natAbs; omega)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hv7]; omega) hcap)
    (fun τ3 h3 => ?_)
  have hz : min (Nat.size a.natAbs) K < K + 1 := by omega
  refine (finishV (k := K) (t := t) cap h3 (min (Nat.size a.natAbs) K) xs (by simp [hv1]) (by simp [hv7])
    (by simp [hv6]) (by simp [hv7]) (by simp [hv8]) (by simp [hv9])
    (hsl _ (by simp) (by
      intro y hy'; rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hz
      · exact hxs y hy')) hmW hcap).post (fun ω hω => ⟨?_, hω.2⟩)
  have e2 : A.step xs (.const a) = min (Nat.size a.natAbs) K :: xs := by show A.c a :: xs = _; rw [hA]
  rw [e2]
  have hω1 := hω.1
  have hl : pre'.length + 2 * (natWord a.natAbs).length = pre.length + 2 * (payload (.const a)).length := by
    rw [hlen']; simp only [payload, Interfaces.intWord, List.length_append, hs]; ring
  rw [hl] at hω1
  exact hω1

end Specs

end NearCubicGates.Close.Expand

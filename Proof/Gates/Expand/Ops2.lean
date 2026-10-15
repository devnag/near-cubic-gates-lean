import Proof.Gates.Expand.Ops

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
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp off readNatM readNatM_spec unaryBody unary_loop
  read_enc_bit natWord_getD_payload)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)

variable {ns nr : ℕ}

section Conv
variable {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr}

theorem EvAt.toV {Wb m k t hd : ℕ} {inp : List Bool} {xs : List ℕ} {σ : WState ns nr}
    (h : EvAt U R Wb m k t inp hd xs σ) :
    ∃ v : Fin 10 → ℕ, EvV U R Wb inp hd 0 v σ ∧ v 1 = senc m xs ∧ v 6 = m ∧ v 7 = k ∧ v 8 = 1 ∧ v 9 = t := by
  classical
  have hn : ∀ i : Fin 10, ∃ x, i ∈ [(1 : Fin 10), 2, 3, 4, 5] → NumOn σ (U i) Wb x := by
    intro i
    by_cases hi : i ∈ [(1 : Fin 10), 2, 3, 4, 5]
    · obtain ⟨x, hx⟩ := h.ev.num i hi; exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h' => absurd h' hi⟩
  choose c hc using hn
  let v : Fin 10 → ℕ := fun i => if i = 1 then senc m xs else if i = 6 then m else if i = 7 then k else
    if i = 8 then 1 else if i = 9 then t else c i
  refine ⟨v, ⟨fun i hi => ?_, h.inp, h.hd, h.ev.zero 1 (by decide), fun j _ h11 => h.ev.zero j h11⟩,
    by simp [v], by simp [v], by simp [v], by simp [v], by simp [v]⟩
  fin_cases i
  · exact absurd rfl hi
  · simpa [v] using h.stk
  · simpa [v] using hc 2 (by decide)
  · simpa [v] using hc 3 (by decide)
  · simpa [v] using hc 4 (by decide)
  · simpa [v] using hc 5 (by decide)
  · simpa [v] using h.ev.mm
  · simpa [v] using h.ev.km
  · simpa [v] using h.ev.one
  · simpa [v] using h.ev.pt

theorem EvV.toAt {Wb m k t hd : ℕ} {inp : List Bool} {xs : List ℕ} {v : Fin 10 → ℕ} {σ : WState ns nr}
    (h : EvV U R Wb inp hd 0 v σ) (h1 : v 1 = senc m xs) (h6 : v 6 = m) (h7 : v 7 = k) (h8 : v 8 = 1)
    (h9 : v 9 = t) : EvAt U R Wb m k t inp hd xs σ := by
  have n6 := h.num 6 (by decide); rw [h6] at n6
  have n7 := h.num 7 (by decide); rw [h7] at n7
  have n8 := h.num 8 (by decide); rw [h8] at n8
  have n9 := h.num 9 (by decide); rw [h9] at n9
  have n1 := h.num 1 (by decide); rw [h1] at n1
  refine ⟨⟨fun i hi => ⟨v i, h.num i ?_⟩, n6, n7, n8, n9, fun j hj => ?_⟩, h.inp, h.hd, n1⟩
  · intro e; subst e; simp at hi
  · by_cases hj1 : j = 1
    · subst hj1; exact h.r1
    · exact h.zero j hj1 hj

end Conv

/-! ## Head moves, the payload register, shifts -/

section More
variable {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr} {σ0 σ : WState ns nr} {Wb hd e : ℕ}
  {inp : List Bool} {v : Fin 10 → ℕ} (cap : ℕ)

theorem Post.seth (h : Post U R σ0 Wb inp hd e v σ) (hd' : ℕ) :
    Post U R σ0 Wb inp hd' e v (σ.seth (U 0) hd') := by
  refine ⟨⟨fun i hi => ?_, by simpa using h.1.inp, by simp, by simpa using h.1.r1,
    fun j h1 h2 => by simpa using h.1.zero j h1 h2⟩, SameExcept.trans h.2 (sameExcept_seth σ (by simp [evS]) _)⟩
  have hn := h.1.num i hi
  exact ⟨by simpa using hn.1, by simp [Function.update_of_ne (uN U hi), hn.2]⟩

theorem Post.setv1 (h : Post U R σ0 Wb inp hd e v σ) (e' : ℕ) :
    Post U R σ0 Wb inp hd e' v (σ.setv (R 1) e') := by
  refine ⟨⟨fun i hi => numOn_setv (h.1.num i hi) _ _, by simpa using h.1.inp, by simpa using h.1.hd, by simp,
    fun j h1 h2 => ?_⟩, SameExcept.trans h.2 (sameExcept_setv σ (by simp [evR]) _)⟩
  simp only [WState.setv_val]
  rw [Function.update_of_ne (rN R h1)]
  exact h.1.zero j h1 h2

theorem opShl (a b : Fin 10) (ha : Scr a) (hb : b ≠ 0) (hab : a ≠ b) (h : Post U R σ0 Wb inp hd e v σ)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (BinW.shl (U a) (U b) (R 2) (R 3)) σ (41 * Wb + 8)
      (Post U R σ0 Wb inp hd e (Function.update v a (2 * v a % 2 ^ Wb))) := by
  have hs := BinW.shl_spec cap Wb (uN U hab) (rN R (by decide)) σ _ _ (h.num a ha.ne0) (h.num b hb) (h.reg 2)
    (h.reg 3) hcap
  rw [← NearCubicWires.WireExponent3_5.UnionMachine.Round.binary_mod] at hs
  exact ⟨_, hs, h.sets a ha _⟩

/-! ## Pop and push as value updates -/

theorem popV (h : Post U R σ0 Wb inp hd e v σ) (m x : ℕ) (xs : List ℕ) (hv1 : v 1 = senc m (x :: xs))
    (hv6 : v 6 = m) (hx : x < m) (hs : senc m (x :: xs) < 2 ^ Wb) (h2m : 2 * m ≤ 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (pop U R) σ (popCost Wb) (fun τ => ∃ v', Post U R σ0 Wb inp hd e v' τ ∧ v' 1 = senc m xs ∧
      v' 2 = x ∧ ∀ i : Fin 10, i ≠ 1 → i ≠ 2 → i ≠ 4 → i ≠ 5 → v' i = v i) := by
  have hm : 0 < m := by omega
  have d := opDivmod cap 1 6 4 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h
    (by rw [hv1]; exact hs) (by rw [hv6]; exact hm) (by rw [hv6]; exact h2m) hcap
  refine Runs.seq d (fun τ hτ => ?_)
  refine (opCopy cap 1 4 (by decide) (by decide) (by decide) hτ hcap).post (fun ρ hρ => ⟨_, hρ, ?_, ?_, ?_⟩)
  · simp [Function.update_apply, hv1, hv6, senc_div m x xs hx]
  · simp [Function.update_apply, hv1, hv6, senc_mod m x xs hx]
  · intro i h1 h2 h4 h5
    simp [Function.update_apply, h1, h2, h4, h5]

theorem pushV (h : Post U R σ0 Wb inp hd e v σ) (m x : ℕ) (xs : List ℕ) (hv1 : v 1 = senc m xs)
    (hv6 : v 6 = m) (hv2 : v 2 = x) (hs : senc m (x :: xs) < 2 ^ Wb) (hm : m < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (push U R) σ (pushCost Wb) (fun τ => ∃ v', Post U R σ0 Wb inp hd e v' τ ∧
      v' 1 = senc m (x :: xs) ∧ ∀ i : Fin 10, i ≠ 1 → i ≠ 4 → i ≠ 5 → v' i = v i) := by
  have hsm : senc m xs * m < 2 ^ Wb := by
    have : senc m xs * m ≤ senc m (x :: xs) := by simp only [senc]; rw [mul_comm]; omega
    omega
  have d := opMul cap 1 6 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) h (by rw [hv1, hv6]; exact hsm) (by rw [hv6]; exact hm) hcap
  refine Runs.seq d (fun τ hτ => ?_)
  have e2v : senc m xs * m + x = senc m (x :: xs) := by simp only [senc]; ring
  refine Runs.seq (opAdd cap 4 2 (by decide) (by decide) (by decide) hτ ?_ hcap) (fun ρ hρ => ?_)
  · simp [Function.update_apply, hv1, hv6, hv2]; omega
  refine (opCopy cap 1 4 (by decide) (by decide) (by decide) hρ hcap).post (fun ρ' hρ' => ⟨_, hρ', ?_, ?_⟩)
  · simp [Function.update_apply, hv1, hv6, hv2]; omega
  · intro i h1 h4 h5
    simp [Function.update_apply, h1, h4, h5]

/-! ## Field readers on the marked input -/

theorem skipNatV (h : Post U R σ0 Wb inp hd e v σ) (x : ℕ) (pre rest : List Bool)
    (hinp : inp = pre ++ enc true (natWord x) ++ rest) (hhd : hd = pre.length) (hcap : natBitLength x + 1 ≤ cap) :
    Runs cap (.wm (Codec.skipNat true (U 0) (R 7) (R 8))) σ (20 * natBitLength x + 20)
      (Post U R σ0 Wb inp (pre.length + 2 * (natWord x).length) e v) :=
  ⟨_, WXExec.wm (Codec.skipNat_spec cap true (U 0) (R 7) (R 8) (rN R (by decide)) x pre rest σ
    (by rw [h.1.inp, hinp]) (by rw [h.1.hd, hhd]) (h.reg 7) (h.reg 8) hcap), h.seth _⟩

theorem skipIntV (h : Post U R σ0 Wb inp hd e v σ) (z : ℤ) (pre rest : List Bool)
    (hinp : inp = pre ++ enc true (Interfaces.intWord z) ++ rest) (hhd : hd = pre.length)
    (hcap : natBitLength z.natAbs + 2 ≤ cap) :
    Runs cap (.wm (Codec.skipInt true (U 0) (R 7) (R 8))) σ (Codec.skipIntCost z)
      (Post U R σ0 Wb inp (pre.length + 2 * (Interfaces.intWord z).length) e v) :=
  ⟨_, WXExec.wm (Codec.skipInt_spec cap true (U 0) (R 7) (R 8) (rN R (by decide)) z pre rest σ
    (by rw [h.1.inp, hinp]) (by rw [h.1.hd, hhd]) (h.reg 7) (h.reg 8) hcap), h.seth _⟩

/-- Read a `natWord` field into the payload register `R 1` (which holds `0`). -/
def readNat1 (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WMX ns nr :=
  .wm (readNatM true (U 0) (R 7) (R 8) (R 1) (R 9) (R 10))

theorem readNatV (h : Post U R σ0 Wb inp hd 0 v σ) (x : ℕ) (pre rest : List Bool)
    (hinp : inp = pre ++ enc true (natWord x) ++ rest) (hhd : hd = pre.length)
    (hcap : 2 ^ (natBitLength x + 1) ≤ cap) :
    Runs cap (readNat1 U R) σ ((natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40))
      (Post U R σ0 Wb inp (pre.length + 2 * (natWord x).length) x v) := by
  have hr := readNatM_spec (cap := cap) true (U 0) (R 7) (R 8) (R 1) (R 9) (R 10) (rN R (by decide))
    (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide))
    (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) x pre rest σ
    (by rw [h.1.inp, hinp]) (by rw [h.1.hd, hhd]) (h.reg 7) (h.reg 8) (h.reg 9) (h.reg 10)
    (by rw [h.1.r1]; omega)
  refine ⟨_, WXExec.wm hr, ?_⟩
  rw [h.1.r1, zero_add]
  exact (h.seth _).setv1 x

/-! ## Counted loops on the payload register -/

theorem loopV (body : WMX ns nr) (n c : ℕ) (hds : ℕ → ℕ) (vs : ℕ → Fin 10 → ℕ)
    (h0 : Post U R σ0 Wb inp (hds 0) n (vs 0) σ)
    (hstep : ∀ j < n, ∀ τ, Post U R σ0 Wb inp (hds j) (n - j - 1) (vs j) τ →
      Runs cap body τ c (Post U R σ0 Wb inp (hds (j + 1)) (n - j - 1) (vs (j + 1))))
    (hcap : n ≤ cap) :
    Runs cap (.whr (R 1) (.seq (WMX.dec (R 1)) body)) σ (n * (c + 4) + 1) (Post U R σ0 Wb inp (hds n) 0 (vs n)) := by
  have key := Runs.count (cap := cap) (K := R 1) (body := body) c n
    (fun j τ => Post U R σ0 Wb inp (hds j) (n - j) (vs j) τ) hcap
    (fun j hj τ hτ _ => (hstep j hj _ (hτ.setv1 (n - j - 1))).post (fun ρ hρ => ⟨by
      have : n - (j + 1) = n - j - 1 := by omega
      rw [this]; exact hρ, hρ.1.r1⟩)) σ (by simpa using h0) h0.1.r1
  exact key.post (fun τ hτ => by simpa using hτ.1)

end More

/-! ## Reading a number field into a BinW number -/

section ReadBin
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

/-- Count the unary prefix of a marked `natWord` into `R 1` and step past its `0`. -/
def unary1 : WMX ns nr := .wm (.seq (.inc (R 7)) (.whr (R 7) (unaryBody true (U 0) (R 7) (R 1))))

/-- One payload bit: `if bit then a := a + b`; `b := 2b mod 2^Wb`. -/
def binStep (a b : Fin 10) : WMX ns nr :=
  .seq (WMX.fwd (U 0)) (.seq (.ifs (U 0) (BinW.add (U a) (U b) (R 2) (R 3)) WMX.skip)
    (.seq (WMX.fwd (U 0)) (BinW.shl (U b) (U 8) (R 2) (R 3))))

/-- **`a := x mod 2^Wb`** from a marked `natWord x` (`b` scratch, ends at `2^ℓ mod 2^Wb`). -/
def readBin (a b : Fin 10) : WMX ns nr :=
  .seq (BinW.zero (U a) (U 8) (R 2) (R 3)) (.seq (BinW.copy (U b) (U 8) (R 2) (R 3))
    (.seq (unary1 U R) (.whr (R 1) (.seq (WMX.dec (R 1)) (binStep U R a b)))))

def binStepCost (Wb : ℕ) : ℕ := 1 + 1 + ((41 * Wb + 3 + 1) + 1 + (1 + 1 + (41 * Wb + 8)))

def readBinCost (Wb ℓ : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((3 + 1 + (10 * ℓ + 9)) + 1 + (ℓ * (binStepCost Wb + 4) + 1)))

variable {U R}

theorem mod_two_pow_succ' (x j : ℕ) : x % 2 ^ (j + 1) = x % 2 ^ j + (if x.testBit j then 2 ^ j else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h2 | h2 <;> simp [h2]

/-- The unary prefix of a marked `natWord x` at `pre`: `R 1 := ℓ`, head past the separator. -/
theorem unary1V (cap : ℕ) {σ0 σ : WState ns nr} {Wb hd : ℕ} {inp : List Bool} {v : Fin 10 → ℕ}
    (h : Post U R σ0 Wb inp hd 0 v σ) (x : ℕ) (pre rest : List Bool)
    (hinp : inp = pre ++ enc true (natWord x) ++ rest) (hhd : hd = pre.length) (hcap : natBitLength x + 1 ≤ cap) :
    Runs cap (unary1 U R) σ (3 + 1 + (10 * natBitLength x + 9))
      (Post U R σ0 Wb inp (pre.length + 2 * (natBitLength x + 1)) (natBitLength x) v) := by
  set ℓ := natBitLength x with hℓ
  have hi := WExec.inc (cap := cap) (R 7) σ (by rw [h.reg 7]; omega)
  set σ1 := σ.setv (R 7) (σ.val (R 7) + 1) with hσ1
  have hst : σ1.st (U 0) = pre ++ (enc true (natWord x) ++ rest) := by
    rw [hσ1]; simp only [WState.setv_st]; rw [h.1.inp, hinp, List.append_assoc]
  have hsh : σ1.sh (U 0) = pre.length := by rw [hσ1]; simp only [WState.setv_sh]; rw [h.1.hd, hhd]
  have hlen := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length x
  have hu := unary_loop cap true (U 0) (R 7) (R 1) (rN R (by decide)) (by omega) ℓ σ1
    (by rw [hσ1]; simp [h.reg 7])
    (fun k hk => by
      rw [hst, hsh, Nat.add_assoc,
        NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.read_pre,
        read_enc_bit true rest _ k (by omega)]
      exact NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_getD_one x k hk)
    (by
      rw [hst, hsh, Nat.add_assoc,
        NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.read_pre,
        read_enc_bit true rest _ ℓ (by omega)]
      exact NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_getD_zero x)
    (by rw [hσ1]; simp [h.1.r1]; omega)
  refine ⟨_, WXExec.wm (WExec.seq hi hu), ?_⟩
  have e : ((σ1.seth (U 0) (σ1.sh (U 0) + stp true * ℓ + stp true)).setv (R 1) (σ1.val (R 1) + ℓ)).setv (R 7) 0 =
      ((σ.seth (U 0) (pre.length + 2 * (ℓ + 1))).setv (R 1) ℓ) := by
    have h71 : σ1.val (R 1) = 0 := by rw [hσ1]; simp [Function.update_of_ne (rN R (by decide : (1 : Fin 12) ≠ 7)), h.1.r1]
    rw [h71, hsh, zero_add]
    apply WState.eq
    · rw [hσ1]; simp [stp]; congr 1
    · rfl
    · funext r
      simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      rw [hσ1]
      simp only [WState.setv_val, Function.update_apply]
      by_cases h7 : r = R 7
      · subst h7; simp [rN R (by decide : (7 : Fin 12) ≠ 1), h.reg 7]
      · simp [h7]
    · rfl
  rw [e]
  exact (h.seth _).setv1 ℓ

theorem readBinV (cap : ℕ) {σ0 σ : WState ns nr} {Wb hd : ℕ} {inp : List Bool} {v : Fin 10 → ℕ}
    (a b : Fin 10) (ha : Scr a) (hb : Scr b) (hab : a ≠ b) (ha8 : a ≠ 8) (hb8 : b ≠ 8)
    (h : Post U R σ0 Wb inp hd 0 v σ) (hv8 : v 8 = 1) (hW : 1 ≤ Wb) (x : ℕ) (pre rest : List Bool)
    (hinp : inp = pre ++ enc true (natWord x) ++ rest) (hhd : hd = pre.length)
    (hcap : natBitLength x + 1 ≤ cap) (hcapW : 2 * Wb + 1 ≤ cap) :
    Runs cap (readBin U R a b) σ (readBinCost Wb (natBitLength x))
      (Post U R σ0 Wb inp (pre.length + 2 * (natWord x).length) 0
        (Function.update (Function.update v a (x % 2 ^ Wb)) b (2 ^ natBitLength x % 2 ^ Wb))) := by
  set ℓ := natBitLength x with hℓ
  have hlen := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length x
  have hpow : 1 < 2 ^ Wb := Nat.one_lt_two_pow (by omega)
  refine Runs.seq (opZero cap a 8 ha (by decide) ha8 h hcapW) (fun τ1 h1 => ?_)
  refine Runs.seq (opCopy cap b 8 hb (by decide) hb8 h1 hcapW) (fun τ2 h2 => ?_)
  refine Runs.seq (unary1V cap h2 x pre rest hinp hhd hcap) (fun τ3 h3 => ?_)
  -- the payload loop
  let vs : ℕ → Fin 10 → ℕ := fun j =>
    Function.update (Function.update v a (x % 2 ^ j % 2 ^ Wb)) b (2 ^ j % 2 ^ Wb)
  let hds : ℕ → ℕ := fun j => pre.length + 2 * (ℓ + 1) + 2 * j
  have hv0 : (Function.update (Function.update v a 0) b ((Function.update v a 0) 8)) = vs 0 := by
    simp only [vs, pow_zero, Nat.mod_one, Nat.zero_mod, Function.update_of_ne hb8.symm, Function.update_of_ne ha8.symm,
      hv8, Nat.one_mod_two_pow (by omega : 0 < Wb)]
  rw [hv0] at h3
  have hl := loopV cap (binStep U R a b) ℓ (binStepCost Wb) (fun j => hds j) vs (by simpa [hds] using h3) ?_ (by omega)
  · refine hl.post (fun τ hτ => ?_)
    have hx : x % 2 ^ ℓ = x := Nat.mod_eq_of_lt (lt_two_pow_natBitLength x)
    have e1 : hds ℓ = pre.length + 2 * (natWord x).length := by simp only [hds]; rw [hlen]; ring
    simpa [vs, hx, e1] using hτ
  intro j hj τ hτ
  -- step to the payload cell, branch on the bit, step on, shift
  have hrd : wbit (τ.seth (U 0) (τ.sh (U 0) + 1)) (U 0) = x.testBit j := by
    unfold wbit
    simp only [WState.seth_st, WState.seth_sh, Function.update_self]
    rw [hτ.1.inp, hτ.1.hd, hinp, List.append_assoc]
    have : hds j + 1 = pre.length + (2 * (ℓ + 1 + j) + 1) := by simp only [hds]; ring
    rw [this, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.read_pre]
    have hrb := read_enc_bit true rest (natWord x) (ℓ + 1 + j) (by omega)
    simp only [stp, off, if_true] at hrb
    rw [hrb, natWord_getD_payload x j hj]
  have hf1 := WXExec.fwd (cap := cap) (U 0) τ
  have hP1 : Post U R σ0 Wb inp (hds j + 1) (ℓ - j - 1) (vs j) (τ.seth (U 0) (τ.sh (U 0) + 1)) := by
    have := hτ.seth (hds j + 1); rwa [hτ.1.hd] at *
  have hlt_a : x % 2 ^ j % 2 ^ Wb < 2 ^ Wb := Nat.mod_lt _ (by positivity)
  -- after the conditional add
  have hstep_add : Runs cap (.ifs (U 0) (BinW.add (U a) (U b) (R 2) (R 3)) WMX.skip) (τ.seth (U 0) (τ.sh (U 0) + 1))
      (41 * Wb + 3 + 1) (Post U R σ0 Wb inp (hds j + 1) (ℓ - j - 1)
        (Function.update (vs j) a (x % 2 ^ (j + 1) % 2 ^ Wb))) := by
    have hva : vs j a = x % 2 ^ j % 2 ^ Wb := by simp [vs, hab]
    have hvb : vs j b = 2 ^ j % 2 ^ Wb := by simp [vs]
    by_cases hbit : x.testBit j = true
    · have hw : wbit (τ.seth (U 0) (τ.sh (U 0) + 1)) (U 0) = true := hrd.trans hbit
      have hsum : x % 2 ^ j % 2 ^ Wb + 2 ^ j % 2 ^ Wb < 2 ^ Wb := by
        rcases Nat.lt_or_ge j Wb with hjW | hjW
        · have h1 : x % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
          have h2 : 2 ^ j < 2 ^ Wb := Nat.pow_lt_pow_right (by norm_num) hjW
          have h3 : 2 ^ (j + 1) ≤ 2 ^ Wb := Nat.pow_le_pow_right (by norm_num) hjW
          rw [Nat.mod_eq_of_lt (h1.trans h2), Nat.mod_eq_of_lt h2]
          rw [pow_succ] at h3; omega
        · have : 2 ^ j % 2 ^ Wb = 0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hjW)
          rw [this, add_zero]; exact hlt_a
      have hadd := opAdd cap a b ha hb.ne0 hab hP1 (by rw [hva, hvb]; exact hsum) hcapW
      refine (Runs.ifsT hw hadd).post (fun ρ hρ => ?_)
      have e : vs j a + vs j b = x % 2 ^ (j + 1) % 2 ^ Wb := by
        rw [hva, hvb, mod_two_pow_succ', if_pos hbit, ← Nat.mod_eq_of_lt hsum, ← Nat.add_mod]
      rw [e] at hρ; exact hρ
    · have hw : wbit (τ.seth (U 0) (τ.sh (U 0) + 1)) (U 0) = false := by rw [hrd]; simpa using hbit
      refine (Runs.ifsF hw (Runs.of (WXExec.skip cap _) ?_)).cost (by omega)
      have e : Function.update (vs j) a (x % 2 ^ (j + 1) % 2 ^ Wb) = vs j := by
        rw [mod_two_pow_succ', if_neg hbit, add_zero, ← hva]
        exact Function.update_eq_self a (vs j)
      rw [e]; exact hP1
  refine Runs.seqE hf1 (Runs.seq hstep_add (fun ρ hρ => ?_))
  have hf2 := WXExec.fwd (cap := cap) (U 0) ρ
  have hP2 := hρ.seth (hds j + 2)
  rw [show ρ.sh (U 0) + 1 = hds j + 2 by rw [hρ.1.hd]] at hf2
  refine Runs.seqE hf2 ((opShl cap b 8 hb (by decide) hb8 hP2 hcapW).post (fun ω hω => ?_))
  have e : Function.update (Function.update (vs j) a (x % 2 ^ (j + 1) % 2 ^ Wb)) b
      (2 * Function.update (vs j) a (x % 2 ^ (j + 1) % 2 ^ Wb) b % 2 ^ Wb) = vs (j + 1) := by
    simp only [vs]
    funext i
    by_cases hia : i = a
    · subst hia; simp [hab]
    · by_cases hib : i = b
      · subst hib
        simp [Function.update_of_ne hab.symm, pow_succ, Nat.mul_mod, Nat.mod_mod]
        ring_nf
      · simp [Function.update_of_ne hia, Function.update_of_ne hib]
  rw [e] at hω
  have : hds j + 2 = hds (j + 1) := by simp only [hds]; ring
  rw [this] at hω
  exact hω

end ReadBin

/-! ## The bit length of a number field -/

section ReadSize
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

/-- One payload bit: `if bit then b := 1`; `a := a + 1`. -/
def sizeStep (a b : Fin 10) : WMX ns nr :=
  .seq (WMX.fwd (U 0)) (.seq (.ifs (U 0) (BinW.copy (U b) (U 8) (R 2) (R 3)) WMX.skip)
    (.seq (WMX.fwd (U 0)) (BinW.inc (U a) (U 8) (R 2) (R 3))))

/-- **`a := Nat.size x`** from a marked `natWord x` (`b` scratch, ends at `[x ≠ 0]`). -/
def readSize (a b : Fin 10) : WMX ns nr :=
  .seq (BinW.zero (U a) (U 8) (R 2) (R 3)) (.seq (BinW.zero (U b) (U 8) (R 2) (R 3))
    (.seq (unary1 U R) (.seq (.whr (R 1) (.seq (WMX.dec (R 1)) (sizeStep U R a b))) (cmov U R b 8 a b))))

def sizeStepCost (Wb : ℕ) : ℕ := 1 + 1 + ((41 * Wb + 3 + 1) + 1 + (1 + 1 + (41 * Wb + 7)))

def readSizeCost (Wb ℓ : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((3 + 1 + (10 * ℓ + 9)) + 1 +
    ((ℓ * (sizeStepCost Wb + 4) + 1) + 1 + cmovCost Wb)))

variable {U R}

theorem size_eq_of_ne (x : ℕ) (hx : x ≠ 0) : Nat.size x = natBitLength x := by
  apply le_antisymm (size_le_natBitLength x)
  unfold natBitLength
  exact Nat.lt_size.mpr (Nat.pow_log_le_self 2 hx)

theorem readSizeV (cap : ℕ) {σ0 σ : WState ns nr} {Wb hd : ℕ} {inp : List Bool} {v : Fin 10 → ℕ}
    (a b : Fin 10) (ha : Scr a) (hb : Scr b) (hab : a ≠ b) (ha8 : a ≠ 8) (hb8 : b ≠ 8)
    (h : Post U R σ0 Wb inp hd 0 v σ) (hv8 : v 8 = 1) (x : ℕ) (pre rest : List Bool)
    (hinp : inp = pre ++ enc true (natWord x) ++ rest) (hhd : hd = pre.length)
    (hℓW : natBitLength x < 2 ^ Wb) (hW : 1 ≤ Wb)
    (hcap : natBitLength x + 1 ≤ cap) (hcapW : 2 * Wb + 1 ≤ cap) :
    Runs cap (readSize U R a b) σ (readSizeCost Wb (natBitLength x))
      (Post U R σ0 Wb inp (pre.length + 2 * (natWord x).length) 0
        (Function.update (Function.update v a (Nat.size x)) b (if x = 0 then 0 else 1))) := by
  set ℓ := natBitLength x with hℓ
  have hlen := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length x
  have hpow : 1 < 2 ^ Wb := Nat.one_lt_two_pow (by omega)
  refine Runs.seq (opZero cap a 8 ha (by decide) ha8 h hcapW) (fun τ1 h1 => ?_)
  refine Runs.seq (opZero cap b 8 hb (by decide) hb8 h1 hcapW) (fun τ2 h2 => ?_)
  refine Runs.seq (unary1V cap h2 x pre rest hinp hhd hcap) (fun τ3 h3 => ?_)
  let vs : ℕ → Fin 10 → ℕ := fun j =>
    Function.update (Function.update v a j) b (if x % 2 ^ j = 0 then 0 else 1)
  let hds : ℕ → ℕ := fun j => pre.length + 2 * (ℓ + 1) + 2 * j
  have hv0 : Function.update (Function.update v a 0) b 0 = vs 0 := by simp [vs, Nat.mod_one]
  rw [hv0] at h3
  refine Runs.seq (loopV cap (sizeStep U R a b) ℓ (sizeStepCost Wb) (fun j => hds j) vs
    (by simpa [hds] using h3) ?_ (by omega)) (fun τ4 h4 => ?_)
  · intro j hj τ hτ
    have hrd : wbit (τ.seth (U 0) (τ.sh (U 0) + 1)) (U 0) = x.testBit j := by
      unfold wbit
      simp only [WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hτ.1.inp, hτ.1.hd, hinp, List.append_assoc]
      have : hds j + 1 = pre.length + (2 * (ℓ + 1 + j) + 1) := by simp only [hds]; ring
      rw [this, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.read_pre]
      have hrb := read_enc_bit true rest (natWord x) (ℓ + 1 + j) (by omega)
      simp only [stp, off, if_true] at hrb
      rw [hrb, natWord_getD_payload x j hj]
    have hf1 := WXExec.fwd (cap := cap) (U 0) τ
    have hP1 : Post U R σ0 Wb inp (hds j + 1) (ℓ - j - 1) (vs j) (τ.seth (U 0) (τ.sh (U 0) + 1)) := by
      have := hτ.seth (hds j + 1); rwa [hτ.1.hd] at *
    have hvb : vs j b = if x % 2 ^ j = 0 then 0 else 1 := by simp [vs]
    have hva : vs j a = j := by simp [vs, hab]
    have hcond : Runs cap (.ifs (U 0) (BinW.copy (U b) (U 8) (R 2) (R 3)) WMX.skip) (τ.seth (U 0) (τ.sh (U 0) + 1))
        (41 * Wb + 3 + 1) (Post U R σ0 Wb inp (hds j + 1) (ℓ - j - 1)
          (Function.update (vs j) b (if x % 2 ^ (j + 1) = 0 then 0 else 1))) := by
      by_cases hbit : x.testBit j = true
      · have hw : wbit (τ.seth (U 0) (τ.sh (U 0) + 1)) (U 0) = true := hrd.trans hbit
        have hc := opCopy cap b 8 hb (by decide) hb8 hP1 hcapW
        refine (Runs.ifsT hw hc).post (fun ρ hρ => ?_)
        have e : vs j 8 = (if x % 2 ^ (j + 1) = 0 then 0 else 1) := by
          have : x % 2 ^ (j + 1) ≠ 0 := by
            rw [mod_two_pow_succ', if_pos hbit]; positivity
          simp [vs, this, Function.update_of_ne ha8.symm, Function.update_of_ne hb8.symm, hv8]
        rw [e] at hρ; exact hρ
      · have hw : wbit (τ.seth (U 0) (τ.sh (U 0) + 1)) (U 0) = false := by rw [hrd]; simpa using hbit
        refine (Runs.ifsF hw (Runs.of (WXExec.skip cap _) ?_)).cost (by omega)
        have e : Function.update (vs j) b (if x % 2 ^ (j + 1) = 0 then 0 else 1) = vs j := by
          rw [mod_two_pow_succ', if_neg hbit, add_zero, ← hvb]
          exact Function.update_eq_self b (vs j)
        rw [e]; exact hP1
    refine Runs.seqE hf1 (Runs.seq hcond (fun ρ hρ => ?_))
    have hf2 := WXExec.fwd (cap := cap) (U 0) ρ
    have hP2 := hρ.seth (hds j + 2)
    rw [show ρ.sh (U 0) + 1 = hds j + 2 by rw [hρ.1.hd]] at hf2
    refine Runs.seqE hf2 ((opInc cap a 8 ha (by decide) ha8 hP2 ?_ hcapW).post (fun ω hω => ?_))
    · simp [Function.update_of_ne hab, hva]; omega
    have e : Function.update (Function.update (vs j) b (if x % 2 ^ (j + 1) = 0 then 0 else 1)) a
        (Function.update (vs j) b (if x % 2 ^ (j + 1) = 0 then 0 else 1) a + 1) = vs (j + 1) := by
      simp only [vs]
      funext i
      by_cases hia : i = a
      · subst hia; simp [hab]
      · by_cases hib : i = b
        · subst hib; simp [Function.update_of_ne hab.symm]
        · simp [Function.update_of_ne hia, Function.update_of_ne hib]
    rw [e] at hω
    have : hds j + 2 = hds (j + 1) := by simp only [hds]; ring
    rw [this] at hω
    exact hω
  -- the final correction: `a := 0` when no bit was set
  have hx : x % 2 ^ ℓ = x := Nat.mod_eq_of_lt (lt_two_pow_natBitLength x)
  have hvn8 : vs ℓ 8 = 1 := by simp [vs, Function.update_of_ne ha8.symm, Function.update_of_ne hb8.symm, hv8]
  have hvnb : vs ℓ b = if x = 0 then 0 else 1 := by simp [vs, hx]
  have hvna : vs ℓ a = ℓ := by simp [vs, hab]
  refine (opCmov cap b 8 a b hb.ne0 (by decide) hb8 ha hb.ne0 hab h4 ?_ ?_ hcapW).post (fun ω hω => ?_)
  · rw [hvnb]; split_ifs <;> omega
  · rw [hvn8]; exact hpow
  have e1 : hds ℓ = pre.length + 2 * (natWord x).length := by simp only [hds]; rw [hlen]; ring
  rw [e1] at hω
  have e2 : (if vs ℓ b < vs ℓ 8 then Function.update (vs ℓ) a (vs ℓ b) else vs ℓ) =
      Function.update (Function.update v a (Nat.size x)) b (if x = 0 then 0 else 1) := by
    rw [hvnb, hvn8]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [if_true, Nat.zero_lt_one, if_true, Nat.size_zero]
      funext i
      by_cases hia : i = a
      · subst hia; simp [hab]
      · by_cases hib : i = b
        · subst hib; simp [vs, Function.update_of_ne hab.symm]
        · simp [vs, Function.update_of_ne hia, Function.update_of_ne hib]
    · simp only [if_neg hx0, lt_irrefl, if_false]
      rw [size_eq_of_ne x hx0]
      show Function.update (Function.update v a ℓ) b (if x % 2 ^ ℓ = 0 then 0 else 1) = _
      rw [hx, if_neg hx0]
  rw [e2] at hω
  exact hω

end ReadSize

end NearCubicGates.Close.Expand

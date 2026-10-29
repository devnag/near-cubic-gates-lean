import SourceAdapters.Compile.CNFGenE

/-!
# Token generator, part F: the half-open rank comparator

proof of `lem:multitape-refuter`; proof of `cor:framed-refuter` (the witness is restricted to the lexicographic half-open prefix `[0, high)`, first
bit most significant). `CNFTokens.rankT 0 n high` is a recursion on the witness length; `rankT_loop` restates it as a
forward pass (greedy subtraction of `2^(n-1-i)`, recording one decision bit per step), the constant `0 < rest`, and a
backward pass over the recorded decisions. `rankP` runs exactly these passes, keeping the decisions as the binary
digits of one register (`rkN`), so the backward pass reads them lowest digit first.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! ## The loop shape of `rankT` -/

/-- The remaining bound before step `i`. -/
def rkH (n high : ℕ) : ℕ → ℕ
  | 0 => high
  | i + 1 => if rkH n high i ≤ 2 ^ (n - 1 - i) then rkH n high i else rkH n high i - 2 ^ (n - 1 - i)

/-- The decision of step `i` (`true`: the witness bit may be `1`). -/
def rkD (n high i : ℕ) : Bool := decide (2 ^ (n - 1 - i) < rkH n high i)

/-- The decisions of the first `i` steps as a binary number, first decision most significant. -/
def rkN (n high : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 2 * rkN n high i + (rkD n high i).toNat

def rkPre (n high i : ℕ) : List RTok := if rkD n high i then [.inp i, .neg, .inp i] else [.inp i, .neg]
def rkSuf (n high i : ℕ) : List RTok := if rkD n high i then [.conj, .disj] else [.conj]

theorem rkH_shift (n high : ℕ) : ∀ i, rkH (n + 1) high (i + 1) = rkH n (rkH (n + 1) high 1) i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      have e1 : rkH (n + 1) high (i + 1 + 1) = if rkH (n + 1) high (i + 1) ≤ 2 ^ (n + 1 - 1 - (i + 1)) then
          rkH (n + 1) high (i + 1) else rkH (n + 1) high (i + 1) - 2 ^ (n + 1 - 1 - (i + 1)) := rfl
      have e2 : rkH n (rkH (n + 1) high 1) (i + 1) = if rkH n (rkH (n + 1) high 1) i ≤ 2 ^ (n - 1 - i) then
          rkH n (rkH (n + 1) high 1) i else rkH n (rkH (n + 1) high 1) i - 2 ^ (n - 1 - i) := rfl
      rw [e1, e2, ih, show n + 1 - 1 - (i + 1) = n - 1 - i by omega]

theorem rkD_shift (n high i : ℕ) : rkD (n + 1) high (i + 1) = rkD n (rkH (n + 1) high 1) i := by
  unfold rkD
  rw [rkH_shift, show n + 1 - 1 - (i + 1) = n - 1 - i by omega]

theorem rkPre_shift (n high i : ℕ) :
    (rkPre n (rkH (n + 1) high 1) i).map (shiftTok 1) = rkPre (n + 1) high (i + 1) := by
  unfold rkPre
  rw [rkD_shift]
  split <;> simp [shiftTok]

theorem rkSuf_shift (n high i : ℕ) :
    (rkSuf n (rkH (n + 1) high 1) i).map (shiftTok 1) = rkSuf (n + 1) high (i + 1) := by
  unfold rkSuf
  rw [rkD_shift]
  split <;> simp [shiftTok]

theorem flatMap_range_succ' {β : Type} (n : ℕ) (f : ℕ → List β) :
    (List.range (n + 1)).flatMap f = f 0 ++ (List.range n).flatMap (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

/-- **`rankT` in loop shape.** -/
theorem rankT_loop : ∀ (n high : ℕ), rankT 0 n high = (List.range n).flatMap (rkPre n high) ++
    [.cst (decide (0 < rkH n high n))] ++ (List.range n).flatMap (fun c => rkSuf n high (n - 1 - c)) := by
  intro n
  induction n with
  | zero => intro high; simp [rankT, rkH]
  | succ n ih =>
      intro high
      set h' := rkH (n + 1) high 1 with hh'
      have hsh : rankT 1 n h' = (List.range n).flatMap (fun i => rkPre (n + 1) high (i + 1)) ++
          [.cst (decide (0 < rkH (n + 1) high (n + 1)))] ++
          (List.range n).flatMap (fun c => rkSuf (n + 1) high (n - c)) := by
        rw [rankT_shift, ih, List.map_append, List.map_append, List.map_flatMap, List.map_flatMap,
          rkH_shift]
        congr 1
        · congr 1
          · exact List.flatMap_congr (fun i _ => rkPre_shift n high i)
        · apply List.flatMap_congr
          intro c hc
          rw [List.mem_range] at hc
          rw [rkSuf_shift, show n - 1 - c + 1 = n - c by omega]
      have hsuf : (List.range (n + 1)).flatMap (fun c => rkSuf (n + 1) high (n + 1 - 1 - c)) =
          (List.range n).flatMap (fun c => rkSuf (n + 1) high (n - c)) ++ rkSuf (n + 1) high 0 := by
        rw [List.range_succ, List.flatMap_append]
        simp
      rw [flatMap_range_succ', hsuf]
      have hd0 : rkD (n + 1) high 0 = decide (2 ^ n < high) := by simp [rkD, rkH]
      by_cases hc : high ≤ 2 ^ n
      · have e : h' = high := by simp [hh', rkH, hc]
        have hd : rkD (n + 1) high 0 = false := by rw [hd0]; simp; omega
        rw [rankT, if_pos hc, show rankT 1 n high = rankT 1 n h' by rw [e], hsh]
        simp [rkPre, rkSuf, hd, List.append_assoc]
      · have e : h' = high - 2 ^ n := by simp [hh', rkH, hc]
        have hd : rkD (n + 1) high 0 = true := by rw [hd0]; simp; omega
        rw [rankT, if_neg hc, show rankT 1 n (high - 2 ^ n) = rankT 1 n h' by rw [e], hsh]
        simp [rkPre, rkSuf, hd, List.append_assoc]

theorem rkN_div (n high : ℕ) : ∀ c j, rkN n high (j + c) / 2 ^ c = rkN n high j := by
  intro c
  induction c with
  | zero => intro j; simp
  | succ c ih =>
      intro j
      rw [show j + (c + 1) = j + c + 1 by omega, rkN, pow_succ', ← Nat.div_div_eq_div_mul]
      have hb : (rkD n high (j + c)).toNat ≤ 1 := by cases rkD n high (j + c) <;> simp
      rw [show (2 * rkN n high (j + c) + (rkD n high (j + c)).toNat) / 2 = rkN n high (j + c) by omega, ih]

theorem rkN_bit (n high c : ℕ) (hc : c < n) : rkN n high n / 2 ^ c % 2 = (rkD n high (n - 1 - c)).toNat := by
  have e := rkN_div n high c (n - 1 - c + 1)
  rw [show n - 1 - c + 1 + c = n by omega] at e
  rw [e, rkN]
  have hb : (rkD n high (n - 1 - c)).toNat ≤ 1 := by cases rkD n high (n - 1 - c) <;> simp
  omega

theorem rkN_lt (n high : ℕ) : ∀ i, rkN n high i < 2 ^ i := by
  intro i
  induction i with
  | zero => simp [rkN]
  | succ i ih =>
      rw [rkN, pow_succ]
      have hb : (rkD n high i).toNat ≤ 1 := by cases rkD n high i <;> simp
      omega

/-! ## Cell helpers -/

variable {C : Ctx}

theorem KC.set' {a : DS VV MM} (h : KC a) (x : Fin VV) (hx : x ∉ kcRegs) (v : ℕ) : KC (a.set x v) :=
  h.of_fr (Fr.set a v (show x ∈ [x] by simp)) (fun y hy h' => by simp at h'; subst h'; exact hx hy)

theorem Ext.set_right {a b : DS VV MM} {toks : List RTok} (h : Ext a b toks) (x : Fin VV) (v : ℕ) :
    Ext a (b.set x v) toks := (h.trans (Ext.of_eq (a := b) (b := b.set x v) rfl rfl rfl rfl)).congr (by simp)

theorem Fr.set_right {a b : DS VV MM} {T : List (Fin VV)} (h : Fr a b T) {x : Fin VV} (hx : x ∈ T) (v : ℕ) :
    Fr a (b.set x v) T := h.trans (Fr.set b v hx)

/-- `forP` with an indexed invariant insensitive to the counter. -/
theorem forP_ind (c lim : Fin VV) (body : St VV MM) (hcl : c ≠ lim) (K t : ℕ) (I : ℕ → DS VV MM → Prop)
    (hK : K < 2 ^ C.Wd) (hlim : ∀ i a, I i a → a.env lim = K)
    (hset : ∀ i a v, I i a → I i (a.set c v))
    (hbody : ∀ i < K, ∀ a, I i a → a.env c = i → Hs C body a t (fun b => I (i + 1) b ∧ b.env c = i))
    (a : DS VV MM) (ha : I 0 a) : Hs C (forP c lim body) a (K * (t + 4) + 4) (fun b => I K b) := by
  let J : ℕ → DS VV MM → Prop := fun k b => I k b ∧ b.env c = k
  have hloop := Hs.loopN (C := C) (c := .lt c lim) (s := .seq body (.op (.inc c))) hcl J K (t + 2)
    (fun k hk b hb => by
      obtain ⟨hIb, hcb⟩ := hb
      refine ⟨by simp [Cnd.eval, hcb, hlim k b hIb, hk], ?_⟩
      refine Hs.seq (t1 := t) (t2 := 1) (hbody k hk b hIb hcb) (fun d ⟨hId, hcd⟩ => ?_)
      exact Hs.op (OpEx.inc c d (by rw [hcd]; omega)) ⟨hset _ _ _ hId, by simp [hcd]⟩)
    (fun b hb => by simp [Cnd.eval, hb.2, hlim K b hb.1])
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := K * (t + 2 + 2) + 2) (hs_zero C c a) (fun b hb => ?_)) (by ring_nf; omega)
    (fun b h => h)
  subst hb
  exact Hs.mono (hloop _ ⟨hset 0 a 0 ha, by simp⟩) le_rfl (fun b hb => hb.1)

/-! ## The passes -/

/-- The running bound and the decision digits (generator registers 58, 59). -/
def gH : Fin VV := ⟨58, by decide⟩
def gD : Fin VV := ⟨59, by decide⟩

/-- The registers the rank generator changes. -/
def rkT : List (Fin VV) := [gJ, gH, gP, gD, gX, gE, gK, gT]

/-- The rank generator's context: constants, token cursor at the end, the witness length in `dN`. -/
def RkC (n : ℕ) (a : DS VV MM) : Prop := KC a ∧ TTend a ∧ a.env dN = n

theorem RkC.of {n : ℕ} {a b : DS VV MM} {toks : List RTok} (h : RkC n a) (hE : Ext a b toks) (hF : Fr a b rkT) :
    RkC n b :=
  ⟨h.1.of_fr hF (by decide), h.2.1.of_ext hE, by rw [hF dN (by decide), h.2.2]⟩

/-- `gP := 2^n`. -/
def powP : St VV MM := .seq (.op (.copy gP v1)) (forP gJ dN (.op (.shl gP)))

theorem powP_spec (n : ℕ) (a : DS VV MM) (hR : RkC n a) (hW : 2 ^ (n + 1) ≤ 2 ^ C.Wd) :
    Hs C powP a (n * 5 + 6) (fun b => RkC n b ∧ b.env gP = 2 ^ n ∧ Ext a b [] ∧ Fr a b [gP, gJ]) := by
  have hn : n < 2 ^ C.Wd := lt_of_lt_of_le (Nat.lt_two_pow_self) (le_trans (Nat.pow_le_pow_right (by omega)
    (Nat.le_succ n)) hW)
  refine Hs.seqc (t1 := 1) (t2 := n * (1 + 4) + 4) (hs_copy C gP v1 a (by decide)) (fun b hb => ?_) (by omega)
  subst hb
  have hb0 : RkC n (a.set gP (a.env v1)) := hR.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set a _ (by simp [rkT]))
  refine Hs.mono (forP_ind (C := C) gJ dN (.op (.shl gP)) (by decide) n 1
    (fun i b => RkC n b ∧ b.env gP = 2 ^ i ∧ Ext a b [] ∧ Fr a b [gP, gJ]) hn (fun i b hb => hb.1.2.2)
    (fun i b v hb => ⟨hb.1.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set b v (by simp [rkT])),
      by rw [DS.set_env_ne _ _ (by decide), hb.2.1], hb.2.2.1.set_right _ _, Fr.set_right hb.2.2.2 (by simp) _⟩)
    (fun i hi b hb hbJ => ?_) _ ⟨hb0, by simp [hR.1.one], Ext.of_eq rfl rfl rfl rfl, Fr.set a _ (by simp)⟩)
    le_rfl (fun b hb => hb)
  have h2 : 2 * 2 ^ i < 2 ^ C.Wd := by
    have : 2 ^ (i + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hi
    rw [pow_succ] at this hW; omega
  refine Hs.op (OpEx.shl gP b (by rw [hb.2.1]; exact h2)) ⟨⟨hb.1.of (Ext.of_eq rfl rfl rfl rfl)
    (Fr.set b _ (by simp [rkT])), by rw [DS.set_env_self, hb.2.1, pow_succ]; ring, hb.2.2.1.set_right _ _,
    Fr.set_right hb.2.2.2 (by simp) _⟩, by rw [DS.set_env_ne _ _ (by decide), hbJ]⟩

/-- The arithmetic of a `1` decision: `gH -= gP`, `gD := 2·gD + 1`. -/
def fwdArP : St VV MM := .seq (.op (.sub gH gP)) (.seq (.op (.shl gD)) (.op (.inc gD)))

/-- One forward step (step index in `gJ`, `gP = 2^(n-i)` on entry). -/
def fwdBodyP : St VV MM :=
  .seq (.op (.half gP)) (.seq (emitInp gJ) (.seq (emitR kc3) (.ite (.lt gP gH) (.seq (emitInp gJ) fwdArP)
    (.op (.shl gD)))))

def fwdP : St VV MM := forP gJ dN fwdBodyP

/-- The forward invariant after `i` steps. -/
def FwdI (n high : ℕ) (a0 : DS VV MM) (i : ℕ) (b : DS VV MM) : Prop :=
  RkC n b ∧ b.env gH = rkH n high i ∧ b.env gP = 2 ^ (n - i) ∧ b.env gD = rkN n high i ∧
    Ext a0 b ((List.range i).flatMap (rkPre n high)) ∧ Fr a0 b rkT

theorem fwdBodyP_spec (n high : ℕ) (a0 : DS VV MM) (hW : 2 ^ (n + 1) ≤ 2 ^ C.Wd) (hn8 : 8 * n + 10 < 2 ^ C.Wd)
    (i : ℕ) (hi : i < n) (a : DS VV MM) (hI : FwdI n high a0 i a) (hJ : a.env gJ = i) :
    Hs C fwdBodyP a 25 (fun b => FwdI n high a0 (i + 1) b ∧ b.env gJ = i) := by
  obtain ⟨hR, hH, hP, hD, hE, hF⟩ := hI
  have hni : 2 ^ (n - i) = 2 * 2 ^ (n - 1 - i) := by
    rw [show n - i = n - 1 - i + 1 by omega, pow_succ]; ring
  have hNlt : rkN n high i < 2 ^ i := rkN_lt n high i
  have hpi : 2 ^ (i + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hi
  have hWn : 2 * 2 ^ n ≤ 2 ^ C.Wd := by rw [pow_succ] at hW; omega
  -- halve the power
  refine Hs.seqc (t1 := 1) (t2 := 23) (hs_half C gP a) (fun b1 hb1 => ?_) (by omega)
  subst hb1
  set a1 := a.set gP (a.env gP / 2) with ha1
  have h1P : a1.env gP = 2 ^ (n - 1 - i) := by rw [ha1, DS.set_env_self, hP, hni]; omega
  have hR1 : RkC n a1 := hR.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set a _ (by simp [rkT]))
  have e1 : ∀ y, y ≠ gP → a1.env y = a.env y := fun y hy => DS.set_env_ne _ _ hy
  -- inp i, neg
  refine Hs.seqc (t1 := 5) (t2 := 17) (emitInp_spec gJ (by decide) (by decide) a1 hR1.2.1 hR1.1
    (by rw [e1 gJ (by decide), hJ]; omega)) (fun b2 hb2 => ?_) (by omega)
  obtain ⟨hE2, hF2⟩ := hb2
  rw [e1 gJ (by decide), hJ] at hE2
  have hR2 : RkC n b2 := hR1.of hE2 (Fr.weaken hF2 (by simp [rkT]))
  refine Hs.seqc (t1 := 1) (t2 := 15) (emitR_spec kc3 .neg b2 hR2.2.1 (by rw [hR2.1.k3]; rfl))
    (fun b3 hb3 => ?_) (by omega)
  obtain ⟨hE3, hF3⟩ := hb3
  have hR3 : RkC n b3 := hR2.of hE3 (Fr.weaken hF3 (by simp))
  have e3 : ∀ y, y ≠ gP → y ≠ gX → b3.env y = a.env y := fun y h1 h2 => by
    rw [hF3 y (by simp), hF2 y (by simp [h2]), e1 y h1]
  have e3P : b3.env gP = 2 ^ (n - 1 - i) := by rw [hF3 gP (by simp), hF2 gP (by decide), h1P]
  have hcomm : ∀ x toks, Ext b3 x toks → Ext a0 x ((List.range i).flatMap (rkPre n high) ++
      ([.inp i, .neg] ++ toks)) := fun x toks hx =>
    (hE.trans ((Ext.of_eq rfl rfl rfl rfl : Ext a a1 []).trans (hE2.trans (hE3.trans hx)))).congr (by simp)
  have hfr : ∀ x T, (∀ y ∈ T, y ∈ rkT) → Fr b3 x T → Fr a0 x rkT := fun x T hT hx =>
    hF.trans ((Fr.set a _ (by simp [rkT])).trans ((Fr.weaken hF2 (by simp [rkT])).trans
      ((Fr.weaken hF3 (by simp)).trans (Fr.weaken hx hT))))
  have hpre : ∀ toks, (List.range (i + 1)).flatMap (rkPre n high) =
      (List.range i).flatMap (rkPre n high) ++ ([.inp i, .neg] ++ toks) ↔ rkPre n high i = [.inp i, .neg] ++ toks := by
    intro toks
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simp
  have hnext : n - 1 - i = n - (i + 1) := by omega
  refine Hs.ite (show gP ≠ gH by decide) (fun hc => ?_) (fun hc => ?_)
  · have hd : 2 ^ (n - 1 - i) < rkH n high i := by
      simpa [Cnd.eval, e3P, e3 gH (by decide) (by decide), hH] using hc
    have hdec : rkD n high i = true := by simp [rkD, hd]
    refine Hs.seqc (t1 := 5) (t2 := 5) (emitInp_spec gJ (by decide) (by decide) b3 hR3.2.1 hR3.1
      (by rw [e3 gJ (by decide) (by decide), hJ]; omega)) (fun b4 hb4 => ?_) (by omega)
    obtain ⟨hE4, hF4⟩ := hb4
    rw [e3 gJ (by decide) (by decide), hJ] at hE4
    have e4 : ∀ y, y ≠ gX → b4.env y = b3.env y := fun y hy => hF4 y (by simp [hy])
    have s5 : Hs C fwdArP b4 5 (fun x => x.env gH = rkH n high i - 2 ^ (n - 1 - i) ∧
        x.env gD = 2 * rkN n high i + 1 ∧ Ext b4 x [] ∧ Fr b4 x [gH, gD]) := by
      apply hs_of_wpc
      simp only [fwdArP, wpc, opwp]
      vsimp [e4 gH (by decide), e4 gP (by decide), e4 gD (by decide), e3 gH (by decide) (by decide),
        e3 gD (by decide) (by decide), e3P, hH, hD]
      and_split
      all_goals first | omega | exact Ext.of_eq rfl rfl rfl rfl | fr_tac | skip
      all_goals (have := pow_succ 2 i; omega)
    refine Hs.mono s5 le_rfl ?_
    rintro x ⟨hx1, hx2, hx3, hx4⟩
    refine ⟨⟨hR3.of (hE4.trans hx3) ((Fr.weaken hF4 (by simp [rkT])).trans (Fr.weaken hx4 (by simp [rkT]))),
      by rw [hx1, rkH, if_neg (by omega)], ?_, by rw [hx2, rkN, hdec]; rfl, ?_, ?_⟩, ?_⟩
    · rw [hx4 gP (by decide), e4 gP (by decide), e3P, hnext]
    · exact (hcomm x [.inp i] ((hE4.trans hx3).congr (by simp))).congr ((hpre [.inp i]).2 (by simp [rkPre, hdec])).symm
    · exact hfr x rkT (fun y hy => hy) ((Fr.weaken hF4 (by simp [rkT])).trans (Fr.weaken hx4 (by simp [rkT])))
    · rw [hx4 gJ (by decide), e4 gJ (by decide), e3 gJ (by decide) (by decide), hJ]
  · have hd : ¬ 2 ^ (n - 1 - i) < rkH n high i := by
      simpa [Cnd.eval, e3P, e3 gH (by decide) (by decide), hH] using hc
    have hdec : rkD n high i = false := by simp [rkD, hd]
    have hDv : b3.env gD = rkN n high i := by rw [e3 gD (by decide) (by decide), hD]
    refine Hs.mono (Hs.op (OpEx.shl gD b3 (by rw [hDv]; have := pow_succ 2 i; omega)) rfl) (by omega) ?_
    rintro x rfl
    refine ⟨⟨hR3.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set b3 _ (by simp [rkT])), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), e3 gH (by decide) (by decide), hH, rkH, if_pos (by omega)]
    · rw [DS.set_env_ne _ _ (by decide), e3P, hnext]
    · rw [DS.set_env_self, hDv, rkN, hdec]; simp
    · exact (hcomm _ [] ((Ext.refl b3).set_right gD _)).congr ((hpre []).2 (by simp [rkPre, hdec])).symm
    · exact hfr _ [gD] (by simp [rkT]) (Fr.set b3 _ (by simp))
    · rw [DS.set_env_ne _ _ (by decide), e3 gJ (by decide) (by decide), hJ]

/-- One backward step (step index `c` in `gJ`, `gD = rkN n / 2^c` on entry). -/
def bwdBodyP : St VV MM :=
  .seq (emitR kc4) (.seq (.op (.dm gD v2 gE gK)) (.seq (.ite (.eq gK v1) (emitR kc5) (.op (.zero gT)))
    (.op (.copy gD gE))))

def bwdP : St VV MM := forP gJ dN bwdBodyP

/-- The backward invariant after `c` steps (tokens counted from the backward pass's start). -/
def BwdI (n high : ℕ) (a0 : DS VV MM) (c : ℕ) (b : DS VV MM) : Prop :=
  RkC n b ∧ b.env gD = rkN n high n / 2 ^ c ∧
    Ext a0 b ((List.range c).flatMap (fun c => rkSuf n high (n - 1 - c))) ∧ Fr a0 b rkT

theorem bwdBodyP_spec (n high : ℕ) (a0 : DS VV MM) (hW : 2 ^ (n + 1) ≤ 2 ^ C.Wd)
    (c : ℕ) (hc : c < n) (a : DS VV MM) (hI : BwdI n high a0 c a) (hJ : a.env gJ = c) :
    Hs C bwdBodyP a 10 (fun b => BwdI n high a0 (c + 1) b ∧ b.env gJ = c) := by
  obtain ⟨hR, hD, hE, hF⟩ := hI
  have hW4 : 4 ≤ 2 ^ C.Wd := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ] at hW; omega
  refine Hs.seqc (t1 := 1) (t2 := 8) (emitR_spec kc4 .conj a hR.2.1 (by rw [hR.1.k4]; rfl)) (fun b1 hb1 => ?_)
    (by omega)
  obtain ⟨hE1, hF1⟩ := hb1
  have hR1 : RkC n b1 := hR.of hE1 (Fr.weaken hF1 (by simp))
  have e1 : ∀ y, b1.env y = a.env y := fun y => hF1 y (by simp)
  refine Hs.seqc (t1 := 1) (t2 := 6) (hs_dm C gD v2 gE gK b1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hR1.1.two]; omega) (by rw [hR1.1.two]; omega)) (fun b2 hb2 => ?_) (by omega)
  subst hb2
  set b2 := (b1.set gE (b1.env gD / b1.env v2)).set gK (b1.env gD % b1.env v2) with hb2
  have hFb2 : Fr b1 b2 [gE, gK] := by rw [hb2]; fr_tac
  have hR2 : RkC n b2 := hR1.of (Ext.of_eq rfl rfl rfl rfl) (Fr.weaken hFb2 (by simp [rkT]))
  have hK : b2.env gK = (rkD n high (n - 1 - c)).toNat := by
    rw [hb2, DS.set_env_self, e1, hR1.1.two, hD, rkN_bit n high c hc]
  have hEv : b2.env gE = rkN n high n / 2 ^ (c + 1) := by
    rw [hb2, DS.set_env_ne _ _ (by decide), DS.set_env_self, e1, hR1.1.two, hD, pow_succ,
      Nat.div_div_eq_div_mul]
  have hsuf : ∀ toks, (List.range (c + 1)).flatMap (fun c => rkSuf n high (n - 1 - c)) =
      (List.range c).flatMap (fun c => rkSuf n high (n - 1 - c)) ++ ([.conj] ++ toks) ↔
        rkSuf n high (n - 1 - c) = [.conj] ++ toks := by
    intro toks
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simp
  have hfin : ∀ x toks, Ext b2 x toks → Fr b2 x [gT] → rkSuf n high (n - 1 - c) = [.conj] ++ toks →
      Hs C (.op (.copy gD gE)) x 1 (fun b => BwdI n high a0 (c + 1) b ∧ b.env gJ = c) := by
    intro x toks hx hfx hs
    refine Hs.op (OpEx.copy gD gE x (by decide)) ⟨⟨hR2.of hx (Fr.weaken hfx (by simp [rkT])) |>.of
      (Ext.of_eq rfl rfl rfl rfl) (Fr.set x _ (by simp [rkT])), ?_, ?_, ?_⟩, ?_⟩
    · rw [DS.set_env_self, hfx gE (by decide), hEv]
    · exact ((hE.trans (hE1.trans ((Ext.of_eq rfl rfl rfl rfl : Ext b1 b2 []).trans hx))).set_right _ _).congr
        (by rw [(hsuf toks).2 hs]; simp)
    · exact hF.trans ((Fr.weaken hF1 (by simp)).trans ((Fr.weaken hFb2
        (by simp [rkT])).trans ((Fr.weaken hfx (by simp [rkT])).trans (Fr.set x _ (by simp [rkT])))))
    · rw [DS.set_env_ne _ _ (by decide), hfx gJ (by decide), hb2, DS.set_env_ne _ _ (by decide),
        DS.set_env_ne _ _ (by decide), e1, hJ]
  refine Hs.seqc (t1 := 3) (t2 := 1) (R1 := fun x => ∃ toks, Ext b2 x toks ∧ Fr b2 x [gT] ∧
      rkSuf n high (n - 1 - c) = [.conj] ++ toks)
    (Hs.ite (show gK ≠ v1 by decide) (fun hc1 => ?_) (fun hc1 => ?_)) (fun x ⟨toks, hx, hfx, hs⟩ =>
      hfin x toks hx hfx hs) (by omega)
  · have hd : rkD n high (n - 1 - c) = true := by
      have : b2.env gK = 1 := by simpa [Cnd.eval, hR2.1.one] using hc1
      rw [hK] at this; cases h : rkD n high (n - 1 - c) <;> simp_all
    refine Hs.mono (emitR_spec kc5 .disj b2 hR2.2.1 (by rw [hR2.1.k5]; rfl)) (by omega) ?_
    rintro x ⟨hx1, hx2⟩
    exact ⟨[.disj], hx1, Fr.weaken hx2 (by simp), by simp [rkSuf, hd]⟩
  · have hd : rkD n high (n - 1 - c) = false := by
      have : ¬ b2.env gK = 1 := by simpa [Cnd.eval, hR2.1.one] using hc1
      rw [hK] at this; cases h : rkD n high (n - 1 - c) <;> simp_all
    refine Hs.mono (hs_zero C gT b2) (by omega) ?_
    rintro x rfl
    exact ⟨[], Ext.of_eq rfl rfl rfl rfl, Fr.set b2 _ (by simp), by simp [rkSuf, hd]⟩

/-- **The rank comparator** (`rankT 0 n high`, `high` in `dH`). -/
def rankP : St VV MM :=
  .seq (.op (.copy gH dH)) (.seq powP (.seq (.op (.zero gD)) (.seq fwdP (.seq (cstP (.lt vZ gH)) bwdP))))

def rankCost (n : ℕ) : ℕ := 50 * n + 40

theorem rankP_spec (n high : ℕ) (a : DS VV MM) (hR : RkC n a) (hH : a.env dH = high)
    (hW : 2 ^ (n + 1) ≤ 2 ^ C.Wd) (hn8 : 8 * n + 10 < 2 ^ C.Wd) :
    Hs C rankP a (rankCost n) (fun b => Ext a b (rankT 0 n high) ∧ Fr a b rkT) := by
  have hn : n < 2 ^ C.Wd := by omega
  refine Hs.seqc (t1 := 1) (t2 := 50 * n + 38) (hs_copy C gH dH a (by decide)) (fun b1 hb1 => ?_)
    (by unfold rankCost; omega)
  subst hb1
  set a1 := a.set gH (a.env dH) with ha1
  have hR1 : RkC n a1 := hR.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set a _ (by simp [rkT]))
  have hF1 : Fr a a1 rkT := Fr.set a _ (by simp [rkT])
  refine Hs.seqc (t1 := n * 5 + 6) (t2 := 45 * n + 31) (powP_spec n a1 hR1 hW) (fun b2 hb2 => ?_) (by omega)
  obtain ⟨hR2, hP2, hE2, hF2⟩ := hb2
  have h2H : b2.env gH = high := by rw [hF2 gH (by decide), ha1, DS.set_env_self, hH]
  refine Hs.seqc (t1 := 1) (t2 := 45 * n + 29) (hs_zero C gD b2) (fun b3 hb3 => ?_) (by omega)
  subst hb3
  set b3 := b2.set gD 0 with hb3
  have hI0 : FwdI n high b3 0 b3 := ⟨hR2.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set b2 _ (by simp [rkT])),
    by rw [hb3, DS.set_env_ne _ _ (by decide), h2H]; rfl, by rw [hb3, DS.set_env_ne _ _ (by decide), hP2]; simp,
    by simp [hb3, rkN], Ext.of_eq rfl rfl rfl rfl, Fr.refl _ _⟩
  refine Hs.seqc (t1 := n * (25 + 4) + 4) (t2 := 16 * n + 18) (forP_ind (C := C) gJ dN fwdBodyP (by decide) n 25
    (FwdI n high b3) hn (fun i b hb => hb.1.2.2)
    (fun i b v hb => ⟨hb.1.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set b v (by simp [rkT])),
      by rw [DS.set_env_ne _ _ (by decide), hb.2.1], by rw [DS.set_env_ne _ _ (by decide), hb.2.2.1],
      by rw [DS.set_env_ne _ _ (by decide), hb.2.2.2.1], hb.2.2.2.2.1.set_right _ _,
      Fr.set_right hb.2.2.2.2.2 (by simp [rkT]) _⟩)
    (fun i hi b hb hbJ => fwdBodyP_spec n high b3 hW hn8 i hi b hb hbJ) b3 hI0) (fun b4 hb4 => ?_) (by omega)
  obtain ⟨hR4, hH4, -, hD4, hE4, hF4⟩ := hb4
  refine Hs.seqc (t1 := 2) (t2 := 14 * n + 15) (cstP_spec (.lt vZ gH) (show vZ ≠ gH by decide) b4 hR4.2.1 hR4.1)
    (fun b5 hb5 => ?_) (by omega)
  obtain ⟨hE5, hF5⟩ := hb5
  have hR5 : RkC n b5 := hR4.of hE5 (Fr.weaken hF5 (by simp))
  have hI0' : BwdI n high b5 0 b5 := ⟨hR5, by rw [hF5 gD (by simp), hD4]; simp, Ext.of_eq rfl rfl rfl rfl,
    Fr.refl _ _⟩
  refine Hs.mono (forP_ind (C := C) gJ dN bwdBodyP (by decide) n 10 (BwdI n high b5) hn (fun i b hb => hb.1.2.2)
    (fun i b v hb => ⟨hb.1.of (Ext.of_eq rfl rfl rfl rfl) (Fr.set b v (by simp [rkT])),
      by rw [DS.set_env_ne _ _ (by decide), hb.2.1], hb.2.2.1.set_right _ _, Fr.set_right hb.2.2.2 (by simp [rkT]) _⟩)
    (fun c hc b hb hbJ => bwdBodyP_spec n high b5 hW c hc b hb hbJ) b5 hI0') (by omega) ?_
  rintro b6 ⟨_, _, hE6, hF6⟩
  refine ⟨(((Ext.of_eq rfl rfl rfl rfl : Ext a a1 []).trans hE2).trans ((Ext.of_eq rfl rfl rfl rfl :
    Ext b2 b3 []).trans (hE4.trans (hE5.trans hE6)))).congr ?_, ?_⟩
  · rw [rankT_loop]
    simp [Cnd.eval, hH4, hR4.1.z]
  · exact hF1.trans ((Fr.weaken hF2 (by simp [rkT])).trans ((Fr.set b2 _ (by simp [rkT])).trans (hF4.trans
      ((Fr.weaken hF5 (by simp)).trans hF6))))

end NearCubicGates.Adapters.Compile

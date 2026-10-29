import SourceAdapters.ShortPCP.Machines.FLangMainQ2
import SourceAdapters.ShortPCP.Machines.FLangRun
import SourceAdapters.ShortPCP.Machines.WidthPrefix
import SourceAdapters.ShortPCP.Machines.ReaderStage

/-!
# Single-run time: the cell stages and the join

proof of `thm:short-pcp-ours` (`V0` runs in time `poly(n, log T)`), (non-adaptive queries), `lem:patch-r` (`V1`),
 (the run X5(a) compiles): the two ordinary stages of `singleRunTime_of_stages` are the `FL` programs
`mainQ` (query half) and `mainD` (decision half), run as cell programs (`FL.flWF`) and as oracle programs without
queries (`oracleOfProgram_runs`). Their budgets are polynomial in `|data| + |R| + 1` (`FL.flBudget_le`: the width
prefix `1^n 0` has `n = size |input|`, so `64^n ≤ 64·|input|^6`), the reader word is polynomially long, and every
address is below `2^(12·|data| + 40)`. **`singleRunTime : Joins.SingleRunTime`.**
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Time

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Close.Cells (leadOnes langBudget VV MM)
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-! ## Sizes -/

theorem leadOnes_pre (w : List Bool) : ∀ s : ℕ, leadOnes (List.replicate s true ++ false :: w) = s
  | 0 => rfl
  | s + 1 => by rw [List.replicate_succ, List.cons_append]; simp [leadOnes, leadOnes_pre w s]

theorem data_ge (q : Request) : 11 ≤ q.data.length := by
  rw [data_eq q]
  simp only [pieces, List.flatten_cons, List.flatten_nil, List.length_append, List.length_nil]
  have := natWord_pos q.code.f; have := natWord_pos q.code.irr
  have := listWord_pos natWord q.code.hBasis; have := natWord_pos q.code.hOffset
  have := listWord_pos NearCubicGates.Adapters.ACSP.Affine.Instance.pairWord q.code.nbr
  have := listWord_pos gateWord q.code.cons
  have := listWord_pos natWord q.code.iBasis
  have := natWord_pos q.code.iOffset; have := frame_pos q.xbar; have := natWord_pos q.dB
  have := listWord_pos frame q.masks
  omega

theorem input_len (q : Request) (R : List Bool) :
    (q.input R).length = 2 * q.data.length + 2 * R.length + 2 := by
  simp only [Request.input, List.length_append, frame_len]; ring

theorem two_pow_size_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.size m ≤ 2 * m := by
  obtain ⟨k, hk⟩ : ∃ k, Nat.size m = k + 1 := ⟨Nat.size m - 1, by have := Nat.size_pos.2 hm; omega⟩
  have : ¬ Nat.size m ≤ k := by omega
  rw [Nat.size_le, not_lt] at this
  rw [hk, pow_succ]; omega

/-- The data bounds for every valid request (through a large clamp). -/
theorem dbounds_of (q : Request) (hv : q.Valid) : DBounds q := by
  obtain ⟨hwf, hf1, hm1, hmt⟩ := valid_pctx q hv
  let G0 : Glob := ⟨16 * (q.data.length * q.data.length + q.data.length + 1), q.data.length + 1, []⟩
  exact (show PCtx G0 q (bitsValue q.data) from ⟨At.self q.data, hwf, hf1, hm1, hmt, le_rfl, le_rfl⟩).dbounds

/-- The clamp of a prefixed input is large. -/
theorem big_of (q : Request) (R : List Bool) (inp : List Bool)
    (hl : leadOnes inp = Nat.size (q.input R).length) :
    Big (globOf inp) q ∧ R.length + 2 ≤ (globOf inp).K ∧ leadOnes inp ≤ (globOf inp).N ∧
      leadOnes inp + 2 ≤ (globOf inp).cap := by
  set m := (q.input R).length with hm
  set n := leadOnes inp with hn
  have hK : (globOf inp).K = 2 * 64 ^ n := rfl
  have hN : (globOf inp).N = 2 * 64 ^ n := rfl
  have hml := input_len q R
  have hd := data_ge q
  have h2n : m < 2 ^ n := by rw [hl]; exact Nat.lt_size_self m
  have h64 : 64 ^ n = (2 ^ n) ^ 6 := by rw [← pow_mul, show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul, mul_comm]
  set Y := q.data.length + 1 with hY
  have hY2 : 2 * Y ≤ 2 ^ n := by omega
  have h6 : (2 * Y) ^ 6 ≤ 64 ^ n := by rw [h64]; exact Nat.pow_le_pow_left hY2 6
  have hY12 : 12 ≤ Y := by omega
  have e1 : (2 * Y) ^ 6 = 64 * (Y ^ 3 * Y ^ 3) := by ring
  have e2 : 1728 ≤ Y ^ 3 := by
    have := Nat.pow_le_pow_left hY12 3; norm_num at this; exact this
  have e3 : Y ^ 3 * 1728 ≤ Y ^ 3 * Y ^ 3 := Nat.mul_le_mul_left _ e2
  have hBig : 2048 * Y ^ 3 ≤ 2 * 64 ^ n := by omega
  have hnK : n < 2 * 64 ^ n := by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    have : 2 ^ n ≤ 64 ^ n := Nat.pow_le_pow_left (by norm_num) n
    omega
  have hcap : 2 * 64 ^ n ≤ (globOf inp).cap := by
    rw [← hK]; exact cap_ge _
  refine ⟨⟨by rw [hK]; exact hBig, by rw [hK, hN]⟩, ?_, by rw [hN]; omega, ?_⟩
  · rw [hK]; have : 2 ^ n ≤ 64 ^ n := Nat.pow_le_pow_left (by norm_num) n
    omega
  · have : n + 2 ≤ 2 * 64 ^ n := by
      have : n < 2 ^ n := Nat.lt_two_pow_self
      have : 2 ^ n ≤ 64 ^ n := Nat.pow_le_pow_left (by norm_num) n
      have : 2 ≤ 2 ^ n := by omega
      omega
    omega

/-! ## The addresses -/

theorem blockAddrs_length (f : ℕ) : ∀ L : List ℕ, (blockAddrs f L).length = L.length * f
  | [] => by simp [blockAddrs]
  | k :: L => by
    have := blockAddrs_length f L
    simp only [blockAddrs, List.flatMap_cons, List.length_append, List.length_map, List.length_range] at this ⊢
    rw [this, List.length_cons]; ring

theorem xs_length (q : Request) (hv : q.Valid) (R : List Bool) :
    (xsOf q R).length = q.masks.length * nT q * q.code.f := by
  letI : Fact (Irreducible (GF.toPoly q.code.irr)) := ⟨valid_irr q hv⟩
  letI : DecidableEq (AdjoinRoot (GF.toPoly q.code.irr)) := Classical.decEq _
  rw [xsOf, blockAddrs_length, blocks, dif_pos (valid_irr q hv), blkAll_length]

/-- `(4·2^f + 2|π0| + |π1| + |πc| + 2)·f` is below `2^(10|data| + 25)`. -/
theorem elems_pow (q : Request) (db : DBounds q) :
    (4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2) * q.code.f ≤ 2 ^ (10 * q.data.length + 25) := by
  have hdA := db.dA
  have hdB := db.dB
  have hdH : dH q ≤ q.dB := Nat.sub_le _ _
  have hdI : dI q ≤ q.dA := Nat.sub_le _ _
  have hfd := db.f
  have hfX : q.code.f < 2 ^ q.data.length :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hP1 : 1 ≤ 2 ^ (8 * q.code.f + 20) := Nat.one_le_two_pow
  have hX1 : 1 ≤ 2 ^ q.data.length := Nat.one_le_two_pow
  generalize hP : 2 ^ (8 * q.code.f + 20) = P at hP1
  generalize hX : 2 ^ q.data.length = X at hX1 hfX hdA hdB
  have h1 : lenR q ≤ (X + 5) * P := by
    have := outLen_le false q.code.f q.dA; rw [hP] at this
    exact le_trans this (Nat.mul_le_mul_right _ (by omega))
  have h2 : lenH q ≤ (X + 5) * P := by
    have := outLen_le true q.code.f (dH q); rw [hP] at this
    exact le_trans this (Nat.mul_le_mul_right _ (by omega))
  have h3 : lenI q ≤ (X + 5) * P := by
    have := outLen_le true q.code.f (dI q); rw [hP] at this
    exact le_trans this (Nat.mul_le_mul_right _ (by omega))
  have h4 : 2 ^ q.code.f ≤ P := by rw [← hP]; exact pf_le _
  have e1 : (32 * X) * P = 4 * ((X + 5) * P) + (28 * X - 20) * P := by
    have : 4 * ((X + 5) * P) + (28 * X - 20) * P = (4 * (X + 5) + (28 * X - 20)) * P := by ring
    rw [this, show 4 * (X + 5) + (28 * X - 20) = 32 * X by omega]
  have h5 : (28 * X - 20) * P ≥ 6 * P := Nat.mul_le_mul_right _ (by omega)
  have hs : 4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2 ≤ (32 * X) * P := by omega
  have h6 : (4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2) * q.code.f ≤ (32 * X) * P * X :=
    Nat.mul_le_mul hs hfX.le
  have e2 : (32 * X) * P * X = 2 ^ (5 + q.data.length + (8 * q.code.f + 20) + q.data.length) := by
    rw [← hX, ← hP, pow_add, pow_add, pow_add]; norm_num; ring
  have h7 : 2 ^ (5 + q.data.length + (8 * q.code.f + 20) + q.data.length) ≤ 2 ^ (10 * q.data.length + 25) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem blkS_lt {F : Type} [Field F] [DecidableEq F] (q : Request) (hv : q.Valid)
    (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F) (c : ℕ → Bool) (k : ℕ) (hk : k ∈ blkS q φ c) :
    k < 4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2 := by
  have hp1 : 1 ≤ 2 ^ (q.domBasis φ).length := Nat.one_le_two_pow
  have hB : (q.domBasis φ).length = q.code.f := domBasis_length q φ
  have hX : ∀ (v : Bool) (BH : List F) (OH : F) (d len pB πB : ℕ) (u : List Bool),
      k ∈ blkX v (q.domBasis φ) BH OH d len pB πB u → k < pB + 2 ^ q.code.f + πB + len + 1 := by
    intro v BH OH d len pB πB u h
    simp only [blkX, List.mem_map] at h
    obtain ⟨j, -, rfl⟩ := h
    have := elemOf_le ((outV v (q.domBasis φ) 0 BH OH d).Q u (idxO (q.domBasis φ).length
      (innD v BH.length d) (j + 1))) (2 ^ (q.domBasis φ).length) len pB πB hp1
    rw [hB] at this ⊢; exact this
  have hmod : GF.ModulusOk q.code.irr q.code.f := ⟨hv.1.1, hv.1.2.1⟩
  have hal : alphaW q c < 2 ^ q.code.f := by
    have := bv_lt ((List.range q.code.f).map c); simpa [alphaW] using this
  simp only [blkS, List.mem_append] at hk
  rcases hk with ((h | h) | h) | h
  · have := hX _ _ _ _ _ _ _ _ h; omega
  · have := hX _ _ _ _ _ _ _ _ h; omega
  · simp only [blkC, List.mem_append, List.mem_map, List.mem_singleton] at h
    rcases h with ⟨i, -, rfl⟩ | rfl
    · have := (nbW_spec q φ hmod hv.1 (alphaW q c) i hal).1; omega
    · omega
  · have := hX _ _ _ _ _ _ _ _ h; omega

/-- **Every address is below `2^L`**, `L = 12·|data| + 40`. -/
theorem xs_lt (q : Request) (hv : q.Valid) (R : List Bool) : ∀ a ∈ xsOf q R, a < 2 ^ addrW q := by
  intro a ha
  have db := dbounds_of q hv
  letI : Fact (Irreducible (GF.toPoly q.code.irr)) := ⟨valid_irr q hv⟩
  letI : DecidableEq (AdjoinRoot (GF.toPoly q.code.irr)) := Classical.decEq _
  rw [xsOf, blocks, dif_pos (valid_irr q hv)] at ha
  simp only [blockAddrs, List.mem_flatMap, List.mem_map, List.mem_range] at ha
  obtain ⟨k, hk, b, hb, rfl⟩ := ha
  simp only [blkAll, List.mem_flatMap] at hk
  obtain ⟨σ, -, hk⟩ := hk
  have h1 := blkS_lt q hv _ _ k hk
  have h2 := elems_pow q db
  have h3 : (k + 1) * q.code.f ≤ (4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2) * q.code.f :=
    Nat.mul_le_mul_right _ h1
  have h4 : 2 ^ (10 * q.data.length + 25) < 2 ^ addrW q := Nat.pow_lt_pow_right (by norm_num) (by unfold addrW; omega)
  have : k * q.code.f + b < (k + 1) * q.code.f := by rw [add_mul, one_mul]; omega
  omega

/-! ## Lengths and budgets -/

theorem readerWord_length (s L : ℕ) (xs : List ℕ) (rest : List Bool) :
    (readerWord s L xs rest).length = s + 1 + xs.length * (2 * L + 5) + 1 + rest.length := by
  have hf : ∀ xs : List ℕ, (xs.flatMap fun a => true :: true :: false :: false ::
      RepairOrdinary.frame (binary L a)).length = xs.length * (2 * L + 5) := by
    intro xs; induction xs with
    | nil => simp
    | cons a xs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, frame_len, binary_length]; ring
  simp only [readerWord, List.length_append, List.length_replicate, List.length_cons, hf]; ring

theorem pow64_X (q : Request) (R : List Bool) (X : ℕ) (hX : X = q.data.length + R.length + 1) :
    64 ^ Nat.size (q.input R).length ≤ 46656 * X ^ 6 ∧ Nat.size (q.input R).length + 1 ≤ 6 * X ∧
      (q.input R).length ≤ 3 * X := by
  have hml := input_len q R
  have h2s := two_pow_size_le (q.input R).length (by omega)
  have hss : Nat.size (q.input R).length < 2 ^ Nat.size (q.input R).length := Nat.lt_two_pow_self
  have h6X : 2 ^ Nat.size (q.input R).length ≤ 6 * X := by omega
  have h64 : 64 ^ Nat.size (q.input R).length = (2 ^ Nat.size (q.input R).length) ^ 6 := by
    rw [← pow_mul, show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul, mul_comm]
  refine ⟨?_, by omega, by omega⟩
  rw [h64]; have := Nat.pow_le_pow_left h6X 6; rw [mul_pow] at this; norm_num at this; exact this

theorem xs_bound (q : Request) (hv : q.Valid) (R : List Bool) :
    (xsOf q R).length ≤ 311 * ((q.data.length + 1) * (q.data.length + 1) * (q.data.length + 1)) := by
  have db := dbounds_of q hv
  have hnT := nT_le db
  have hnm := db.nm
  have hfd := db.f
  rw [xs_length q hv R]
  have := Nat.mul_le_mul (Nat.mul_le_mul (show q.masks.length ≤ q.data.length + 1 by omega)
    (show nT q ≤ 311 * (q.data.length + 1) by omega)) (show q.code.f ≤ q.data.length + 1 by omega)
  have e : (q.data.length + 1) * (311 * (q.data.length + 1)) * (q.data.length + 1) =
    311 * ((q.data.length + 1) * (q.data.length + 1) * (q.data.length + 1)) := by ring
  omega

theorem xs_K (q : Request) (hv : q.Valid) (R : List Bool) :
    (xsOf q R).length + 2 ≤ 2048 * (q.data.length + 1) ^ 3 := by
  have h := xs_bound q hv R
  have hc3 : (q.data.length + 1) ^ 3 = (q.data.length + 1) * (q.data.length + 1) * (q.data.length + 1) := by ring
  have hP1 : 0 < (q.data.length + 1) * (q.data.length + 1) * (q.data.length + 1) :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)
  rw [hc3]; omega

theorem rw_bound (q : Request) (hv : q.Valid) (R : List Bool) (X : ℕ) (hX : X = q.data.length + R.length + 1) :
    (readerWord (Nat.size (q.input R).length) (addrW q) (xsOf q R) (q.input R)).length ≤ 34000 * X ^ 6 := by
  obtain ⟨-, hs, hm⟩ := pow64_X q R X hX
  have hxs1 := xs_bound q hv R
  have hX1 : 1 ≤ X := by omega
  have hD : q.data.length + 1 ≤ X := by omega
  generalize hY : q.data.length + 1 = Y at hxs1 hD
  have hX3 : Y * Y * Y ≤ X * X * X := Nat.mul_le_mul (Nat.mul_le_mul hD hD) hD
  have hL : 2 * addrW q + 5 ≤ 109 * X := by unfold addrW; omega
  have hrw : (xsOf q R).length * (2 * addrW q + 5) ≤ 311 * (X * X * X) * (109 * X) :=
    Nat.mul_le_mul (le_trans hxs1 (Nat.mul_le_mul_left _ hX3)) hL
  have e4 : 311 * (X * X * X) * (109 * X) = 33899 * (X * X * X * X) := by ring
  have hX6 : X * X * X * (X * X * X) = X ^ 6 := by ring
  have hX4 : X * X * X * X ≤ X ^ 6 := by
    rw [← hX6]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left X (Nat.mul_le_mul hX1 hX1))
  have hX16 : X ≤ X ^ 6 := le_trans (Nat.le_mul_of_pos_left X (Nat.mul_le_mul (Nat.mul_le_mul hX1 hX1) hX1)) hX4
  rw [readerWord_length]; omega

theorem pw_bound (q : Request) (R : List Bool) (X : ℕ) (hX : X = q.data.length + R.length + 1) :
    (prefixWord (q.input R)).length ≤ 34000 * X ^ 6 := by
  obtain ⟨-, hs, hm⟩ := pow64_X q R X hX
  have hX1 : 1 ≤ X := by omega
  have : X ≤ X ^ 6 := Nat.le_self_pow (by norm_num) X
  simp only [prefixWord, List.length_append, List.length_replicate, List.length_cons]; omega

/-- The budget of an `FL` run on a prefixed input, polynomially in `X`. -/
theorem budget_X (main : S) (inp : List Bool) (X : ℕ) (hX : 1 ≤ X) (h64 : 64 ^ leadOnes inp ≤ 46656 * X ^ 6)
    (hl : inp.length ≤ 34000 * X ^ 6) :
    langBudget noCallee zF VV MM inp (preCost inp + costS (globOf inp) main + 1) ≤
      flConst main * 80657 ^ (dpS main + 5) * X ^ (6 * (dpS main + 5)) := by
  have h := flBudget_le main inp
  have h1 : 64 ^ leadOnes inp + inp.length + 1 ≤ 80657 * X ^ 6 := by
    have : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX; omega
  calc _ ≤ flConst main * (64 ^ leadOnes inp + inp.length + 1) ^ (dpS main + 5) := h
    _ ≤ flConst main * (80657 * X ^ 6) ^ (dpS main + 5) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = flConst main * 80657 ^ (dpS main + 5) * X ^ (6 * (dpS main + 5)) := by rw [mul_pow, ← pow_mul]; ring

theorem readWord_length (s L : ℕ) (rest : List Bool) :
    ∀ (xs : List ℕ) (ans : List Bool), ans.length = xs.length →
      (readWord s L xs ans rest).length = (readerWord s L xs rest).length
  | [], [], _ => by simp [readWord, readerWord]
  | a :: xs, b :: ans, h => by
    have ih := readWord_length s L rest xs ans (by simpa using h)
    simp only [readWord, readerWord, List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    simp only [List.zipWith_cons_cons, List.flatten_cons, List.flatMap_cons, List.length_append, List.length_cons]
    omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## The two cell stages -/

/-- Valid requests with coins. -/
abbrev VReq : Type := {x : Request × List Bool // x.1.Valid}

/-- The input of the query half. -/
def in2 (r : VReq) : List Bool := prefixWord (r.1.1.input r.1.2)

/-- The input of the decision half (the answers of the oracle `r.2`). -/
noncomputable def in4 (r : VReq × (ℕ → Bool)) : List Bool :=
  readWord (Nat.size (r.1.1.1.input r.1.1.2).length) (addrW r.1.1.1) (xsOf r.1.1.1 r.1.1.2)
    ((xsOf r.1.1.1 r.1.1.2).map r.2) (r.1.1.1.input r.1.1.2)

theorem lead2 (r : VReq) : leadOnes (in2 r) = Nat.size (r.1.1.input r.1.2).length := leadOnes_pre _ _
theorem lead4 (r : VReq × (ℕ → Bool)) : leadOnes (in4 r) = Nat.size (r.1.1.1.input r.1.1.2).length :=
  leadOnes_pre _ _

theorem size_pos' (q : Request) (R : List Bool) : 1 ≤ Nat.size (q.input R).length :=
  Nat.size_pos.2 (by rw [input_len]; omega)

theorem wfQ : wfS mainQ 0 = true := by decide
theorem wfD : wfS mainD 0 = true := by decide

theorem runQ (r : VReq) :
    (evalS (globOf (in2 r)) mainQ (s0 (in2 r))).out =
        RepairOrdinary.frame (readerWord (Nat.size (r.1.1.input r.1.2).length) (addrW r.1.1) (xsOf r.1.1 r.1.2)
          (r.1.1.input r.1.2)) ∧
      (evalS (globOf (in2 r)) mainQ (s0 (in2 r))).bad = false := by
  obtain ⟨⟨q, R⟩, hv⟩ := r
  have hl := lead2 ⟨(q, R), hv⟩
  obtain ⟨bg, hR, hN, hc⟩ := big_of q R (in2 ⟨(q, R), hv⟩) hl
  have := mainQ_spec (G := globOf (in2 ⟨(q, R), hv⟩)) q hv bg R (leadOnes (in2 ⟨(q, R), hv⟩)) rfl hl rfl
    (s0 (in2 ⟨(q, R), hv⟩)) rfl hR hN hc
  rw [hl] at this
  exact ⟨by rw [this.1]; exact List.nil_append _, this.2⟩

theorem runD (r : VReq × (ℕ → Bool)) {F : Type} [Field F] [DecidableEq F]
    (φ : AdjoinRoot (GF.toPoly r.1.1.1.code.irr) →+* F) (hφ : Function.Bijective φ) :
    (evalS (globOf (in4 r)) mainD (s0 (in4 r))).out =
        RepairOrdinary.frame [r.1.1.1.patchedVerdict φ (r.1.1.1.decode φ r.2) r.1.1.2] ∧
      (evalS (globOf (in4 r)) mainD (s0 (in4 r))).bad = false := by
  obtain ⟨⟨⟨q, R⟩, hv⟩, o⟩ := r
  have hl := lead4 ⟨⟨(q, R), hv⟩, o⟩
  obtain ⟨bg, hR, hN, hc⟩ := big_of q R (in4 ⟨⟨(q, R), hv⟩, o⟩) hl
  have hxs := xs_K q hv R
  have hlin := bg.lin
  have := mainD_spec (G := globOf (in4 ⟨⟨(q, R), hv⟩, o⟩)) q hv bg (Nat.size (q.input R).length) (addrW q) R o rfl
    (s0 (in4 ⟨⟨(q, R), hv⟩, o⟩)) (by show leadOnes _ + 1 = _; rw [hl])
    hR (by have := bg.K; omega) (by unfold addrW; omega) φ hφ
  exact ⟨by rw [this.1]; exact List.nil_append _, this.2⟩

/-- The query half as a word function. -/
noncomputable def wf2 := flWF in2 mainQ wfQ (fun r => by rw [lead2]; exact size_pos' _ _)
  (fun r => by rw [lead2]; simp [in2, prefixWord]) (fun r => (runQ r).2)

theorem badD (r : VReq × (ℕ → Bool)) : (evalS (globOf (in4 r)) mainD (s0 (in4 r))).bad = false := by
  have hirr := valid_irr r.1.1.1 r.1.2
  letI : Fact (Irreducible (GF.toPoly r.1.1.1.code.irr)) := ⟨hirr⟩
  letI : DecidableEq (AdjoinRoot (GF.toPoly r.1.1.1.code.irr)) := Classical.decEq _
  exact (runD r (RingHom.id _) Function.bijective_id).2

/-- The decision half as a word function. -/
noncomputable def wf4 := flWF in4 mainD wfD (fun r => by rw [lead4]; exact size_pos' _ _)
  (fun r => by rw [lead4]; simp [in4, readWord]) badD

/-- **The cell stages** (stages 2 and 4 of `singleRunTime_of_stages`). -/
theorem cellStages : CellStages := by
  set E := dpS mainQ + dpS mainD + 5 with hE
  refine ⟨oracleOfProgram wf2.program, oracleOfProgram wf4.program, fun q _ => addrW q, xsOf,
    (flConst mainQ + flConst mainD + 1) * 80657 ^ E + 34000, 6 * E, ?_⟩
  intro q hv R
  set X := q.data.length + R.length + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hXe : X ^ 6 ≤ X ^ (6 * E) := Nat.pow_le_pow_right hX1 (by omega)
  have hmono : ∀ (c d : ℕ), c ≤ flConst mainQ + flConst mainD + 1 → d + 5 ≤ E →
      c * 80657 ^ (d + 5) * X ^ (6 * (d + 5)) ≤ ((flConst mainQ + flConst mainD + 1) * 80657 ^ E + 34000) * X ^ (6 * E) := by
    intro c d hc hd
    have h1 : 80657 ^ (d + 5) ≤ 80657 ^ E := Nat.pow_le_pow_right (by norm_num) hd
    have h2 : X ^ (6 * (d + 5)) ≤ X ^ (6 * E) := Nat.pow_le_pow_right hX1 (by omega)
    have h3 : c * 80657 ^ (d + 5) ≤ (flConst mainQ + flConst mainD + 1) * 80657 ^ E := Nat.mul_le_mul hc h1
    exact Nat.mul_le_mul (by omega) h2
  obtain ⟨h64, -, -⟩ := pow64_X q R X hX
  have hrw := rw_bound q hv R X hX
  refine ⟨xs_lt q hv R, ?_, fun o => ?_, fun F _ _ φ hφ o => ?_⟩
  · exact le_trans hrw (le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_left _ hXe))
  · have hr := oracleOfProgram_runs wf2 o ⟨(q, R), hv⟩ _ (runQ ⟨(q, R), hv⟩).1
    refine runs_mono hr ?_
    have hb := budget_X mainQ (in2 ⟨(q, R), hv⟩) X hX1 (by rw [lead2]; exact h64) (pw_bound q R X hX)
    exact le_trans hb (hmono _ _ (by omega) (by omega))
  · have hr := oracleOfProgram_runs wf4 o ⟨⟨(q, R), hv⟩, o⟩ _ (runD ⟨⟨(q, R), hv⟩, o⟩ φ hφ).1
    refine runs_mono hr ?_
    have hl4 : (in4 ⟨⟨(q, R), hv⟩, o⟩).length ≤ 34000 * X ^ 6 := by
      rw [in4, readWord_length _ _ _ _ _ (List.length_map _)]; exact hrw
    have hb := budget_X mainD (in4 ⟨⟨(q, R), hv⟩, o⟩) X hX1 (by rw [lead4]; exact h64) hl4
    exact le_trans hb (hmono _ _ (by omega) (by omega))

/-- **Join P04 item 6 (`SingleRunTime`), proved** (proof of `thm:short-pcp-ours`; `lem:patch-r`). -/
theorem singleRunTime : SingleRunTime :=
  singleRunTime_of_stages WidthPrefix.prefixStage ReaderRun.readerStage cellStages

end NearCubicGates.Adapters.ShortPCP.Time

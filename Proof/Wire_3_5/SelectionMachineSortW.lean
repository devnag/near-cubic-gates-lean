import Proof.Wire_3_5.SelectionMachineSortRound

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.RadixSemantics

variable {ns nr : ℕ}

/-- Count the bits of the first record of the stream on `A` into `K` (none if the stream is empty). -/
def measureW (A : Fin (ns + 1)) (CA K : Fin nr) : WM ns nr :=
  .seq (.whs A (.seq (WM.fwdC A CA) (.seq (WM.fwdC A CA) (.inc K)))) (WM.rewind A CA)

/-- The loop of double rounds. -/
def roundsW (A B : Fin (ns + 1)) (CA CB K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (round A B CA CB) (round B A CA CB)))

/-- **The sort**: `W` double rounds, `W` the width of the first record. -/
def sortW (A B : Fin (ns + 1)) (CA CB K : Fin nr) : WM ns nr := .seq (measureW A CA K) (roundsW A B CA CB K)

/-- A round's cost for `N` records of width `W`. -/
def rc (W N : ℕ) : ℕ := 2 * (N * (30 * (W - 1) + 46) + 1) + 15 * (N * (2 * W + 1)) + 10

/-- The sort's cost for `N` records of width `W`. -/
def sortCost (W N : ℕ) : ℕ := 27 * W + 4 + (W * (2 * rc W N + 6) + 1)

/-! ## Costs of fixed-width records -/

theorem word_length_eq (r : StablePartition.Record) : (word r).length = r.2.length + 1 := by simp [word]

theorem rb_length_width (W : ℕ) (hW : 1 ≤ W) : ∀ (rs : List StablePartition.Record),
    (∀ r ∈ rs, (word r).length = W) → (StablePartition.recordsBits rs).length = rs.length * (2 * W + 1)
  | [], _ => by simp [StablePartition.recordsBits]
  | r :: rs, h => by
    rw [recordsBits_cons, List.length_append, recordBits_length, rb_length_width W hW rs
      (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]
    have hr := h r List.mem_cons_self
    rw [word_length_eq] at hr
    rw [List.length_cons]
    have e : (rs.length + 1) * (2 * W + 1) = rs.length * (2 * W + 1) + (2 * W + 1) := by ring
    rw [e]; omega

theorem phaseCost_width (W : ℕ) (hW : 1 ≤ W) : ∀ (rs : List StablePartition.Record),
    (∀ r ∈ rs, (word r).length = W) → phaseCost rs = rs.length * (30 * (W - 1) + 46) + 1
  | [], _ => by simp [phaseCost]
  | r :: rs, h => by
    have ih := phaseCost_width W hW rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    have hr := h r List.mem_cons_self
    rw [word_length_eq] at hr
    unfold phaseCost at ih ⊢
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have e : (rs.length + 1) * (30 * (W - 1) + 46) = rs.length * (30 * (W - 1) + 46) + (30 * (W - 1) + 46) := by
      ring
    have hr' : r.2.length = W - 1 := by omega
    rw [e, hr']
    omega

theorem roundCost_width (W : ℕ) (hW : 1 ≤ W) (rs : List StablePartition.Record)
    (h : ∀ r ∈ rs, (word r).length = W) : roundCost rs = rc W rs.length := by
  unfold roundCost rc
  rw [phaseCost_width W hW rs h, rb_length_width W hW rs h]

theorem round_length (rs : List StablePartition.Record) : (RadixRound.records rs).length = rs.length := by
  rw [(round_perm rs).length_eq, List.length_map]

/-! ## The loop of double rounds -/

section Rounds
variable (cap : ℕ) {A B : Fin (ns + 1)} {CA CB K : Fin nr}
variable (hAB : A ≠ B) (hC : CA ≠ CB) (hKA : K ≠ CA) (hKB : K ≠ CB)
include hAB hC hKA hKB

theorem rounds_spec (W : ℕ) (hW : 1 ≤ W) : ∀ (k : ℕ) (rs : List StablePartition.Record) (σ : WState ns nr),
    (∀ r ∈ rs, (word r).length = W) → σ.st A = StablePartition.stream rs → σ.sh A = 0 →
    (σ.st B).length = (StablePartition.stream rs).length → σ.sh B = 0 → σ.val CA = 0 → σ.val CB = 0 →
    σ.val K = k → (StablePartition.stream rs).length + 2 ≤ cap → k ≤ cap →
    ∃ junk : List Bool, junk.length = (StablePartition.stream rs).length ∧
      WExec cap (roundsW A B CA CB K) σ
        (((σ.sets A (StablePartition.stream (RadixIteration.records (2 * k) rs))).sets B junk).setv K 0)
        (k * (2 * rc W rs.length + 6) + 1)
  | 0, rs, σ, _, hA, _, hBl, _, _, _, hK, _, _ => by
    refine ⟨σ.st B, hBl, ?_⟩
    have e : ((σ.sets A (StablePartition.stream (RadixIteration.records (2 * 0) rs))).sets B (σ.st B)).setv K 0 = σ := by
      apply WState.eq
      · rfl
      · funext j; simp only [WState.setv_st, WState.sets_st, Function.update_apply]
        split_ifs with h1 h2 <;> subst_vars <;> simp_all [RadixIteration.records]
      · funext j; simp only [WState.setv_val, WState.sets_val, Function.update_apply]
        split_ifs with h1 <;> subst_vars <;> simp_all
      · rfl
    rw [e]
    exact WExec.cast cap (WExec.whrF hK) rfl (by omega)
  | k + 1, rs, σ, hw, hA, hAh, hBl, hBh, hCA, hCB, hK, hcap, hk => by
    -- decrement
    have d := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have hK1 : σ1.val K = k := by simp [hσ1, hK]
    -- round A → B
    have r1 := round_spec cap hAB hC rs σ1 (by simp [hσ1, hA]) (by simp [hσ1, hAh]) (by simp [hσ1, hBl])
      (by simp [hσ1, hBh]) (by simp [hσ1, hCA, Ne.symm hKA]) (by simp [hσ1, hCB, Ne.symm hKB]) hcap
    set rs1 := RadixRound.records rs with hrs1
    set σ2 := σ1.sets B (StablePartition.stream rs1) with hσ2
    have hlen1 : (StablePartition.stream rs1).length = (StablePartition.stream rs).length :=
      RadixRound.stream_length rs
    -- round B → A
    have r2 := round_spec cap (Ne.symm hAB) hC rs1 σ2 (by simp [hσ2]) (by simp [hσ2, hσ1, hBh])
      (by rw [hlen1]; simp [hσ2, hσ1, hAB, hA]) (by simp [hσ2, hσ1, hAh])
      (by simp [hσ2, hσ1, hCA, Ne.symm hKA]) (by simp [hσ2, hσ1, hCB, Ne.symm hKB]) (by rw [hlen1]; exact hcap)
    set rs2 := RadixRound.records rs1 with hrs2
    set σ3 := σ2.sets A (StablePartition.stream rs2) with hσ3
    have hlen2 : (StablePartition.stream rs2).length = (StablePartition.stream rs).length := by
      rw [RadixRound.stream_length, hlen1]
    have hw1 : ∀ r ∈ rs1, (word r).length = W := round_width hw
    have hw2 : ∀ r ∈ rs2, (word r).length = W := round_width hw1
    have hN2 : rs2.length = rs.length := by rw [hrs2, round_length, hrs1, round_length]
    -- the rest of the loop
    obtain ⟨junk, hjl, h3⟩ := rounds_spec W hW k rs2 σ3 hw2 (by simp [hσ3]) (by simp [hσ3, hσ2, hσ1, hAh])
      (by simp [hσ3, hσ2, Ne.symm hAB, hlen1, hlen2]) (by simp [hσ3, hσ2, hσ1, hBh])
      (by simp [hσ3, hσ2, hσ1, hCA, Ne.symm hKA]) (by simp [hσ3, hσ2, hσ1, hCB, Ne.symm hKB])
      (by simp [hσ3, hσ2, hK1]) (by rw [hlen2]; exact hcap) (by omega)
    refine ⟨junk, by rw [hjl, hlen2], ?_⟩
    have hrec : RadixIteration.records (2 * (k + 1)) rs = RadixIteration.records (2 * k) rs2 := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      rfl
    rw [hrec]
    have hbody := WExec.seq d (WExec.seq r1 r2)
    refine WExec.cast cap (WExec.whrT (by omega) hbody h3) ?_ ?_
    · apply WState.eq
      · rfl
      · funext j; simp only [hσ3, hσ2, hσ1, WState.setv_st, WState.sets_st, Function.update_apply]
        split_ifs <;> rfl
      · funext j; simp only [hσ3, hσ2, hσ1, WState.setv_val, WState.sets_val, Function.update_apply]
        split_ifs <;> rfl
      · rfl
    · rw [roundCost_width W hW rs hw, roundCost_width W hW rs1 hw1, hN2, hrs1, round_length]
      nlinarith

end Rounds

/-! ## Measuring the width -/

section Measure
variable (cap : ℕ) (σ : WState ns nr) {A : Fin (ns + 1)} {CA K : Fin nr} (hKA : K ≠ CA)
include hKA

/-- The measuring state: `A` (and `CA`) at `p`, `K` at `j`. -/
def mst (p j : ℕ) : WState ns nr := ((σ.seth A p).setv CA p).setv K j

theorem countLoop : ∀ (bits pre post : List Bool) (j : ℕ), σ.st A = pre ++ frameP bits ++ false :: post →
    pre.length + 2 * bits.length < cap → j + bits.length ≤ cap →
    WExec cap (.whs A (.seq (WM.fwdC A CA) (.seq (WM.fwdC A CA) (.inc K)))) (mst σ (A := A) (CA := CA) (K := K)
      pre.length j) (mst σ (A := A) (CA := CA) (K := K) (pre.length + 2 * bits.length) (j + bits.length))
      (17 * bits.length + 1)
  | [], pre, post, j, hA, _, _ => by
    have hbit : wbit (mst σ (A := A) (CA := CA) (K := K) pre.length j) A = false := by
      simp only [mst, wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
        hA, frameP_nil, List.append_nil, rd_app0, rd_cons0]
    simpa using WExec.whsF (cap := cap) (P := (.seq (WM.fwdC A CA) (.seq (WM.fwdC A CA) (.inc K)) : WM ns nr)) hbit
  | b :: bits, pre, post, j, hA, hp, hj => by
    have hA' : σ.st A = (pre ++ [true, b]) ++ frameP bits ++ false :: post := by
      rw [hA, frameP_cons]; simp
    have hA2 : σ.st A = pre ++ (true :: b :: (frameP bits ++ false :: post)) := by
      rw [hA, frameP_cons]; simp
    have hbit : wbit (mst σ (A := A) (CA := CA) (K := K) pre.length j) A = true := by
      simp only [mst, wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
        hA2, rd_app0, rd_cons0]
    simp only [List.length_cons] at hp hj
    have f1 := wfwdC_spec cap A CA (mst σ (A := A) (CA := CA) (K := K) pre.length j)
      (by simp [mst, Ne.symm hKA]; omega)
    have e1 : ((mst σ (A := A) (CA := CA) (K := K) pre.length j).seth A
        ((mst σ (A := A) (CA := CA) (K := K) pre.length j).sh A + 1)).setv CA
        ((mst σ (A := A) (CA := CA) (K := K) pre.length j).val CA + 1) =
        mst σ (A := A) (CA := CA) (K := K) (pre.length + 1) j := by
      apply WState.eq
      · funext x; simp only [mst, WState.setv_sh, WState.seth_sh, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
      · funext x; simp only [mst, WState.setv_val, WState.seth_val, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
    rw [e1] at f1
    have f2 := wfwdC_spec cap A CA (mst σ (A := A) (CA := CA) (K := K) (pre.length + 1) j)
      (by simp [mst, Ne.symm hKA]; omega)
    have e2 : ((mst σ (A := A) (CA := CA) (K := K) (pre.length + 1) j).seth A
        ((mst σ (A := A) (CA := CA) (K := K) (pre.length + 1) j).sh A + 1)).setv CA
        ((mst σ (A := A) (CA := CA) (K := K) (pre.length + 1) j).val CA + 1) =
        mst σ (A := A) (CA := CA) (K := K) (pre.length + 1 + 1) j := by
      apply WState.eq
      · funext x; simp only [mst, WState.setv_sh, WState.seth_sh, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
      · funext x; simp only [mst, WState.setv_val, WState.seth_val, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
    rw [e2] at f2
    have ik := WExec.inc (cap := cap) K (mst σ (A := A) (CA := CA) (K := K) (pre.length + 1 + 1) j)
      (by simp [mst]; omega)
    have e3 : (mst σ (A := A) (CA := CA) (K := K) (pre.length + 1 + 1) j).setv K
        ((mst σ (A := A) (CA := CA) (K := K) (pre.length + 1 + 1) j).val K + 1) =
        mst σ (A := A) (CA := CA) (K := K) (pre.length + 1 + 1) (j + 1) := by
      apply WState.eq
      · rfl
      · rfl
      · funext x; simp only [mst, WState.setv_val, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
    rw [e3] at ik
    have h2 := countLoop bits (pre ++ [true, b]) post (j + 1) hA' (by simp; omega) (by omega)
    have hl : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    rw [hl] at h2
    refine WExec.cast cap (WExec.whsT hbit (WExec.seq f1 (WExec.seq f2 ik)) h2) ?_ (by simp; omega)
    congr 1 <;> simp <;> omega

/-- **Measuring**: `K` receives the width of the first record, or `0` for an empty stream. -/
theorem measure_spec (W : ℕ) (rs : List StablePartition.Record) (hw : ∀ r ∈ rs, (word r).length = W)
    (hA : σ.st A = StablePartition.stream rs) (hAh : σ.sh A = 0) (hCA : σ.val CA = 0) (hK : σ.val K = 0)
    (hcap : (StablePartition.stream rs).length + 2 ≤ cap) :
    WExec cap (measureW A CA K) σ (σ.setv K (if rs = [] then 0 else W)) (27 * W + 3) := by
  have e0 : mst σ (A := A) (CA := CA) (K := K) 0 0 = σ := by
    apply WState.eq
    · funext x; simp only [mst, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · funext x; simp only [mst, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  cases rs with
  | nil =>
    have hbit : wbit σ A = false := by
      simp only [wbit, hA, hAh]; rfl
    have h1 := WExec.whsF (cap := cap) (P := (.seq (WM.fwdC A CA) (.seq (WM.fwdC A CA) (.inc K)) : WM ns nr)) hbit
    have h2 := wrewind_spec cap A CA 0 σ hCA (by omega)
    have e : (σ.setv CA 0).seth A (σ.sh A - 0) = σ := by
      apply WState.eq
      · funext x; simp only [WState.seth_sh, WState.setv_sh, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
      · funext x; simp only [WState.seth_val, WState.setv_val, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
    rw [e] at h2
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext x; simp only [WState.setv_val, Function.update_apply, if_true]
      split_ifs <;> simp_all
    · rfl
  | cons r rest =>
    have hwr : (word r).length = W := hw r List.mem_cons_self
    have hA' : σ.st A = [] ++ frameP (word r) ++ false :: (StablePartition.recordsBits rest ++ [false]) := by
      rw [hA, StablePartition.stream, recordsBits_cons, recordBits_eq]
      simp [word, frameP_cons]
    have hlen : (StablePartition.stream (r :: rest)).length ≥ 2 * W + 1 := by
      rw [StablePartition.stream, recordsBits_cons, List.length_append, List.length_append, recordBits_length]
      simp [word] at hwr
      omega
    have h1 := countLoop cap σ hKA (word r) [] _ 0 hA' (by simp; omega) (by omega)
    simp only [List.length_nil, Nat.zero_add] at h1
    rw [e0, hwr] at h1
    have h2 := wrewind_spec cap A CA (2 * W) (mst σ (A := A) (CA := CA) (K := K) (2 * W) W)
      (by simp [mst, Ne.symm hKA]) (by simp [mst, Ne.symm hKA]; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    apply WState.eq
    · funext x; simp only [mst, WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · funext x; simp only [mst, WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl

end Measure

/-! ## The sort -/

/-- **`sortW` meets `SortSpec`**. -/
theorem sortW_spec (cap W : ℕ) {S S' : Fin (ns + 1)} {CA CB K : Fin nr} (hSS' : S ≠ S') (hC : CA ≠ CB)
    (hKA : K ≠ CA) (hKB : K ≠ CB) : SortSpec cap W (sortW S S' CA CB K) S S' [CA, CB, K] sortCost := by
  intro σ l hW hl hS hSh hS' hS'h hr hcap
  have hCA : σ.val CA = 0 := hr CA (by simp)
  have hCB : σ.val CB = 0 := hr CB (by simp)
  have hK : σ.val K = 0 := hr K (by simp)
  set rs := l.map (keyRec W) with hrs
  have hw : ∀ r ∈ rs, (word r).length = W := by
    intro r hr'
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr'
    rw [word_keyRec W x hW, binary_length]
  have hS1 : σ.st S = StablePartition.stream rs := hS
  have hcap1 : (StablePartition.stream rs).length + 2 ≤ cap := hcap
  set k := if rs = [] then 0 else W with hk
  have hkW : k ≤ W := by rw [hk]; split_ifs <;> omega
  have m := measure_spec cap σ hKA W rs hw hS1 hSh hCA hK hcap1
  set σ1 := σ.setv K k with hσ1
  have hkcap : k ≤ cap := by
    rw [hk]
    split_ifs with h
    · omega
    · have hl1 := rb_length_width W hW rs hw
      have hne : 1 ≤ rs.length := by
        rcases Nat.eq_zero_or_pos rs.length with h0 | h0
        · exact absurd (List.length_eq_zero_iff.mp h0) h
        · exact h0
      have : (StablePartition.stream rs).length = (StablePartition.recordsBits rs).length + 1 := by
        simp [StablePartition.stream]
      have h3 : 1 * (2 * W + 1) ≤ rs.length * (2 * W + 1) := Nat.mul_le_mul_right _ hne
      omega
  obtain ⟨junk, hjl, h2⟩ := rounds_spec cap hSS' hC hKA hKB W hW k rs σ1 hw (by simp [hσ1, hS1])
    (by simp [hσ1, hSh]) (by simp [hσ1, hS', keyStream, hrs]) (by simp [hσ1, hS'h])
    (by simp [hσ1, hCA, Ne.symm hKA]) (by simp [hσ1, hCB, Ne.symm hKB]) (by simp [hσ1]) hcap1 hkcap
  have hX : StablePartition.stream (RadixIteration.records (2 * k) rs) = keyStream W (sorted l) := by
    by_cases h0 : l = []
    · subst h0
      simp [hk, hrs, RadixIteration.records, keyStream, sorted]
    · have hne : rs ≠ [] := by simpa [hrs] using h0
      rw [hk, if_neg hne, hrs, radix_sorted W hW l hl]
      rfl
  refine ⟨junk, by rw [hjl]; rfl, ?_⟩
  refine WExec.cast cap (WExec.seq m h2) ?_ ?_
  · rw [hX]
    apply WState.eq
    · rfl
    · rfl
    · funext x; simp only [hσ1, WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
  · unfold sortCost
    have hlen : rs.length = l.length := by simp [hrs]
    rw [hlen]
    have := Nat.mul_le_mul_right (2 * rc W l.length + 6) hkW
    omega

end NearCubicWires.WireExponent3_5.SelectionMachine.Sort

import Proof.Gates.Codec.Transcode
import Proof.Gates.Codec.ParityW
import Proof.Gates.Codec.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Codec

/-! ## Helpers -/

theorem nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 x; omega

theorem one_le_nbl (x : ℕ) : 1 ≤ natBitLength x := by unfold natBitLength; omega

theorem two_pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with h0 | hx
  · subst h0; simp
  · have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
    rw [pow_succ]; omega

theorem pow_chain (T : ℕ) (hT : 1 ≤ T) : T ≤ T ^ 2 ∧ T ^ 2 ≤ T ^ 3 ∧ T ^ 3 ≤ T ^ 4 ∧ 1 ≤ T ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · exact Nat.pow_le_pow_right hT (by norm_num)
  · exact Nat.pow_le_pow_right hT (by norm_num)
  · nlinarith

/-- `(nbl x + c)·(a·x + b) ≤ (c + 1)·(a + b)·(S+1)^2` for `x ≤ S`. -/
theorem nbl_mul_le (x S a b c : ℕ) (hx : x ≤ S) :
    (natBitLength x + c) * (a * x + b) ≤ (c + 1) * (a + b) * (S + 1) ^ 2 := by
  have h1 : natBitLength x + c ≤ (c + 1) * (S + 1) := by have := nbl_le x; nlinarith
  have h2 : a * x + b ≤ (a + b) * (S + 1) := by nlinarith
  calc (natBitLength x + c) * (a * x + b) ≤ ((c + 1) * (S + 1)) * ((a + b) * (S + 1)) := Nat.mul_le_mul h1 h2
    _ = (c + 1) * (a + b) * (S + 1) ^ 2 := by ring

theorem fIntCost_le (n S : ℕ) (hn : n ≤ S) : fIntCost n ≤ 253 * (S + 1) ^ 2 := by
  unfold fIntCost
  have := pow_chain (S + 1) (by omega)
  have : n ^ 2 ≤ (S + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

theorem fGateCost_le (q n S : ℕ) (hq : q ≤ S) (hn : n ≤ S) : fGateCost q n ≤ 3600 * (S + 1) ^ 3 := by
  unfold fGateCost
  have hc := pow_chain (S + 1) (by omega)
  have h1 := nbl_mul_le q S 100 200 10 hq
  have h2 : (q + 1) * (fIntCost n + 4) ≤ (S + 1) * (257 * (S + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by have := fIntCost_le n S hn; nlinarith)
  have h3 : (S + 1) * (257 * (S + 1) ^ 2) = 257 * (S + 1) ^ 3 := by ring
  nlinarith

theorem circuitWCost_le (q n K L S : ℕ) (hq : q ≤ S) (hn : n ≤ S) (hK : K ≤ S) (hL : L ≤ S) :
    circuitWCost q n K L ≤ 20000 * (S + 1) ^ 4 := by
  unfold circuitWCost
  have hc := pow_chain (S + 1) (by omega)
  have h1 := nbl_mul_le K S 100 200 10 hK
  have h2 := nbl_mul_le L S 100 200 10 hL
  have h3 : K * (fGateCost q n + 4) ≤ (S + 1) * (3604 * (S + 1) ^ 3) :=
    Nat.mul_le_mul (by omega) (by have := fGateCost_le q n S hq hn; nlinarith)
  have h3' : (S + 1) * (3604 * (S + 1) ^ 3) = 3604 * (S + 1) ^ 4 := by ring
  have h4 : K * (fIntCost n + 4) ≤ (S + 1) * (257 * (S + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by have := fIntCost_le n S hn; nlinarith)
  have h4' : (S + 1) * (257 * (S + 1) ^ 2) = 257 * (S + 1) ^ 3 := by ring
  have h5 : L * (51 + 4) ≤ 55 * (S + 1) := by nlinarith
  linarith

/-- The class at the field positions of `circuitW_spec` (the counts `cK`, `cL` are at most the stream length). -/
theorem circuitWCost_field_le (q : ℕ) (w : List Bool) (p S : ℕ) (hq : q ≤ S) (hw : w.length ≤ S) :
    circuitWCost q w.length (cK w p) (cL w p q) ≤ 20000 * (S + 1) ^ 4 :=
  circuitWCost_le q w.length _ _ S hq hw (le_trans (fieldLen_le w p) hw) (le_trans (fieldLen_le w _) hw)

theorem unframeW_cost_le (m : ℕ) : m * (14 + 4) + 1 ≤ 19 * (m + 1) := by omega

theorem copyRW_cost_le (n : ℕ) :
    22 * n + 1 + 1 + 7 + 1 + (18 * (2 * n + 1) + 3 + 1 + (5 * (2 * n + 1) + 1 + 1 + (5 * (2 * n + 1) + 1))) ≤
      100 * (n + 1) := by omega

theorem transcodeW_cost_le (m cb S B : ℕ) (hm : m ≤ S) (hcb : cb ≤ B) : m * (cb + 4) + 1 ≤ (S + 1) * (B + 5) := by
  have : m * (cb + 4) ≤ S * (B + 4) := Nat.mul_le_mul hm (by omega)
  nlinarith

theorem transcodeW_class (m S : ℕ) (hm : m ≤ S) : m * (20000 * (S + 1) ^ 4 + 4) + 1 ≤ 20005 * (S + 1) ^ 5 := by
  have h := transcodeW_cost_le m (20000 * (S + 1) ^ 4) S (20000 * (S + 1) ^ 4) hm le_rfl
  have hc := pow_chain (S + 1) (by omega)
  have e : (S + 1) * (20000 * (S + 1) ^ 4 + 5) = 20000 * (S + 1) ^ 5 + 5 * (S + 1) := by ring
  have h5 : S + 1 ≤ (S + 1) ^ 5 := by
    calc S + 1 = (S + 1) ^ 1 := (pow_one _).symm
      _ ≤ (S + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-! ## List loops, parity rows -/

theorem map_add4_sum_le (cs : List ℕ) (c0 : ℕ) (hc : ∀ c ∈ cs, c ≤ c0) :
    (cs.map fun c => c + 4).sum ≤ cs.length * (c0 + 4) := by
  have := List.sum_le_card_nsmul (cs.map fun c => c + 4) (c0 + 4) (by
    intro x hx; obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hx; have := hc c hc'; omega)
  simpa using this

theorem loopHead_le (m S : ℕ) (hm : m ≤ S) :
    (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) ≤ 360 * (S + 1) ^ 2 := by
  have h1 : natBitLength m + 2 ≤ 3 * (S + 1) := by have := nbl_le m; omega
  have h2 : 40 * 2 ^ natBitLength m + 40 ≤ 120 * (S + 1) := by have := two_pow_nbl_le m; omega
  calc (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) ≤ (3 * (S + 1)) * (120 * (S + 1)) :=
        Nat.mul_le_mul h1 h2
    _ = 360 * (S + 1) ^ 2 := by ring

/-- `skipListCost m cs ≤ 360·(S+1)^2 + |cs|·(c₀+4) + 2`. -/
theorem skipListCost_le (m S c0 : ℕ) (cs : List ℕ) (hm : m ≤ S) (hc : ∀ c ∈ cs, c ≤ c0) :
    skipListCost m cs ≤ 360 * (S + 1) ^ 2 + cs.length * (c0 + 4) + 2 := by
  unfold skipListCost
  have := loopHead_le m S hm
  have := map_add4_sum_le cs c0 hc
  omega

/-- `copyListCost m cs ≤ 3700·(S+1)^2 + |cs|·(c₀+4) + 3`. -/
theorem copyListCost_le (m S c0 : ℕ) (cs : List ℕ) (hm : m ≤ S) (hc : ∀ c ∈ cs, c ≤ c0) :
    copyListCost m cs ≤ 3700 * (S + 1) ^ 2 + cs.length * (c0 + 4) + 3 := by
  unfold copyListCost
  have := loopHead_le m S hm
  have := map_add4_sum_le cs c0 hc
  have := nbl_mul_le m S 100 200 10 hm
  omega

theorem natWord_len_c (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by
  simp [natWord, WilliamsPublishedForm.framedNatBits, WilliamsPublishedForm.fixedWidthNatBits]; omega

theorem natWord_length_le (x S : ℕ) (hx : natBitLength x ≤ S) : (natWord x).length ≤ 2 * S + 1 := by
  rw [natWord_len_c]; omega

/-- A parity row's skip cost (`rowCost`, the `rb` of `parRow_spec`). -/
theorem rowCost_le (row : List ℕ) (S : ℕ) (hl : row.length ≤ S) (hx : ∀ x ∈ row, natBitLength x ≤ S) :
    rowCost row ≤ 400 * (S + 1) ^ 2 := by
  unfold rowCost
  have h := skipListCost_le row.length S (20 * S + 20) (row.map fun x => 20 * natBitLength x + 20) hl
    (by intro c hc; obtain ⟨x, hx', rfl⟩ := List.mem_map.1 hc; have := hx x hx'; omega)
  rw [List.length_map] at h
  have h2 : row.length * (20 * S + 20 + 4) ≤ S * (24 * (S + 1)) := Nat.mul_le_mul hl (by omega)
  have hc := pow_chain (S + 1) (by omega)
  nlinarith

/-- **`parRow_spec` cost class.** -/
theorem parRow_cost_le (Lb r rb : ℕ) (row : List ℕ) (S B : ℕ) (hLb : Lb ≤ S) (hr : r ≤ S) (hrb : rb ≤ B)
    (hl : row.length ≤ S) (hx : ∀ x ∈ row, natBitLength x ≤ S) :
    18 * Lb + 3 + 1 + (5 * Lb + 1) + 1 + (18 * r + 3 + 1 + (r * (rb + 4) + 1 + 1 +
      copyListCost row.length (row.map fun x => 60 * (natWord x).length + 60))) ≤ 4000 * (S + 1) ^ 2 * (B + 1) := by
  have hcl := copyListCost_le row.length S (120 * S + 120) (row.map fun x => 60 * (natWord x).length + 60) hl
    (by intro c hc; obtain ⟨x, hx', rfl⟩ := List.mem_map.1 hc; have := natWord_length_le x S (hx x hx'); omega)
  rw [List.length_map] at hcl
  have h2 : row.length * (120 * S + 120 + 4) ≤ S * (124 * (S + 1)) := Nat.mul_le_mul hl (by omega)
  have h3 : r * (rb + 4) ≤ S * (B + 4) := Nat.mul_le_mul hr (by omega)
  have hc := pow_chain (S + 1) (by omega)
  have h4 : (S + 1) ^ 2 * 1 ≤ (S + 1) ^ 2 * (B + 1) := Nat.mul_le_mul_left _ (by omega)
  have h5 : S * (B + 4) ≤ 4 * (S + 1) ^ 2 * (B + 1) := by nlinarith
  nlinarith

/-- **`callPairW_spec` cost class** (`c1`, `c2` the two `copyCircuitCost`s, `r0 = |natWord 0 ++ ratWord ω|`). -/
theorem callPairW_cost_le (q L i j cb c1 c2 r0 S B : ℕ) (hq : q ≤ S) (hL : L ≤ S) (hi : i ≤ S) (hj : j ≤ S)
    (hr0 : r0 ≤ S) (hcb : cb ≤ B) (hc1 : c1 ≤ B) (hc2 : c2 ≤ B) :
    (natBitLength q + 10) * (100 * q + 200) + 1 + (16 * (natWord 1).length + 1 +
      ((18 * L + 3 + 1 + (5 * L + 1)) + 1 + ((18 * i + 3 + 1 + (i * (cb + 4) + 1 + 1 + c1)) + 1 +
      ((18 * L + 3 + 1 + (5 * L + 1)) + 1 + ((18 * j + 3 + 1 + (j * (cb + 4) + 1 + 1 + c2)) + 1 +
      (16 * r0 + 1 + 7)))))) ≤ 5000 * (S + 1) ^ 2 * (B + 1) := by
  have h1 := nbl_mul_le q S 100 200 10 hq
  have hn1 : (natWord 1).length = 3 := rfl
  have h3 : i * (cb + 4) ≤ S * (B + 4) := Nat.mul_le_mul hi (by omega)
  have h4 : j * (cb + 4) ≤ S * (B + 4) := Nat.mul_le_mul hj (by omega)
  have hc := pow_chain (S + 1) (by omega)
  have h5 : (S + 1) ^ 2 * 1 ≤ (S + 1) ^ 2 * (B + 1) := Nat.mul_le_mul_left _ (by omega)
  have h6 : S * (B + 4) ≤ 4 * (S + 1) ^ 2 * (B + 1) := by nlinarith
  have h7 : B ≤ (S + 1) ^ 2 * (B + 1) := by nlinarith
  nlinarith

/-- **`callOneW_spec` cost class** (`c1 = copyCircuitCost`, `cp` the parity writer's cost, `nt = |natWord t|`,
`nE = |emptyCW|`, `rwl = |ratWord ω|`). -/
theorem callOneW_cost_le (q L j cb c1 cp nt nE rwl S B : ℕ) (hq : q ≤ S) (hL : L ≤ S) (hj : j ≤ S) (hnt : nt ≤ S)
    (hne : nE ≤ S) (hrw : rwl ≤ S) (hcb : cb ≤ B) (hc1 : c1 ≤ B) (hcp : cp ≤ B) :
    (natBitLength q + 10) * (100 * q + 200) + 1 + (16 * nt + 1 +
      ((18 * L + 3 + 1 + (5 * L + 1)) + 1 + ((18 * j + 3 + 1 + (j * (cb + 4) + 1 + 1 + c1)) + 1 +
      (16 * nE + 1 + (cp + 1 + (16 * rwl + 1 + 7)))))) ≤ 5000 * (S + 1) ^ 2 * (B + 1) := by
  have h1 := nbl_mul_le q S 100 200 10 hq
  have h4 : j * (cb + 4) ≤ S * (B + 4) := Nat.mul_le_mul hj (by omega)
  have hc := pow_chain (S + 1) (by omega)
  have h5 : (S + 1) ^ 2 * 1 ≤ (S + 1) ^ 2 * (B + 1) := Nat.mul_le_mul_left _ (by omega)
  have h6 : S * (B + 4) ≤ 4 * (S + 1) ^ 2 * (B + 1) := by nlinarith
  have h7 : B ≤ (S + 1) ^ 2 * (B + 1) := by nlinarith
  nlinarith

theorem emptyCW_length : emptyCW.length = 12 := rfl

/-! ## The per-circuit costs by the circuit's word length -/

section Circuits
open NearCubicGates.Close.Interfaces

theorem listWord_len {α : Type} (f : α → List Bool) (xs : List α) :
    (listWord f xs).length = (natWord xs.length).length + (xs.flatMap f).length := by
  simp [listWord]

theorem flatMap_len_ge {α : Type} (f : α → List Bool) (hf : ∀ x, 1 ≤ (f x).length) :
    ∀ xs : List α, xs.length ≤ (xs.flatMap f).length
  | [] => by simp
  | x :: xs => by
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := flatMap_len_ge f hf xs; have := hf x; omega

theorem mem_flatMap_len {α : Type} (f : α → List Bool) {xs : List α} {x : α} (hx : x ∈ xs) :
    (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons y xs ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hx with rfl | h
    · omega
    · have := ih h; omega

theorem listWord_count_le {α : Type} (f : α → List Bool) (hf : ∀ x, 1 ≤ (f x).length) (xs : List α) :
    xs.length ≤ (listWord f xs).length := by
  rw [listWord_len]; have := flatMap_len_ge f hf xs; omega

theorem listWord_mem_le {α : Type} (f : α → List Bool) {xs : List α} {x : α} (hx : x ∈ xs) :
    (f x).length ≤ (listWord f xs).length := by
  rw [listWord_len]; have := mem_flatMap_len f hx; omega

theorem natWord_len_pos (v : ℕ) : 1 ≤ (natWord v).length := by rw [natWord_len_c]; omega

theorem intWord_len_pos (z : ℤ) : 1 ≤ (Interfaces.intWord z).length := by
  simp only [Interfaces.intWord, List.length_append]; have := natWord_len_pos (if z < 0 then 1 else 0); omega

theorem nbl_le_intWord (z : ℤ) : natBitLength z.natAbs ≤ (Interfaces.intWord z).length := by
  simp only [Interfaces.intWord, List.length_append, natWord_len_c]; omega

theorem intCost_le (z : ℤ) : intCost z ≤ 61 + 20 * (Interfaces.intWord z).length := by
  unfold intCost skipIntCost
  have := nbl_le_intWord z
  have h1 : natBitLength (if z < 0 then 1 else 0) = 1 := by split_ifs <;> rfl
  omega

theorem gateWord_len_pos {n : ℕ} (g : NormalizedThresholdGate n) : 1 ≤ (gateWord g).length := by
  simp only [gateWord, List.length_append]; have := intWord_len_pos g.threshold; omega

theorem bitWord_len (b : Bool) : (bitWord b).length = 3 := by cases b <;> rfl

theorem gate_parts {n : ℕ} (g : NormalizedThresholdGate n) :
    n ≤ (gateWord g).length ∧ (∀ z ∈ List.ofFn g.weight, (Interfaces.intWord z).length ≤ (gateWord g).length) ∧
      (Interfaces.intWord g.threshold).length ≤ (gateWord g).length := by
  have hw : (listWord Interfaces.intWord (List.ofFn g.weight)).length ≤ (gateWord g).length := by
    simp only [gateWord, List.length_append]; omega
  refine ⟨?_, fun z hz => le_trans (listWord_mem_le Interfaces.intWord hz) hw, by simp [gateWord]⟩
  have := listWord_count_le Interfaces.intWord intWord_len_pos (List.ofFn g.weight)
  simp only [List.length_ofFn] at this
  omega

theorem circuit_parts {n : ℕ} (C : NCircuit n) :
    C.gates.length ≤ (circuitWord C).length ∧ (∀ g ∈ C.gates, (gateWord g).length ≤ (circuitWord C).length) ∧
      C.coeffs.length ≤ (circuitWord C).length ∧ (∀ z ∈ C.coeffs, (Interfaces.intWord z).length ≤ (circuitWord C).length) ∧
      C.table.length ≤ (circuitWord C).length := by
  have h1 : (listWord gateWord C.gates).length ≤ (circuitWord C).length := by
    simp only [circuitWord, List.length_append]; omega
  have h2 : (listWord Interfaces.intWord C.coeffs).length ≤ (circuitWord C).length := by
    simp only [circuitWord, List.length_append]; omega
  have h3 : (listWord bitWord C.table).length ≤ (circuitWord C).length := by
    simp only [circuitWord, List.length_append]; omega
  refine ⟨le_trans (listWord_count_le gateWord gateWord_len_pos _) h1,
    fun g hg => le_trans (listWord_mem_le gateWord hg) h1,
    le_trans (listWord_count_le Interfaces.intWord intWord_len_pos _) h2,
    fun z hz => le_trans (listWord_mem_le Interfaces.intWord hz) h2,
    le_trans (listWord_count_le bitWord (fun b => by rw [bitWord_len]; omega) _) h3⟩

/-- One gate's skip cost. -/
theorem gateCost_le {n : ℕ} (g : NormalizedThresholdGate n) (S : ℕ) (hS : (gateWord g).length ≤ S) :
    gateCost g ≤ 600 * (S + 1) ^ 2 := by
  obtain ⟨hn, hw, ht⟩ := gate_parts g
  unfold gateCost
  have h1 := skipListCost_le n S (61 + 20 * S) ((List.ofFn g.weight).map intCost) (by omega)
    (by intro c hc; obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hc; have := intCost_le z; have := hw z hz; omega)
  simp only [List.length_map, List.length_ofFn] at h1
  have h2 := intCost_le g.threshold
  have h3 : n * (61 + 20 * S + 4) ≤ S * (65 * (S + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have hc := pow_chain (S + 1) (by omega)
  nlinarith

/-- **The skip cost of one circuit** (the `cb` of the call writers and of the circuit seek). -/
theorem circuitCost_le {n : ℕ} (C : NCircuit n) (S : ℕ) (hS : (circuitWord C).length ≤ S) :
    circuitCost C ≤ 2000 * (S + 1) ^ 3 := by
  obtain ⟨hG, hg, hCc, hz, hT⟩ := circuit_parts C
  unfold circuitCost
  have hc := pow_chain (S + 1) (by omega)
  have h1 := skipListCost_le C.gates.length S (600 * (S + 1) ^ 2) (C.gates.map gateCost) (by omega)
    (by intro c hc'; obtain ⟨g, hg', rfl⟩ := List.mem_map.1 hc'; exact gateCost_le g S (le_trans (hg g hg') hS))
  have h2 := skipListCost_le C.coeffs.length S (61 + 20 * S) (C.coeffs.map intCost) (by omega)
    (by intro c hc'; obtain ⟨z, hz', rfl⟩ := List.mem_map.1 hc'; have := intCost_le z; have := hz z hz'; omega)
  have h3 := skipListCost_le C.table.length S 60 (C.table.map bitCost) (by omega)
    (by intro c hc'; obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc'; unfold bitCost
        have : natBitLength (if b then 1 else 0) = 1 := by cases b <;> rfl
        omega)
  simp only [List.length_map] at h1 h2 h3
  have e1 : C.gates.length * (600 * (S + 1) ^ 2 + 4) ≤ (S + 1) * (604 * (S + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1' : (S + 1) * (604 * (S + 1) ^ 2) = 604 * (S + 1) ^ 3 := by ring
  have e2 : C.coeffs.length * (61 + 20 * S + 4) ≤ (S + 1) * (65 * (S + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have e3 : C.table.length * (60 + 4) ≤ (S + 1) * 64 := Nat.mul_le_mul (by omega) le_rfl
  nlinarith

/-- **The copy cost of one circuit** (`copyCircuitCost`, in the call writers' costs). -/
theorem copyCircuitCost_le {n : ℕ} (C : NCircuit n) (S : ℕ) (hS : (circuitWord C).length ≤ S) (hn : n ≤ S) :
    copyCircuitCost C ≤ 20000 * (S + 1) ^ 3 := by
  obtain ⟨hG, hg, hCc, hz, hT⟩ := circuit_parts C
  unfold copyCircuitCost
  have hc := pow_chain (S + 1) (by omega)
  have hgate : ∀ gt ∈ C.gates, copyListCost n ((List.ofFn gt.weight).map
      fun z => 60 * (Interfaces.intWord z).length + 121) + 1 + (60 * (Interfaces.intWord gt.threshold).length + 121) ≤
      4100 * (S + 1) ^ 2 := by
    intro gt hgt
    obtain ⟨-, hw, ht⟩ := gate_parts gt
    have hgS := le_trans (hg gt hgt) hS
    have h := copyListCost_le n S (60 * S + 121) ((List.ofFn gt.weight).map
      fun z => 60 * (Interfaces.intWord z).length + 121) hn
      (by intro c hc'; obtain ⟨z, hz', rfl⟩ := List.mem_map.1 hc'; have := hw z hz'; omega)
    simp only [List.length_map, List.length_ofFn] at h
    have h2 : n * (60 * S + 121 + 4) ≤ S * (125 * (S + 1)) := Nat.mul_le_mul hn (by omega)
    nlinarith
  have h1 := copyListCost_le C.gates.length S (4100 * (S + 1) ^ 2) (C.gates.map fun gt =>
    copyListCost n ((List.ofFn gt.weight).map fun z => 60 * (Interfaces.intWord z).length + 121) + 1 +
      (60 * (Interfaces.intWord gt.threshold).length + 121)) (by omega)
    (by intro c hc'; obtain ⟨g, hg', rfl⟩ := List.mem_map.1 hc'; exact hgate g hg')
  have h2 := copyListCost_le C.coeffs.length S (60 * S + 121) (C.coeffs.map fun z => 60 * (Interfaces.intWord z).length + 121)
    (by omega) (by intro c hc'; obtain ⟨z, hz', rfl⟩ := List.mem_map.1 hc'; have := hz z hz'; omega)
  have h3 := copyListCost_le C.table.length S 240 (C.table.map fun b => 60 * (bitWord b).length + 60) (by omega)
    (by intro c hc'; obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc'; rw [bitWord_len])
  simp only [List.length_map] at h1 h2 h3
  have e1 : C.gates.length * (4100 * (S + 1) ^ 2 + 4) ≤ (S + 1) * (4104 * (S + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1' : (S + 1) * (4104 * (S + 1) ^ 2) = 4104 * (S + 1) ^ 3 := by ring
  have e2 : C.coeffs.length * (60 * S + 121 + 4) ≤ (S + 1) * (125 * (S + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have e3 : C.table.length * (240 + 4) ≤ (S + 1) * 244 := Nat.mul_le_mul (by omega) le_rfl
  nlinarith

end Circuits

section Wrap
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.Interfaces NearCubicGates.Close.Worker.Format

/-- `Codec.unframeW_spec` with its cost class. -/
theorem unframeW_class {ns nr : ℕ} (cap : ℕ)
    (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP K : Fin nr) (hKO : K ≠ OP) (bits : List Bool)
    (m : ℕ) (σ : WState ns nr) (hs : σ.st src = RepairOrdinary.frame bits) (hsh : σ.sh src = 0)
    (hd : σ.sh dst = (σ.st dst).length) (hK : σ.val K = m) (hm : m ≤ cap) (hc : σ.val OP + m ≤ cap) :
    WExec cap (unframeW src dst OP K) σ
      (((appendO σ dst OP (prefixBits bits m)).seth src (2 * min m bits.length)).setv K 0)
      (19 * (m + 1)) := by
  refine WExec.mono ?_ (unframeW_cost_le m)
  apply Codec.unframeW_spec <;> assumption

/-- `Codec.copyRW_spec` with its cost class. -/
theorem copyRW_class {ns nr : ℕ} (cap : ℕ)
    (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP T D : Fin nr) (hOT : OP ≠ T) (hOD : OP ≠ D)
    (hTD : T ≠ D) (x rest : List Bool) (σ : WState ns nr) (hst : σ.st src = RepairOrdinary.frame x ++ rest)
    (hsh : σ.sh src = 0) (hd : σ.st dst = []) (hdh : σ.sh dst = 0) (hO : σ.val OP = 0) (hT : σ.val T = 0)
    (hD : σ.val D = 0) (hc : 4 * x.length + 4 ≤ cap) :
    WExec cap (copyRW src dst OP T D) σ (σ.sets dst (RepairOrdinary.frame x))
      (100 * (x.length + 1)) := by
  refine WExec.mono ?_ (copyRW_cost_le x.length)
  apply Codec.copyRW_spec <;> assumption

/-- `Codec.transcodeW_spec` with its cost class. -/
theorem transcodeW_class' {ns nr : ℕ} (cap : ℕ)
    (W o : Fin (ns + 1)) (hWo : W ≠ o) (A : Fin 18 ↪ Fin nr) (C : Fin nr) (hC : ∀ i, A i ≠ C)
    (q m cb : ℕ) (σ : WState ns nr) (hq : σ.val (A 6) = q) (hz : ∀ i : Fin 18, i ≠ 6 → i ≠ 13 → σ.val (A i) = 0)
    (ho : σ.sh o = (σ.st o).length) (hC0 : σ.val C = m) (hm : m ≤ cap)
    (hcap1 : (σ.st W).length + q + 1 ≤ cap)
    (hcapO : σ.val (A 13) + 2 * ((List.range m).flatMap fun j => Interfaces.circuitWord (circAt (σ.st W) q (σ.sh W) j)).length +
      q + 7 * (σ.st W).length + 6 * natBitLength q + 20 ≤ cap)
    (hcb : ∀ j < m, circuitWCost q (σ.st W).length (cK (σ.st W) (circPos (σ.st W) q (σ.sh W) j))
      (cL (σ.st W) (circPos (σ.st W) q (σ.sh W) j) q) ≤ cb)
    (S B : ℕ) (hmS : m ≤ S) (hcbB : cb ≤ B) :
    WExec cap (transcodeW W o A C) σ
      ((appendO (σ.seth W (circPos (σ.st W) q (σ.sh W) m)) o (A 13)
        (cwPrefix (circAt (σ.st W) q (σ.sh W)) m)).setv C 0)
      ((S + 1) * (B + 5)) := by
  refine WExec.mono ?_ (transcodeW_cost_le m cb S B hmS hcbB)
  apply Codec.transcodeW_spec <;> assumption

/-- `Codec.parRow_spec` with its cost class. -/
theorem parRow_class {ns nr : ℕ} (cap : ℕ)
    (S o : Fin (ns + 1)) (hSo : S ≠ o) (Rg : Fin 16 ↪ Fin nr) (LS : Fin nr) (hLS : ∀ k, LS ≠ Rg k)
    (rows : ℕ → List ℕ) (R r : ℕ) (hr : r < R) (rb V Lb : ℕ) (hrb : ∀ j < R, rowCost (rows j) ≤ rb)
    (hfit : ∀ j < R, 2 ^ (natBitLength (rows j).length + 1) ≤ cap ∧ (rows j).length ≤ cap ∧
      ∀ x ∈ rows j, natBitLength x + 1 ≤ cap)
    (hrc : 2 * r ≤ cap) (hLb : 2 * Lb ≤ cap)
    (hrw : (rows r).length + V + 6 * natBitLength (rows r).length + 6 ≤ cap)
    (rest : List Bool) (τ : WState ns nr) (hst : τ.st S = rowPrefix rows R ++ rest) (hshL : τ.sh S ≤ Lb)
    (ho : τ.sh o = (τ.st o).length)
    (hz : ∀ k : Fin 16, k ≠ 7 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → τ.val (Rg k) = 0)
    (hR : τ.val (Rg 14) = r) (hLv : τ.val LS = Lb)
    (hV : τ.val (Rg 7) + (marks (listWord natWord (rows r))).length ≤ V)
    (Z B : ℕ) (hLbS : Lb ≤ Z) (hrS : r ≤ Z) (hrbB : rb ≤ B)
    (hlS : (rows r).length ≤ Z) (hxS : ∀ x ∈ rows r, natBitLength x ≤ Z) :
    WExec cap (parRow S o Rg LS) τ
      (appendO (τ.seth S (rowPrefix rows (r + 1)).length) o (Rg 7) (marks (listWord natWord (rows r))))
      (4000 * (Z + 1) ^ 2 * (B + 1)) := by
  refine WExec.mono ?_ (parRow_cost_le Lb r rb (rows r) Z B hLbS hrS hrbB hlS hxS)
  apply Codec.parRow_spec <;> assumption

/-- `Codec.callPairW_spec` with its cost class. -/
theorem callPairW_class {ns nr : ℕ} (cap : ℕ) (Rg : Fin 16 ↪ Fin nr)
    (CW o : Fin (ns + 1)) (hCo : CW ≠ o) {q : ℕ} (Cs : ℕ → NCircuit q) (N i j : ℕ)
    (hi : i < N) (hj : j < N) (ω : ℚ) (cb V L : ℕ)
    (hfit : ∀ k < N, CircuitFits cap (Cs k)) (hcb : ∀ k < N, circuitCost (Cs k) ≤ cb)
    (hcopy : ∀ k < N, CopyFits cap V (Cs k)) (hNc : 2 * N ≤ cap) (hLc : 2 * L ≤ cap)
    (hqc : q + V + 6 * natBitLength q + 6 ≤ cap)
    (rest : List Bool) (σ : WState ns nr) (hst : σ.st CW = cwPrefix Cs N ++ rest) (hshL : σ.sh CW ≤ L)
    (hLN : (cwPrefix Cs N).length ≤ L) (ho : σ.sh o = (σ.st o).length)
    (hz : ∀ k : Fin 16, k ≠ 7 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → σ.val (Rg k) = 0)
    (hQ : σ.val (Rg 15) = q) (hRi : σ.val (Rg 13) = i) (hRj : σ.val (Rg 14) = j) (hL : σ.val (Rg 12) = L)
    (hV : σ.val (Rg 7) + (RepairOrdinary.frame (callWord (pairCallOf Cs i j ω))).length ≤ V)
    (S B : ℕ) (hqS : q ≤ S) (hLS : L ≤ S) (hiS : i ≤ S) (hjS : j ≤ S)
    (hr0S : (natWord 0 ++ ratWord ω).length ≤ S) (hcbB : cb ≤ B) (hc1B : copyCircuitCost (Cs i) ≤ B)
    (hc2B : copyCircuitCost (Cs j) ≤ B) :
    WExec cap (callPairW CW o Rg ω) σ
      (appendO (σ.seth CW (cwPrefix Cs (j + 1)).length) o (Rg 7)
        (RepairOrdinary.frame (callWord (pairCallOf Cs i j ω))))
      (5000 * (S + 1) ^ 2 * (B + 1)) := by
  refine WExec.mono ?_ (callPairW_cost_le q L i j cb _ _ _ S B hqS hLS hiS hjS hr0S hcbB hc1B hc2B)
  apply Codec.callPairW_spec <;> assumption

/-- `Codec.callOneW_spec` with its cost class. -/
theorem callOneW_class {ns nr : ℕ} (cap : ℕ) (Rg : Fin 16 ↪ Fin nr)
    (CW o SUP : Fin (ns + 1)) (hCo : CW ≠ o) (hSo : SUP ≠ o) (hSC : SUP ≠ CW) {q : ℕ}
    (Cs : ℕ → NCircuit q) (N j : ℕ) (hj : j < N) (ps : List ℕ) (t : ℕ) (ht : t = if ps = [] then 0 else 2)
    (parW : WM ns nr) (ω : ℚ) (cb V L cp pSup : ℕ)
    (hfit : ∀ k < N, CircuitFits cap (Cs k)) (hcb : ∀ k < N, circuitCost (Cs k) ≤ cb)
    (hcopy : ∀ k < N, CopyFits cap V (Cs k)) (hNc : 2 * N ≤ cap) (hLc : 2 * L ≤ cap)
    (hqc : q + V + 6 * natBitLength q + 6 ≤ cap)
    (rest : List Bool) (σ : WState ns nr) (hst : σ.st CW = cwPrefix Cs N ++ rest) (hshL : σ.sh CW ≤ L)
    (ho : σ.sh o = (σ.st o).length)
    (hz : ∀ k : Fin 16, k ≠ 7 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → σ.val (Rg k) = 0)
    (hQ : σ.val (Rg 15) = q) (hRj : σ.val (Rg 13) = j) (hL : σ.val (Rg 12) = L)
    (hV : σ.val (Rg 7) + (RepairOrdinary.frame (callWord (oneCallOf Cs j ps ω))).length ≤ V)
    (hpar : ∀ τ : WState ns nr, (∀ k : Fin 16, k ≠ 7 → τ.val (Rg k) = σ.val (Rg k)) →
      (∀ r, (∀ k : Fin 16, r ≠ Rg k) → τ.val r = σ.val r) → τ.sh o = (τ.st o).length → τ.st SUP = σ.st SUP → τ.sh SUP = σ.sh SUP →
      τ.val (Rg 7) + (marks (listWord natWord ps)).length ≤ V →
      WExec cap parW τ (appendO (τ.seth SUP pSup) o (Rg 7) (marks (listWord natWord ps))) cp)
    (S B : ℕ) (hqS : q ≤ S) (hLS : L ≤ S) (hjS : j ≤ S) (hntS : (natWord t).length ≤ S)
    (hneS : emptyCW.length ≤ S) (hrwS : (ratWord ω).length ≤ S) (hcbB : cb ≤ B) (hc1B : copyCircuitCost (Cs j) ≤ B)
    (hcpB : cp ≤ B) :
    WExec cap (callOneW CW o Rg t parW ω) σ
      (appendO ((σ.seth CW (cwPrefix Cs (j + 1)).length).seth SUP pSup) o (Rg 7)
        (RepairOrdinary.frame (callWord (oneCallOf Cs j ps ω))))
      (5000 * (S + 1) ^ 2 * (B + 1)) := by
  refine WExec.mono ?_ (callOneW_cost_le q L j cb _ cp _ _ _ S B hqS hLS hjS hntS hneS hrwS hcbB hc1B hcpB)
  apply Codec.callOneW_spec <;> assumption

/-- `Codec.circuitW_spec` with its cost class. -/
theorem circuitW_class {ns nr : ℕ} (cap : ℕ)
    (W o : Fin (ns + 1)) (A : Fin 18 ↪ Fin nr) (σ : WState ns nr) (q : ℕ)
    (h : CirPre cap W o A σ q)
    (S : ℕ) (hqS : q ≤ S) (hwS : (σ.st W).length ≤ S) :
    WExec cap (circuitW W o A) σ
      (appendO (σ.seth W (circuitEnd (σ.st W) (σ.sh W) q)) o (A 13)
        (marks (Interfaces.circuitWord (readCircuit q ((σ.st W).drop (σ.sh W))).1)))
      (20000 * (S + 1) ^ 4) := by
  refine WExec.mono ?_ (circuitWCost_field_le q (σ.st W) (σ.sh W) S hqS hwS)
  apply Codec.circuitW_spec <;> assumption

end Wrap

end NearCubicGates.Close.WorkerArith

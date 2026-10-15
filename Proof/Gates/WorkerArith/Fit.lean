import Proof.Gates.WorkerArith.FitSpec

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close

theorem nbl_le' (n : ℕ) : natBitLength n ≤ n + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 n; omega

theorem two_pow_nbl_le' (n : ℕ) : 2 ^ natBitLength n ≤ 2 * (n + 1) := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    rw [pow_succ]; omega

theorem natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by simp [natWord]

/-- `W ≤ W^3`, `W^2 ≤ W^3`, `1 ≤ W^3` for `W ≥ 1`. -/
theorem cube_facts {W : ℕ} (h : 1 ≤ W) : 1 ≤ W ^ 3 ∧ W ≤ W ^ 3 ∧ W ^ 2 ≤ W ^ 3 :=
  ⟨Nat.one_le_pow _ _ h, by simpa using Nat.pow_le_pow_right h (show 1 ≤ 3 by norm_num),
    Nat.pow_le_pow_right h (by norm_num)⟩

theorem nbl_le_natWord (v : ℕ) : natBitLength v ≤ (natWord v).length := by rw [natWord_len]; omega

/-- The list-header cost at a count `m ≤ W`. -/
theorem header_le {m W : ℕ} (h : m ≤ W) :
    (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) ≤ (W + 3) * (80 * W + 120) := by
  have h1 := nbl_le' m
  have h2 := two_pow_nbl_le' m
  exact Nat.mul_le_mul (by omega) (by omega)

theorem sum_le_of_le {xs : List ℕ} {B : ℕ} (h : ∀ c ∈ xs, c ≤ B) : ((xs.map fun c => c + 4).sum) ≤ xs.length * (B + 4) := by
  have := List.sum_le_card_nsmul (xs.map fun c => c + 4) (B + 4) (by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; have := h c hc; omega)
  simpa using this

theorem skipListCost_le {m W B : ℕ} {cs : List ℕ} (hm : m ≤ W) (hl : cs.length ≤ W) (h : ∀ c ∈ cs, c ≤ B) :
    Codec.skipListCost m cs ≤ (W + 3) * (80 * W + 120) + 2 + W * (B + 4) := by
  unfold Codec.skipListCost
  have h1 := header_le hm
  have h2 := sum_le_of_le h
  have h3 : cs.length * (B + 4) ≤ W * (B + 4) := Nat.mul_le_mul_right _ hl
  omega

/-! ## Rows -/

theorem rowCost_le {q W : ℕ} (row : List ℕ) (hx : ∀ x ∈ row, x < q) (hl : row.length ≤ q) (hW : q + 2 ≤ W) :
    Codec.rowCost row ≤ 100000 * W ^ 3 := by
  unfold Codec.rowCost
  have hb : ∀ c ∈ row.map (fun x => 20 * natBitLength x + 20), c ≤ 20 * W + 40 := by
    intro c hc
    obtain ⟨x, hxr, rfl⟩ := List.mem_map.mp hc
    have := nbl_le' x; have := hx x hxr; omega
  have h := skipListCost_le (m := row.length) (W := W) (B := 20 * W + 40) (cs := row.map _) (by omega)
    (by rw [List.length_map]; omega) hb
  have hW1 : 1 ≤ W := by omega
  obtain ⟨c1, c2, c3⟩ := cube_facts hW1
  have : (W + 3) * (80 * W + 120) + 2 + W * (20 * W + 40 + 4) ≤ 100000 * W ^ 3 := by nlinarith
  omega

theorem listWord_nat_len (row : List ℕ) :
    (Interfaces.listWord natWord row).length = 2 * natBitLength row.length + 1 + (row.map fun x => 2 * natBitLength x + 1).sum := by
  unfold Interfaces.listWord
  rw [List.length_append, natWord_len, List.length_flatMap]
  congr 1
  congr 1
  exact List.map_congr_left (fun x _ => natWord_len x)

theorem rowSizeFit : RowSizeFit := by
  intro q row W hx hl hW
  have hW1 : 1 ≤ W := by omega
  refine ⟨rowCost_le row hx hl hW, ⟨?_, by omega, fun x hxr => ?_⟩, ?_⟩
  · have := two_pow_nbl_le' row.length; rw [pow_succ]; omega
  · have := nbl_le' x; have := hx x hxr; omega
  · rw [listWord_nat_len]
    have hs : (row.map fun x => 2 * natBitLength x + 1).sum ≤ row.length * (2 * W + 3) := by
      have := List.sum_le_card_nsmul (row.map fun x => 2 * natBitLength x + 1) (2 * W + 3) (by
        intro a ha; obtain ⟨x, hxr, rfl⟩ := List.mem_map.mp ha; have := nbl_le' x; have := hx x hxr; omega)
      simpa using this
    have h1 := nbl_le' row.length
    have h2 : row.length * (2 * W + 3) ≤ W * (2 * W + 3) := Nat.mul_le_mul_right _ (by omega)
    nlinarith

/-! ## Circuits -/

theorem len_le_flatMap {α : Type} (f : α → List Bool) {xs : List α} {x : α} (hx : x ∈ xs) :
    (f x).length ≤ (xs.flatMap f).length := by
  rw [List.length_flatMap]; exact List.le_sum_of_mem (List.mem_map_of_mem hx)

theorem count_le_flatMap {α : Type} (f : α → List Bool) (xs : List α) (h : ∀ x, 1 ≤ (f x).length) :
    xs.length ≤ (xs.flatMap f).length := by
  rw [List.length_flatMap]
  have := List.length_le_sum_of_one_le (xs.map fun x => (f x).length) (by
    intro a ha; obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; exact h x)
  simpa using this

theorem intWord_pos (z : ℤ) : 1 ≤ (Interfaces.intWord z).length := by
  simp [Interfaces.intWord]; omega

theorem nbl_le_intWord (z : ℤ) : natBitLength z.natAbs ≤ (Interfaces.intWord z).length := by
  simp [Interfaces.intWord]; omega

theorem listWord_len_ge {α : Type} (f : α → List Bool) (xs : List α) :
    (xs.flatMap f).length ≤ (Interfaces.listWord f xs).length := by
  simp [Interfaces.listWord]

/-- Sizes of a circuit word: counts and every number are at most the word length `L`. -/
structure Sizes {q : ℕ} (C : Interfaces.NCircuit q) (L : ℕ) : Prop where
  g : C.gates.length ≤ L
  c : C.coeffs.length ≤ L
  t : C.table.length ≤ L
  gw : ∀ gt ∈ C.gates, (∀ z ∈ List.ofFn gt.weight, (Interfaces.intWord z).length ≤ L) ∧ (Interfaces.intWord gt.threshold).length ≤ L
  cw : ∀ z ∈ C.coeffs, (Interfaces.intWord z).length ≤ L

theorem sizes {q : ℕ} (C : Interfaces.NCircuit q) : Sizes C (Interfaces.circuitWord C).length := by
  have hG := listWord_len_ge Interfaces.gateWord C.gates
  have hC := listWord_len_ge Interfaces.intWord C.coeffs
  have hT := listWord_len_ge Interfaces.bitWord C.table
  have hL : (Interfaces.circuitWord C).length = (Interfaces.listWord Interfaces.gateWord C.gates).length +
      (Interfaces.listWord Interfaces.intWord C.coeffs).length + (Interfaces.listWord Interfaces.bitWord C.table).length := by
    simp [Interfaces.circuitWord]; omega
  have gpos : ∀ gt : NormalizedThresholdGate q, 1 ≤ (Interfaces.gateWord gt).length := fun gt => by
    have := intWord_pos gt.threshold; simp [Interfaces.gateWord]; omega
  have bpos : ∀ b : Bool, 1 ≤ (Interfaces.bitWord b).length := fun b => by simp [Interfaces.bitWord]
  refine ⟨?_, ?_, ?_, fun gt hgt => ⟨fun z hz => ?_, ?_⟩, fun z hz => ?_⟩
  · have := count_le_flatMap Interfaces.gateWord C.gates gpos; omega
  · have := count_le_flatMap Interfaces.intWord C.coeffs intWord_pos; omega
  · have := count_le_flatMap Interfaces.bitWord C.table bpos; omega
  · have h1 := len_le_flatMap Interfaces.intWord hz
    have h2 := listWord_len_ge Interfaces.intWord (List.ofFn gt.weight)
    have h3 := len_le_flatMap Interfaces.gateWord hgt
    have h4 : (Interfaces.listWord Interfaces.intWord (List.ofFn gt.weight)).length ≤ (Interfaces.gateWord gt).length := by
      simp [Interfaces.gateWord]
    omega
  · have h3 := len_le_flatMap Interfaces.gateWord hgt
    have h4 : (Interfaces.intWord gt.threshold).length ≤ (Interfaces.gateWord gt).length := by simp [Interfaces.gateWord]
    omega
  · have := len_le_flatMap Interfaces.intWord hz; omega

theorem pow_nbl_succ_le {m W : ℕ} (h : m ≤ W) : 2 ^ (natBitLength m + 1) ≤ 4 * W + 4 := by
  have := two_pow_nbl_le' m; rw [pow_succ]; omega

theorem nbl01 (b : Prop) [Decidable b] : natBitLength (if b then 1 else 0) ≤ 1 := by
  split_ifs <;> decide

theorem intCost_le {z : ℤ} {W : ℕ} (h : (Interfaces.intWord z).length ≤ W) : Codec.intCost z ≤ 20 * W + 81 := by
  unfold Codec.intCost Codec.skipIntCost
  have := nbl_le_intWord z
  have := nbl01 (z < 0)
  omega

theorem copyListCost_le {m W B : ℕ} {cs : List ℕ} (hm : m ≤ W) (hl : cs.length ≤ W) (h : ∀ c ∈ cs, c ≤ B) :
    Codec.copyListCost m cs ≤ (W + 3) * (80 * W + 120) + 1 + ((W + 11) * (100 * W + 200) + 1 + (W * (B + 4) + 1)) := by
  unfold Codec.copyListCost
  have h1 := header_le hm
  have h2 := sum_le_of_le h
  have h3 : cs.length * (B + 4) ≤ W * (B + 4) := Nat.mul_le_mul_right _ hl
  have h4 : (natBitLength m + 10) * (100 * m + 200) ≤ (W + 11) * (100 * W + 200) := by
    have := nbl_le' m; exact Nat.mul_le_mul (by omega) (by omega)
  omega

theorem circuitSizeFit : CircuitSizeFit := by
  intro q C W hW
  obtain ⟨sg, sc, st, sgw, scw⟩ := sizes C
  set L := (Interfaces.circuitWord C).length with hLdef
  have hW2 : 2 ≤ W := by omega
  have hW1 : 1 ≤ W := by omega
  have hq : q ≤ W := by omega
  have hLW : L ≤ W := by omega
  obtain ⟨c1, c2, c3⟩ := cube_facts hW1
  refine ⟨?_, ?_, ?_, fun cap V hcap => ?_⟩
  · -- the circuit fits capacity `4W + 4`
    refine ⟨fun gt hgt => ⟨pow_nbl_succ_le hq, by omega, fun z hz => ?_, ?_⟩, pow_nbl_succ_le (by omega), by omega,
      pow_nbl_succ_le (by omega), by omega, fun z hz => ?_, pow_nbl_succ_le (by omega), by omega, by omega⟩
    · have := nbl_le_intWord z; have := (sgw gt hgt).1 z hz; omega
    · have := nbl_le_intWord gt.threshold; have := (sgw gt hgt).2; omega
    · have := nbl_le_intWord z; have := scw z hz; omega
  · -- the skip cost
    have hgate : ∀ gt ∈ C.gates, Codec.gateCost gt ≤
        (W + 3) * (80 * W + 120) + 2 + W * (20 * W + 81 + 4) + 1 + (20 * W + 81) := by
      intro gt hgt
      unfold Codec.gateCost
      have h1 := skipListCost_le (m := q) (W := W) (B := 20 * W + 81)
        (cs := (List.ofFn gt.weight).map Codec.intCost) hq (by simp; omega) (by
          intro c hc; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc
          exact intCost_le (((sgw gt hgt).1 z hz).trans hLW))
      have h2 := intCost_le (((sgw gt hgt).2).trans hLW)
      omega
    have hG := skipListCost_le (m := C.gates.length) (W := W) (cs := C.gates.map Codec.gateCost) (by omega)
      (by simp; omega) (fun c hc => by obtain ⟨gt, hgt, rfl⟩ := List.mem_map.mp hc; exact hgate gt hgt)
    have hC := skipListCost_le (m := C.coeffs.length) (W := W) (B := 20 * W + 81) (cs := C.coeffs.map Codec.intCost)
      (by omega) (by simp; omega) (fun c hc => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc; exact intCost_le ((scw z hz).trans hLW))
    have hT := skipListCost_le (m := C.table.length) (W := W) (B := 40) (cs := C.table.map Codec.bitCost)
      (by omega) (by simp; omega) (fun c hc => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc; unfold Codec.bitCost; have := nbl01 (b = true); omega)
    unfold Codec.circuitCost
    nlinarith
  · -- the copy cost
    have hgate : ∀ gt ∈ C.gates, Codec.copyListCost q ((List.ofFn gt.weight).map
        fun z => 60 * (Interfaces.intWord z).length + 121) + 1 + (60 * (Interfaces.intWord gt.threshold).length + 121) ≤
        (W + 3) * (80 * W + 120) + 1 + ((W + 11) * (100 * W + 200) + 1 + (W * (60 * W + 121 + 4) + 1)) + 1 +
          (60 * W + 121) := by
      intro gt hgt
      have h1 := copyListCost_le (m := q) (W := W) (B := 60 * W + 121)
        (cs := (List.ofFn gt.weight).map fun z => 60 * (Interfaces.intWord z).length + 121) hq (by simp; omega) (by
          intro c hc; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc; have := (sgw gt hgt).1 z hz; omega)
      have h2 := (sgw gt hgt).2
      omega
    have hG := copyListCost_le (m := C.gates.length) (W := W) (by omega) (by simp; omega)
      (cs := C.gates.map fun gt => Codec.copyListCost q ((List.ofFn gt.weight).map
        fun z => 60 * (Interfaces.intWord z).length + 121) + 1 + (60 * (Interfaces.intWord gt.threshold).length + 121))
      (fun c hc => by obtain ⟨gt, hgt, rfl⟩ := List.mem_map.mp hc; exact hgate gt hgt)
    have hC := copyListCost_le (m := C.coeffs.length) (W := W) (B := 60 * W + 121)
      (cs := C.coeffs.map fun z => 60 * (Interfaces.intWord z).length + 121) (by omega) (by simp; omega) (fun c hc => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc; have := scw z hz; omega)
    have hT := copyListCost_le (m := C.table.length) (W := W) (B := 240)
      (cs := C.table.map fun b => 60 * (Interfaces.bitWord b).length + 60) (by omega) (by simp; omega) (fun c hc => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc
        have : (Interfaces.bitWord b).length ≤ 3 := by
          simp [Interfaces.bitWord]; have := nbl01 (b = true); omega
        omega)
    unfold Codec.copyCircuitCost
    nlinarith
  · -- the copy capacities
    have hq6 := nbl_le' q
    refine ⟨by omega, (pow_nbl_succ_le hq).trans (by omega), by omega, by omega, fun m hm => ?_⟩
    have hmW : m ≤ W := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> omega
    have := nbl_le' m
    exact ⟨(pow_nbl_succ_le hmW).trans (by omega), by omega, by omega⟩

end NearCubicGates.Close.WorkerArith.WorkerBounds

import Proof.Gates.Recovery.AfterHeadStep

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g)

theorem wP_input (ν : ℕ) (z : BitInput (2 ^ ν)) (j : Fin (wP s g).tapeCount) :
    (wP s g).inputTapes (List.ofFn z) j = if j.val = 0 then RepairOrdinary.frame (List.ofFn z) else [] := rfl

theorem width_piece (k : ℕ) (hk : k < 31) (ht : sz K k = (wP s g).tapeCount) (xw q : Fin 32) (hxq : xw ≠ q)
    (A : Fin (T K) → List Bool) (ν : ℕ) (z : BitInput (2 ^ ν))
    (hx : A (sh K xw) = RepairOrdinary.frame (List.ofFn z)) (hq : A (sh K q) = []) (hbl : BlankFrom K k A) :
    ∃ n, n ≤ 2 * ((OuterM.widthDonor s.mw (g.sv s)).K * (2 ^ ν + 1) ^ 1) + 2 ∧ ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat
        ((ports K).program (ordinary (RecoveryFocus.machine (widBank K k hk ht xw q hxq).slot (wP s g).machine)))
        n A A' ∧
      BlankFrom K (k + 1) A' ∧ (∀ i : Fin 32, i ≠ xw → i ≠ q → A' (sh K i) = A (sh K i)) ∧
      A' (sh K q) = List.replicate (g.width s ν) true := by
  obtain ⟨out, hr, ho⟩ := CheckedPCPP.wordFunction_ready (OuterM.widthDonor s.mw (g.sv s)).unary ⟨2 ^ ν, z⟩
  obtain ⟨n, hn, h⟩ := exact_time hr
  have h0 : 0 < (wP s g).tapeCount := by have := (wP s g).twoTapes; omega
  have hout0 : ((wP s g).outputTape).val ≠ 0 := (wP s g).outputFresh
  have hl1 : ([(⟨0, h0⟩, xw), ((wP s g).outputTape, q)].map Prod.fst).Nodup := by
    simp only [List.map_cons, List.map_nil]
    exact nodup2 (fun e => hout0 (by rw [← e]))
  have hl2 : ([(⟨0, h0⟩, xw), ((wP s g).outputTape, q)].map Prod.snd).Nodup := by simpa using nodup2 hxq
  obtain ⟨hR, hB, hU, hW⟩ := bank_piece K k hk ht [(⟨0, h0⟩, xw), ((wP s g).outputTape, q)] hl1 hl2 h A
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [hx]; rfl
      · rw [hq]
        show [] = (wP s g).inputTapes (List.ofFn z) (wP s g).outputTape
        rw [wP_input, if_neg hout0])
    (by
      intro j hj
      show (wP s g).inputTapes (List.ofFn z) j = []
      rw [wP_input, if_neg]
      intro h0'
      apply hj
      simp only [List.map_cons, List.map_nil, List.mem_cons]
      exact Or.inl (Fin.ext h0'))
    hbl
  refine ⟨n, hn, _, hR, hB, ?_, ?_⟩
  · intro i hi1 hi2
    apply hU
    simp [hi1, hi2]
  · rw [hW ((wP s g).outputTape, q) (by simp), ho]
    show List.replicate (OuterM.qOf s.mw (g.sv s) (2 ^ ν)) true = _
    rw [OuterM.qOf_two_pow]
    rfl

/-- **The `ν` piece** (piece 10): `1^ν` on NU (`9`) from `frame z` on XN (`29`). -/
theorem nu_piece (A : Fin (T K) → List Bool) (ν : ℕ) (z : BitInput (2 ^ ν))
    (hx : A (sh K 29) = RepairOrdinary.frame (List.ofFn z)) (hq : A (sh K 9) = []) (hbl : BlankFrom K 10 A) :
    ∃ n, n ≤ nuDonor.K * (2 ^ ν + 1) ∧ ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat
        ((ports K).program (ordinary (RecoveryFocus.machine (nuBank K).slot nuDonor.M))) n A A' ∧
      BlankFrom K 11 A' ∧ (∀ i : Fin 32, i ≠ 29 → i ≠ 9 → A' (sh K i) = A (sh K i)) ∧
      A' (sh K 9) = List.replicate ν true := by
  obtain ⟨out, hr, ho⟩ := nuDonor.run (List.ofFn z)
  obtain ⟨n, hn, h⟩ := exact_time hr
  have hl1 : ([(nuDonor.inp, (29 : Fin 32)), (nuDonor.outp, 9)].map Prod.fst).Nodup := by
    simpa using nodup2 nuDonor.ne
  have hl2 : ([(nuDonor.inp, (29 : Fin 32)), (nuDonor.outp, 9)].map Prod.snd).Nodup := by decide
  obtain ⟨hR, hB, hU, hW⟩ := bank_piece K 10 (by decide) rfl [(nuDonor.inp, 29), (nuDonor.outp, 9)] hl1 hl2 h A
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [hx]; simp [oneBank]
      · rw [hq]; simp [oneBank, Ne.symm nuDonor.ne])
    (by
      intro j hj
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      show oneBank nuDonor.inp _ j = []
      unfold oneBank
      split_ifs with he
      · exact absurd he hj.1
      · rfl)
    hbl
  refine ⟨n, by simpa [List.length_ofFn] using hn, _, hR, hB, ?_, ?_⟩
  · intro i hi1 hi2
    apply hU
    simp [hi1, hi2]
  · rw [hW (nuDonor.outp, 9) (by simp), ho, List.length_ofFn, Nat.log_pow (by norm_num)]

/-! ## The pieces 0–10, by definition -/

section Pieces

variable (c : Cfg)

theorem pieces_0 : pieces K c ⟨0, by decide⟩ = copyP K 0 (by decide) le_rfl (sh K 0) (sh K 4) := rfl
theorem pieces_1 : pieces K c ⟨1, by decide⟩ = copyP K 1 (by decide) le_rfl (sh K 0) (sh K 25) := rfl
theorem pieces_2 : pieces K c ⟨2, by decide⟩ = ordinary (RecoveryFocus.machine (b2 K).slot (wP s g).machine) := rfl
theorem pieces_3 : pieces K c ⟨3, by decide⟩ = copyP K 3 (by decide) le_rfl (sh K 0) (sh K 26) := rfl
theorem pieces_4 : pieces K c ⟨4, by decide⟩ = ordinary (RecoveryFocus.machine (b4 K).slot (wP s g).machine) := rfl
theorem pieces_5 : pieces K c ⟨5, by decide⟩ = copyP K 5 (by decide) le_rfl (sh K 0) (sh K 27) := rfl
theorem pieces_6 : pieces K c ⟨6, by decide⟩ = ordinary (RecoveryFocus.machine (b6 K).slot (wP s g).machine) := rfl
theorem pieces_7 : pieces K c ⟨7, by decide⟩ = copyP K 7 (by decide) le_rfl (sh K 0) (sh K 28) := rfl
theorem pieces_8 : pieces K c ⟨8, by decide⟩ = ordinary (RecoveryFocus.machine (b8 K).slot (wP s g).machine) := rfl
theorem pieces_9 : pieces K c ⟨9, by decide⟩ = copyP K 9 (by decide) le_rfl (sh K 0) (sh K 29) := rfl
theorem pieces_10 : pieces K c ⟨10, by decide⟩ = ordinary (RecoveryFocus.machine (nuBank K).slot nuDonor.M) := rfl

end Pieces

end NearCubicGates.Close.Recovery.After

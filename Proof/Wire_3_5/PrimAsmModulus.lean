import Proof.Wire_3_5.GF2Primitive
import Proof.MachineModel.Layout
import Proof.MachineModel.OrdinaryRewindWorkspace

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Modulus
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5

/-! ## The words -/

theorem binary_zero' (ℓ : ℕ) : binary ℓ 0 = List.replicate ℓ false := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [binary, ih, List.replicate_succ]

theorem binary_one (ℓ : ℕ) : binary (ℓ + 1) 1 = true :: List.replicate ℓ false := by
  simp [binary, binary_zero']

theorem binary_ones (ℓ : ℕ) : binary ℓ (2 ^ ℓ - 1) = List.replicate ℓ true := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    have h1 : (2 ^ (ℓ + 1) - 1) % 2 = 1 := by
      have : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
      rw [pow_succ]; omega
    have h2 : (2 ^ (ℓ + 1) - 1) / 2 = 2 ^ ℓ - 1 := by
      have : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
      rw [pow_succ]; omega
    simp [binary, h1, h2, ih, List.replicate_succ]

theorem frame_eq_marks (w : List Bool) : frame w = Streaming.marks w ++ [false] := by
  have h := Streaming.frame_append w []
  simpa [frame] using h

/-! ## The bank kernel

Tapes: `0` the unary degree, `1 … 4` the zero words, `5` the word `1`, `6` the word `2^ℓ − 1`, `7` the zeros. States:
`0` first mark, `1` first bit, `2` mark, `3` bit, `4` the last zero, `5` halt. -/

def bankK : Machine 8 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 5
  rule := fun q bits =>
    if q.val = 0 then
      some (if bits 0 then
          ⟨1, ![none, some true, some true, some true, some true, some true, some true, some false],
            ![.stay, .right, .right, .right, .right, .right, .right, .right]⟩
        else ⟨4, ![none, some false, some false, some false, some false, some false, some false, some false],
            ![.stay, .stay, .stay, .stay, .stay, .stay, .stay, .right]⟩)
    else if q.val = 1 then
      some ⟨2, ![none, some false, some false, some false, some false, some true, some true, some false],
        fun _ => .right⟩
    else if q.val = 2 then
      some (if bits 0 then
          ⟨3, ![none, some true, some true, some true, some true, some true, some true, some false],
            ![.stay, .right, .right, .right, .right, .right, .right, .right]⟩
        else ⟨4, ![none, some false, some false, some false, some false, some false, some false, some false],
            ![.stay, .stay, .stay, .stay, .stay, .stay, .stay, .right]⟩)
    else if q.val = 3 then
      some ⟨2, ![none, some false, some false, some false, some false, some false, some true, some false],
        fun _ => .right⟩
    else if q.val = 4 then
      some ⟨5, ![none, none, none, none, none, none, none, some false], fun _ => .stay⟩
    else none

/-- A configuration: the unary degree `U` at `u`, the words `A` (four times), `B`, `C` at their ends, the zeros `Z` at
its end. -/
def bcfg (q : Fin 6) (u : ℕ) (U A B C Z : List Bool) : Configuration 8 6 :=
  ⟨q, ![u, A.length, A.length, A.length, A.length, B.length, C.length, Z.length], ![U, A, A, A, A, B, C, Z]⟩

theorem first_step (U : List Bool) (h : readTapeBit U 0 = true) :
    step bankK (bcfg 0 0 U [] [] [] []) = some (bcfg 1 0 U [true] [true] [true] [false]) := by
  simp [step, bankK, bcfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, writeTapeBit]

theorem firstBit_step (U A B C Z : List Bool) :
    step bankK (bcfg 1 0 U A B C Z) = some (bcfg 2 1 U (A ++ [false]) (B ++ [true]) (C ++ [true]) (Z ++ [false])) := by
  simp [step, bankK, bcfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

theorem mark_step (u : ℕ) (U A B C Z : List Bool) (h : readTapeBit U u = true) :
    step bankK (bcfg 2 u U A B C Z) = some (bcfg 3 u U (A ++ [true]) (B ++ [true]) (C ++ [true]) (Z ++ [false])) := by
  simp [step, bankK, bcfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

theorem bit_step (u : ℕ) (U A B C Z : List Bool) :
    step bankK (bcfg 3 u U A B C Z) =
      some (bcfg 2 (u + 1) U (A ++ [false]) (B ++ [false]) (C ++ [true]) (Z ++ [false])) := by
  simp [step, bankK, bcfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

theorem end_step (u : ℕ) (U A B C Z : List Bool) (h : readTapeBit U u = false) :
    step bankK (bcfg 2 u U A B C Z) = some ⟨4, ![u, A.length, A.length, A.length, A.length, B.length, C.length,
      Z.length + 1], ![U, A ++ [false], A ++ [false], A ++ [false], A ++ [false], B ++ [false], C ++ [false],
        Z ++ [false]]⟩ := by
  simp [step, bankK, bcfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

theorem write_end2 (Z : List Bool) (b c : Bool) : writeTapeBit (Z ++ [b]) (Z.length + 1) c = Z ++ [b, c] := by
  have h := write_end (Z ++ [b]) c
  simpa using h

theorem last_step (u : ℕ) (U A B C Z : List Bool) :
    step bankK ⟨4, ![u, A.length, A.length, A.length, A.length, B.length, C.length, Z.length + 1],
      ![U, A ++ [false], A ++ [false], A ++ [false], A ++ [false], B ++ [false], C ++ [false], Z ++ [false]]⟩ =
      some ⟨5, ![u, A.length, A.length, A.length, A.length, B.length, C.length, Z.length + 1],
        ![U, A ++ [false], A ++ [false], A ++ [false], A ++ [false], B ++ [false], C ++ [false],
          Z ++ [false] ++ [false]]⟩ := by
  simp [step, bankK, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end, write_end2]

/-- The loop over the degree after the first unit. -/
theorem bank_loop (ℓ : ℕ) (d : ℕ) : ∀ u, u + d = ℓ → 1 ≤ u →
    Timed bankK (2 * d)
      (bcfg 2 u (List.replicate ℓ true) (Streaming.marks (List.replicate u false))
        (Streaming.marks (true :: List.replicate (u - 1) false)) (Streaming.marks (List.replicate u true))
        (List.replicate (2 * u) false))
      (bcfg 2 ℓ (List.replicate ℓ true) (Streaming.marks (List.replicate ℓ false))
        (Streaming.marks (true :: List.replicate (ℓ - 1) false)) (Streaming.marks (List.replicate ℓ true))
        (List.replicate (2 * ℓ) false)) := by
  induction d with
  | zero =>
    intro u hu _
    rw [Nat.add_zero] at hu
    subst hu
    exact Timed.refl _ _
  | succ d ih =>
    intro u hu h1
    have hr : readTapeBit (List.replicate ℓ true) u = true := read_replicate_true ℓ u (by omega)
    have s1 := Timed.single (p := bankK) (by rfl) (mark_step u (List.replicate ℓ true)
      (Streaming.marks (List.replicate u false)) (Streaming.marks (true :: List.replicate (u - 1) false))
      (Streaming.marks (List.replicate u true)) (List.replicate (2 * u) false) hr)
    have s2 := Timed.single (p := bankK) (by rfl) (bit_step u (List.replicate ℓ true)
      (Streaming.marks (List.replicate u false) ++ [true]) (Streaming.marks (true :: List.replicate (u - 1) false) ++ [true])
      (Streaming.marks (List.replicate u true) ++ [true]) (List.replicate (2 * u) false ++ [false]))
    have e1 : Streaming.marks (List.replicate u false) ++ [true] ++ [false] = Streaming.marks (List.replicate (u + 1) false) := by
      rw [List.replicate_succ', Streaming.marks_append]; simp [Streaming.marks]
    have e2 : Streaming.marks (true :: List.replicate (u - 1) false) ++ [true] ++ [false] =
        Streaming.marks (true :: List.replicate (u + 1 - 1) false) := by
      rw [show u + 1 - 1 = (u - 1) + 1 by omega, List.replicate_succ', ← List.cons_append, Streaming.marks_append]
      simp [Streaming.marks]
    have e3 : Streaming.marks (List.replicate u true) ++ [true] ++ [true] = Streaming.marks (List.replicate (u + 1) true) := by
      rw [List.replicate_succ', Streaming.marks_append]; simp [Streaming.marks]
    have e4 : List.replicate (2 * u) false ++ [false] ++ [false] = List.replicate (2 * (u + 1)) false := by
      rw [show 2 * (u + 1) = 2 * u + 1 + 1 by ring, List.replicate_succ', List.replicate_succ']
    rw [e1, e2, e3, e4] at s2
    have s3 := ih (u + 1) (by omega) (by omega)
    have h := (s1.trans s2).trans s3
    rw [show 1 + 1 + 2 * d = 2 * (d + 1) by ring] at h
    exact h

/-- The final configuration of the kernel. -/
def bankFinal (ℓ : ℕ) : Fin 8 → List Bool :=
  ![List.replicate ℓ true, frame (binary ℓ 0), frame (binary ℓ 0), frame (binary ℓ 0), frame (binary ℓ 0),
    frame (binary ℓ 1), frame (binary ℓ (2 ^ ℓ - 1)), List.replicate (2 * ℓ + 2) false]

theorem bank_run (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ∃ r : ExecutionReceipt 8 6,
    run bankK (2 * ℓ + 2) ![List.replicate ℓ true, [], [], [], [], [], [], []] = some r ∧
      r.final.tapes = bankFinal ℓ ∧ r.steps = 2 * ℓ + 2 := by
  set U := List.replicate ℓ true with hU
  have s1 := Timed.single (p := bankK) (by rfl) (first_step U (read_replicate_true ℓ 0 (by omega)))
  have s2 := Timed.single (p := bankK) (by rfl) (firstBit_step U [true] [true] [true] [false])
  have s2' : Timed bankK 1 (bcfg 1 0 U [true] [true] [true] [false])
      (bcfg 2 1 U (Streaming.marks (List.replicate 1 false)) (Streaming.marks (true :: List.replicate (1 - 1) false))
        (Streaming.marks (List.replicate 1 true)) (List.replicate (2 * 1) false)) := s2
  have s3 := bank_loop ℓ (ℓ - 1) 1 (by omega) le_rfl
  have s4 := Timed.single (p := bankK) (by rfl) (end_step ℓ U (Streaming.marks (List.replicate ℓ false))
    (Streaming.marks (true :: List.replicate (ℓ - 1) false)) (Streaming.marks (List.replicate ℓ true))
    (List.replicate (2 * ℓ) false) (read_replicate_end ℓ true))
  have s5 := Timed.single (p := bankK) (by rfl) (last_step ℓ U (Streaming.marks (List.replicate ℓ false))
    (Streaming.marks (true :: List.replicate (ℓ - 1) false)) (Streaming.marks (List.replicate ℓ true))
    (List.replicate (2 * ℓ) false))
  have h := (((s1.trans s2').trans s3).trans s4).trans s5
  obtain ⟨r, hr, hf, hs⟩ := h.run rfl
  have hinit : bcfg 0 0 U [] [] [] [] = initialConfiguration bankK ![U, [], [], [], [], [], [], []] := by
    apply configuration_ext
    · rfl
    · funext k; fin_cases k <;> rfl
    · rfl
  rw [hinit] at hr
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [show 1 + 1 + 2 * (ℓ - 1) + 1 + 1 = 2 * ℓ + 2 by omega] at hr
    exact hr
  · rw [hf]
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    funext k
    fin_cases k <;> simp [bankFinal, hU, frame_eq_marks, binary_zero', binary_one, binary_ones, List.replicate_succ',
      show 2 * (ℓ' + 1) + 2 = 2 * (ℓ' + 1) + 1 + 1 by ring]
  · rw [hs]; omega

/-- **The bank stage**: the kernel under base `Rewind`, all heads back at `0`. -/
theorem bank_step (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ∃ tout : Fin (8 + 1) → List Bool,
    Step (Rewind.machine bankK) (4 * ℓ + 6) (fun _ => 0)
      (Fin.addCases ![List.replicate ℓ true, [], [], [], [], [], [], []] (fun _ => [])) (fun _ => 0) tout ∧
      ∀ i : Fin 8, tout (i.castAdd 1) = bankFinal ℓ i := by
  obtain ⟨src, hsrc, hf, hs⟩ := bank_run ℓ hℓ
  obtain ⟨r, hr, htapes, _, hheads, hsteps, _⟩ := Rewind.Workspace.reset_workspace bankK _ _ src hsrc 0
  refine ⟨r.final.tapes, ⟨r, ?_, funext hheads, rfl, ?_⟩, ?_⟩
  · rw [show 2 * src.steps + 2 = 4 * ℓ + 6 by rw [hs]; ring] at hr
    exact hr
  · rw [hsteps, hs]; omega
  · intro i
    rw [htapes i, hf]

/-! ## The flag cells -/

/-- One transition writing `false` on all eight (blank) tapes. -/
def cellsK : Machine 8 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some false, fun _ => .stay⟩ else none

theorem cells_step : Step cellsK 1 (fun _ => 0) (fun _ => []) (fun _ => 0) (fun _ => [false]) := by
  have hs : step cellsK (⟨0, fun _ => 0, fun _ => []⟩ : Configuration 8 2) = some ⟨1, fun _ => 0, fun _ => [false]⟩ := by
    simp [step, cellsK]
    apply configuration_ext
    · rfl
    · funext k; simp [applyAction, HeadMove.apply]
    · funext k; simp [applyAction, writeTapeBit]
  obtain ⟨r, hr, hf, hsteps⟩ := (Timed.single (p := cellsK) (by rfl) hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], le_of_eq hsteps⟩

/-! ## The layout and the machine

Seventeen tapes: `0` the unary degree, `1 + j` the search bank's tape `j` (`j < 15`), `16` the kernel's rewind log. -/

def sb (j : Fin 15) : Fin 17 := ⟨1 + j.val, by omega⟩

def s1 : Fin (8 + 1) → Fin 17 := ![0, 1, 2, 3, 12, 4, 5, 11, 16]
def s2 : Fin 8 → Fin 17 := ![6, 7, 8, 9, 10, 13, 14, 15]

theorem s1_inj : Function.Injective s1 := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [s1]
theorem s2_inj : Function.Injective s2 := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [s2]
theorem sb_inj : Function.Injective sb := by
  intro a b h; have := congrArg Fin.val h; simp [sb] at this; exact Fin.ext this

/-- **The modulus machine.** -/
noncomputable def modM :=
  Composition.machine (Composition.machine (RecoveryFocus.machine s1 (Rewind.machine bankK))
    (RecoveryFocus.machine s2 cellsK)) (RecoveryFocus.machine sb GF2.searchM)

/-! ## The run -/

theorem inst_at {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → List Bool)
    (tout : Fin t → List Bool) (j : Fin t) (i : Fin u) (hij : slots j = i) : install slots A tout i = tout j := by
  subst hij
  exact install_slot slots hi A tout j

theorem inst_off {t u : ℕ} (slots : Fin t → Fin u) (A : Fin u → List Bool) (tout : Fin t → List Bool) (i : Fin u)
    (h : ∀ k, slots k ≠ i) : install slots A tout i = A i :=
  install_other slots A tout i h

theorem dock0 {t u s : ℕ} {p : Machine t s} {n : ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A : Fin u → List Bool) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n (fun _ => 0) A (fun _ => 0) (install slots A tout) := by
  have h' := h.dock slots hi (fun _ => 0) A (fun _ => rfl) hA
  rwa [GF2.dockH_zero'] at h'

/-- The search's stale entry bank (all words `0`, all flags `false`). -/
def junk0 : GF2.Junk := ⟨0, 0, false, false, false, false, false⟩

/-- The run's cost: the bank, the flags, the search. -/
def modCost (ℓ : ℕ) : ℕ := 4 * ℓ + 6 + 1 + 1 + 1 + GF2.searchCost ℓ

theorem modulus_step (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ∃ tout : Fin 17 → List Bool,
    Step modM (modCost ℓ) (fun _ => 0) (fun i => if i.val = 0 then List.replicate ℓ true else []) (fun _ => 0) tout ∧
      tout 0 = List.replicate ℓ true ∧ tout 12 = frame (binary ℓ (GF.firstPrimitive ℓ)) := by
  set A0 : Fin 17 → List Bool := fun i => if i.val = 0 then List.replicate ℓ true else [] with hA0
  -- the bank
  obtain ⟨tout1, h1l, ht1⟩ := bank_step ℓ hℓ
  have h1 := dock0 h1l s1 s1_inj A0 (by
    intro k
    fin_cases k <;> rfl)
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = install s1 A0 tout1 := ⟨_, rfl⟩
  rw [← hA1] at h1
  have hA1b : ∀ i : Fin 8, A1 (s1 (i.castAdd 1)) = bankFinal ℓ i := by
    intro i; rw [hA1, inst_at s1 s1_inj _ _ (i.castAdd 1) _ rfl, ht1 i]
  have hA1o : ∀ i : Fin 17, (∀ k, s1 k ≠ i) → A1 i = [] := by
    intro i hi
    rw [hA1, inst_off s1 _ _ i hi]
    have h0 : i ≠ 0 := fun h => hi 0 (by rw [h]; rfl)
    have hv : i.val ≠ 0 := fun h => h0 (Fin.ext h)
    simp only [hA0]
    exact if_neg hv
  -- the flags
  have h2 := dock0 cells_step s2 s2_inj A1 (by
    intro k
    exact hA1o _ (by intro k'; fin_cases k <;> fin_cases k' <;> decide))
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = install s2 A1 (fun _ => [false]) := ⟨_, rfl⟩
  rw [← hA2] at h2
  have hA2f : ∀ k : Fin 8, A2 (s2 k) = [false] := by
    intro k; rw [hA2, inst_at s2 s2_inj _ _ k _ rfl]
  have hA2o : ∀ i : Fin 17, (∀ k, s2 k ≠ i) → A2 i = A1 i := by
    intro i hi; rw [hA2, inst_off s2 _ _ i hi]
  -- the search
  have h3l := GF2.search_run ℓ (2 * ℓ + 2) junk0 0 0 false false false hℓ le_rfl
  have hin : ∀ j : Fin 15, A2 (sb j) = GF2.srIn ℓ (2 * ℓ + 2) junk0 0 0 false false false j := by
    intro j
    fin_cases j
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 1
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 2
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 3
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 5
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 6
    · exact hA2f 0
    · exact hA2f 1
    · exact hA2f 2
    · exact hA2f 3
    · exact hA2f 4
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 7
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 4
    · exact hA2f 5
    · exact hA2f 6
    · exact hA2f 7
  have h3 := dock0 h3l sb sb_inj A2 hin
  have h := (h1.seq h2).seq h3
  refine ⟨_, h, ?_, ?_⟩
  · rw [inst_off sb _ _ 0 (by intro k h; have := congrArg Fin.val h; simp [sb] at this),
      hA2o _ (by intro k; fin_cases k <;> decide)]
    exact hA1b 0
  · rw [inst_at sb sb_inj _ _ 11 12 rfl]
    exact GF2.srBank_out ℓ (2 * ℓ + 2) junk0 false

end NearCubicWires.WireExponent3_5.PrimAsm.Modulus

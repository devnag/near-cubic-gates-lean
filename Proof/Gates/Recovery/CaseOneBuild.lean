import Proof.Gates.Recovery.CaseOneHead

/-!
# The Case 1 machine, part 4: the amplifier's input word

`build_exec`: from the entry state, `buildW` (head, cyclic table, frame end, rewinds) leaves exactly
`frame (amplifierInput ⟨q, cycFn a w q⟩) = frame (frame q.bits ++ boolFunctionTable (cycFn a w q))` on `X`
(`sec:all-lengths`, "Run the general amplifier" on the Case 1 hard function, `sec:gadget-extract`), with every
head at `0` and every
other stream unchanged. The cost is `O(q·2^q)`, independent of `|w|` (the cyclic loop never reads past the first frame
of `W`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.CaseOneMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)

/-- The cost of `buildW`. -/
def buildCost (q : ℕ) : ℕ := 200 * (q + 1) * (2 ^ q + 1)

/-- The register capacity `buildW` needs. -/
def buildCap (a q : ℕ) : ℕ := 8 * 2 ^ q + 8 * q + 2 * 2 ^ a + 20

/-- **The amplifier's input word.** -/
theorem build_exec (tA : ℕ) (a q : ℕ) (w : BitInput (2 ^ a)) (rest addr : List Bool) (cap : ℕ)
    (hcap : buildCap a q ≤ cap) :
    ∃ τ n, WXExec cap (buildW tA) (initCaseOne tA (frame (List.ofFn w) ++ rest) addr q) τ n ∧ n ≤ buildCost q ∧
      τ.st (X tA) = frame (frame q.bits ++ boolFunctionTable (Recovery.cycFn a w q)) ∧ τ.sh (X tA) = 0 ∧
      τ.cell = false ∧
      (∀ i, i ≠ X tA → τ.st i = (initCaseOne tA (frame (List.ofFn w) ++ rest) addr q).st i ∧ τ.sh i = 0) := by
  set s0 := initCaseOne tA (frame (List.ofFn w) ++ rest) addr q with hs0
  set wl := List.ofFn w with hwl
  have hL : wl.length = 2 ^ a := by simp [hwl]
  have hL1 : 0 < wl.length := by rw [hL]; positivity
  have hq2 : q < 2 ^ q := Nat.lt_two_pow_self
  have hbl := bits_len_le q
  unfold buildCap at hcap
  have hhl := hdr_length q
  obtain ⟨t1, n1, e1, hn1, hX1, hXh1, hO1, hK1, hS1, hc1, hk1⟩ := head_exec tA cap (frame wl ++ rest) addr q
    (by omega)
  have dWX : W tA ≠ X tA := by cdst
  have hW1 : t1.st (W tA) = marks wl ++ false :: rest := by
    rw [(hk1 _ dWX).1]; simp [hs0, initCaseOne, threeWords, frame_eq_marks]
  have hWh1 : t1.sh (W tA) = 2 * 0 := (hk1 _ dWX).2
  -- the cyclic table
  have x2 := cycW_spec cap (W := W tA) (X := X tA) (opX := opX) (SC := SC) (rK := rK) dWX (by decide) (by decide)
    (by decide) wl rest (by rw [hL]; omega) (2 ^ q) 0 t1 hL1 hW1 hWh1 (by rw [hS1]) hK1 (by omega)
    (by rw [hX1, hXh1]) (by rw [hO1, hhl]; omega)
  obtain ⟨t2, ht2, e2⟩ := named (WXExec.wm x2)
  set T := cycFrom wl 0 (2 ^ q) with hT
  have hTl : T.length = 2 ^ q := cycFrom_length _ _ _
  have hX2 : t2.st (X tA) = hdr q ++ marks T := by rw [ht2]; simp [pos, appendO, hX1]
  have hXh2 : t2.sh (X tA) = (hdr q ++ marks T).length := by
    rw [ht2]; simp [pos, appendO, Function.update_apply, Ne.symm dWX, hXh1]
  have hO2 : t2.val opX = (hdr q ++ marks T).length := by
    rw [ht2]; simp (config := { decide := true }) [pos, appendO, Function.update_apply, hO1]
  have hS2 : t2.val SC = 2 * (2 ^ q % wl.length) := by
    rw [ht2]; simp (config := { decide := true }) [pos, appendO, Function.update_apply]
  have hWh2 : t2.sh (W tA) = 2 * (2 ^ q % wl.length) := by
    rw [ht2]; simp [pos, appendO, Function.update_apply]
  have hmT : (marks T).length = 2 * 2 ^ q := by rw [marks_length, hTl]
  have hmod : 2 ^ q % wl.length ≤ 2 ^ q := Nat.mod_le _ _
  -- the frame end
  have x3 := Codec.emitBit_spec (cap := cap) (X tA) opX false t2 (by rw [hXh2, hX2])
    (by rw [hO2]; simp [hhl, hmT]; omega)
  obtain ⟨t3, ht3, e3⟩ := named (WXExec.wm x3)
  have x4 := wrewind_spec (cap := cap) (X tA) opX ((hdr q ++ marks T).length + 1) t3
    (by rw [ht3]; simp (config := { decide := true }) [appendO, Function.update_apply, hO2])
    (by rw [ht3]; simp (config := { decide := true }) [appendO, Function.update_apply, hO2, hhl, hmT]; omega)
  obtain ⟨t4, ht4, e4⟩ := named (WXExec.wm x4)
  have x5 := wrewind_spec (cap := cap) (W tA) SC (2 * (2 ^ q % wl.length)) t4
    (by rw [ht4, ht3]; simp (config := { decide := true }) [appendO, Function.update_apply, hS2])
    (by rw [ht4, ht3]; simp (config := { decide := true }) [appendO, Function.update_apply, hS2]; omega)
  obtain ⟨t5, ht5, e5⟩ := named (WXExec.wm x5)
  have whole := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))
  refine ⟨t5, _, whole, ?_, ?_, ?_, ?_, ?_⟩
  · have hh : headCost q = 100 * (q * 2 ^ q) + 100 * q + 100 * 2 ^ q + 100 := by unfold headCost; ring
    have hb : buildCost q = 200 * (q * 2 ^ q) + 200 * q + 200 * 2 ^ q + 200 := by unfold buildCost; ring
    rw [hb]
    rw [hh] at hn1
    simp only [List.length_append, hhl, hmT, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    omega
  · rw [ht5, ht4, ht3]
    simp [appendO, Function.update_apply, hX2, dWX, Ne.symm dWX]
    rw [xWord_eq, CaseOneSem.table_cycFn, ← cycFrom_zero_eq, ← hwl, ← hT]
    simp [hdr, List.append_assoc]
  · rw [ht5, ht4, ht3]
    simp [appendO, Function.update_apply, Ne.symm dWX, hXh2]
  · rw [ht5, ht4, ht3, ht2]; simp [pos, appendO, hc1]
  · intro i hi
    by_cases hiW : i = W tA
    · subst hiW
      have hst : t5.st (W tA) = t2.st (W tA) := by rw [ht5, ht4, ht3]; simp [appendO, Function.update_apply, hi]
      have hsh : t5.sh (W tA) = 0 := by rw [ht5, ht4, ht3]; simp [appendO, Function.update_apply, hi, hWh2]
      refine ⟨?_, hsh⟩
      rw [hst, ht2]; simp [pos, appendO, Function.update_apply, hi, (hk1 _ hi).1, hs0]
    · rw [ht5, ht4, ht3, ht2]
      simp [pos, appendO, Function.update_apply, hi, hiW, hk1 _ hi, hs0]

end NearCubicGates.Close.Recovery.CaseOneMachine

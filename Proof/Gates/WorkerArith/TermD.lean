import Proof.Gates.WorkerArith.TermC

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit circuitWord listWord)
open NearCubicGates.Close.Codec (oneCallOf pairCallOf cwPrefix rowPrefix emptyCW)

variable {ns nr : ℕ}

/-- **A call branch in ideal form**: an exact writer run from the start with the call stream emptied, then
`callFinW`. -/
theorem callBranch_ideal {B1 B2 : ℕ} (ctr : Counter B1 B2) (E : TermEnv ns nr)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) (f : Fin 40) (hf : f = 0 ∨ f = 39)
    {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ} {rows : ℕ → List ℕ} {Rn : ℕ} {c : Call} {w pre rest : List Bool}
    (cap Z : ℕ) {σ : WState ns nr} (ρ : WState ns nr) (Wp : WM ns nr) (cW : ℕ)
    (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (ew : WExec cap Wp (σ.sets E.S1 []) ρ cW)
    (hF : FinPre E σ ρ c Z)
    (h7 : σ.val (E.R 7) ≤ Z) (h8 : σ.val (E.R 8) ≤ Z) (hZc : Z + (frame (callWord c)).length ≤ cap)
    (hcap : σ.val (E.R 9) + 8 * ((callWord c).length + w.length + ctr.budget c w) + 60 ≤ cap) :
    ∃ τ, WXExec cap (.seq (.wm Wp) (callFinW E ctr tmap f hf)) σ τ
        (cW + 1 + finCost ctr.program.program.tapeCount (callWord c).length w.length (ctr.budget c w)
          (frame (callWord c)).length Z) ∧
      SimW (termIdeal σ tmap E (pre.length + w.length + 1 + w.length)
        (bitWord (decide (σ.val (E.R f) ≠ 0)) ++ outputWord (ctr.value c w))) τ := by
  obtain ⟨τ1, e1, s1⟩ := callFin_ideal ctr E tmap f hf cap Z hB hF h7 h8 hZc hcap
  have e := WXExec.seq (WXExec.wm ew) e1
  have hs0 : SimW (σ.sets E.S1 []) σ := CheckedPCPP.SimW.symm (Worker.simW_sets σ E.S1 [] (blank_nil hB.b1))
  obtain ⟨τ', e', s'⟩ := wxexec_sim e σ hs0
  exact ⟨τ', e', CheckedPCPP.SimW.trans s1 s'⟩

/-! ## Call-word sizes -/

theorem callWord_one_len {q : ℕ} (Cs : ℕ → NCircuit q) (j : ℕ) (ps : List ℕ) (ω : ℚ) :
    (callWord (oneCallOf Cs j ps ω)).length = (natWord q).length + (natWord (if ps = [] then 0 else 2)).length +
      (circuitWord (Cs j)).length + 12 + (listWord natWord ps).length + (ratWord ω).length := by
  have h := congrArg List.length (Codec.frame_oneCall Cs j ps ω)
  simp only [List.length_append, Codec.marks_length, List.length_singleton, frame_len', emptyCW_length] at h
  omega

theorem callWord_pair_len {q : ℕ} (Cs : ℕ → NCircuit q) (i j : ℕ) (ω : ℚ) :
    (callWord (pairCallOf Cs i j ω)).length = (natWord q).length + 3 + (circuitWord (Cs i)).length +
      (circuitWord (Cs j)).length + 3 + (ratWord ω).length := by
  have h := congrArg List.length (Codec.frame_pairCall Cs i j ω)
  have h1 : (natWord 1).length = 3 := rfl
  have h0 : (natWord 0).length = 3 := rfl
  simp only [List.length_append, Codec.marks_length, List.length_singleton, frame_len', h1, h0] at h
  omega

theorem natWord_len_le (x Z : ℕ) (h : x ≤ Z) : (natWord x).length ≤ 2 * Z + 3 := by
  rw [natWord_len_c]; have := nbl_le x; omega

theorem callWord_one_le {q : ℕ} (Cs : ℕ → NCircuit q) (j : ℕ) (ps : List ℕ) (ω : ℚ) (Z : ℕ) (hq : q ≤ Z)
    (hc : (circuitWord (Cs j)).length ≤ Z) (hp : (listWord natWord ps).length ≤ 2 * Z + 10)
    (hω : (ratWord ω).length ≤ Z) : (callWord (oneCallOf Cs j ps ω)).length ≤ 10 * Z + 40 := by
  rw [callWord_one_len]
  have h1 := natWord_len_le q Z hq
  have h2 : (natWord (if ps = [] then 0 else 2)).length ≤ 5 := by split_ifs <;> decide
  omega

theorem callWord_pair_le {q : ℕ} (Cs : ℕ → NCircuit q) (i j : ℕ) (ω : ℚ) (Z : ℕ) (hq : q ≤ Z)
    (hi : (circuitWord (Cs i)).length ≤ Z) (hj : (circuitWord (Cs j)).length ≤ Z)
    (hω : (ratWord ω).length ≤ Z) : (callWord (pairCallOf Cs i j ω)).length ≤ 10 * Z + 40 := by
  rw [callWord_pair_len]
  have h1 := natWord_len_le q Z hq
  omega

theorem listWord_nil_len : (listWord natWord ([] : List ℕ)).length = 3 := rfl

theorem listWord_single_le (u Z : ℕ) (hu : u ≤ Z) : (listWord natWord [u]).length ≤ 2 * Z + 10 := by
  have h := natWord_len_le u Z hu
  simp [listWord] at h ⊢
  have h1 : natBitLength 1 = 1 := rfl
  omega

/-- The cost class of a call writer. -/
def writerCost (Z B : ℕ) : ℕ := 30000000 * (Z + 13) ^ 4 * (B + 1)

/-- The parity-writer budget. -/
def parB (Z B : ℕ) : ℕ := 4000 * (Z + 13) ^ 2 * (B + 1)

theorem callOne_cost_fit (Z B : ℕ) : 5000 * (Z + 12 + 1) ^ 2 * (parB Z B + 1) ≤ 20010000 * (Z + 13) ^ 4 * (B + 1) := by
  unfold parB
  have h : (Z + 12 + 1) = Z + 13 := by ring
  rw [h]
  have hp : 0 < (Z + 13) ^ 2 * (B + 1) := by positivity
  nlinarith [hp]

end NearCubicGates.Close.WorkerArith

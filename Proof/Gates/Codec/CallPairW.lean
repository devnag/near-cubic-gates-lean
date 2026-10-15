import Proof.Gates.Codec.CallPair

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

section Regs
variable (Rg : Fin 16 ↪ Fin nr)

theorem Rg_ne {a b : Fin 16} (h : a ≠ b) : Rg a ≠ Rg b := Rg.injective.ne h

/-- The copy registers `Rg 0 … Rg 7`. -/
def rgC : Fin 8 ↪ Fin nr := ⟨fun i => Rg ⟨i.val, by omega⟩, fun a b h => by
  have := Rg.injective h; ext; simpa using congrArg Fin.val this⟩

/-- The `writeNatM` registers: `Rg 15` (the value `q`), `Rg 1 … Rg 6`, `Rg 7`. -/
def rgW : Fin 8 ↪ Fin nr :=
  ⟨fun i => if i.val = 0 then Rg 15 else Rg ⟨i.val, by omega⟩, fun a b h => by
    have key : ∀ i : Fin 8, (if i.val = 0 then (15 : Fin 16) else ⟨i.val, by omega⟩) = (if i.val = 0 then (15 : Fin 16) else ⟨i.val, by omega⟩) := fun _ => rfl
    have h' : Rg (if a.val = 0 then 15 else ⟨a.val, by omega⟩) = Rg (if b.val = 0 then 15 else ⟨b.val, by omega⟩) := by
      have ea : (if a.val = 0 then Rg 15 else Rg ⟨a.val, by omega⟩) = Rg (if a.val = 0 then 15 else ⟨a.val, by omega⟩) := by
        split <;> rfl
      have eb : (if b.val = 0 then Rg 15 else Rg ⟨b.val, by omega⟩) = Rg (if b.val = 0 then 15 else ⟨b.val, by omega⟩) := by
        split <;> rfl
      rw [← ea, ← eb]; exact h
    have := Rg.injective h'
    clear key h h'
    fin_cases a <;> fin_cases b <;> simp_all (config := { decide := true })⟩

theorem rgC_val (i : Fin 8) : rgC Rg i = Rg ⟨i.val, by omega⟩ := rfl

theorem fetchRegs : FetchRegs (rgC Rg) (Rg 8) (Rg 9) (Rg 13) (Rg 10) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, Rg_ne Rg (by decide), Rg_ne Rg (by decide),
    Rg_ne Rg (by decide), Rg_ne Rg (by decide), Rg_ne Rg (by decide), Rg_ne Rg (by decide)⟩ <;>
    (rw [rgC_val]; apply Rg_ne; intro h; have := congrArg Fin.val h; simp at this; omega)

theorem fetchRegs' : FetchRegs (rgC Rg) (Rg 8) (Rg 9) (Rg 14) (Rg 10) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, Rg_ne Rg (by decide), Rg_ne Rg (by decide),
    Rg_ne Rg (by decide), Rg_ne Rg (by decide), Rg_ne Rg (by decide), Rg_ne Rg (by decide)⟩ <;>
    (rw [rgC_val]; apply Rg_ne; intro h; have := congrArg Fin.val h; simp at this; omega)

end Regs

/-- The pair call of the worker (v2 lines 2209–2215): circuits `i` and `j`, no parity, radius `ω`. -/
def pairCallOf {q : ℕ} (Cs : ℕ → NCircuit q) (i j : ℕ) (ω : ℚ) : Call := ⟨q, .pair, Cs i, Cs j, [], ω⟩

/-- **The pair-call writer.** -/
def callPairW (CW o : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) (ω : ℚ) : WM ns nr :=
  .seq (writeNatM o (rgW Rg))
  (.seq (emitMarks o (Rg 7) (natWord 1))
  (.seq (rewindCW CW (Rg 12) (Rg 11) (Rg 10))
  (.seq (fetchCircuit CW o (rgC Rg) (Rg 8) (Rg 9) (Rg 13) (Rg 10) (fetchRegs Rg).hm)
  (.seq (rewindCW CW (Rg 12) (Rg 11) (Rg 10))
  (.seq (fetchCircuit CW o (rgC Rg) (Rg 8) (Rg 9) (Rg 14) (Rg 10) (fetchRegs' Rg).hm)
  (.seq (emitMarks o (Rg 7) (natWord 0 ++ ratWord ω)) (emitC o (Rg 7) false)))))))

section Spec
variable (Rg : Fin 16 ↪ Fin nr)

theorem rgW_zero : rgW Rg 0 = Rg 15 := rfl
theorem rgW_one : rgW Rg 1 = Rg 1 := rfl
theorem rgW_two : rgW Rg 2 = Rg 2 := rfl
theorem rgW_three : rgW Rg 3 = Rg 3 := rfl
theorem rgW_four : rgW Rg 4 = Rg 4 := rfl
theorem rgW_five : rgW Rg 5 = Rg 5 := rfl
theorem rgW_six : rgW Rg 6 = Rg 6 := rfl
theorem rgW_seven : rgW Rg 7 = Rg 7 := rfl
theorem rgC_seven : rgC Rg 7 = Rg 7 := rfl

theorem cwPrefix_length_mono {q : ℕ} (Cs : ℕ → NCircuit q) {a b : ℕ} (h : a ≤ b) :
    (cwPrefix Cs a).length ≤ (cwPrefix Cs b).length := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · rw [cwPrefix_succ, List.length_append]; have := ih (by omega); omega
    · have : a = b + 1 := by omega
      subst this; exact le_rfl

theorem frame_pairCall {q : ℕ} (Cs : ℕ → NCircuit q) (i j : ℕ) (ω : ℚ) :
    RepairOrdinary.frame (callWord (pairCallOf Cs i j ω)) =
      marks (natWord q) ++ marks (natWord 1) ++ marks (circuitWord (Cs i)) ++ marks (circuitWord (Cs j)) ++
        marks (natWord 0 ++ ratWord ω) ++ [false] := by
  rw [frame_eq_marks]
  simp [callWord, pairCallOf, kindTag, listWord, marksApp, List.append_assoc]

theorem callPairW_spec (CW o : Fin (ns + 1)) (hCo : CW ≠ o) {q : ℕ} (Cs : ℕ → NCircuit q) (N i j : ℕ)
    (hi : i < N) (hj : j < N) (ω : ℚ) (cb V L : ℕ)
    (hfit : ∀ k < N, CircuitFits cap (Cs k)) (hcb : ∀ k < N, circuitCost (Cs k) ≤ cb)
    (hcopy : ∀ k < N, CopyFits cap V (Cs k)) (hNc : 2 * N ≤ cap) (hLc : 2 * L ≤ cap)
    (hqc : q + V + 6 * natBitLength q + 6 ≤ cap)
    (rest : List Bool) (σ : WState ns nr) (hst : σ.st CW = cwPrefix Cs N ++ rest) (hshL : σ.sh CW ≤ L)
    (hLN : (cwPrefix Cs N).length ≤ L) (ho : σ.sh o = (σ.st o).length)
    (hz : ∀ k : Fin 16, k ≠ 7 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → σ.val (Rg k) = 0)
    (hQ : σ.val (Rg 15) = q) (hRi : σ.val (Rg 13) = i) (hRj : σ.val (Rg 14) = j) (hL : σ.val (Rg 12) = L)
    (hV : σ.val (Rg 7) + (RepairOrdinary.frame (callWord (pairCallOf Cs i j ω))).length ≤ V) :
    WExec cap (callPairW CW o Rg ω) σ
      (appendO (σ.seth CW (cwPrefix Cs (j + 1)).length) o (Rg 7)
        (RepairOrdinary.frame (callWord (pairCallOf Cs i j ω))))
      ((natBitLength q + 10) * (100 * q + 200) + 1 + (16 * (natWord 1).length + 1 +
        ((18 * L + 3 + 1 + (5 * L + 1)) + 1 + ((18 * i + 3 + 1 + (i * (cb + 4) + 1 + 1 + copyCircuitCost (Cs i))) + 1 +
        ((18 * L + 3 + 1 + (5 * L + 1)) + 1 + ((18 * j + 3 + 1 + (j * (cb + 4) + 1 + 1 + copyCircuitCost (Cs j))) + 1 +
        (16 * (natWord 0 ++ ratWord ω).length + 1 + 7))))))) := by
  have hlen := congrArg List.length (frame_pairCall Cs i j ω)
  simp only [List.length_append, marks_length, List.length_singleton] at hlen
  have hV' := hV
  rw [hlen] at hV'
  have hVc : V + 4 ≤ cap := (hcopy i hi).1
  have h7 : ∀ k : Fin 16, k ≠ 7 → (Rg k ≠ Rg 7) := fun k hk => Rg_ne Rg hk
  -- 1. `natWord q`
  have e1 := writeNatM_spec cap o (rgW Rg) σ (by rw [rgW_one]; exact hz 1 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_two]; exact hz 2 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_three]; exact hz 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_four]; exact hz 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_five]; exact hz 5 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_six]; exact hz 6 (by decide) (by decide) (by decide) (by decide) (by decide)) ho
    (by rw [rgW_zero, rgW_seven, hQ]; omega)
  rw [rgW_zero, rgW_seven, hQ] at e1
  set σ1 := appendO σ o (Rg 7) (marks (natWord q)) with hσ1
  -- 2. the tag
  have e2 := emitMarks_spec cap o (Rg 7) (natWord 1) σ1 (by simp [hσ1, ho]) (by simp only [hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  set σ2 := appendO σ1 o (Rg 7) (marks (natWord 1)) with hσ2
  -- 3. rewind
  have v2 : ∀ k : Fin 16, k ≠ 7 → σ2.val (Rg k) = σ.val (Rg k) := fun k hk => by
    simp [hσ2, hσ1, Function.update_of_ne (h7 k hk)]
  have e3 := rewindCW_spec cap CW (Rg 12) (Rg 11) (Rg 10) (Rg_ne Rg (by decide)) (Rg_ne Rg (by decide))
    (Rg_ne Rg (by decide)) σ2
    (by rw [v2 11 (by decide)]; exact hz 11 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v2 10 (by decide)]; exact hz 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v2 12 (by decide), hL]; simp [hσ2, hσ1, Function.update_of_ne hCo]; exact hshL)
    (by rw [v2 12 (by decide), hL]; omega)
  rw [v2 12 (by decide), hL] at e3
  set σ3 := σ2.seth CW 0 with hσ3
  -- 4. circuit `i`
  have e4 := fetchCircuit_spec cap CW o hCo (rgC Rg) (Rg 8) (Rg 9) (Rg 13) (Rg 10) (fetchRegs Rg) Cs N i hi cb V
    hfit hcb (hcopy i hi) (by omega) rest σ3 (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hCo, hst])
    (by simp [hσ3])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, ho, marks_length]; omega)
    (fun k hk => by
      rw [rgC_val]
      show σ2.val (Rg ⟨k.val, by omega⟩) = 0
      have hk7 : (⟨k.val, by omega⟩ : Fin 16) ≠ 7 := fun h => hk (Fin.ext (by simpa using congrArg Fin.val h))
      rw [v2 _ hk7]
      exact hz _ hk7 (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega))
    (by show σ2.val (Rg 8) = 0; rw [v2 8 (by decide)]; exact hz 8 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ2.val (Rg 9) = 0; rw [v2 9 (by decide)]; exact hz 9 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ2.val (Rg 10) = 0; rw [v2 10 (by decide)]; exact hz 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ2.val (Rg 13) = i; rw [v2 13 (by decide)]; exact hRi)
    (by rw [rgC_seven]; show σ2.val (Rg 7) + _ ≤ V; simp only [hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  rw [rgC_seven] at e4
  set σ4 := appendO (σ3.seth CW (cwPrefix Cs (i + 1)).length) o (Rg 7) (marks (circuitWord (Cs i))) with hσ4
  -- 5. rewind
  have v4 : ∀ k : Fin 16, k ≠ 7 → σ4.val (Rg k) = σ.val (Rg k) := fun k hk => by
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (h7 k hk)]
  have hmono := cwPrefix_length_mono Cs (show i + 1 ≤ N by omega)
  have e5 := rewindCW_spec cap CW (Rg 12) (Rg 11) (Rg 10) (Rg_ne Rg (by decide)) (Rg_ne Rg (by decide))
    (Rg_ne Rg (by decide)) σ4
    (by rw [v4 11 (by decide)]; exact hz 11 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v4 10 (by decide)]; exact hz 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v4 12 (by decide), hL]; simp [hσ4, hσ3, Function.update_apply, hCo]; omega)
    (by rw [v4 12 (by decide), hL]; omega)
  rw [v4 12 (by decide), hL] at e5
  set σ5 := σ4.seth CW 0 with hσ5
  -- 6. circuit `j`
  have e6 := fetchCircuit_spec cap CW o hCo (rgC Rg) (Rg 8) (Rg 9) (Rg 14) (Rg 10) (fetchRegs' Rg) Cs N j hj cb V
    hfit hcb (hcopy j hj) (by omega) rest σ5
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hCo, hst])
    (by simp [hσ5])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, ho, marks_length]; omega)
    (fun k hk => by
      rw [rgC_val]
      show σ4.val (Rg ⟨k.val, by omega⟩) = 0
      have hk7 : (⟨k.val, by omega⟩ : Fin 16) ≠ 7 := fun h => hk (Fin.ext (by simpa using congrArg Fin.val h))
      rw [v4 _ hk7]
      exact hz _ hk7 (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega))
    (by show σ4.val (Rg 8) = 0; rw [v4 8 (by decide)]; exact hz 8 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ4.val (Rg 9) = 0; rw [v4 9 (by decide)]; exact hz 9 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ4.val (Rg 10) = 0; rw [v4 10 (by decide)]; exact hz 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ4.val (Rg 14) = j; rw [v4 14 (by decide)]; exact hRj)
    (by rw [rgC_seven]; show σ4.val (Rg 7) + _ ≤ V; simp only [hσ4, hσ3, hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  rw [rgC_seven] at e6
  set σ6 := appendO (σ5.seth CW (cwPrefix Cs (j + 1)).length) o (Rg 7) (marks (circuitWord (Cs j))) with hσ6
  -- 7. empty parity list and radius
  have e7 := emitMarks_spec cap o (Rg 7) (natWord 0 ++ ratWord ω) σ6
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, ho, marks_length]; omega)
    (by simp only [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  set σ7 := appendO σ6 o (Rg 7) (marks (natWord 0 ++ ratWord ω)) with hσ7
  -- 8. closing `false`
  have e8 := emitC_spec (cap := cap) o (Rg 7) false σ7
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, ho, marks_length]; omega)
    (by simp only [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ le_rfl
  rw [frame_pairCall]
  apply WState.eq
  · funext y; by_cases hy : y = CW
    · subst hy; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hCo]
    · by_cases hyo : y = o
      · subst hyo; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hy, ho, marks_length]
        omega
      · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyo]
  · funext y; by_cases hyo : y = o
    · subst hyo; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hCo.symm]
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hyo]
  · funext r
    by_cases hr : r = Rg 7
    · subst hr; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, marks_length]; omega
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hr]
  · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO]

/-! ## Single and parity calls -/

/-- The single/parity call of the worker: circuit `j`, the empty second circuit, parity list `ps`, radius `ω`
(`Worker.Guess.singleCall`: tag `parity` when the list is nonempty, `single` otherwise). -/
def oneCallOf {q : ℕ} (Cs : ℕ → NCircuit q) (j : ℕ) (ps : List ℕ) (ω : ℚ) : Call :=
  ⟨q, if ps = [] then .single else .parity, Cs j, NCircuit.empty q, ps, ω⟩

/-- The word of the empty second circuit (the same for every width). -/
def emptyCW : List Bool := natWord 0 ++ natWord 0 ++ (natWord 1 ++ bitWord false)

theorem circuitWord_empty (q : ℕ) : circuitWord (NCircuit.empty q) = emptyCW := by
  simp [circuitWord, NCircuit.empty, listWord, emptyCW]

/-- **The single/parity call writer**, generic in the parity-list program `parW` (which appends
`marks (listWord natWord ps)`). The tag word `natWord t` is passed in (`0` single, `2` parity). -/
def callOneW (CW o : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) (t : ℕ) (parW : WM ns nr) (ω : ℚ) : WM ns nr :=
  .seq (writeNatM o (rgW Rg))
  (.seq (emitMarks o (Rg 7) (natWord t))
  (.seq (rewindCW CW (Rg 12) (Rg 11) (Rg 10))
  (.seq (fetchCircuit CW o (rgC Rg) (Rg 8) (Rg 9) (Rg 13) (Rg 10) (fetchRegs Rg).hm)
  (.seq (emitMarks o (Rg 7) emptyCW)
  (.seq parW
  (.seq (emitMarks o (Rg 7) (ratWord ω)) (emitC o (Rg 7) false)))))))

theorem frame_oneCall {q : ℕ} (Cs : ℕ → NCircuit q) (j : ℕ) (ps : List ℕ) (ω : ℚ) :
    RepairOrdinary.frame (callWord (oneCallOf Cs j ps ω)) =
      marks (natWord q) ++ marks (natWord (if ps = [] then 0 else 2)) ++ marks (circuitWord (Cs j)) ++
        marks emptyCW ++ marks (listWord natWord ps) ++ marks (ratWord ω) ++ [false] := by
  rw [frame_eq_marks, ← circuitWord_empty q]
  by_cases h : ps = [] <;> simp [callWord, oneCallOf, kindTag, h, marksApp, List.append_assoc]

theorem callOneW_spec (CW o SUP : Fin (ns + 1)) (hCo : CW ≠ o) (hSo : SUP ≠ o) (hSC : SUP ≠ CW) {q : ℕ}
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
      WExec cap parW τ (appendO (τ.seth SUP pSup) o (Rg 7) (marks (listWord natWord ps))) cp) :
    WExec cap (callOneW CW o Rg t parW ω) σ
      (appendO ((σ.seth CW (cwPrefix Cs (j + 1)).length).seth SUP pSup) o (Rg 7)
        (RepairOrdinary.frame (callWord (oneCallOf Cs j ps ω))))
      ((natBitLength q + 10) * (100 * q + 200) + 1 + (16 * (natWord t).length + 1 +
        ((18 * L + 3 + 1 + (5 * L + 1)) + 1 + ((18 * j + 3 + 1 + (j * (cb + 4) + 1 + 1 + copyCircuitCost (Cs j))) + 1 +
        (16 * emptyCW.length + 1 + (cp + 1 + (16 * (ratWord ω).length + 1 + 7))))))) := by
  have hlen := congrArg List.length (frame_oneCall Cs j ps ω)
  simp only [List.length_append, marks_length, List.length_singleton] at hlen
  rw [← ht] at hlen
  have hV' := hV
  rw [hlen] at hV'
  have hVc : V + 4 ≤ cap := (hcopy j hj).1
  have h7 : ∀ k : Fin 16, k ≠ 7 → (Rg k ≠ Rg 7) := fun k hk => Rg_ne Rg hk
  have e1 := writeNatM_spec cap o (rgW Rg) σ (by rw [rgW_one]; exact hz 1 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_two]; exact hz 2 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_three]; exact hz 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_four]; exact hz 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_five]; exact hz 5 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rgW_six]; exact hz 6 (by decide) (by decide) (by decide) (by decide) (by decide)) ho
    (by rw [rgW_zero, rgW_seven, hQ]; omega)
  rw [rgW_zero, rgW_seven, hQ] at e1
  set σ1 := appendO σ o (Rg 7) (marks (natWord q)) with hσ1
  have e2 := emitMarks_spec cap o (Rg 7) (natWord t) σ1 (by simp [hσ1, ho]) (by simp only [hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  set σ2 := appendO σ1 o (Rg 7) (marks (natWord t)) with hσ2
  have v2 : ∀ k : Fin 16, k ≠ 7 → σ2.val (Rg k) = σ.val (Rg k) := fun k hk => by
    simp [hσ2, hσ1, Function.update_of_ne (h7 k hk)]
  have e3 := rewindCW_spec cap CW (Rg 12) (Rg 11) (Rg 10) (Rg_ne Rg (by decide)) (Rg_ne Rg (by decide))
    (Rg_ne Rg (by decide)) σ2
    (by rw [v2 11 (by decide)]; exact hz 11 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v2 10 (by decide)]; exact hz 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v2 12 (by decide), hL]; simp [hσ2, hσ1, Function.update_of_ne hCo]; exact hshL)
    (by rw [v2 12 (by decide), hL]; omega)
  rw [v2 12 (by decide), hL] at e3
  set σ3 := σ2.seth CW 0 with hσ3
  have e4 := fetchCircuit_spec cap CW o hCo (rgC Rg) (Rg 8) (Rg 9) (Rg 13) (Rg 10) (fetchRegs Rg) Cs N j hj cb V
    hfit hcb (hcopy j hj) (by omega) rest σ3 (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hCo, hst])
    (by simp [hσ3])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, ho, marks_length]; omega)
    (fun k hk => by
      rw [rgC_val]
      show σ2.val (Rg ⟨k.val, by omega⟩) = 0
      have hk7 : (⟨k.val, by omega⟩ : Fin 16) ≠ 7 := fun h => hk (Fin.ext (by simpa using congrArg Fin.val h))
      rw [v2 _ hk7]
      exact hz _ hk7 (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega))
    (by show σ2.val (Rg 8) = 0; rw [v2 8 (by decide)]; exact hz 8 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ2.val (Rg 9) = 0; rw [v2 9 (by decide)]; exact hz 9 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ2.val (Rg 10) = 0; rw [v2 10 (by decide)]; exact hz 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by show σ2.val (Rg 13) = j; rw [v2 13 (by decide)]; exact hRj)
    (by rw [rgC_seven]; show σ2.val (Rg 7) + _ ≤ V; simp only [hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  rw [rgC_seven] at e4
  set σ4 := appendO (σ3.seth CW (cwPrefix Cs (j + 1)).length) o (Rg 7) (marks (circuitWord (Cs j))) with hσ4
  have e5 := emitMarks_spec cap o (Rg 7) emptyCW σ4
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, ho, marks_length]; omega)
    (by simp only [hσ4, hσ3, hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  set σ5 := appendO σ4 o (Rg 7) (marks emptyCW) with hσ5
  have e6 := hpar σ5
    (fun k hk => by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (h7 k hk)])
    (fun r hr => by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (hr 7)])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, ho, marks_length]; omega)
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hSo, hSC])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hSo, hSC])
    (by simp only [hσ5, hσ4, hσ3, hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  set σ6 := appendO (σ5.seth SUP pSup) o (Rg 7) (marks (listWord natWord ps)) with hσ6
  have e7 := emitMarks_spec cap o (Rg 7) (ratWord ω) σ6
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, hSo.symm, ho, marks_length]; omega)
    (by simp only [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  set σ7 := appendO σ6 o (Rg 7) (marks (ratWord ω)) with hσ7
  have e8 := emitC_spec (cap := cap) o (Rg 7) false σ7
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hCo.symm, hSo.symm, ho, marks_length]; omega)
    (by simp only [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO_val, WState.seth_val, WState.setv_val, Function.update_self, marks_length, List.length_append]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ le_rfl
  rw [frame_oneCall, ← ht]
  apply WState.eq
  · funext y; by_cases hy : y = CW
    · subst hy; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hCo, hSC.symm]
    · by_cases hyS : y = SUP
      · subst hyS; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hSo, hy]
      · by_cases hyo : y = o
        · subst hyo; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hy, hyS, ho, marks_length]
          omega
        · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyo,
            Function.update_of_ne hyS]
  · funext y; by_cases hyo : y = o
    · subst hyo; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hCo.symm, hSo.symm]
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hyo]
  · funext r
    by_cases hr : r = Rg 7
    · subst hr; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, marks_length]; omega
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hr]
  · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO]

end Spec

end NearCubicGates.Close.Codec

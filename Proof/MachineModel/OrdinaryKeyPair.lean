import Proof.MachineModel.OrdinaryKeyField

/-! Two bounded coordinate fields appended on six fixed tapes, with shared
erased scratch and actual delimiters/handoffs. Neither output nor input table
is rewound. The caller has already emitted the framed cell-bit prefix. -/
namespace NearCubicWires.RepairOrdinary.KeyPair
open LocalBitMultitape Streaming RankBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 6 ≃ Fin 6 where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def swap : Fin 6 ≃ Fin 6 where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 6 → Fin 6) = ![0, 1, 4, 5, 2, 3] := rfl
@[simp] theorem swap_inverse : (swap.symm : Fin 6 → Fin 6) = ![2, 3, 0, 1, 4, 5] := rfl

def config {s : ℕ} (state : Fin s) (first templateFirst second templateSecond out : List Bool)
    (capacity : ℕ) : Configuration 6 s :=
  ⟨state, ![0, 0, 0, 0, out.length, 0],
    ![first, templateFirst, second, templateSecond, out, List.replicate capacity false]⟩

@[simp] theorem config_cells {s : ℕ} (state : Fin s) (a ta b tb out : List Bool) (cap : ℕ) :
    (config state a ta b tb out cap).tapeCells = a.length + ta.length + b.length + tb.length + out.length + cap := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ, Nat.add_assoc]

theorem place {s : ℕ} (state : Fin s) (a ta b tb out : List Bool) (cap : ℕ) :
    TapeRenaming.config layout (TapeEmbedding.config (fun _ : Fin 2 => 0) ![b, tb]
      (KeyPrefix.ready state a ta out cap)) = config state a ta b tb out cap := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, KeyPrefix.ready, config, Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, KeyPrefix.ready, config, Fin.addCases]

theorem swap_config {s : ℕ} (state : Fin s) (a ta b tb out : List Bool) (cap : ℕ) :
    TapeRenaming.config swap (config state a ta b tb out cap) = config state b tb a ta out cap := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeRenaming.config, config]
  · funext i; fin_cases i <;> simp [TapeRenaming.config, config]

def first : Machine 6 4 := TapeRenaming.machine layout (TapeEmbedding.machine 2 KeyPrefix.machine)
def second : Machine 6 4 := TapeRenaming.machine swap first
def close : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 1
  rule := fun state _ => if state.val = 0 then
    some ⟨1, fun i => if i.val = 4 then some false else none,
      fun i => if i.val = 4 then .right else .stay⟩ else none
def tail : Machine 6 6 := Composition.machine second close
def machine : Machine 6 10 := Composition.machine first tail

theorem first_run (bits suffix templateBits b tb out : List Bool) (cap : ℕ)
    (hw : bits.length = templateBits.length) (hc : 2 * bits.length ≤ cap) :
    Executes first (4 * bits.length + 2)
      ((marks bits ++ suffix).length + (frame templateBits).length + b.length + tb.length + out.length + 4 * bits.length + cap)
      (config 0 (marks bits ++ suffix) (frame templateBits) b tb out cap)
      (config 3 (marks bits ++ suffix) (frame templateBits) b tb (out ++ marks bits) cap) := by
  obtain ⟨r, hr, hf, hs, hp⟩ := KeyPrefix.field_run bits suffix templateBits out cap hw hc
  let extraHeads := fun _ : Fin 2 => 0
  let extraTapes : Fin 2 → List Bool := ![b, tb]
  have he := TapeEmbedding.run_embed KeyPrefix.machine extraHeads extraTapes _ _ r hr
  have hn := TapeRenaming.run_rename layout (TapeEmbedding.machine 2 KeyPrefix.machine) _ _ _ he
  refine ⟨TapeRenaming.receipt layout (TapeEmbedding.receipt extraHeads extraTapes r), ?_, ?_, hs.le, ?_⟩
  · simpa only [extraHeads, extraTapes, place, first] using hn
  · change TapeRenaming.config layout (TapeEmbedding.config extraHeads extraTapes r.final) = _
    rw [hf]
    exact place _ _ _ _ _ _ _
  · change r.peakTapeCells + TapeEmbedding.extraCells extraTapes ≤ _
    simp [TapeEmbedding.extraCells, extraTapes, Fin.sum_univ_succ] at hp ⊢
    omega

theorem second_run (a ta bits suffix templateBits out : List Bool) (cap : ℕ)
    (hw : bits.length = templateBits.length) (hc : 2 * bits.length ≤ cap) :
    Executes second (4 * bits.length + 2)
      (a.length + ta.length + (marks bits ++ suffix).length + (frame templateBits).length + out.length + 4 * bits.length + cap)
      (config 0 a ta (marks bits ++ suffix) (frame templateBits) out cap)
      (config 3 a ta (marks bits ++ suffix) (frame templateBits) (out ++ marks bits) cap) := by
  obtain ⟨r, hr, hf, hs, hp⟩ := first_run bits suffix templateBits a ta out cap hw hc
  have hn := TapeRenaming.run_rename swap first _ _ r hr
  refine ⟨TapeRenaming.receipt swap r, by simpa only [swap_config, second] using hn, ?_, hs, ?_⟩
  · change TapeRenaming.config swap r.final = _
    rw [hf, swap_config]
  · change r.peakTapeCells ≤ _
    omega

theorem close_run (a ta b tb out : List Bool) (cap : ℕ) :
    Executes close 1 (a.length + ta.length + b.length + tb.length + out.length + cap + 1)
      (config 0 a ta b tb out cap) (config 1 a ta b tb (out ++ [false]) cap) := by
  have he : step close (config 0 a ta b tb out cap) = some (config 1 a ta b tb (out ++ [false]) cap) := by
    simp [step, close, config]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction, write_append]
  have hp := Prefix.step (by simp : (config 0 a ta b tb out cap).tapeCells ≤
      a.length + ta.length + b.length + tb.length + out.length + cap + 1)
    (by rfl : close.halted (0 : Fin 2) = false) he (Prefix.refl _ (by simp; omega))
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (by rfl) (by simp; omega)
  exact ⟨r, hr, hf, hs.le, hb⟩

theorem pair_run (a suffixA templateA b suffixB templateB out : List Bool) (cap : ℕ)
    (ha : a.length = templateA.length) (hb : b.length = templateB.length)
    (hca : 2 * a.length ≤ cap) (hcb : 2 * b.length ≤ cap) :
    Executes machine (4 * (a.length + b.length) + 7)
      ((marks a ++ suffixA).length + (frame templateA).length + (marks b ++ suffixB).length +
        (frame templateB).length + out.length + 4 * (a.length + b.length) + cap + 1)
      (config 0 (marks a ++ suffixA) (frame templateA) (marks b ++ suffixB) (frame templateB) out cap)
      (config 9 (marks a ++ suffixA) (frame templateA) (marks b ++ suffixB) (frame templateB)
        (out ++ frame (a ++ b)) cap) := by
  let sourceA := marks a ++ suffixA
  let sourceB := marks b ++ suffixB
  let space := sourceA.length + (frame templateA).length + sourceB.length + (frame templateB).length +
    out.length + 4 * (a.length + b.length) + cap + 1
  have hp : Executes first (4 * a.length + 2) space
      (config 0 sourceA (frame templateA) sourceB (frame templateB) out cap)
      (config 3 sourceA (frame templateA) sourceB (frame templateB) (out ++ marks a) cap) := by
    obtain ⟨r, hr, hf, hs, hb⟩ := first_run a suffixA templateA sourceB (frame templateB) out cap ha hca
    exact ⟨r, hr, hf, hs, by dsimp [space, sourceA]; omega⟩
  have hq : Executes second (4 * b.length + 2) space
      (config 0 sourceA (frame templateA) sourceB (frame templateB) (out ++ marks a) cap)
      (config 3 sourceA (frame templateA) sourceB (frame templateB) (out ++ marks a ++ marks b) cap) := by
    obtain ⟨r, hr, hf, hs, hp⟩ := second_run sourceA (frame templateA) b suffixB templateB (out ++ marks a) cap hb hcb
    refine ⟨r, hr, hf, hs, ?_⟩
    dsimp [space, sourceB]
    simp only [List.length_append, marks_length] at hp ⊢
    omega
  have hz : Executes close 1 space
      (config 0 sourceA (frame templateA) sourceB (frame templateB) (out ++ marks a ++ marks b) cap)
      (config 1 sourceA (frame templateA) sourceB (frame templateB) (out ++ marks a ++ marks b ++ [false]) cap) := by
    obtain ⟨r, hr, hf, hs, hp⟩ := close_run sourceA (frame templateA) sourceB (frame templateB) (out ++ marks a ++ marks b) cap
    refine ⟨r, hr, hf, hs, ?_⟩
    dsimp [space]
    simp only [List.length_append, marks_length] at hp
    omega
  have htail := hq.join hz rfl
  have hj := hp.join htail rfl
  have ho : out ++ marks a ++ marks b ++ [false] = out ++ frame (a ++ b) := by
    rw [frame_append, ← marks_frame]
    simp [List.append_assoc]
  have he : (4 * a.length + 2) + 1 + (4 * b.length + 2 + 1 + 1) = 4 * (a.length + b.length) + 7 := by omega
  rw [he] at hj
  have hzero : Fin.castAdd 6 (0 : Fin 4) = (0 : Fin 10) := by decide
  have hnine : Fin.natAdd 4 (Fin.natAdd 4 (1 : Fin 2)) = (9 : Fin 10) := by decide
  simpa only [ho, machine, tail, Composition.leftConfig, Composition.rightConfig, config,
    space, sourceA, sourceB, hzero, hnine] using hj

end NearCubicWires.RepairOrdinary.KeyPair

import SourceAdapters.RAMACSP.GenBound
import Proof.Gates.CellsPack.Lang
import Proof.Gates.Cells.OutLen

/-!
# The generator as an ordinary word function

Paper: `lem:generator` ("There is an algorithm that, given `x ∈ {0,1}^n` … and an integer `t ≥ n` in binary,
outputs `x̄` and the instance `I_x` … in `poly(n, log t)` steps") and `cor:short-pcp-clock` ("The construction does
not test the promise"): on the word `frame x ++ frame (bits t)` of every clock request, the machine halts within
`K·(n + |bits t| + 1)^e` steps with output `frame (frame x̄ ++ word)`.

The word function is `composeFramed (composeFramed prefix boost) main`:
- `prefix`: `w ↦ frame (1^s 0 ++ w)`, `s = size |w|` (`Machines.WidthPrefix.prefixWF`);
- `boost`: the `FL` stage `boostFL c` (`GenRun`), `↦ frame (1^(c+s) 0 ++ w)` with `c = boostC V`, so that the run
  constants `K = N = 2·64^(c+s)` exceed every number of the run (`lin_bound`) on every request;
- `main`: the cell program `mainP` (`GenMain`) with the callee `sumWF Shoup ConsWF`, packed by
  `Cells.wordFunction_of_lang` (L `Proof/Gates/Cells/Run.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicGates.Adapters.Machine.ComposeCarry
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)
open Polynomial

variable (V : Verifier)

/-- The boost: `64^c` dominates the linear constant. -/
def boostC : ℕ := linConst V + 4

/-- The main stage's input word. -/
def inpOf (r : ClockRequest) : List Bool := boostWord (boostC V) (ClockRequest.word r)

theorem lead_inpOf (r : ClockRequest) :
    leadOnes (inpOf V r) = boostC V + Nat.size (ClockRequest.word r).length :=
  NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_rep _ _

/-- `linConst · Y < 64^(c + s)`. -/
theorem lin_lt_pow (r : ClockRequest) :
    linConst V * Yr r < 64 ^ (boostC V + Nat.size (ClockRequest.word r).length) := by
  have h1 : linConst V < 2 ^ boostC V := by
    have := Nat.lt_two_pow_self (n := boostC V); unfold boostC at *; omega
  have h2 := Yr_le_pow r
  have h3 : 2 ^ boostC V * 2 ^ Nat.size (ClockRequest.word r).length ≤
      64 ^ (boostC V + Nat.size (ClockRequest.word r).length) := by
    rw [← pow_add]; exact Nat.pow_le_pow_left (by norm_num) _
  calc linConst V * Yr r < 2 ^ boostC V * Yr r := Nat.mul_lt_mul_of_pos_right h1 (one_le_Yr r)
    _ ≤ 2 ^ boostC V * 2 ^ Nat.size (ClockRequest.word r).length := Nat.mul_le_mul_left _ h2
    _ ≤ _ := h3

theorem bnd_f : Bnd (fun r => fieldExp V r.2) := ⟨linConst V, 1, fun r => by
  have := lin_bound V r; show fieldExp V r.2 ≤ linConst V * Yr r ^ 1; rw [pow_one]
  generalize 2 ^ inExp V r = P at this
  generalize 2 ^ colExp V r.2 = Q at this
  omega⟩

theorem bnd_len : Bnd (fun r => (ClockRequest.word r).length) := ⟨1, 1, fun r => by simp [Yr]⟩

theorem bnd_nt : Bnd (fun r => r.1.1 + natBitLength r.2 + 1) := ⟨1, 1, fun r => by
  have := word_len r
  have : natBitLength r.2 ≤ r.2.bits.length + 1 := by
    rcases Nat.eq_zero_or_pos r.2 with h | h
    · rw [h]; simp [natBitLength]
    · have := Nat.size_eq_bits_len r.2
      unfold natBitLength
      have h2 := Nat.lt_size_self r.2
      have h3 : Nat.log 2 r.2 < Nat.size r.2 := Nat.log_lt_of_lt_pow (by omega) h2
      omega
  simp only [Yr, pow_one]; omega⟩

/-- The two callee budgets. -/
def calleeBud (Ks es Kc ec : ℕ) (r : ClockRequest) : ℕ :=
  (2 * (8 + dropBudget (fieldExp V r.2) (Ks * (fieldExp V r.2 + 1) ^ es)) + 2) +
    (2 * (8 + dropBudget (ClockRequest.word r).length (Kc * (r.1.1 + natBitLength r.2 + 1) ^ ec)) + 2)

theorem bnd_calleeBud (Ks es Kc ec : ℕ) : Bnd (calleeBud V Ks es Kc ec) := by
  have hd : ∀ L B, dropBudget L B = 120 * L + 129 + 2 * B := fun L B => by unfold dropBudget; ring
  refine (((((Bnd.const 600).add (Bnd.mul (Bnd.const 240) (bnd_f V))).add (Bnd.mul (Bnd.const 4)
    (Bnd.mul (Bnd.const Ks) (Bnd.pow ((bnd_f V).add (Bnd.const 1)) es)))).add (Bnd.mul (Bnd.const 240) (bnd_len))).add
    (Bnd.mul (Bnd.const 4) (Bnd.mul (Bnd.const Kc) (Bnd.pow (bnd_nt) ec)))).mono (fun r => ?_)
  unfold calleeBud; rw [hd, hd]; omega

theorem linConst_pos : 1 ≤ linConst V := by
  unfold linConst
  generalize 2 ^ tagExp V = D
  generalize clockConst V = c
  generalize tagExp V = d
  have : 1 ≤ (D + 1) * (c + d + 10) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 1 ≤ (D + 1) * (c + d + 10) := this
    _ ≤ 1000 * (D + 1) * (c + d + 10) := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num)

/-! ## The main stage's size conditions -/

section Main

variable (irrPoly : ℕ → (ZMod 2)[X]) {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : ConsWF V irrPoly Kc ec)

/-- The main stage's sizes: width and call room `4·64^L`, call budget `(AB + 1)·2^(aB·L)`. -/
def zG (AB aB : ℕ) : Sz := zM 4 6 (AB + 1) aB

theorem sixtyfour_pow (L : ℕ) : 2 ^ (6 * L) = 64 ^ L := by rw [pow_mul]; norm_num

theorem mainFits (AB aB : ℕ) (hB : ∀ r, calleeBud V Ks es Kc ec r ≤ AB * Yr r ^ aB) (r : ClockRequest) :
    MainFits V (Ks := Ks) (es := es) (Kc := Kc) (ec := ec) r
      (ctxOf (genCallee V irrPoly WS WC) (zG AB aB) (inpOf V r)) (globOf (inpOf V r)) := by
  set s := Nat.size (ClockRequest.word r).length with hs
  set L := boostC V + s with hL
  have hlead : leadOnes (inpOf V r) = L := lead_inpOf V r
  have hK : (globOf (inpOf V r)).K = 2 * 64 ^ L := by show kOf _ = _; unfold kOf; rw [hlead]
  have hN : (globOf (inpOf V r)).N = 2 * 64 ^ L := hK
  have hW : (ctxOf (genCallee V irrPoly WS WC) (zG AB aB) (inpOf V r)).Wd = 4 * 64 ^ L := by
    show 2 ^ (6 * leadOnes (inpOf V r)) * 4 = _; rw [hlead, sixtyfour_pow]; ring
  have hLk : (ctxOf (genCallee V irrPoly WS WC) (zG AB aB) (inpOf V r)).Lk = 4 * 64 ^ L := by
    show 2 ^ (6 * leadOnes (inpOf V r)) * 4 = _; rw [hlead, sixtyfour_pow]; ring
  have hBk : (ctxOf (genCallee V irrPoly WS WC) (zG AB aB) (inpOf V r)).Bk = 2 ^ (aB * L) * (AB + 1) := by
    show 2 ^ (aB * leadOnes (inpOf V r)) * (AB + 1) = _; rw [hlead]
  have hlin := lin_bound V r
  have hlt := lin_lt_pow V r
  rw [← hs, ← hL] at hlt
  have hY1 := one_le_Yr r
  have hYw : Yr r = 2 * r.1.1 + 2 * r.2.bits.length + 3 := by have := word_len r; simp only [Yr]; omega
  have hlc : 1 ≤ linConst V := linConst_pos V
  have hYl : Yr r ≤ linConst V * Yr r := Nat.le_mul_of_pos_left _ hlc
  have hA : r.1.1 + r.2.bits.length + fieldExp V r.2 + clockConst V + tagExp V + 20 ≤ linConst V * Yr r := by
    have := hlin; generalize 2 ^ inExp V r = P at this; generalize 2 ^ colExp V r.2 = Q at this; omega
  have hP : 2 ^ inExp V r ≤ linConst V * Yr r := by
    have := hlin; generalize 2 ^ inExp V r = P at this ⊢; generalize 2 ^ colExp V r.2 = Q at this; omega
  have hQ : 16 * 2 ^ colExp V r.2 + 2 * laneExp V r.2 + 2 * tau V r.2 + 2 ≤ linConst V * Yr r := by
    have := hlin; generalize 2 ^ inExp V r = P at this; generalize 2 ^ colExp V r.2 = Q at this ⊢; omega
  clear hlin
  have hWlt : 4 * 64 ^ L < 2 ^ (4 * 64 ^ L) := Nat.lt_two_pow_self
  -- the callee budgets
  have hbud : calleeBud V Ks es Kc ec r ≤ 2 ^ (aB * L) * (AB + 1) := by
    have h1 := hB r
    have h2 : Yr r ^ aB ≤ 2 ^ (aB * s) := by
      rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Yr_le_pow r) aB
    have h3 : 2 ^ (aB * s) ≤ 2 ^ (aB * L) := Nat.pow_le_pow_right (by norm_num) (by rw [hL]; nlinarith)
    have h4 : AB * Yr r ^ aB ≤ (AB + 1) * 2 ^ (aB * L) :=
      Nat.mul_le_mul (by omega) (h2.trans h3)
    rw [Nat.mul_comm (2 ^ (aB * L))]; omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => ?_, ?_, ?_, ?_⟩
  · rw [hK]; omega
  · rw [hK, hN]
  · show 2 ^ inExp V r ≤ _; rw [hN]; omega
  · rw [hK]; omega
  · rw [hN]; omega
  · rw [hK, hN]
  · rw [hLk]; omega
  · rw [hLk]; omega
  · rw [hBk, sumBudget_inl]
    have : calleeBud V Ks es Kc ec r = (2 * (8 + dropBudget (fieldExp V r.2) (Ks * (fieldExp V r.2 + 1) ^ es)) + 2) +
      (2 * (8 + dropBudget (ClockRequest.word r).length (Kc * (r.1.1 + natBitLength r.2 + 1) ^ ec)) + 2) := rfl
    simp only [List.length_replicate]
    omega
  · rw [hBk, sumBudget_inr]
    have : calleeBud V Ks es Kc ec r = (2 * (8 + dropBudget (fieldExp V r.2) (Ks * (fieldExp V r.2 + 1) ^ es)) + 2) +
      (2 * (8 + dropBudget (ClockRequest.word r).length (Kc * (r.1.1 + natBitLength r.2 + 1) ^ ec)) + 2) := rfl
    omega
  · rw [hW]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rw [hW]; omega

/-! ## The main stage as a word function -/

/-- The cost bound of the main stage's run. -/
def mainN (AB aB : ℕ) (r : ClockRequest) : ℕ :=
  mainCost V irrPoly (ctxOf (genCallee V irrPoly WS WC) (zG AB aB) (inpOf V r)) (globOf (inpOf V r)) (inpOf V r) r

/-- **The main stage** (`wordFunction_of_lang`). -/
noncomputable def mainWF (AB aB : ℕ) (hB : ∀ r, calleeBud V Ks es Kc ec r ≤ AB * Yr r ^ aB) :
    WordFunction ClockRequest (inpOf V)
      (fun r => RepairSource.frame (RepairSource.frame (ownXbar V r) ++ (ownInst V irrPoly (ownCons V irrPoly) r).word))
      (fun r => langBudget (genCallee V irrPoly WS WC) (zG AB aB) VV MM (inpOf V r) (mainN V irrPoly WS WC AB aB r)) :=
  wordFunction_of_lang (inpOf V) _ (genCallee V irrPoly WS WC) (zG AB aB) (mainP V) (mainN V irrPoly WS WC AB aB)
    (fun r => main_run V irrPoly WS WC 4 6 (AB + 1) aB r (boostC V + Nat.size (ClockRequest.word r).length)
      (by unfold boostC; omega) (mainFits V irrPoly WS WC AB aB hB r))
    (fun r => by show 1 ≤ 2 ^ (6 * _) * 4; have := Nat.one_le_two_pow (n := 6 * leadOnes (inpOf V r)); omega)

/-! ## Polynomial bounds of the main stage -/

theorem bnd_pow_s (c : ℕ) : Bnd (fun r => 2 ^ (c * Nat.size (ClockRequest.word r).length)) :=
  (Bnd.mul (Bnd.const (2 ^ c)) (Bnd.pow Bnd.scale c)).mono (fun r => pow_size_scale c r)

theorem bnd_pow_L (c : ℕ) : Bnd (fun r => 2 ^ (c * leadOnes (inpOf V r))) := by
  refine (Bnd.mul (Bnd.const (2 ^ (c * boostC V))) (bnd_pow_s c)).mono (fun r => ?_)
  rw [lead_inpOf, Nat.mul_add, pow_add]

theorem bnd_kOf : Bnd (fun r => kOf (inpOf V r)) :=
  (Bnd.mul (Bnd.const 2) (bnd_pow_L V 6)).mono (fun r => by unfold kOf; rw [← sixtyfour_pow])

theorem bnd_lead : Bnd (fun r => leadOnes (inpOf V r)) := by
  refine (Bnd.add (Bnd.const (boostC V)) Bnd.scale).mono (fun r => ?_)
  rw [lead_inpOf]
  have := Nat.size_le.2 (Nat.lt_two_pow_self (n := (ClockRequest.word r).length))
  simp only [Yr, pow_one] at *; omega

end Main

section Main2

variable (irrPoly : ℕ → (ZMod 2)[X]) {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : ConsWF V irrPoly Kc ec)

theorem bnd_costS (q : S) : Bnd (fun r => costS (globOf (inpOf V r)) q) := by
  have hk := bnd_kOf V
  refine (Bnd.mul (Bnd.mul (Bnd.const (8 * szS q)) ((Bnd.mul (Bnd.const 400) (Bnd.pow (hk.add (Bnd.const 1)) 3)).add
    (Bnd.const 400))) (Bnd.pow (hk.add (Bnd.const 1)) (dpS q))).mono (fun r => ?_)
  have := costS_le (globOf (inpOf V r)) q
  unfold opc at this
  exact this.trans (le_of_eq (by simp only [globOf]))

include WC in
theorem bnd_cw : Bnd (fun r => (consWord V irrPoly r).length) := by
  refine (Bnd.add (Bnd.mul (Bnd.const Kc) (Bnd.pow (bnd_nt) ec)) (Bnd.const 1)).mono (fun r => ?_)
  have h1 := NearCubicGates.Close.Cells.wf_out_len WC r
  have h2 : (consWord V irrPoly r).length ≤ (RepairSource.frame (consWord V irrPoly r)).length := by
    rw [FL.frame_len]; omega
  exact h2.trans h1

theorem bnd_mainN (AB aB : ℕ) : Bnd (mainN V irrPoly WS WC AB aB) := by
  have hL := bnd_lead V
  have hk := bnd_kOf V
  have hW := bnd_pow_L V 6
  have hB := bnd_pow_L V aB
  have hn : Bnd (fun r => r.1.1) := ⟨1, 1, fun r => by have := word_len r; simp only [Yr, pow_one]; omega⟩
  have hb : Bnd (fun r => r.2.bits.length) := ⟨1, 1, fun r => by have := word_len r; simp only [Yr, pow_one]; omega⟩
  refine (((((((((((Bnd.mul (Bnd.const 20) hL).add (Bnd.mul (Bnd.const 5) hk)).add (Bnd.const 200)).add
    (bnd_costS V (stageA V))).add (Bnd.mul (Bnd.const 15) (bnd_f V))).add (Bnd.mul (Bnd.const 8) hW)).add
    (Bnd.mul (Bnd.const (2 * (AB + 1))) hB)).add (bnd_costS V stageB1)).add
    ((Bnd.mul (Bnd.const 12) hn).add (Bnd.mul (Bnd.const 12) hb))).add
    (Bnd.mul (Bnd.const 10) (bnd_cw V irrPoly WC))).add ((bnd_costS V stageB2).add (bnd_costS V (.emit (.k 0))))).mono
    (fun r => ?_)
  unfold mainN mainCost preCost callIrrCost callConsCost
  simp only [ctxOf, zG, zM, Sz.Lk, Sz.Bk]
  rw [show (6 * leadOnes (inpOf V r)) = 6 * leadOnes (inpOf V r) from rfl]
  ring_nf
  omega

theorem bnd_stage3 (AB aB : ℕ) :
    Bnd (fun r => langBudget (genCallee V irrPoly WS WC) (zG AB aB) VV MM (inpOf V r) (mainN V irrPoly WS WC AB aB r)) := by
  have hL := bnd_lead V
  have hW := bnd_pow_L V 6
  have hB := bnd_pow_L V aB
  have hG : Bnd (fun r => NearCubicGates.Close.CellsPack.Gof (genCallee V irrPoly WS WC) (zG AB aB)
      (leadOnes (inpOf V r))) := by
    refine ((((Bnd.mul (Bnd.const 8) hW).add (Bnd.mul (Bnd.const (AB + 1)) hB)).add hL).add
      (Bnd.const (AB + aB + 30 + TSK (genCallee V irrPoly WS WC)))).mono (fun r => ?_)
    unfold NearCubicGates.Close.CellsPack.Gof
    simp only [zG, zM, Sz.W, Sz.Lk, Sz.Bk]
    ring_nf; omega
  have hI : Bnd (fun r => (inpOf V r).length) := by
    refine ((hL.add (Bnd.const 1)).add bnd_len).mono (fun r => le_of_eq ?_)
    show (inpOf V r).length = leadOnes (inpOf V r) + 1 + (ClockRequest.word r).length
    rw [lead_inpOf]; simp only [inpOf, boostWord, List.length_append, List.length_replicate, List.length_cons]
    ring
  refine ((Bnd.mul (Bnd.const (10 ^ 6)) (Bnd.mul ((bnd_mainN V irrPoly WS WC AB aB).add (Bnd.const 1))
    (Bnd.pow hG 2))).add (Bnd.mul (Bnd.const 10) hI)).mono (fun r => ?_)
  exact NearCubicGates.Close.CellsPack.lang_le2 _ _ _ _

end Main2

/-! ## The prefix and boost stages -/

/-- The width-prefix stage on clock requests (pcptime's `prefixWF`). -/
noncomputable def stageP : WordFunction ClockRequest ClockRequest.word
    (fun r => frame (Time.prefixWord (ClockRequest.word r)))
    (fun r => Machines.WidthPrefix.prefixBudget (ClockRequest.word r).length) where
  program := Machines.WidthPrefix.prefixWF.program
  realizes r := Machines.WidthPrefix.prefixWF.realizes (ClockRequest.word r)

theorem wf_onesFL (d : ℕ) : ∀ c : ℕ, wfS (onesFL c) d = true
  | 0 => rfl
  | c + 1 => by simp only [onesFL, wfS, Bool.and_eq_true]; exact ⟨rfl, wf_onesFL d c⟩

theorem wf_boostFL (c : ℕ) : wfS (boostFL c) 0 = true := by
  simp only [boostFL, wfS, Bool.and_eq_true]
  exact ⟨wf_onesFL 0 c, by decide⟩

theorem prefix_lead (r : ClockRequest) :
    leadOnes (Time.prefixWord (ClockRequest.word r)) = Nat.size (ClockRequest.word r).length :=
  NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_rep _ _

/-- **The boost stage** (`boostFL`, `GenRun`). -/
noncomputable def boostWF :
    WordFunction ClockRequest (fun r => Time.prefixWord (ClockRequest.word r)) (fun r => frame (inpOf V r))
      (fun r => langBudget noCallee zF VV MM (Time.prefixWord (ClockRequest.word r))
        (preCost (Time.prefixWord (ClockRequest.word r)) +
          costS (globOf (Time.prefixWord (ClockRequest.word r))) (boostFL (boostC V)) + 1)) :=
  let F := flWF (fun r : ClockRequest => Time.prefixWord (ClockRequest.word r)) (boostFL (boostC V)) (wf_boostFL _)
    (fun r => by rw [prefix_lead]; exact Nat.size_pos.mpr (by rw [word_len]; omega))
    (fun r => by
      rw [prefix_lead]
      simp only [Time.prefixWord, List.length_append, List.length_replicate, List.length_cons]; omega)
    (fun r => (boostFL_spec (boostC V) (List.ofFn r.1.2) r.2.bits).2)
  ⟨F.program, fun r => by
    obtain ⟨rc, h1, h2⟩ := F.realizes r
    exact ⟨rc, h1, h2.trans (boostFL_spec (boostC V) (List.ofFn r.1.2) r.2.bits).1⟩⟩

theorem bnd_stage1 : Bnd (fun r => Machines.WidthPrefix.prefixBudget (ClockRequest.word r).length) :=
  (Bnd.mul (Bnd.const 200) (Bnd.pow Bnd.scale 2)).mono (fun r => by unfold Machines.WidthPrefix.prefixBudget; simp [Yr])

theorem bnd_stage2 : Bnd (fun r => langBudget noCallee zF VV MM (Time.prefixWord (ClockRequest.word r))
    (preCost (Time.prefixWord (ClockRequest.word r)) +
      costS (globOf (Time.prefixWord (ClockRequest.word r))) (boostFL (boostC V)) + 1)) := by
  have hs : Bnd (fun r => Nat.size (ClockRequest.word r).length) := ⟨1, 1, fun r => by
    have := Nat.size_le.2 (Nat.lt_two_pow_self (n := (ClockRequest.word r).length)); simp only [Yr, pow_one]; omega⟩
  refine (Bnd.mul (Bnd.const (flConst (boostFL (boostC V)))) (Bnd.pow ((((bnd_pow_s 6).add (hs.add (Bnd.const 1))).add
    bnd_len).add (Bnd.const 2)) (dpS (boostFL (boostC V)) + 5))).mono (fun r => ?_)
  refine (flBudget_le (boostFL (boostC V)) (Time.prefixWord (ClockRequest.word r))).trans ?_
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
  rw [prefix_lead, ← sixtyfour_pow]
  simp only [Time.prefixWord, List.length_append, List.length_replicate, List.length_cons]
  omega

/-! ## The generator from the constraint circuit's printer -/

/-- The whole generator: prefix, boost, main stage. -/
noncomputable def genWF (irrPoly : ℕ → (ZMod 2)[X]) {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es)
    (WC : ConsWF V irrPoly Kc ec) (AB aB : ℕ) (hB : ∀ r, calleeBud V Ks es Kc ec r ≤ AB * Yr r ^ aB) :=
  NearCubicGates.Adapters.Code.composeFramed (NearCubicGates.Adapters.Code.composeFramed stageP (boostWF V))
    (mainWF V irrPoly WS WC AB aB hB)

/-- **The generator from the constraint circuit's printer** (`lem:generator`): given Shoup's machine
(`PolyTimeIrrChoice`) and an ordinary
machine printing the constraint circuit's serialization (`ConsWF`), the generator of the instance
`ownInst V irrPoly (ownCons V irrPoly)` is an ordinary word function within `K·(n + |bits t| + 1)^e`. -/
theorem generatorMachine_of_consWF (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])
    (hP : Published.Shoup.PolyTimeIrrChoice irrPoly) (hC : ∃ K e : ℕ, Nonempty (ConsWF V irrPoly K e)) :
    GeneratorMachine V irrPoly (ownCons V irrPoly) := by
  obtain ⟨Ks, es, ⟨WS⟩⟩ := hP
  obtain ⟨Kc, ec, ⟨WC⟩⟩ := hC
  obtain ⟨AB, aB, hB⟩ := bnd_calleeBud V Ks es Kc ec
  have hT : Bnd (fun r => (2 * ((2 * Machines.WidthPrefix.prefixBudget (ClockRequest.word r).length + 2) + 1 +
      (2 * langBudget noCallee zF VV MM (Time.prefixWord (ClockRequest.word r))
        (preCost (Time.prefixWord (ClockRequest.word r)) +
          costS (globOf (Time.prefixWord (ClockRequest.word r))) (boostFL (boostC V)) + 1) + 2)) + 2) + 1 +
      (2 * langBudget (genCallee V irrPoly WS WC) (zG AB aB) VV MM (inpOf V r) (mainN V irrPoly WS WC AB aB r) + 2)) :=
    ((Bnd.mul (Bnd.const 2) ((((Bnd.mul (Bnd.const 2) bnd_stage1).add (Bnd.const 3)).add
      (Bnd.mul (Bnd.const 2) (bnd_stage2 V))).add (Bnd.const 2))).add (Bnd.const 3)).add
      (Bnd.mul (Bnd.const 2) (bnd_stage3 V irrPoly WS WC AB aB)) |>.add (Bnd.const 2) |>.mono (fun r => by omega)
  obtain ⟨A, a, hA⟩ := hT
  refine ⟨A * 3 ^ a, a, ⟨wordFunctionRelax (fun r => ?_) (genWF V irrPoly WS WC AB aB hB)⟩⟩
  calc _ ≤ A * Yr r ^ a := hA r
    _ ≤ A * (3 * (r.1.1 + natBitLength r.2 + 1)) ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Yr_le_input r) a)
    _ = A * 3 ^ a * (r.1.1 + natBitLength r.2 + 1) ^ a := by rw [mul_pow]; ring

end NearCubicGates.Adapters.RAMACSP.Gen

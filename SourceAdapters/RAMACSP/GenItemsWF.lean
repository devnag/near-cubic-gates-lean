import SourceAdapters.RAMACSP.GenItemsRun
import SourceAdapters.RAMACSP.GenFinal
import Proof.Gates.CellsPack.Lang
import Proof.Gates.Cells.OutLen

/-!
# The machine-items printer as an ordinary word function

Paper: `lem:generator`. The machine-item printer is one ordinary word
function with a globally fixed polynomial budget on the request encoding.

The word function is `composeFramed (composeFramed prefix boost) main`, as the generator's (`GenFinal`):
- `prefix`: `w ↦ frame (1^s 0 ++ w)`, `s = size |w|` (`GenFinal.stageP`);
- `boost`: `↦ frame (1^(c+s) 0 ++ w)` with `c = boostI V`, so that the run constants `K = N = 2·64^(c+s)` exceed the
  constants of the code terms (`cB V`), the masks of the field, the coordinate array (`mH·mH·f` bits) and every loop
  count, on every request (`iFits`);
- `main`: the cell program `itemsMainP V body` (`GenItemsRun`) with the callee of Shoup's machine and the coordinate
  machine.
`machineItemsWF_of_printer`: from Shoup's machine, the coordinate machine (`Joins.CoordArrayWF`) and a printing
program `body` that prints the numbers `machineNums V irrPoly r` from every state of the item printer, the seam's
`MachineItemsWF V irrPoly` holds.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMACSP.Gen
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicGates.Adapters.Machine.ComposeCarry
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

variable (V : Verifier)

/-! ## The boost -/

/-- The boost constant: `64^c` dominates the linear constant and the constants of the code terms. -/
def boostI : ℕ := linConst V + cB V + 10

/-- The main stage's input word. -/
def inpI (r : ClockRequest) : List Bool := boostWord (boostI V) (ClockRequest.word r)

theorem lead_inpI (r : ClockRequest) :
    leadOnes (inpI V r) = boostI V + Nat.size (ClockRequest.word r).length :=
  NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_rep _ _

theorem le_sixtyfour_pow (n : ℕ) : n ≤ 64 ^ n := by
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : 2 ^ n ≤ 64 ^ n := Nat.pow_le_pow_left (by norm_num) n
  omega

/-- **The run constants dominate**: with `X = linConst · Y`, `X + cB + 10 ≤ 64^L`, `X³ ≤ 64^L`, `64 ≤ 64^L`. -/
theorem big_bound (r : ClockRequest) :
    linConst V * Yr r + cB V + 10 ≤ 64 ^ (boostI V + Nat.size (ClockRequest.word r).length) ∧
      (linConst V * Yr r) ^ 3 ≤ 64 ^ (boostI V + Nat.size (ClockRequest.word r).length) ∧
      64 ≤ 64 ^ (boostI V + Nat.size (ClockRequest.word r).length) := by
  set s := Nat.size (ClockRequest.word r).length
  set c := boostI V with hc
  set Y := Yr r
  set l := linConst V
  have hY1 : 1 ≤ Y := one_le_Yr r
  have hY : Y ≤ 2 ^ s := Yr_le_pow r
  have h2s : 2 ^ s ≤ 64 ^ s := Nat.pow_le_pow_left (by norm_num) s
  have hcb : c ≤ 64 ^ c := le_sixtyfour_pow c
  have e : 64 ^ (c + s) = 64 ^ c * 64 ^ s := pow_add _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    have h1 : l * Y + cB V + 10 ≤ c * Y := by
      have : (l + cB V + 10) * Y = l * Y + (cB V + 10) * Y := by ring
      have : cB V + 10 ≤ (cB V + 10) * Y := Nat.le_mul_of_pos_right _ hY1
      have : c * Y = (l + cB V + 10) * Y := by rw [hc]; rfl
      omega
    calc l * Y + cB V + 10 ≤ c * Y := h1
      _ ≤ 64 ^ c * 64 ^ s := Nat.mul_le_mul hcb (hY.trans h2s)
  · rw [e, mul_pow]
    have hl : l < 2 ^ l := Nat.lt_two_pow_self
    have hl3 : l ^ 3 ≤ 64 ^ c := by
      calc l ^ 3 ≤ (2 ^ l) ^ 3 := Nat.pow_le_pow_left (le_of_lt hl) 3
        _ = 8 ^ l := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 64 ^ l := Nat.pow_le_pow_left (by norm_num) l
        _ ≤ 64 ^ c := Nat.pow_le_pow_right (by norm_num) (by rw [hc]; unfold boostI; omega)
    have hY3 : Y ^ 3 ≤ 64 ^ s := by
      calc Y ^ 3 ≤ (2 ^ s) ^ 3 := Nat.pow_le_pow_left hY 3
        _ = 8 ^ s := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 64 ^ s := Nat.pow_le_pow_left (by norm_num) s
    exact Nat.mul_le_mul hl3 hY3
  · calc 64 = 64 ^ 1 := by norm_num
      _ ≤ 64 ^ (c + s) := Nat.pow_le_pow_right (by norm_num) (by rw [hc]; unfold boostI; omega)

/-! ## The callee budgets -/

section Budget

variable (irrPoly : ℕ → (ZMod 2)[X])

theorem irrI_lt (r : ClockRequest) : irrI V irrPoly r < 2 ^ (fieldExp V r.2 + 1) := WireExponent3_5.GF.ofPoly_lt _ _

theorem nbl_smallI (r : ClockRequest) :
    natBitLength (fieldExp V r.2) ≤ fieldExp V r.2 + 1 ∧ natBitLength (irrI V irrPoly r) ≤ fieldExp V r.2 + 1 ∧
      natBitLength (domExp V r.2) ≤ fieldExp V r.2 + 1 := by
  have := domExp_add_two_le_fieldExp V r.2
  refine ⟨natBitLength_le _, natBitLength_le_of_lt (by omega) (irrI_lt V irrPoly r), ?_⟩
  have := natBitLength_le (domExp V r.2); omega

theorem coordIn_len (r : ClockRequest) : (coordIn V irrPoly r).length ≤ 6 * fieldExp V r.2 + 9 := by
  obtain ⟨a, b, c⟩ := nbl_smallI V irrPoly r
  simp only [coordIn, Joins.coordInput, coordRequest, List.length_append, FL.natWord_len]
  have : modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2) = irrI V irrPoly r := rfl
  rw [this]; omega

theorem bnd_coordIn : Bnd (fun r => (coordIn V irrPoly r).length) :=
  ((Bnd.mul (Bnd.const 6) (bnd_f V)).add (Bnd.const 9)).mono (fun r => coordIn_len V irrPoly r)

/-- The two callee budgets. -/
def iCalleeBud (Ks es Kc ec : ℕ) (r : ClockRequest) : ℕ :=
  (2 * (8 + dropBudget (fieldExp V r.2) (Ks * (fieldExp V r.2 + 1) ^ es)) + 2) +
  (2 * (8 + dropBudget ((coordIn V irrPoly r).length + 1)
    (2 * (8 + dropBudget (coordIn V irrPoly r).length (Kc * ((coordIn V irrPoly r).length + 1) ^ ec)) + 2)) + 2)

theorem bnd_iCalleeBud (Ks es Kc ec : ℕ) : Bnd (iCalleeBud V irrPoly Ks es Kc ec) := by
  have hd : ∀ L B, dropBudget L B = 120 * L + 129 + 2 * B := fun L B => by unfold dropBudget; ring
  have hc := bnd_coordIn V irrPoly
  refine (((((Bnd.const 5000).add (Bnd.mul (Bnd.const 240) (bnd_f V))).add (Bnd.mul (Bnd.const 4)
    (Bnd.mul (Bnd.const Ks) (Bnd.pow ((bnd_f V).add (Bnd.const 1)) es)))).add (Bnd.mul (Bnd.const 2000) hc)).add
    (Bnd.mul (Bnd.const 16) (Bnd.mul (Bnd.const Kc) (Bnd.pow (hc.add (Bnd.const 1)) ec)))).mono (fun r => ?_)
  unfold iCalleeBud; rw [hd, hd, hd]; omega

theorem iBud_inl (Ks es Kc ec : ℕ) (r : ClockRequest) (h : 1 ≤ fieldExp V r.2) :
    iBud V irrPoly Ks es Kc ec (.inl ⟨fieldExp V r.2, h⟩) ≤ iCalleeBud V irrPoly Ks es Kc ec r := by
  unfold iBud iCalleeBud
  rw [sumBudget_inl]
  simp only [List.length_replicate]
  omega

theorem iBud_co (Ks es Kc ec : ℕ) (r : ClockRequest) :
    iBud V irrPoly Ks es Kc ec (.inr (.inl r)) ≤ iCalleeBud V irrPoly Ks es Kc ec r := by
  unfold iBud iCalleeBud
  rw [sumBudget_inr]
  simp only [sumInput, sumBudget_inl, List.length_cons]
  omega

end Budget

/-! ## The main stage's size conditions -/

section Main

variable (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)
  {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordRWF V irrPoly hI Kc ec)

theorem wordW_le_col (t : ℕ) : wordW V t ≤ 2 ^ colExp V t := by
  rw [wordW_eq]; exact Nat.pow_le_pow_right (by norm_num) (by unfold colExp; omega)

theorem iFits (AB aB : ℕ) (hB : ∀ r, iCalleeBud V irrPoly Ks es Kc ec r ≤ AB * Yr r ^ aB) (r : ClockRequest) :
    IFits V irrPoly (Ks := Ks) (es := es) (Kc := Kc) (ec := ec) r
      (ctxOf (itemsCallee V irrPoly hI WS WC) (zG AB aB) (inpI V r)) (globOf (inpI V r)) := by
  set s := Nat.size (ClockRequest.word r).length with hs
  set L := boostI V + s with hL
  have hlead : leadOnes (inpI V r) = L := lead_inpI V r
  have hK : (globOf (inpI V r)).K = 2 * 64 ^ L := by show kOf _ = _; unfold kOf; rw [hlead]
  have hN : (globOf (inpI V r)).N = 2 * 64 ^ L := hK
  have hW : (ctxOf (itemsCallee V irrPoly hI WS WC) (zG AB aB) (inpI V r)).Wd = 4 * 64 ^ L := by
    show 2 ^ (6 * leadOnes (inpI V r)) * 4 = _; rw [hlead, sixtyfour_pow]; ring
  have hLk : (ctxOf (itemsCallee V irrPoly hI WS WC) (zG AB aB) (inpI V r)).Lk = 4 * 64 ^ L := by
    show 2 ^ (6 * leadOnes (inpI V r)) * 4 = _; rw [hlead, sixtyfour_pow]; ring
  have hBk : (ctxOf (itemsCallee V irrPoly hI WS WC) (zG AB aB) (inpI V r)).Bk = 2 ^ (aB * L) * (AB + 1) := by
    show 2 ^ (aB * leadOnes (inpI V r)) * (AB + 1) = _; rw [hlead]
  have hcap : (globOf (inpI V r)).cap + 1 = 2 ^ (globOf (inpI V r)).K := cap_add _
  obtain ⟨hb1, hb3, hb64⟩ := big_bound V r
  rw [← hs, ← hL] at hb1 hb3 hb64
  have hlin := lin_bound V r
  set X := linConst V * Yr r with hX
  have hmf := domExp_add_two_le_fieldExp V r.2
  have hwc := wordW_le_col V r.2
  have hfX : fieldExp V r.2 + 20 ≤ X := by
    have := hlin; generalize 2 ^ inExp V r = P at this; generalize 2 ^ colExp V r.2 = Q at this; omega
  have hwX : 16 * wordW V r.2 ≤ X := by
    have := hlin; generalize 2 ^ inExp V r = P at this; omega
  have hA : r.1.1 + r.2.bits.length + fieldExp V r.2 + clockConst V + tagExp V + 20 ≤ X := by
    have := hlin; generalize 2 ^ inExp V r = P at this; generalize 2 ^ colExp V r.2 = Q at this; omega
  -- the coordinate array is at most `X³`
  have hD : cwN V r ≤ X ^ 3 := by
    have h1 : domExp V r.2 ≤ X := by omega
    have h2 : fieldExp V r.2 ≤ X := by omega
    show domExp V r.2 * domExp V r.2 * fieldExp V r.2 ≤ X ^ 3
    calc domExp V r.2 * domExp V r.2 * fieldExp V r.2 ≤ X * X * X := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h2
      _ = X ^ 3 := by ring
  have hXX : 2 * X ≤ 64 ^ L := by
    have h20 : 20 ≤ X := by omega
    have e : X ^ 3 = X * (X * X) := by ring
    have h2 : X * 2 ≤ X * (X * X) := Nat.mul_le_mul_left X (le_trans (by norm_num : 2 ≤ 20 * 20) (Nat.mul_le_mul h20 h20))
    omega
  have hKbig : X + cB V + 10 ≤ (globOf (inpI V r)).K := by rw [hK]; omega
  have hKD : cwN V r + 8 ≤ (globOf (inpI V r)).K := by rw [hK]; omega
  have hcB := cB_16 V
  -- `cap` dominates `cB + 2^(f+8)`
  have hcapB : cB V + 2 ^ (fieldExp V r.2 + 8) ≤ (globOf (inpI V r)).cap := by
    set K := (globOf (inpI V r)).K
    have h1 : cB V < 2 ^ (K - 1) := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 2 ^ (fieldExp V r.2 + 8) ≤ 2 ^ (K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hdf : 2 ^ (domExp V r.2 + 8) ≤ 2 ^ (fieldExp V r.2 + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlinp := linConst_pos V
  -- the callee budgets
  have hbud : iCalleeBud V irrPoly Ks es Kc ec r ≤ 2 ^ (aB * L) * (AB + 1) := by
    have h1 := hB r
    have h2 : Yr r ^ aB ≤ 2 ^ (aB * s) := by
      rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Yr_le_pow r) aB
    have h3 : 2 ^ (aB * s) ≤ 2 ^ (aB * L) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
    have h4 : AB * Yr r ^ aB ≤ (AB + 1) * 2 ^ (aB * L) :=
      Nat.mul_le_mul (by omega) (h2.trans h3)
    rw [Nat.mul_comm (2 ^ (aB * L))]; omega
  obtain ⟨n1, n2, n3⟩ := nbl_smallI V irrPoly r
  have hWlt : 4 * 64 ^ L < 2 ^ (4 * 64 ^ L) := Nat.lt_two_pow_self
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun h => ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [hK, hN]
  · omega
  · rw [hK, hN]
  · rw [hN]; omega
  · omega
  · omega
  · omega
  · omega
  · rw [hLk]; omega
  · rw [hLk]; omega
  · rw [hBk]; exact (iBud_inl V irrPoly Ks es Kc ec r h).trans hbud
  · rw [hBk]; exact (iBud_co V irrPoly Ks es Kc ec r).trans hbud
  · rw [hW]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rw [hW]; omega
  · rw [hW]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ## The main stage as a word function -/

variable (body : P)

/-- The cost bound of the main stage's run. -/
def mainNI (AB aB : ℕ) (r : ClockRequest) : ℕ :=
  iCost V irrPoly body (ctxOf (itemsCallee V irrPoly hI WS WC) (zG AB aB) (inpI V r)) (globOf (inpI V r)) (inpI V r) r

/-- **The main stage** (`wordFunction_of_lang`). -/
noncomputable def mainWFI (hwf : WF baseA body) (hok : Ok 0 body)
    (hden : ∀ (G : Glob) (r : ClockRequest) (s : FS), Room V r G → Base V r s → CoordV V irrPoly hI r s →
      den G s body = machineNums V irrPoly r)
    (hbound : ∀ r x, x ∈ machineNums V irrPoly r → x < 2 ^ (fieldExp V r.2 + 1))
    (AB aB : ℕ) (hB : ∀ r, iCalleeBud V irrPoly Ks es Kc ec r ≤ AB * Yr r ^ aB) :
    WordFunction ClockRequest (inpI V) (fun r => RepairSource.frame (machineItemsWord V irrPoly r))
      (fun r => langBudget (itemsCallee V irrPoly hI WS WC) (zG AB aB) VV MM (inpI V r)
        (mainNI V irrPoly hI WS WC body AB aB r)) :=
  wordFunction_of_lang (inpI V) _ (itemsCallee V irrPoly hI WS WC) (zG AB aB) (itemsMainP V body)
    (mainNI V irrPoly hI WS WC body AB aB)
    (fun r => items_run V irrPoly hI WS WC body hwf hok hden hbound 4 6 (AB + 1) aB r
      (boostI V + Nat.size (ClockRequest.word r).length) (by unfold boostI; omega)
      (iFits V irrPoly hI WS WC AB aB hB r))
    (fun r => by show 1 ≤ 2 ^ (6 * _) * 4; have := Nat.one_le_two_pow (n := 6 * leadOnes (inpI V r)); omega)

end Main

/-! ## Polynomial bounds -/

section Bounds

theorem bnd_pow_LI (c : ℕ) : Bnd (fun r => 2 ^ (c * leadOnes (inpI V r))) := by
  refine (Bnd.mul (Bnd.const (2 ^ (c * boostI V))) (bnd_pow_s c)).mono (fun r => ?_)
  rw [lead_inpI, Nat.mul_add, pow_add]

theorem bnd_kOfI : Bnd (fun r => kOf (inpI V r)) :=
  (Bnd.mul (Bnd.const 2) (bnd_pow_LI V 6)).mono (fun r => by unfold kOf; rw [← sixtyfour_pow])

theorem bnd_leadI : Bnd (fun r => leadOnes (inpI V r)) := by
  refine (Bnd.add (Bnd.const (boostI V)) Bnd.scale).mono (fun r => ?_)
  rw [lead_inpI]
  have := Nat.size_le.2 (Nat.lt_two_pow_self (n := (ClockRequest.word r).length))
  simp only [Yr, pow_one] at *; omega

theorem bnd_costSI (q : S) : Bnd (fun r => costS (globOf (inpI V r)) q) := by
  have hk := bnd_kOfI V
  refine (Bnd.mul (Bnd.mul (Bnd.const (8 * szS q)) ((Bnd.mul (Bnd.const 400) (Bnd.pow (hk.add (Bnd.const 1)) 3)).add
    (Bnd.const 400))) (Bnd.pow (hk.add (Bnd.const 1)) (dpS q))).mono (fun r => ?_)
  have := costS_le (globOf (inpI V r)) q
  unfold opc at this
  exact this.trans (le_of_eq (by simp only [globOf]))

variable (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)
  {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordRWF V irrPoly hI Kc ec) (body : P)

theorem bnd_cwN : Bnd (fun r => cwN V r) := by
  refine (Bnd.mul (Bnd.mul (bnd_f V) (bnd_f V)) (bnd_f V)).mono (fun r => ?_)
  have := domExp_add_two_le_fieldExp V r.2
  show domExp V r.2 * domExp V r.2 * fieldExp V r.2 ≤ fieldExp V r.2 * fieldExp V r.2 * fieldExp V r.2
  exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) le_rfl

theorem bnd_mainNI (AB aB : ℕ) : Bnd (mainNI V irrPoly hI WS WC body AB aB) := by
  have hL := bnd_leadI V
  have hk := bnd_kOfI V
  have hW := bnd_pow_LI V 6
  have hB := bnd_pow_LI V aB
  have hf := bnd_f V
  refine ((((((((((((Bnd.mul (Bnd.const 20) hL).add (Bnd.mul (Bnd.const 5) hk)).add (Bnd.const 400)).add
    (bnd_costSI V (stageRI V))).add (Bnd.mul (Bnd.const 64) hf)).add (Bnd.mul (Bnd.const 8) hW)).add
    (Bnd.mul (Bnd.const (2 * (AB + 1))) hB)).add (bnd_costSI V lenP)).add
    (Bnd.mul (Bnd.const 10) (bnd_cwN V))).add (bnd_costSI V setupP)).add (bnd_costSI V (comp body))).add
    (bnd_costSI V (.emit (.k 0)))).mono (fun r => ?_)
  obtain ⟨n1, n2, n3⟩ := nbl_smallI V irrPoly r
  unfold mainNI iCost preCost callIrrCost callCoordCost
  simp only [ctxOf, zG, zM, Sz.Lk, Sz.Bk]
  ring_nf
  ring_nf at n1 n2 n3
  omega

theorem bnd_stage3I (AB aB : ℕ) :
    Bnd (fun r => langBudget (itemsCallee V irrPoly hI WS WC) (zG AB aB) VV MM (inpI V r)
      (mainNI V irrPoly hI WS WC body AB aB r)) := by
  have hL := bnd_leadI V
  have hW := bnd_pow_LI V 6
  have hB := bnd_pow_LI V aB
  have hG : Bnd (fun r => NearCubicGates.Close.CellsPack.Gof (itemsCallee V irrPoly hI WS WC) (zG AB aB)
      (leadOnes (inpI V r))) := by
    refine ((((Bnd.mul (Bnd.const 8) hW).add (Bnd.mul (Bnd.const (AB + 1)) hB)).add hL).add
      (Bnd.const (AB + aB + 30 + TSK (itemsCallee V irrPoly hI WS WC)))).mono (fun r => ?_)
    unfold NearCubicGates.Close.CellsPack.Gof
    simp only [zG, zM, Sz.W, Sz.Lk, Sz.Bk]
    ring_nf; omega
  have hI' : Bnd (fun r => (inpI V r).length) := by
    refine ((hL.add (Bnd.const 1)).add bnd_len).mono (fun r => le_of_eq ?_)
    show (inpI V r).length = leadOnes (inpI V r) + 1 + (ClockRequest.word r).length
    rw [lead_inpI]; simp only [inpI, boostWord, List.length_append, List.length_replicate, List.length_cons]
    ring
  refine ((Bnd.mul (Bnd.const (10 ^ 6)) (Bnd.mul ((bnd_mainNI V irrPoly hI WS WC body AB aB).add (Bnd.const 1))
    (Bnd.pow hG 2))).add (Bnd.mul (Bnd.const 10) hI')).mono (fun r => ?_)
  exact NearCubicGates.Close.CellsPack.lang_le2 _ _ _ _

end Bounds

/-! ## The boost stage -/

/-- **The boost stage** (`boostFL`, `GenRun`) with the constant `boostI V`. -/
noncomputable def boostWFI :
    WordFunction ClockRequest (fun r => Time.prefixWord (ClockRequest.word r)) (fun r => frame (inpI V r))
      (fun r => langBudget noCallee zF VV MM (Time.prefixWord (ClockRequest.word r))
        (preCost (Time.prefixWord (ClockRequest.word r)) +
          costS (globOf (Time.prefixWord (ClockRequest.word r))) (boostFL (boostI V)) + 1)) :=
  let F := flWF (fun r : ClockRequest => Time.prefixWord (ClockRequest.word r)) (boostFL (boostI V)) (wf_boostFL _)
    (fun r => by rw [prefix_lead]; exact Nat.size_pos.mpr (by rw [word_len]; omega))
    (fun r => by
      rw [prefix_lead]
      simp only [Time.prefixWord, List.length_append, List.length_replicate, List.length_cons]; omega)
    (fun r => (boostFL_spec (boostI V) (List.ofFn r.1.2) r.2.bits).2)
  ⟨F.program, fun r => by
    obtain ⟨rc, h1, h2⟩ := F.realizes r
    exact ⟨rc, h1, h2.trans (boostFL_spec (boostI V) (List.ofFn r.1.2) r.2.bits).1⟩⟩

theorem bnd_stage2I : Bnd (fun r => langBudget noCallee zF VV MM (Time.prefixWord (ClockRequest.word r))
    (preCost (Time.prefixWord (ClockRequest.word r)) +
      costS (globOf (Time.prefixWord (ClockRequest.word r))) (boostFL (boostI V)) + 1)) := by
  have hs : Bnd (fun r => Nat.size (ClockRequest.word r).length) := ⟨1, 1, fun r => by
    have := Nat.size_le.2 (Nat.lt_two_pow_self (n := (ClockRequest.word r).length)); simp only [Yr, pow_one]; omega⟩
  refine (Bnd.mul (Bnd.const (flConst (boostFL (boostI V)))) (Bnd.pow ((((bnd_pow_s 6).add (hs.add (Bnd.const 1))).add
    bnd_len).add (Bnd.const 2)) (dpS (boostFL (boostI V)) + 5))).mono (fun r => ?_)
  refine (flBudget_le (boostFL (boostI V)) (Time.prefixWord (ClockRequest.word r))).trans ?_
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
  rw [prefix_lead, ← sixtyfour_pow]
  simp only [Time.prefixWord, List.length_append, List.length_replicate, List.length_cons]
  omega

/-! ## The seam -/

/-- The whole printer: prefix, boost, main stage. -/
noncomputable def itemsWF (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)
    {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordRWF V irrPoly hI Kc ec) (body : P)
    (hwf : WF baseA body) (hok : Ok 0 body)
    (hden : ∀ (G : Glob) (r : ClockRequest) (s : FS), Room V r G → Base V r s → CoordV V irrPoly hI r s →
      den G s body = machineNums V irrPoly r)
    (hbound : ∀ r x, x ∈ machineNums V irrPoly r → x < 2 ^ (fieldExp V r.2 + 1))
    (AB aB : ℕ) (hB : ∀ r, iCalleeBud V irrPoly Ks es Kc ec r ≤ AB * Yr r ^ aB) :=
  NearCubicGates.Adapters.Code.composeFramed (NearCubicGates.Adapters.Code.composeFramed stageP (boostWFI V))
    (mainWFI V irrPoly hI WS WC body hwf hok hden hbound AB aB hB)

/-- **The machine-items printer from a printing program**: given Shoup's machine (`PolyTimeIrrChoice`), its
irreducibility (`IrreducibleChoice`), the coordinate machine (`Joins.CoordArrayWF`), and a printing program `body`
that, from every state of the item printer, prints the numbers `machineNums V irrPoly r` (each below `2^{f+1}`), the
machine items are printed by an ordinary machine within `K·(n + |bits t| + 1)^e` (the seam `MachineItemsWF`). -/
theorem machineItemsWF_of_printer (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])
    (hP : Published.Shoup.PolyTimeIrrChoice irrPoly) (hI : Published.Shoup.IrreducibleChoice irrPoly)
    (hC : Joins.CoordArrayWF) (body : P) (hwf : WF baseA body) (hok : Ok 0 body)
    (hden : ∀ (G : Glob) (r : ClockRequest) (s : FS), Room V r G → Base V r s →
      CoordV V irrPoly hI r s → den G s body = machineNums V irrPoly r)
    (hbound : ∀ r x, x ∈ machineNums V irrPoly r → x < 2 ^ (fieldExp V r.2 + 1)) :
    Gen.MachineItemsWF V irrPoly := by
  obtain ⟨Ks, es, ⟨WS⟩⟩ := hP
  obtain ⟨Kc, ec, ⟨WC⟩⟩ := coordWF hC V irrPoly hI
  obtain ⟨AB, aB, hB⟩ := bnd_iCalleeBud V irrPoly Ks es Kc ec
  have hT : Bnd (fun r => (2 * ((2 * Machines.WidthPrefix.prefixBudget (ClockRequest.word r).length + 2) + 1 +
      (2 * langBudget noCallee zF VV MM (Time.prefixWord (ClockRequest.word r))
        (preCost (Time.prefixWord (ClockRequest.word r)) +
          costS (globOf (Time.prefixWord (ClockRequest.word r))) (boostFL (boostI V)) + 1) + 2)) + 2) + 1 +
      (2 * langBudget (itemsCallee V irrPoly hI WS WC) (zG AB aB) VV MM (inpI V r)
        (mainNI V irrPoly hI WS WC body AB aB r) + 2)) :=
    ((Bnd.mul (Bnd.const 2) ((((Bnd.mul (Bnd.const 2) bnd_stage1).add (Bnd.const 3)).add
      (Bnd.mul (Bnd.const 2) (bnd_stage2I V))).add (Bnd.const 2))).add (Bnd.const 3)).add
      (Bnd.mul (Bnd.const 2) (bnd_stage3I V irrPoly hI WS WC body AB aB)) |>.add (Bnd.const 2) |>.mono (fun r => by omega)
  obtain ⟨A, a, hA⟩ := hT
  refine ⟨A * 3 ^ a, a, ⟨wordFunctionRelax (fun r => ?_)
    (itemsWF V irrPoly hI WS WC body hwf hok hden hbound AB aB hB)⟩⟩
  calc _ ≤ A * Yr r ^ a := hA r
    _ ≤ A * (3 * (r.1.1 + natBitLength r.2 + 1)) ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Yr_le_input r) a)
    _ = A * 3 ^ a * (r.1.1 + natBitLength r.2 + 1) ^ a := by rw [mul_pow]; ring

end NearCubicGates.Adapters.RAMACSP.Gen.Items

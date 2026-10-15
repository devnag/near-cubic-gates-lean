import Proof.Gates.WordPrograms.WMX
import Proof.Wire_3_5.SelectionMachineSortRound

set_option autoImplicit false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (copyPair emitB rst copyLoop_rst emitB_rst fwdA_rst rd_app0)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## Record streams -/

/-- **The stream of the records `ws`**: their frames, then one `false`. -/
def recStream (ws : List (List Bool)) : List Bool := ws.flatMap frame ++ [false]

theorem flatMap_frame_length (L : ℕ) : ∀ (ws : List (List Bool)), (∀ w ∈ ws, w.length = L) →
    (ws.flatMap frame).length = ws.length * (2 * L + 1)
  | [], _ => by simp
  | w :: ws, h => by
    rw [List.flatMap_cons, List.length_append, frame_length, h w (by simp),
      flatMap_frame_length L ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]
    simp only [List.length_cons]
    ring

theorem recStream_length (L : ℕ) (ws : List (List Bool)) (h : ∀ w ∈ ws, w.length = L) :
    (recStream ws).length = ws.length * (2 * L + 1) + 1 := by
  rw [recStream, List.length_append, flatMap_frame_length L ws h]; rfl

/-- Record `i` sits at position `i·(2L + 1)`. -/
theorem recStream_split (L : ℕ) (ws : List (List Bool)) (h : ∀ w ∈ ws, w.length = L) (i : ℕ) (hi : i < ws.length) :
    recStream ws = (ws.take i).flatMap frame ++ frameP ws[i] ++ false :: ((ws.drop (i + 1)).flatMap frame ++ [false]) ∧
      ((ws.take i).flatMap frame).length = i * (2 * L + 1) := by
  constructor
  · have e : ws = ws.take i ++ ws[i] :: ws.drop (i + 1) := by simp
    conv_lhs => rw [recStream, e]
    rw [List.flatMap_append, List.flatMap_cons, frame_eq_frameP]
    simp
  · rw [flatMap_frame_length L _ (fun w hw => h w (List.mem_of_mem_take hw)), List.length_take,
      Nat.min_eq_left (by omega)]

theorem recStream_bit_rec (L : ℕ) (ws : List (List Bool)) (h : ∀ w ∈ ws, w.length = L) (hL : 1 ≤ L) (i : ℕ)
    (hi : i < ws.length) : readTapeBit (recStream ws) (i * (2 * L + 1)) = true := by
  obtain ⟨e, hl⟩ := recStream_split L ws h i hi
  rw [e, ← hl, List.append_assoc, rd_app0]
  have hw : ws[i].length = L := h _ (List.getElem_mem hi)
  obtain ⟨b, bs, hb⟩ : ∃ b bs, ws[i] = b :: bs := by
    cases hc : ws[i] with
    | nil => rw [hc] at hw; simp at hw; omega
    | cons b bs => exact ⟨b, bs, rfl⟩
  rw [hb]; rfl

theorem recStream_bit_end (L : ℕ) (ws : List (List Bool)) (h : ∀ w ∈ ws, w.length = L) :
    readTapeBit (recStream ws) (ws.length * (2 * L + 1)) = false := by
  rw [← flatMap_frame_length L ws h, recStream, rd_app0]; rfl

/-! ## Copying one record to the work stream -/

/-- Copy the record at `I`'s head to `Wk` (as its frame), step `I` past it, and return `Wk`'s head to `0`. -/
def copyRec (I Wk : Fin (ns + 1)) (CI CW : Fin nr) : WM ns nr :=
  .seq (.whs I (copyPair I Wk CI CW)) (.seq (emitB Wk CW false) (.seq (WM.fwdC I CI) (WM.rewind Wk CW)))

theorem rst_self (σ : WState ns nr) {I Wk : Fin (ns + 1)} {CI CW : Fin nr} (hIW : I ≠ Wk) (hC : CI ≠ CW) (p : ℕ)
    (hIh : σ.sh I = p) (hCI : σ.val CI = p) (hWh : σ.sh Wk = 0) (hCW : σ.val CW = 0) :
    rst σ I Wk CI CW (σ.st Wk) p [] = σ := by
  apply WState.eq
  · funext j; simp only [rst, Function.update_apply, List.length_nil]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  · funext j; simp only [rst, Function.update_apply]
    split_ifs with h1
    · subst h1; simp [overlay]
    · rfl
  · funext j; simp only [rst, Function.update_apply, List.length_nil]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  · rfl

/-- **One record copied**: `Wk := frame w` (head `0`, `CW` back at `0`), `I` and `CI` advanced past the record. -/
theorem copyRec_spec (cap : ℕ) {I Wk : Fin (ns + 1)} {CI CW : Fin nr} (hIW : I ≠ Wk) (hC : CI ≠ CW) (σ : WState ns nr)
    (pre w post : List Bool) (hI : σ.st I = pre ++ frameP w ++ false :: post) (hIh : σ.sh I = pre.length)
    (hCI : σ.val CI = pre.length) (hWh : σ.sh Wk = 0) (hCW : σ.val CW = 0) (hWl : (σ.st Wk).length ≤ 2 * w.length + 1)
    (hcap : pre.length + 2 * w.length + 2 ≤ cap) :
    WExec cap (copyRec I Wk CI CW) σ
      (((σ.sets Wk (frame w)).seth I (pre.length + 2 * w.length + 1)).setv CI (pre.length + 2 * w.length + 1))
      (40 * w.length + 22) := by
  have e0 := rst_self σ hIW hC pre.length hIh hCI hWh hCW
  have h1 := copyLoop_rst cap σ (σ.st Wk) hIW hC w pre [] post hI (by omega) (by simp; omega)
  rw [e0, List.nil_append] at h1
  have h2 := emitB_rst cap σ (σ.st Wk) hIW hC (pre.length + 2 * w.length) (frameP w) false (by simp; omega)
  have h3 := fwdA_rst cap σ (σ.st Wk) hIW hC (pre.length + 2 * w.length) (frameP w ++ [false]) (by omega)
  set τ := rst σ I Wk CI CW (σ.st Wk) (pre.length + 2 * w.length + 1) (frameP w ++ [false]) with hτ
  have h4 := wrewind_spec cap Wk CW (2 * w.length + 1) τ (by simp [hτ, rst]) (by simp [hτ, rst]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by omega)
  have hov : overlay (frameP w ++ [false]) (σ.st Wk) = frame w := by
    rw [overlay, List.drop_eq_nil_of_le (by simp; omega), List.append_nil, frame_eq_frameP]
  apply WState.eq
  · funext j; simp only [hτ, rst, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext j; simp only [hτ, rst, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply, hov]
  · funext j; simp only [hτ, rst, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

/-! ## The loop -/

/-- **The record loop**: for every record of `I`, copy it to `Wk`, run `body`; then rewind `I`. -/
def recLoop (I Wk : Fin (ns + 1)) (CI CW : Fin nr) (body : WMX ns nr) : WMX ns nr :=
  .seq (.whs I (.seq (.wm (copyRec I Wk CI CW)) body)) (.wm (WM.rewind I CI))

/-- The state the body of record `i` starts from: `σ` with `Wk := frame w`, `I` and `CI` past the record. -/
def atRec (I Wk : Fin (ns + 1)) (CI : Fin nr) (σ : WState ns nr) (w : List Bool) (p : ℕ) : WState ns nr :=
  ((σ.sets Wk (frame w)).seth I p).setv CI p

/-- What the loop needs of a body run: the stream `I`, its head and the counters are untouched, `Wk` is back at `0`
and no longer than a record. -/
structure BodyFrame (I Wk : Fin (ns + 1)) (CI CW : Fin nr) (L : ℕ) (σ τ : WState ns nr) : Prop where
  st : τ.st I = σ.st I
  sh : τ.sh I = σ.sh I
  ci : τ.val CI = σ.val CI
  cw : τ.val CW = σ.val CW
  wh : τ.sh Wk = 0
  wl : (τ.st Wk).length ≤ 2 * L + 1

section Loop
variable (cap L : ℕ) {I Wk : Fin (ns + 1)} {CI CW : Fin nr} (body : WMX ns nr) (ws : List (List Bool))
  (Inv : ℕ → WState ns nr → Prop) (c : ℕ → ℕ)

/-- The per-record hypothesis of the loop: from any state satisfying `Inv i` (with the loop's own data in place), the
body run on record `i` reaches `Inv (i + 1)` in `c i` steps without disturbing the loop. -/
def BodySpec : Prop :=
  ∀ i (hi : i < ws.length) (σ : WState ns nr), Inv i σ → σ.st I = recStream ws → σ.sh I = i * (2 * L + 1) →
    σ.val CI = i * (2 * L + 1) → σ.val CW = 0 → σ.sh Wk = 0 → (σ.st Wk).length ≤ 2 * L + 1 →
    ∃ τ, WXExec cap body (atRec I Wk CI σ ws[i] ((i + 1) * (2 * L + 1))) τ (c i) ∧ Inv (i + 1) τ ∧
      BodyFrame I Wk CI CW L (atRec I Wk CI σ ws[i] ((i + 1) * (2 * L + 1))) τ

variable {cap L body ws Inv c}

theorem whsLoop_spec (hIW : I ≠ Wk) (hC : CI ≠ CW) (hw : ∀ w ∈ ws, w.length = L) (hL : 1 ≤ L)
    (hcap : ws.length * (2 * L + 1) + 2 * L + 2 ≤ cap) (hb : BodySpec cap L (I := I) (Wk := Wk) (CI := CI) (CW := CW)
      body ws Inv c) :
    ∀ (m i : ℕ) (σ : WState ns nr), i + m = ws.length → Inv i σ → σ.st I = recStream ws → σ.sh I = i * (2 * L + 1) →
      σ.val CI = i * (2 * L + 1) → σ.val CW = 0 → σ.sh Wk = 0 → (σ.st Wk).length ≤ 2 * L + 1 →
      ∃ τ, WXExec cap (.whs I (.seq (.wm (copyRec I Wk CI CW)) body)) σ τ
          ((∑ j ∈ Finset.range m, (c (i + j) + (40 * L + 25))) + 1) ∧ Inv ws.length τ ∧
        τ.st I = recStream ws ∧ τ.sh I = ws.length * (2 * L + 1) ∧ τ.val CI = ws.length * (2 * L + 1) ∧
        τ.val CW = 0
  | 0, i, σ, hm, hI, hst, hsh, hci, hcw, _, _ => by
    have hiN : i = ws.length := by omega
    subst hiN
    have hbit : wbit σ I = false := by unfold wbit; rw [hst, hsh]; exact recStream_bit_end L ws hw
    exact ⟨σ, WXExec.whsF hbit, hI, hst, hsh, hci, hcw⟩
  | m + 1, i, σ, hm, hI, hst, hsh, hci, hcw, hwh, hwl => by
    have hi : i < ws.length := by omega
    have hbit : wbit σ I = true := by unfold wbit; rw [hst, hsh]; exact recStream_bit_rec L ws hw hL i hi
    obtain ⟨e, hl⟩ := recStream_split L ws hw i hi
    have hwi : ws[i].length = L := hw _ (List.getElem_mem hi)
    have hcopy := copyRec_spec cap hIW hC σ _ ws[i] _ (by rw [hst, e]) (by rw [hsh, hl]) (by rw [hci, hl]) hwh hcw
      (by rw [hwi]; exact hwl) (by rw [hl, hwi]; nlinarith)
    have hp : ((ws.take i).flatMap frame).length + 2 * ws[i].length + 1 = (i + 1) * (2 * L + 1) := by
      rw [hl, hwi]; ring
    rw [hp] at hcopy
    obtain ⟨τ, hτ, hIτ, hfr⟩ := hb i hi σ hI hst hsh hci hcw hwh hwl
    have hcw' : τ.val CW = 0 := by rw [hfr.cw]; simp [atRec, Ne.symm hC, hcw]
    obtain ⟨ρ, hρ, hIρ, h1, h2, h3, h4⟩ := whsLoop_spec hIW hC hw hL hcap hb m (i + 1) τ (by omega) hIτ
      (by rw [hfr.st]; simp [atRec, Function.update_of_ne hIW, hst]) (by rw [hfr.sh]; simp [atRec])
      (by rw [hfr.ci]; simp [atRec]) hcw' hfr.wh hfr.wl
    refine ⟨ρ, WXExec.mono (WXExec.whsT hbit (WXExec.seq (WXExec.wm hcopy) hτ) hρ) ?_, hIρ, h1, h2, h3, h4⟩
    rw [Finset.sum_range_succ']
    have e2 : ∑ j ∈ Finset.range m, (c (i + (j + 1)) + (40 * L + 25)) =
        ∑ j ∈ Finset.range m, (c (i + 1 + j) + (40 * L + 25)) :=
      Finset.sum_congr rfl (fun j _ => by rw [show i + (j + 1) = i + 1 + j by omega])
    simp only [Nat.add_zero]
    rw [e2]
    rw [hwi] at hcopy ⊢
    omega

/-- **The record loop.** From the record stream of `ws` (fixed width `L ≥ 1`) on `I` (head `0`), the counters
`CI = CW = 0`, a work stream `Wk` (head `0`, at most `2L + 1` cells) and `Inv 0`, with the per-record hypothesis
`BodySpec`: the loop reaches a state `τ` with `Inv N τ` (N records), and the final state is `τ` with `I`'s head and
`CI` back at `0`; cost `Σ_{i < N} (c i + 50L + 30) + 3`. -/
theorem recLoop_spec (hIW : I ≠ Wk) (hC : CI ≠ CW) (hw : ∀ w ∈ ws, w.length = L) (hL : 1 ≤ L)
    (hcap : ws.length * (2 * L + 1) + 2 * L + 2 ≤ cap)
    (hb : BodySpec cap L (I := I) (Wk := Wk) (CI := CI) (CW := CW) body ws Inv c) (σ : WState ns nr) (h0 : Inv 0 σ)
    (hst : σ.st I = recStream ws) (hsh : σ.sh I = 0) (hci : σ.val CI = 0) (hcw : σ.val CW = 0) (hwh : σ.sh Wk = 0)
    (hwl : (σ.st Wk).length ≤ 2 * L + 1) :
    ∃ τ, Inv ws.length τ ∧ τ.st I = recStream ws ∧ τ.val CW = 0 ∧
      WXExec cap (recLoop I Wk CI CW body) σ ((τ.setv CI 0).seth I 0)
        ((∑ i ∈ Finset.range ws.length, (c i + (50 * L + 30))) + 3) := by
  obtain ⟨τ, hτ, hI, h1, h2, h3, h4⟩ := whsLoop_spec hIW hC hw hL hcap hb ws.length 0 σ (by omega) h0 hst
    (by simp [hsh]) (by simp [hci]) hcw hwh hwl
  have hr := wrewind_spec cap I CI (ws.length * (2 * L + 1)) τ h3 (by omega)
  rw [h2, Nat.sub_self] at hr
  refine ⟨τ, hI, h1, h4, WXExec.mono (WXExec.seq hτ (WXExec.wm hr)) ?_⟩
  simp only [Nat.zero_add]
  have e : ∑ i ∈ Finset.range ws.length, (c i + (50 * L + 30)) =
      ∑ i ∈ Finset.range ws.length, (c i + (40 * L + 25)) + ws.length * (10 * L + 5) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  rw [e]
  nlinarith

end Loop

/-! ## Output streams: appending records -/

def OutOn (σ : WState ns nr) (O : Fin (ns + 1)) (CO : Fin nr) (out L0 : List Bool) : Prop :=
  σ.st O = overlay out L0 ∧ σ.sh O = out.length ∧ σ.val CO = out.length

/-- A fresh output stream (`out = []`): any contents, head `0`, counter `0`. -/
theorem outOn_start (σ : WState ns nr) (O : Fin (ns + 1)) (CO : Fin nr) (hO : σ.sh O = 0) (hC : σ.val CO = 0) :
    OutOn σ O CO [] (σ.st O) := ⟨by simp [overlay], by simpa using hO, by simpa using hC⟩

/-- Append the framed word on `Src` (head `0`) to the output stream `O`; `Src`'s head comes back to `0`. -/
def appendRec (Src O : Fin (ns + 1)) (CS CO : Fin nr) : WM ns nr :=
  .seq (.whs Src (copyPair Src O CS CO)) (.seq (emitB O CO false) (WM.rewind Src CS))

/-- **Append one record**: `out := out ++ frame w`; everything else unchanged. -/
theorem appendRec_spec (cap : ℕ) {Src O : Fin (ns + 1)} {CS CO : Fin nr} (hSO : Src ≠ O) (hC : CS ≠ CO)
    (σ : WState ns nr) (w post out L0 : List Bool) (hS : σ.st Src = frameP w ++ false :: post) (hSh : σ.sh Src = 0)
    (hCS : σ.val CS = 0) (hO : OutOn σ O CO out L0) (hcap : out.length + 2 * w.length + 2 ≤ cap) :
    WExec cap (appendRec Src O CS CO) σ
      (((σ.sets O (overlay (out ++ frame w) L0)).seth O (out ++ frame w).length).setv CO (out ++ frame w).length)
      (40 * w.length + 11) := by
  have e0 : rst σ Src O CS CO L0 ([] : List Bool).length out = σ := by
    apply WState.eq
    · funext j; simp only [rst, Function.update_apply, List.length_nil]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all [hO.2.1]
    · funext j; simp only [rst, Function.update_apply]
      split_ifs with h1
      · subst h1; rw [hO.1]
      · rfl
    · funext j; simp only [rst, Function.update_apply, List.length_nil]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all [hO.2.2]
    · rfl
  have h1 := copyLoop_rst cap σ L0 hSO hC w [] out post (by simpa using hS) (by simp; omega) (by omega)
  rw [e0] at h1
  simp only [List.length_nil, Nat.zero_add] at h1
  have h2 := emitB_rst cap σ L0 hSO hC (2 * w.length) (out ++ frameP w) false (by simp; omega)
  set τ := rst σ Src O CS CO L0 (2 * w.length) (out ++ frameP w ++ [false]) with hτ
  have h3 := wrewind_spec cap Src CS (2 * w.length) τ (by simp [hτ, rst, hC]) (by simp [hτ, rst, hC]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  have ef : out ++ frameP w ++ [false] = out ++ frame w := by rw [frame_eq_frameP, List.append_assoc]
  apply WState.eq
  · funext j; simp only [hτ, rst, ef, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext j; simp only [hτ, rst, ef, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
  · funext j; simp only [hτ, rst, ef, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

theorem appendRec_out (σ : WState ns nr) (O : Fin (ns + 1)) (CO : Fin nr) (out L0 w : List Bool) :
    OutOn (((σ.sets O (overlay (out ++ frame w) L0)).seth O (out ++ frame w).length).setv CO
      (out ++ frame w).length) O CO (out ++ frame w) L0 := ⟨by simp, by simp, by simp⟩

/-- Close an output stream: write its final `false` and return its head to `0`. -/
def closeOut (O : Fin (ns + 1)) (CO : Fin nr) : WM ns nr := .seq (.wr O false) (WM.rewind O CO)

theorem closeOut_spec (cap : ℕ) {O : Fin (ns + 1)} {CO : Fin nr} (σ : WState ns nr) (out L0 : List Bool)
    (hO : OutOn σ O CO out L0) (hcap : out.length ≤ cap) :
    WExec cap (closeOut O CO) σ (((σ.sets O (overlay (out ++ [false]) L0)).seth O 0).setv CO 0)
      (5 * out.length + 3) := by
  have h1 := WExec.wr (cap := cap) O false σ
  rw [hO.1, hO.2.1, StablePartition.Workspace.overlay_write] at h1
  have h2 := wrewind_spec cap O CO out.length (σ.sets O (overlay (out ++ [false]) L0)) (by simp [hO.2.2])
    (by simp [hO.2.2]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  have hsh := hO.2.1
  apply WState.eq
  · funext j; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl
  · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
  · rfl

/-- A closed output stream over a short old content is exactly the record stream. -/
theorem overlay_short (out L0 : List Bool) (h : L0.length ≤ out.length) : overlay out L0 = out := by
  rw [overlay, List.drop_eq_nil_of_le h, List.append_nil]

/-- `WMX` forms. -/
def appendRecX (Src O : Fin (ns + 1)) (CS CO : Fin nr) : WMX ns nr := .wm (appendRec Src O CS CO)
def closeOutX (O : Fin (ns + 1)) (CO : Fin nr) : WMX ns nr := .wm (closeOut O CO)

/-! Programs are opaque to consumers: use the spec theorems. -/
attribute [irreducible] copyRec recLoop appendRec closeOut

end NearCubicGates.Close.WordPrograms

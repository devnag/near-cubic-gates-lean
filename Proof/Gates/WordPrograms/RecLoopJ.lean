import Proof.Gates.WordPrograms.RecLoop

/-! # The record loop over a stream with a tail (`recLoopJ`)

A reused stream written from its start (`OutOn`, `overlay`) holds the new record stream followed by whatever was left
of its old contents. **`recLoopJ_spec`** is `recLoop_spec` for `I = recStream ws ++ junk`: the loop reads only the
records and the end marker, so the tail is never touched. Same program (`recLoop`), same costs. -/

set_option autoImplicit false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (copyPair emitB rst copyLoop_rst emitB_rst fwdA_rst rd_app0)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

theorem readTapeBit_app_lt (l junk : List Bool) (k : ℕ) (hk : k < l.length) :
    readTapeBit (l ++ junk) k = readTapeBit l k := by
  unfold readTapeBit
  rw [List.getD_append _ _ _ _ hk]

section LoopJ
variable (cap L : ℕ) {I Wk : Fin (ns + 1)} {CI CW : Fin nr} (body : WMX ns nr) (ws : List (List Bool))
  (Inv : ℕ → WState ns nr → Prop) (c : ℕ → ℕ) (junk : List Bool)

/-- The per-record hypothesis of the loop: from any state satisfying `Inv i` (with the loop's own data in place), the
body run on record `i` reaches `Inv (i + 1)` in `c i` steps without disturbing the loop. -/
def BodySpecJ : Prop :=
  ∀ i (hi : i < ws.length) (σ : WState ns nr), Inv i σ → σ.st I = recStream ws ++ junk → σ.sh I = i * (2 * L + 1) →
    σ.val CI = i * (2 * L + 1) → σ.val CW = 0 → σ.sh Wk = 0 → (σ.st Wk).length ≤ 2 * L + 1 →
    ∃ τ, WXExec cap body (atRec I Wk CI σ ws[i] ((i + 1) * (2 * L + 1))) τ (c i) ∧ Inv (i + 1) τ ∧
      BodyFrame I Wk CI CW L (atRec I Wk CI σ ws[i] ((i + 1) * (2 * L + 1))) τ

variable {cap L body ws Inv c junk}

theorem whsLoopJ_spec (hIW : I ≠ Wk) (hC : CI ≠ CW) (hw : ∀ w ∈ ws, w.length = L) (hL : 1 ≤ L)
    (hcap : ws.length * (2 * L + 1) + 2 * L + 2 ≤ cap) (hb : BodySpecJ cap L (I := I) (Wk := Wk) (CI := CI) (CW := CW)
      body ws Inv c junk) :
    ∀ (m i : ℕ) (σ : WState ns nr), i + m = ws.length → Inv i σ → σ.st I = recStream ws ++ junk → σ.sh I = i * (2 * L + 1) →
      σ.val CI = i * (2 * L + 1) → σ.val CW = 0 → σ.sh Wk = 0 → (σ.st Wk).length ≤ 2 * L + 1 →
      ∃ τ, WXExec cap (.whs I (.seq (.wm (copyRec I Wk CI CW)) body)) σ τ
          ((∑ j ∈ Finset.range m, (c (i + j) + (40 * L + 25))) + 1) ∧ Inv ws.length τ ∧
        τ.st I = recStream ws ++ junk ∧ τ.sh I = ws.length * (2 * L + 1) ∧ τ.val CI = ws.length * (2 * L + 1) ∧
        τ.val CW = 0
  | 0, i, σ, hm, hI, hst, hsh, hci, hcw, _, _ => by
    have hiN : i = ws.length := by omega
    subst hiN
    have hbit : wbit σ I = false := by unfold wbit; rw [hst, hsh]; rw [readTapeBit_app_lt _ _ _ (by rw [recStream_length L ws hw]; omega)]; exact recStream_bit_end L ws hw
    exact ⟨σ, WXExec.whsF hbit, hI, hst, hsh, hci, hcw⟩
  | m + 1, i, σ, hm, hI, hst, hsh, hci, hcw, hwh, hwl => by
    have hi : i < ws.length := by omega
    have hbit : wbit σ I = true := by unfold wbit; rw [hst, hsh]; rw [readTapeBit_app_lt _ _ _ (by rw [recStream_length L ws hw]; nlinarith)]; exact recStream_bit_rec L ws hw hL i hi
    obtain ⟨e, hl⟩ := recStream_split L ws hw i hi
    have hwi : ws[i].length = L := hw _ (List.getElem_mem hi)
    have hcopy := copyRec_spec cap hIW hC σ ((ws.take i).flatMap frame) ws[i]
      ((ws.drop (i + 1)).flatMap frame ++ false :: junk) (by rw [hst, e]; simp [List.append_assoc])
      (by rw [hsh, hl]) (by rw [hci, hl]) hwh hcw
      (by rw [hwi]; exact hwl) (by rw [hl, hwi]; nlinarith)
    have hp : ((ws.take i).flatMap frame).length + 2 * ws[i].length + 1 = (i + 1) * (2 * L + 1) := by
      rw [hl, hwi]; ring
    rw [hp] at hcopy
    obtain ⟨τ, hτ, hIτ, hfr⟩ := hb i hi σ hI hst hsh hci hcw hwh hwl
    have hcw' : τ.val CW = 0 := by rw [hfr.cw]; simp [atRec, Ne.symm hC, hcw]
    obtain ⟨ρ, hρ, hIρ, h1, h2, h3, h4⟩ := whsLoopJ_spec hIW hC hw hL hcap hb m (i + 1) τ (by omega) hIτ
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
theorem recLoopJ_spec (hIW : I ≠ Wk) (hC : CI ≠ CW) (hw : ∀ w ∈ ws, w.length = L) (hL : 1 ≤ L)
    (hcap : ws.length * (2 * L + 1) + 2 * L + 2 ≤ cap)
    (hb : BodySpecJ cap L (I := I) (Wk := Wk) (CI := CI) (CW := CW) body ws Inv c junk) (σ : WState ns nr) (h0 : Inv 0 σ)
    (hst : σ.st I = recStream ws ++ junk) (hsh : σ.sh I = 0) (hci : σ.val CI = 0) (hcw : σ.val CW = 0) (hwh : σ.sh Wk = 0)
    (hwl : (σ.st Wk).length ≤ 2 * L + 1) :
    ∃ τ, Inv ws.length τ ∧ τ.st I = recStream ws ++ junk ∧ τ.val CW = 0 ∧
      WXExec cap (recLoop I Wk CI CW body) σ ((τ.setv CI 0).seth I 0)
        ((∑ i ∈ Finset.range ws.length, (c i + (50 * L + 30))) + 3) := by
  obtain ⟨τ, hτ, hI, h1, h2, h3, h4⟩ := whsLoopJ_spec hIW hC hw hL hcap hb ws.length 0 σ (by omega) h0 hst
    (by simp [hsh]) (by simp [hci]) hcw hwh hwl
  have hr := wrewind_spec cap I CI (ws.length * (2 * L + 1)) τ h3 (by omega)
  rw [h2, Nat.sub_self] at hr
  unfold recLoop
  refine ⟨τ, hI, h1, h4, WXExec.mono (WXExec.seq hτ (WXExec.wm hr)) ?_⟩
  simp only [Nat.zero_add]
  have e : ∑ i ∈ Finset.range ws.length, (c i + (50 * L + 30)) =
      ∑ i ∈ Finset.range ws.length, (c i + (40 * L + 25)) + ws.length * (10 * L + 5) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  rw [e]
  nlinarith

end LoopJ

end NearCubicGates.Close.WordPrograms

import Proof.Gates.CounterMachine.ReqCond
import Proof.Gates.Codec.Emit
import Proof.Gates.Codec.Copy

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (writeNatM writeNatM_spec appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord)

variable {ns nr : ℕ} (cap : ℕ)

theorem appendO_nil' (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (ho : σ.sh o = (σ.st o).length) :
    appendO σ o OP [] = σ := appendO_nil σ o OP ho

theorem appendO_sh_eq (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (u : List Bool)
    (ho : σ.sh o = (σ.st o).length) : (appendO σ o OP u).sh o = ((appendO σ o OP u).st o).length := by
  simp [appendO, ho]

/-! ## An indexed loop -/

/-- **The indexed loop**: `body` handles element `t` with the index register `X = x0 + t` (and increments it), reading
`g t` on `s` and appending `marks (u t)` to `o`; the loop runs `m` times (`k` counted down). -/
theorem idxLoop_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (k X OP : Fin nr) (hkX : k ≠ X) (hkO : k ≠ OP)
    (hXO : X ≠ OP) (body : WM ns nr) (g u : ℕ → List Bool) (cost : ℕ → ℕ) (ok : WState ns nr → Prop) (x0 N V : ℕ)
    (hok_h : ∀ σ x, ok σ → ok (σ.seth s x)) (hok_v : ∀ σ x, ok σ → ok (σ.setv k x))
    (hok_x : ∀ σ x, ok σ → ok (σ.setv X x)) (hok_o : ∀ σ w, ok σ → ok (appendO σ o OP w))
    (hbody : ∀ t, t < N → ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ → σ.st s = pre ++ g t ++ rest →
      σ.sh s = pre.length → σ.sh o = (σ.st o).length → σ.val X = x0 + t → σ.val OP + (marks (u t)).length ≤ V →
      WExec cap body σ (((appendO σ o OP (marks (u t))).seth s (pre.length + (g t).length)).setv X (x0 + t + 1))
        (cost t)) :
    ∀ (m j : ℕ) (pre rest : List Bool) (σ : WState ns nr), j + m ≤ N → ok σ →
      σ.st s = pre ++ ((List.range m).map fun i => g (j + i)).flatten ++ rest →
      σ.sh s = pre.length → σ.sh o = (σ.st o).length → σ.val k = m → m ≤ cap → σ.val X = x0 + j →
      σ.val OP + (marks ((List.range m).map fun i => u (j + i)).flatten).length ≤ V →
      WExec cap (listLoop k body) σ
        ((((appendO σ o OP (marks ((List.range m).map fun i => u (j + i)).flatten)).setv k 0).seth s
          (pre.length + ((List.range m).map fun i => g (j + i)).flatten.length)).setv X (x0 + j + m))
        (((List.range m).map fun i => cost (j + i) + 4).sum + 1)
  | 0, j, pre, rest, σ, _, _, _, hsh, ho, hk, _, hX, _ => by
    have e : (((appendO σ o OP (marks ((List.range 0).map fun i => u (j + i)).flatten)).setv k 0).seth s
        (pre.length + ((List.range 0).map fun i => g (j + i)).flatten.length)).setv X (x0 + j + 0) = σ := by
      simp only [List.range_zero, List.map_nil, List.flatten_nil, List.length_nil, Nat.add_zero]
      rw [show marks ([] : List Bool) = [] from rfl, appendO_nil σ o OP ho]
      apply WState.eq
      · funext i; by_cases hi : i = s
        · subst hi; simp [hsh]
        · simp [Function.update_of_ne hi]
      · simp
      · funext r; by_cases h1 : r = X
        · subst h1; simp [hX]
        · by_cases h2 : r = k
          · subst h2; simp [Function.update_of_ne h1, hk]
          · simp [Function.update_of_ne h1, Function.update_of_ne h2]
      · simp
    rw [e]
    exact WExec.mono (WExec.whrF (by simpa using hk)) (by simp)
  | m + 1, j, pre, rest, σ, hjm, hσ, hst, hsh, ho, hk, hcap, hX, hV => by
    have h1 := WExec.dec (cap := cap) k σ (by rw [hk]; omega)
    set σ1 := σ.setv k (σ.val k - 1) with hσ1
    have hok1 : ok σ1 := hok_v σ _ hσ
    have hsplit : ((List.range (m + 1)).map fun i => g (j + i)).flatten =
        g j ++ ((List.range m).map fun i => g (j + 1 + i)).flatten := by
      rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
      congr 2; apply List.map_congr_left; intro i _
      simp only [Function.comp_apply, Nat.succ_eq_add_one]; rw [show j + (i + 1) = j + 1 + i by omega]
    have hsplitU : ((List.range (m + 1)).map fun i => u (j + i)).flatten =
        u j ++ ((List.range m).map fun i => u (j + 1 + i)).flatten := by
      rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
      congr 2; apply List.map_congr_left; intro i _
      simp only [Function.comp_apply, Nat.succ_eq_add_one]; rw [show j + (i + 1) = j + 1 + i by omega]
    have hst1 : σ1.st s = pre ++ g j ++ (((List.range m).map fun i => g (j + 1 + i)).flatten ++ rest) := by
      simp only [hσ1, WState.setv_st]; rw [hst, hsplit]; simp [List.append_assoc]
    have hV' : σ.val OP + (marks (u j)).length + (marks ((List.range m).map fun i => u (j + 1 + i)).flatten).length
        ≤ V := by rw [hsplitU, marksApp, List.length_append] at hV; omega
    have e1 : σ1.val OP = σ.val OP := by simp [hσ1, Function.update_of_ne hkO.symm]
    have h2 := hbody j (by omega) pre _ σ1 hok1 hst1 (by simp [hσ1, hsh]) (by simp [hσ1, ho])
      (by simp [hσ1, Function.update_of_ne hkX.symm, hX])
      (by rw [e1]; exact le_trans (Nat.le_add_right _ _) hV')
    set σ2 := ((appendO σ1 o OP (marks (u j))).seth s (pre.length + (g j).length)).setv X (x0 + j + 1) with hσ2
    have hok2 : ok σ2 := hok_x _ _ (hok_h _ _ (hok_o _ _ hok1))
    have hst2 : σ2.st s = (pre ++ g j) ++ ((List.range m).map fun i => g (j + 1 + i)).flatten ++ rest := by
      simp only [hσ2, WState.setv_st, WState.seth_st]
      simp [appendO, Function.update_of_ne hso, hσ1, hst, hsplit, List.append_assoc]
    have h3 := idxLoop_spec s o hso k X OP hkX hkO hXO body g u cost ok x0 N V hok_h hok_v hok_x hok_o hbody m (j + 1)
      (pre ++ g j) rest σ2 (by omega) hok2 hst2 (by simp [hσ2])
      (by simp [hσ2, appendO, ho, hσ1, Function.update_of_ne hso.symm])
      (by simp [hσ2, hσ1, appendO, Function.update_of_ne hkX, Function.update_of_ne hkO, hk])
      (by omega) (by simp [hσ2]; omega)
      (by
        have e2 : σ2.val OP = σ.val OP + (marks (u j)).length := by
          simp [hσ2, hσ1, appendO, Function.update_of_ne hXO.symm, Function.update_of_ne hkO.symm]
        rw [e2]; omega)
    have hne : σ.val k ≠ 0 := by rw [hk]; simp
    refine WExec.cast cap (WExec.whrT hne (WExec.seq h1 h2) h3) ?_ (by
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      have : ((List.range m).map ((fun i => cost (j + i) + 4) ∘ Nat.succ)).sum =
          ((List.range m).map fun i => cost (j + 1 + i) + 4).sum := by
        congr 1; apply List.map_congr_left; intro i _
        simp only [Function.comp_apply, Nat.succ_eq_add_one]; rw [show j + (i + 1) = j + 1 + i by omega]
      rw [this]; simp; omega)
    apply WState.eq
    · funext i; by_cases hi : i = s
      · subst hi; simp [hσ2, appendO, Function.update_of_ne hso, hsplit]; ring
      · by_cases hio : i = o
        · subst hio; simp [hσ2, hσ1, appendO, Function.update_of_ne hi, ho, hsplitU, marksApp]; ring
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hi, Function.update_of_ne hio]
    · funext i; by_cases hio : i = o
      · subst hio; simp [hσ2, hσ1, appendO, Function.update_of_ne hso.symm, hsplitU, marksApp]
      · by_cases hi : i = s
        · subst hi; simp [hσ2, hσ1, appendO, Function.update_of_ne hio]
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hio, Function.update_of_ne hi]
    · funext r; by_cases c1 : r = X
      · subst c1; simp [hσ2, hσ1, appendO, Function.update_of_ne hXO, Function.update_of_ne hkX.symm]; ring
      · by_cases c2 : r = k
        · subst c2; simp [hσ2, hσ1, appendO, Function.update_of_ne c1, Function.update_of_ne hkO]
        · by_cases c3 : r = OP
          · subst c3; simp [hσ2, hσ1, appendO, Function.update_of_ne c1, Function.update_of_ne c2, hsplitU,
              marksApp]; ring
          · simp [hσ2, hσ1, appendO, Function.update_of_ne c1, Function.update_of_ne c2, Function.update_of_ne c3]
    · simp [hσ2, hσ1, appendO]

/-! ## A constant-output loop -/

/-- `m` times `body`, each appending `marks w` (no input read). -/
theorem constLoop_spec (o : Fin (ns + 1)) (k OP : Fin nr) (hkO : k ≠ OP) (body : WM ns nr) (w : List Bool) (c V : ℕ)
    (hbody : ∀ σ : WState ns nr, σ.sh o = (σ.st o).length → σ.val OP + (marks w).length ≤ V →
      WExec cap body σ (appendO σ o OP (marks w)) c) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.sh o = (σ.st o).length → σ.val k = m → m ≤ cap →
      σ.val OP + m * (marks w).length ≤ V →
      WExec cap (listLoop k body) σ ((appendO σ o OP (marks ((List.replicate m w).flatten))).setv k 0)
        (m * (c + 4) + 1)
  | 0, σ, ho, hk, _, _ => by
    have e : (appendO σ o OP (marks ((List.replicate 0 w).flatten))).setv k 0 = σ := by
      simp only [List.replicate_zero, List.flatten_nil]
      rw [show marks ([] : List Bool) = [] from rfl, appendO_nil σ o OP ho, ← hk, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.whrF (by simpa using hk)) (by simp)
  | m + 1, σ, ho, hk, hcap, hV => by
    have h1 := WExec.dec (cap := cap) k σ (by rw [hk]; omega)
    set σ1 := σ.setv k (σ.val k - 1) with hσ1
    have e1 : σ1.val OP = σ.val OP := by simp [hσ1, Function.update_of_ne hkO.symm]
    have h2 := hbody σ1 (by simp [hσ1, ho]) (by rw [e1]; nlinarith)
    have h3 := constLoop_spec o k OP hkO body w c V hbody m (appendO σ1 o OP (marks w))
      (by simp [appendO, hσ1, ho]) (by simp [appendO, hσ1, Function.update_of_ne hkO, hk]) (by omega)
      (by simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_self]; rw [e1]
          nlinarith)
    have hne : σ.val k ≠ 0 := by rw [hk]; simp
    refine WExec.cast cap (WExec.whrT hne (WExec.seq h1 h2) h3) ?_ (by ring_nf; omega)
    rw [appendO_append]
    apply WState.eq
    · funext i; by_cases hi : i = o
      · subst hi; simp [appendO, hσ1, List.replicate_succ, marksApp]
      · simp [appendO, hσ1, Function.update_of_ne hi]
    · funext i; by_cases hi : i = o
      · subst hi; simp [appendO, hσ1, List.replicate_succ, marksApp]
      · simp [appendO, hσ1, Function.update_of_ne hi]
    · funext r; by_cases c1 : r = k
      · subst c1; simp [appendO, hσ1, Function.update_of_ne hkO]
      · by_cases c2 : r = OP
        · subst c2; simp [appendO, hσ1, Function.update_of_ne c1, List.replicate_succ, marksApp]
        · simp [appendO, hσ1, Function.update_of_ne c1, Function.update_of_ne c2]
    · simp [appendO, hσ1]

end NearCubicGates.Close.CounterMachine

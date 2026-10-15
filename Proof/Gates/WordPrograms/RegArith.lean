import Proof.Gates.WordPrograms.RecLoopJ
import Proof.Gates.WordPrograms.Hoare
import Proof.Gates.WordPrograms.OutX
import Proof.Gates.WordPrograms.CopyN

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- `B := B + A`, `A` kept (`T` is `0` before and after). -/
def addR (A B T : Fin nr) : WMX ns nr :=
  .seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup A B T)) (.wm (WM.move T A))

theorem addR_spec (cap : ℕ) {A B T : Fin nr} (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T) (σ : WState ns nr)
    (hT : σ.val T = 0) (hcap : σ.val B + σ.val A ≤ cap) :
    WXExec cap (addR A B T) σ (σ.setv B (σ.val B + σ.val A)) (18 * σ.val A + 3) := by
  have h1 := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup_spec (cap := cap) A B T hAB hAT hBT (σ.val A) σ rfl
    (by omega) (by omega) (by rw [hT]; omega)
  have h2 := wmove_spec (cap := cap) T A (Ne.symm hAT) (σ.val A)
    (((σ.setv A 0).setv B (σ.val B + σ.val A)).setv T (σ.val T + σ.val A)) (by simp [hT])
    (by simp [hT]; omega) (by simp [Function.update_apply, hAT, hAB, hT]; omega)
  refine (WXExec.seq (WXExec.wm h1) (WXExec.wm h2)).cast cap ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [WState.setv_val, Function.update_apply]
  by_cases r1 : r = A
  · rw [r1]; simp [hAB, hAT, hT, Ne.symm hAT]
  · by_cases r2 : r = T
    · rw [r2]; simp [Ne.symm hAT, Ne.symm hBT, hT]
    · simp [r1, r2]

def mulR (A A2 B C T : Fin nr) : WMX ns nr := repK A A2 (addR B C T)

theorem mulR_spec (cap : ℕ) {A A2 B C T : Fin nr} (hR : [A, A2, B, C, T].Nodup) (σ : WState ns nr)
    (hA2 : σ.val A2 = 0) (hT : σ.val T = 0) (hcap : σ.val C + σ.val A * σ.val B ≤ cap) (hcapA : 2 * σ.val A ≤ cap) :
    WXExec cap (mulR A A2 B C T) σ (σ.setv C (σ.val C + σ.val A * σ.val B))
      (σ.val A * (18 * σ.val B + 3 + 8) + 7 * σ.val A + 3) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR
  have hst := Runs.repE (cap := cap) (K := A) (K2 := A2) (body := addR B C T) h1 (18 * σ.val B + 3) (σ.val A)
    (fun k => σ.setv C (σ.val C + k * σ.val B)) (by omega)
    (fun k => by simp [Function.update_apply, h3])
    (fun k => by simp [Function.update_apply, h6])
    (fun k hk v1 v2 => by
      have hh := addR_spec cap (A := B) (B := C) (T := T) h8 h9 h10
        (((σ.setv C (σ.val C + k * σ.val B)).setv A v1).setv A2 v2)
        (by simp [Function.update_apply, Ne.symm h10, Ne.symm h4, Ne.symm h7, hT])
        (by
          simp [Function.update_apply, Ne.symm h3, Ne.symm h6, h8, Ne.symm h2, Ne.symm h5]
          have : k * σ.val B + σ.val B ≤ σ.val A * σ.val B := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
          omega)
      have eb : (((σ.setv C (σ.val C + k * σ.val B)).setv A v1).setv A2 v2).val B = σ.val B := by
        simp [Function.update_apply, Ne.symm h2, Ne.symm h5, h8]
      rw [eb] at hh
      refine hh.cast cap ?_ le_rfl
      apply WState.eq <;> try rfl
      funext r
      simp only [WState.setv_val, Function.update_apply]
      by_cases r1 : r = C
      · rw [r1]; simp [Ne.symm h3, Ne.symm h6, h8]; ring
      · simp [r1])
    (by simp [Function.update_apply, h3]) (by simp [Function.update_apply, h6, hA2])
  have e0 : σ.setv C (σ.val C + 0 * σ.val B) = σ := by simp [BinW.setv_same]
  rw [e0] at hst
  exact hst

theorem flatMap_take_succ' {α β : Type} (l : List α) (f : α → List β) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).flatMap f = (l.take j).flatMap f ++ f l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.flatMap_append]; simp

/-- Append every record of `I` to `O`. -/
def copyAll (I Wk O : Fin (ns + 1)) (CI CW CS CO : Fin nr) : WMX ns nr := recLoop I Wk CI CW (appendRecX Wk O CS CO)

end NearCubicGates.Close.WordPrograms

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

theorem copyAll_spec (cap : ℕ) {I Wk O : Fin (ns + 1)} {CI CW CS CO : Fin nr} (hS : [I, Wk, O].Nodup)
    (hR : [CI, CW, CS, CO].Nodup) (L : ℕ) (hL : 1 ≤ L) (xs : List ℕ) (σ : WState ns nr) (junk out L0 : List Bool)
    (hI : σ.st I = recStream (xs.map (binary L)) ++ junk) (hIh : σ.sh I = 0) (hCI : σ.val CI = 0)
    (hCW : σ.val CW = 0) (hCS : σ.val CS = 0) (hWh : σ.sh Wk = 0) (hWl : (σ.st Wk).length ≤ 2 * L + 1)
    (hO : OutOn σ O CO out L0) (hcap : xs.length * (2 * L + 1) + 2 * L + 2 ≤ cap)
    (hcapO : out.length + xs.length * (2 * L + 1) + 1 ≤ cap) :
    Runs cap (copyAll I Wk O CI CW CS CO) σ (xs.length * (40 * L + 11 + (50 * L + 30)) + 3) (fun τ =>
      OutOn τ O CO (out ++ xs.flatMap fun x => frame (binary L x)) L0 ∧ τ.sh Wk = 0 ∧
        (τ.st Wk).length ≤ 2 * L + 1 ∧ SameExcept σ τ [Wk, O] [CO]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hS hR
  obtain ⟨⟨hIW, hIO⟩, hWO⟩ := hS
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := hR
  let Inv : ℕ → WState ns nr → Prop := fun i ρ =>
    OutOn ρ O CO (out ++ (xs.take i).flatMap fun x => frame (binary L x)) L0 ∧ ρ.sh Wk = 0 ∧
      (ρ.st Wk).length ≤ 2 * L + 1 ∧ SameExcept σ ρ [I, Wk, O] [CI, CW, CO]
  have hwl : ∀ w ∈ xs.map (binary L), w.length = L := by
    intro w hw; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw; simp
  have hb : BodySpecJ cap L (I := I) (Wk := Wk) (CI := CI) (CW := CW) (appendRecX Wk O CS CO) (xs.map (binary L))
      Inv (fun _ => 40 * L + 11) junk := by
    intro i hi ρ hInv _ _ _ _ hwh _
    simp only [List.length_map] at hi
    obtain ⟨a1, -, -, a4⟩ := hInv
    rw [List.getElem_map]
    set τ1 := atRec I Wk CI ρ (binary L xs[i]) ((i + 1) * (2 * L + 1)) with hτ1
    have hO1 : OutOn τ1 O CO (out ++ (xs.take i).flatMap fun x => frame (binary L x)) L0 :=
      ⟨by simp [hτ1, atRec, Function.update_of_ne (Ne.symm hWO), a1.1],
        by simp [hτ1, atRec, Function.update_of_ne (Ne.symm hIO), a1.2.1],
        by simp [hτ1, atRec, Function.update_of_ne (Ne.symm h3), a1.2.2]⟩
    have hlen : ((xs.take i).flatMap fun x => frame (binary L x)).length = i * (2 * L + 1) := by
      have := segRecs_length L xs 0 i (by omega)
      simpa [segRecs] using this
    have ha := appendRec_spec cap hWO h6 τ1 (binary L xs[i]) [] _ L0 (by simp [hτ1, atRec, BinW.frame_frameP])
      (by simp [hτ1, atRec, Function.update_of_ne (Ne.symm hIW), hwh])
      (by simp [hτ1, atRec, Function.update_of_ne (Ne.symm h2), a4.val (show CS ∉ [CI, CW, CO] by simp [Ne.symm h2, Ne.symm h4, h6]), hCS])
      hO1 (by rw [List.length_append, hlen, binary_length]
              have : (i + 1) * (2 * L + 1) ≤ xs.length * (2 * L + 1) := Nat.mul_le_mul_right _ (by omega)
              nlinarith)
    rw [binary_length] at ha
    refine ⟨_, WXExec.wm ha, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    · simp [Function.update_of_ne (Ne.symm hWO), flatMap_take_succ' xs _ i hi, List.append_assoc]
    · simp [flatMap_take_succ' xs _ i hi, List.append_assoc]
    · simp [flatMap_take_succ' xs _ i hi, List.append_assoc]
    · simp [hτ1, atRec, Function.update_of_ne hWO, Function.update_of_ne (Ne.symm hIW), hwh]
    · simp [hτ1, atRec, Function.update_of_ne hWO, frame_length]
    · refine a4.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp [hτ1, atRec]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [hτ1, atRec, Function.update_of_ne hx.1, Function.update_of_ne hx.2.1, Function.update_of_ne hx.2.2]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hτ1, atRec, Function.update_of_ne hr.1, Function.update_of_ne hr.2.2]
    · exact ⟨by simp [Function.update_of_ne hIO], by simp [Function.update_of_ne hIO],
        by simp [Function.update_of_ne h3], by simp [Function.update_of_ne h5],
        by simp [hτ1, atRec, Function.update_of_ne hWO, Function.update_of_ne (Ne.symm hIW), hwh],
        by simp [hτ1, atRec, Function.update_of_ne hWO, frame_length]⟩
  obtain ⟨τ, hInv, hτI, hτCW, hloop⟩ := recLoopJ_spec (cap := cap) (L := L) (I := I) (Wk := Wk) (CI := CI)
    (CW := CW) (body := appendRecX Wk O CS CO) hIW h1 hwl hL (by simp only [List.length_map]; omega) hb σ
    ⟨by simpa using hO, hWh, hWl, SameExcept.refl _ _ _⟩ hI hIh hCI hCW hWh hWl
  simp only [List.length_map, List.take_length] at hInv hloop
  obtain ⟨c1, c2, c3, c4⟩ := hInv
  rw [List.take_of_length_le (le_refl _)] at c1
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
  refine ⟨_, hloop, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne (Ne.symm hIO), c1.1]
  · simp [Function.update_of_ne (Ne.symm hIO), c1.2.1]
  · simp [Function.update_of_ne (Ne.symm h3), c1.2.2]
  · simp [Function.update_of_ne (Ne.symm hIW), c2]
  · simp [Function.update_of_ne (Ne.symm hIW), c3]
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [c4.cell]⟩
    · by_cases hx0 : x = I
      · rw [hx0]; simp [hτI, hI, hIh]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        have := c4.1 x (by simp [hx0, hx.1, hx.2])
        simp [Function.update_of_ne hx0, this.1, this.2]
    · by_cases r0 : r = CI
      · rw [r0]; simp [hCI]
      · by_cases r1 : r = CW
        · rw [r1]; simp [Function.update_of_ne (Ne.symm h1), hτCW, hCW]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          simp [Function.update_of_ne r0]
          exact c4.2.1 r (by simp [r0, r1, hr])

end NearCubicGates.Close.WordPrograms

import Proof.Gates.WordPrograms.RecLoop
import Proof.Gates.WordPrograms.BinW

set_option autoImplicit false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

/-- `τ` agrees with `σ` outside the streams `S` and the registers `Rg`. -/
def SameExcept (σ τ : WState ns nr) (S : List (Fin (ns + 1))) (Rg : List (Fin nr)) : Prop :=
  (∀ x, x ∉ S → τ.st x = σ.st x ∧ τ.sh x = σ.sh x) ∧ (∀ r, r ∉ Rg → τ.val r = σ.val r) ∧ τ.cell = σ.cell

theorem SameExcept.refl (σ : WState ns nr) (S : List (Fin (ns + 1))) (Rg : List (Fin nr)) : SameExcept σ σ S Rg :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl⟩

theorem SameExcept.trans {σ τ ρ : WState ns nr} {S : List (Fin (ns + 1))} {Rg : List (Fin nr)}
    (h1 : SameExcept σ τ S Rg) (h2 : SameExcept τ ρ S Rg) : SameExcept σ ρ S Rg :=
  ⟨fun x hx => ⟨(h2.1 x hx).1.trans (h1.1 x hx).1, (h2.1 x hx).2.trans (h1.1 x hx).2⟩,
    fun r hr => (h2.2.1 r hr).trans (h1.2.1 r hr), h2.2.2.trans h1.2.2⟩

/-- Sum the record stream on `I` into `ACC`. -/
def sumStream (I Wk ACC : Fin (ns + 1)) (CI CW F R : Fin nr) : WMX ns nr := recLoop I Wk CI CW (BinW.add ACC Wk F R)

/-- **The stream sum.** -/
theorem sumStream_spec (cap W : ℕ) {I Wk ACC : Fin (ns + 1)} {CI CW F R : Fin nr} (hIW : I ≠ Wk) (hIA : I ≠ ACC)
    (hWA : Wk ≠ ACC) (hd : [CI, CW, F, R].Nodup) (hW : 1 ≤ W) (l : List ℕ) (acc : ℕ) (σ : WState ns nr)
    (hI : σ.st I = recStream (l.map (binary W))) (hIh : σ.sh I = 0) (hA : NumOn σ ACC W acc) (hWh : σ.sh Wk = 0)
    (hWl : (σ.st Wk).length ≤ 2 * W + 1) (hCI : σ.val CI = 0) (hCW : σ.val CW = 0) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hsum : acc + l.sum < 2 ^ W) (hcap : l.length * (2 * W + 1) + 2 * W + 2 ≤ cap) :
    ∃ τ, WXExec cap (sumStream I Wk ACC CI CW F R) σ τ ((∑ _i ∈ Finset.range l.length, (91 * W + 33)) + 3) ∧
      NumOn τ ACC W (acc + l.sum) ∧ SameExcept σ τ [Wk, ACC] [] := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_true] at hd
  obtain ⟨⟨hCICW, hCIF, hCIR⟩, ⟨hCWF, hCWR⟩, hFR⟩ := hd
  set ws := l.map (binary W) with hws
  have hwsl : ws.length = l.length := by simp [hws]
  have hw : ∀ w ∈ ws, w.length = W := by intro w hw'; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw'; simp
  -- the invariant: the partial sum on `ACC`, the scratch registers at `0`, everything else as at the start
  let Inv : ℕ → WState ns nr → Prop := fun i τ =>
    NumOn τ ACC W (acc + (l.take i).sum) ∧ τ.val F = 0 ∧ τ.val R = 0 ∧
      (∀ x, x ≠ Wk → x ≠ ACC → x ≠ I → τ.st x = σ.st x ∧ τ.sh x = σ.sh x) ∧
      (∀ r, r ≠ CI → r ≠ CW → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  have hb : BodySpec cap W (I := I) (Wk := Wk) (CI := CI) (CW := CW) (BinW.add ACC Wk F R) ws Inv
      (fun _ => 41 * W + 3) := by
    intro i hi τ hτ hst hsh hci hcw hwh hwl
    obtain ⟨hAτ, hFτ, hRτ, hoth, hval, hcell⟩ := hτ
    have hil : i < l.length := by rwa [← hwsl]
    set τ0 := atRec I Wk CI τ ws[i] ((i + 1) * (2 * W + 1)) with hτ0
    have hwi : ws[i] = binary W l[i] := by simp [hws]
    have hA0 : NumOn τ0 ACC W (acc + (l.take i).sum) :=
      ⟨by simp [hτ0, atRec, Function.update_of_ne (Ne.symm hWA), hAτ.1],
        by simp [hτ0, atRec, Function.update_of_ne (Ne.symm hIA), hAτ.2]⟩
    have hW0 : NumOn τ0 Wk W l[i] := ⟨by simp [hτ0, atRec, hwi], by simp [hτ0, atRec, Function.update_of_ne (Ne.symm hIW), hwh]⟩
    have htake : (l.take (i + 1)).sum = (l.take i).sum + l[i] := by
      rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem hil]; simp
    have hle : (l.take (i + 1)).sum ≤ l.sum := by
      conv_rhs => rw [← List.take_append_drop (i + 1) l]
      rw [List.sum_append]; omega
    have h := BinW.add_spec cap W (Ne.symm hWA) hFR τ0 _ _ hA0 hW0 (by simp [hτ0, atRec, (Ne.symm hCIF), hFτ])
      (by simp [hτ0, atRec, (Ne.symm hCIR), hRτ]) (by omega) (by omega)
    refine ⟨_, h, ⟨⟨by simp [htake, Nat.add_assoc], by simp [hτ0, atRec, Function.update_of_ne (Ne.symm hIA), hAτ.2]⟩,
      by simp [hτ0, atRec, (Ne.symm hCIF), hFτ], by simp [hτ0, atRec, (Ne.symm hCIR), hRτ], fun x hx1 hx2 hx3 => ?_,
      fun r hr1 hr2 => ?_, by simp [hτ0, atRec, hcell]⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [hτ0, atRec, Function.update_of_ne hx1, Function.update_of_ne hx2, Function.update_of_ne hx3, hoth x hx1 hx2 hx3]
    · simp [hτ0, atRec, Function.update_of_ne hr1, hval r hr1 hr2]
    · simp [hτ0, atRec, Function.update_of_ne hIA, Function.update_of_ne hIW]
    · simp [hτ0, atRec]
    · simp
    · simp
    · simp [hτ0, atRec, Function.update_of_ne (Ne.symm hIW), hwh]
    · simp [hτ0, atRec, Function.update_of_ne hWA, hw _ (List.getElem_mem hi)]
  have h0 : Inv 0 σ := ⟨by simpa using hA, hF, hR, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, rfl⟩
  obtain ⟨τ, hτ, hIτ, hcwτ, hrun⟩ := recLoop_spec (Wk := Wk) hIW hCICW hw hW (by rwa [hwsl]) hb σ h0 hI hIh hCI hCW hWh
    hWl
  obtain ⟨hAτ, -, -, hoth, hval, hcell⟩ := hτ
  refine ⟨_, WXExec.mono hrun (by rw [hwsl]; simp; ring_nf; omega), ⟨by simpa [hwsl, Function.update_of_ne (Ne.symm hIA)] using hAτ.1,
    by simp [Function.update_of_ne (Ne.symm hIA), hAτ.2]⟩, fun x hx => ?_, fun r _ => ?_, by simp [hcell]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    by_cases hxI : x = I
    · subst hxI; simp [hIτ, hI, hIh]
    · simp [Function.update_of_ne hxI, hoth x hx.1 hx.2 hxI]
  · by_cases hr1 : r = CI
    · subst hr1; simp [hCI]
    · by_cases hr2 : r = CW
      · subst hr2; simp [Function.update_of_ne (Ne.symm hCICW), hcwτ, hCW]
      · simp [Function.update_of_ne hr1, hval r hr1 hr2]

/-! Programs are opaque to consumers: use the spec theorems. -/
attribute [irreducible] sumStream

end NearCubicGates.Close.WordPrograms

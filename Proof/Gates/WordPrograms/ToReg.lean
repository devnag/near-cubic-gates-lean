import Proof.Gates.WordPrograms.SInt

/-! # A number word into a register

Loop counts read from the input (a monomial's degree, the dimensions) are words; loops count in registers.
**`toReg X ONE Z R NZ F Rr`**: `R := r₀ + x` and `X := 0`, by `x` decrements (`toReg_spec`), cost `x·(83W+30) + 41W+14`.
`nzP` sets the flag `NZ := [x ≠ 0]` (`nzP_spec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

/-- `NZ := [x ≠ 0]` (`NZ = F = Rr = 0` before; `F`, `Rr` are `0` after). -/
def nzP (X Z : Fin (ns + 1)) (NZ F Rr : Fin nr) : WMX ns nr :=
  .seq (.wm (SInt.zTestW X Z F Rr)) (.ifr F (WMX.dec F) (WMX.inc NZ))

theorem nzP_spec (cap W : ℕ) {X Z : Fin (ns + 1)} {NZ F Rr : Fin nr} (hXZ : X ≠ Z) (hR : [NZ, F, Rr].Nodup)
    (σ : WState ns nr) (x z : ℕ) (hX : NumOn σ X W x) (hZ : NumOn σ Z W z) (hNZ : σ.val NZ = 0) (hF : σ.val F = 0)
    (hRr : σ.val Rr = 0) (hx : x < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (nzP X Z NZ F Rr) σ (σ.setv NZ (decide (x ≠ 0)).toNat) (41 * W + 12) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨h1, h2⟩, h3⟩ := hR
  have hz := SInt.zTestW_spec cap W hXZ h3 σ x z hX hZ hF hRr hx hcap
  by_cases hx0 : x = 0
  · have hv : (σ.setv F (decide (x = 0)).toNat).val F ≠ 0 := by simp [hx0]
    have hd := WXExec.dec cap F (σ.setv F (decide (x = 0)).toNat) (by simp [hx0]; omega)
    refine (WXExec.seq (WXExec.wm hz) (WXExec.ifrT hv hd)).cast cap ?_ (by omega)
    apply WState.eq <;> try rfl
    funext r; by_cases hr : r = F
    · subst hr; simp [hx0, hF, Function.update_of_ne (Ne.symm h1)]
    · by_cases hr2 : r = NZ
      · subst hr2; simp [hx0, hNZ, Function.update_of_ne h1]
      · simp [Function.update_of_ne hr, Function.update_of_ne hr2]
  · have hv : (σ.setv F (decide (x = 0)).toNat).val F = 0 := by simp [hx0]
    have hi := WXExec.inc cap NZ (σ.setv F (decide (x = 0)).toNat) (by
      simp [Function.update_of_ne h1, hNZ]; omega)
    refine (WXExec.seq (WXExec.wm hz) (WXExec.ifrF hv hi)).cast cap ?_ (by omega)
    apply WState.eq <;> try rfl
    funext r; by_cases hr : r = F
    · subst hr; simp [hx0, hF, Function.update_of_ne (Ne.symm h1)]
    · by_cases hr2 : r = NZ
      · subst hr2; simp [hx0, hNZ, Function.update_of_ne h1]
      · simp [Function.update_of_ne hr, Function.update_of_ne hr2]

/-- `R := R + x`, `X := 0` (`ONE` holds `1`, `Z` any word of the width). -/
def toReg (X ONE Z : Fin (ns + 1)) (R NZ F Rr : Fin nr) : WMX ns nr :=
  .seq (nzP X Z NZ F Rr)
    (.whr NZ (.seq (WMX.dec NZ) (.seq (BinW.sub X ONE F Rr) (.seq (WMX.inc R) (nzP X Z NZ F Rr)))))

theorem toReg_spec (cap W : ℕ) {X ONE Z : Fin (ns + 1)} {R NZ F Rr : Fin nr} (hS : [X, ONE, Z].Nodup)
    (hR : [R, NZ, F, Rr].Nodup) (σ : WState ns nr) (x z r0 : ℕ) (hX : NumOn σ X W x) (hONE : NumOn σ ONE W 1)
    (hZ : NumOn σ Z W z) (hRv : σ.val R = r0) (hNZ : σ.val NZ = 0) (hF : σ.val F = 0) (hRr : σ.val Rr = 0)
    (hx : x < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) (hcapR : r0 + x < cap) :
    WXExec cap (toReg X ONE Z R NZ F Rr) σ ((σ.sets X (frame (binary W 0))).setv R (r0 + x))
      (x * (83 * W + 30) + 41 * W + 14) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hS hR
  obtain ⟨⟨hXO, hXZ⟩, hOZ⟩ := hS
  obtain ⟨⟨hRN, hRF, hRR⟩, ⟨hNF, hNR⟩, hFR⟩ := hR
  -- the state with `k` left to count
  let st : ℕ → WState ns nr := fun k =>
    ((σ.sets X (frame (binary W k))).setv R (r0 + (x - k))).setv NZ (decide (k ≠ 0)).toNat
  have hst : ∀ k ≤ x, NumOn (st k) X W k := fun k _ => ⟨by simp [st], by simp [st, hX.2]⟩
  have h0 := nzP_spec cap W (NZ := NZ) (F := F) (Rr := Rr) hXZ (by simp [hNF, hNR, hFR]) σ x z hX hZ hNZ hF hRr hx hcap
  have e0 : σ.setv NZ (decide (x ≠ 0)).toNat = st x := by
    apply WState.eq
    · rfl
    · funext i; by_cases hi : i = X
      · subst hi; simp [st, hX.1]
      · simp [st, Function.update_of_ne hi]
    · funext q; by_cases hq : q = NZ
      · subst hq; simp [st]
      · by_cases hq2 : q = R
        · subst hq2; simp [st, hq, hRv]
        · simp [st, Function.update_of_ne hq, Function.update_of_ne hq2]
    · rfl
  rw [e0] at h0
  have hloop := Runs.whr (cap := cap) (r := NZ)
    (P := .seq (WMX.dec NZ) (.seq (BinW.sub X ONE F Rr) (.seq (WMX.inc R) (nzP X Z NZ F Rr))))
    (fun k τ => k ≤ x ∧ τ = st k) (83 * W + 28) (fun τ => τ = st 0)
    (fun τ ⟨_, h⟩ => ⟨by rw [h]; simp [st], h⟩) ?_ x (st x) ⟨le_rfl, rfl⟩
  · obtain ⟨τ, e, hτ⟩ := hloop
    refine (WXExec.seq h0 e).cast cap ?_ (by nlinarith)
    rw [hτ]
    apply WState.eq <;> try rfl
    funext q; by_cases hq : q = NZ
    · subst hq; simp [st, Function.update_of_ne (Ne.symm hRN), hNZ]
    · simp [st, Function.update_of_ne hq]
  · rintro k τ ⟨hk, rfl⟩
    refine ⟨by simp [st], ?_⟩
    have hv1 : (st (k + 1)).val NZ = 1 := by simp [st]
    have hd := WXExec.dec cap NZ (st (k + 1)) (by rw [hv1]; omega)
    set τ1 := (st (k + 1)).setv NZ ((st (k + 1)).val NZ - 1) with hτ1
    have hX1 : NumOn τ1 X W (k + 1) := ⟨by simp [τ1, st], by simp [τ1, st, hX.2]⟩
    have hO1 : NumOn τ1 ONE W 1 := ⟨by simp [τ1, st, Function.update_of_ne (Ne.symm hOZ), Function.update_of_ne
      (Ne.symm hXO), hONE.1], by simp [τ1, st, Function.update_of_ne (Ne.symm hXO), hONE.2]⟩
    have hsub := BinW.sub_spec (A := X) (B := ONE) (F := F) (R := Rr) cap W hXO hFR τ1 (k + 1) 1 hX1 hO1
      (by simp [τ1, st, Function.update_of_ne (Ne.symm hNF), Function.update_of_ne (Ne.symm hRF), hF])
      (by simp [τ1, st, Function.update_of_ne (Ne.symm hNR), Function.update_of_ne (Ne.symm hRR), hRr]) (by omega)
      (by omega) hcap
    set τ2 := τ1.sets X (frame (binary W (k + 1 - 1))) with hτ2
    have hi := WXExec.inc cap R τ2 (by
      simp [τ2, τ1, st, Function.update_of_ne hRN]; omega)
    set τ3 := τ2.setv R (τ2.val R + 1) with hτ3
    have hn := nzP_spec cap W (NZ := NZ) (F := F) (Rr := Rr) hXZ (by simp [hNF, hNR, hFR]) τ3 k z
      ⟨by simp [τ3, τ2], by simp [τ3, τ2, τ1, st, hX.2]⟩
      ⟨by simp [τ3, τ2, τ1, st, Function.update_of_ne (Ne.symm hXZ), hZ.1], by
        simp [τ3, τ2, τ1, st, Function.update_of_ne (Ne.symm hXZ), hZ.2]⟩
      (by simp [τ3, τ2, τ1, st, Function.update_of_ne (Ne.symm hRN)])
      (by simp [τ3, τ2, τ1, st, Function.update_of_ne (Ne.symm hRF), Function.update_of_ne (Ne.symm hNF), hF])
      (by simp [τ3, τ2, τ1, st, Function.update_of_ne (Ne.symm hRR), Function.update_of_ne (Ne.symm hNR), hRr])
      (by omega) hcap
    refine ⟨_, (WXExec.seq hd (WXExec.seq hsub (WXExec.seq hi hn))).mono (by omega), by omega, ?_⟩
    apply WState.eq
    · rfl
    · funext i; by_cases hi : i = X
      · subst hi; simp [τ3, τ2, st]
      · simp [τ3, τ2, τ1, st, Function.update_of_ne hi]
    · funext q; by_cases hq : q = NZ
      · subst hq; simp [τ3, τ2, τ1, st, Function.update_of_ne (Ne.symm hRN)]
      · by_cases hq2 : q = R
        · subst hq2; simp [τ3, τ2, τ1, st, hq, Function.update_of_ne hRN]; omega
        · simp [τ3, τ2, τ1, st, Function.update_of_ne hq, Function.update_of_ne hq2]
    · rfl

attribute [irreducible] toReg

end NearCubicGates.Close.WordPrograms

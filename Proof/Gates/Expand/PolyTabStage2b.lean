import Proof.Gates.Expand.PolyTabStage2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (stp enc_length)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Codec
open NearCubicWires.RepairRepresentation (natWord)

local notation "encP" => NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc

theorem encP_false (w : List Bool) : encP false w = w := rfl
theorem stp_false : stp false = 1 := rfl

section Gen
variable {ns nr : ℕ} (cap : ℕ)

/-- Copy one monomial: its variable list, then its coefficient. -/
def cpMono (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (copyList false s o R (copyNat false s o R)) (copyInt false s o R)

def cpMonoCost {V : ℕ} (t : Finset (Fin V) × ℤ) : ℕ :=
  copyListCost ((t.1.sort (· ≤ ·)).map Fin.val).length
    (((t.1.sort (· ≤ ·)).map Fin.val).map fun x => 60 * (natWord x).length + 60) + 1 +
    (60 * (Interfaces.intWord t.2).length + 121)

theorem cpNatList_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (V : ℕ)
    (xs : List ℕ) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ encP false (Interfaces.listWord natWord xs) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hcap : 2 ^ (natBitLength xs.length + 1) ≤ cap) (hlen : xs.length ≤ cap)
    (hcapw : xs.length + V + 6 * natBitLength xs.length + 6 ≤ cap)
    (hV : σ.val (R 7) + (marks (Interfaces.listWord natWord xs)).length ≤ V) :
    WExec cap (copyList false s o R (copyNat false s o R)) σ
      ((appendO σ o (R 7) (marks (Interfaces.listWord natWord xs))).seth s
        (pre.length + stp false * (Interfaces.listWord natWord xs).length))
      (copyListCost xs.length (xs.map fun x => 60 * (natWord x).length + 60)) := by
  refine copyList_spec cap false s o hso R (copyNat false s o R) natWord (fun x => 60 * (natWord x).length + 60)
    (fun σ => σ.val (R 1) = 0 ∧ σ.val (R 2) = 0) V (fun σ x h => by simpa using h)
    (fun σ x h => by
      simp [Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 0 by decide)),
        Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 0 by decide)), h.1, h.2])
    (fun σ w h => by
      simp [appendO, Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 7 by decide)),
        Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 7 by decide)), h.1, h.2])
    xs ?_ pre rest σ ⟨hz 1 (by decide), hz 2 (by decide)⟩ hst hsh ho hz hcap hlen (by omega) hV
  intro x _ pre' rest' σ' hok hst' hsh' ho' hV'
  exact copyNat_spec cap false s o hso R x pre' rest' σ' hst' hsh' ho' hok.1 hok.2
    (by rw [marks_length] at hV'; omega)

theorem cpMono_spec {V : ℕ} (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (Vb : ℕ) (hVcap : Vb + 4 ≤ cap)
    (t : Finset (Fin V) × ℤ) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ encP false (monoWord t) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hcap : 2 ^ (natBitLength V + 1) ≤ cap) (hlen : V ≤ cap) (hcapw : V + Vb + 6 * natBitLength V + 6 ≤ cap)
    (hV : σ.val (R 7) + (marks (monoWord t)).length ≤ Vb) :
    WExec cap (cpMono s o R) σ ((appendO σ o (R 7) (marks (monoWord t))).seth s (pre.length + (monoWord t).length))
      (cpMonoCost t) := by
  set xs := (t.1.sort (· ≤ ·)).map Fin.val with hxs
  have hxl : xs.length ≤ V := by
    rw [hxs, List.length_map, Finset.length_sort]; exact (Finset.card_le_univ _).trans (by simp)
  have hnb : natBitLength xs.length ≤ natBitLength V := Nat.add_le_add_right (Nat.log_mono_right hxl) 1
  have hsplit : encP false (monoWord t) = encP false (Interfaces.listWord natWord xs) ++ encP false (Interfaces.intWord t.2) := by
    simp [monoWord, encP_false, hxs]
  have hml : (marks (monoWord t)).length = (marks (Interfaces.listWord natWord xs)).length +
      (marks (Interfaces.intWord t.2)).length := by
    simp only [monoWord, ← hxs]; rw [marksApp, List.length_append]
  have hA := cpNatList_spec cap s o hso R Vb xs pre (encP false (Interfaces.intWord t.2) ++ rest) σ
    (by rw [hst, hsplit]; simp [List.append_assoc]) hsh ho hz
    (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcap) (by omega) (by omega) (by omega)
  set σ1 := (appendO σ o (R 7) (marks (Interfaces.listWord natWord xs))).seth s
    (pre.length + stp false * (Interfaces.listWord natWord xs).length) with hσ1
  have hB := copyInt_spec cap false s o hso R t.2 (pre ++ encP false (Interfaces.listWord natWord xs)) rest σ1
    (by simp only [hσ1, WState.seth_st, appendO, WState.setv_st, WState.sets_st]; rw [Function.update_of_ne hso, hst, hsplit]; simp [List.append_assoc])
    (by simp [hσ1, encP_false, stp_false])
    (by simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), ho])
    (by simp [hσ1, appendO, Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 7 by decide)), hz 1 (by decide)])
    (by simp [hσ1, appendO, Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 7 by decide)), hz 2 (by decide)])
    (by
      have e1 : σ1.val (R 7) = σ.val (R 7) + 2 * (Interfaces.listWord natWord xs).length := by
        simp [hσ1, appendO, marks_length]
      rw [e1]; rw [marks_length, marks_length, marks_length] at hml; rw [marks_length] at hV; omega)
  refine WExec.cast cap (WExec.seq hA hB) ?_ (by unfold cpMonoCost; rw [← hxs])
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = s
    · subst hj; simp [hσ1, appendO, Function.update_of_ne hso, monoWord, stp_false, encP_false, ← hxs]; ring
    · by_cases hjo : j = o
      · subst hjo; simp [hσ1, appendO, Function.update_of_ne hj, ho, monoWord, marksApp, ← hxs]; ring
      · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), monoWord, marksApp, ← hxs]
    · by_cases hj : j = s
      · subst hj; simp [hσ1, appendO, Function.update_of_ne hjo]
      · simp [hσ1, appendO, Function.update_of_ne hjo, Function.update_of_ne hj]
  · funext q; by_cases hr7 : q = R 7
    · subst hr7; simp [hσ1, appendO, monoWord, marksApp, ← hxs]; ring
    · simp [hσ1, appendO, Function.update_of_ne hr7]

/-- Copy the raw terms word on `s` to `o` as `frame (termsWord P)`, and rewind `o`. -/
def cpTerms (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (m : Fin nr) (hm : ∀ i : Fin 8, R i ≠ m) : WMX ns nr :=
  .seq (.wm (copyList false s o (withCount R m hm) (cpMono s o R)))
    (.seq (.wm (emitC o (R 7) false)) (.wm (WM.rewind o (R 7))))

def cpTermsCost {V : ℕ} (P : Terms V) : ℕ :=
  copyListCost P.length (P.map cpMonoCost) + 1 + (7 + 1 + (5 * (2 * (termsWord P).length + 1) + 1))

theorem cpTerms_spec {V : ℕ} (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (m : Fin nr)
    (hm : ∀ i : Fin 8, R i ≠ m) (P : Terms V) (rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = termsWord P ++ rest) (hsh : σ.sh s = 0) (hos : σ.st o = []) (hoh : σ.sh o = 0)
    (hz : ∀ i : Fin 8, σ.val (R i) = 0) (hm0 : σ.val m = 0)
    (hcapV : 2 ^ (natBitLength V + 1) ≤ cap) (hlenV : V ≤ cap)
    (hcapP : 2 ^ (natBitLength P.length + 1) ≤ cap) (hlenP : P.length ≤ cap)
    (hcapw : V + P.length + 6 * natBitLength V + 6 * natBitLength P.length + 2 * (termsWord P).length + 20 ≤ cap) :
    WXExec cap (cpTerms s o R m hm) σ ((σ.sets o (frame (termsWord P))).seth s (termsWord P).length)
      (cpTermsCost P) := by
  set Vb := 2 * (termsWord P).length + 2 with hVb
  have hW7 : withCount R m hm 7 = R 7 := withCount_ne R m hm 7 (by decide)
  have hmR : ∀ i : Fin 8, m ≠ R i := fun i e => hm i e.symm
  have hz' : ∀ i : Fin 8, i ≠ 7 → σ.val (withCount R m hm i) = 0 := by
    intro i _
    by_cases h0 : i = 0
    · subst h0; simp [hm0]
    · rw [withCount_ne R m hm i h0]; exact hz i
  have h := copyList_spec cap false s o hso (withCount R m hm) (cpMono s o R) monoWord cpMonoCost
    (fun σ => ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0) Vb
    (fun σ x h i hi => by simpa using h i hi)
    (fun σ x h i hi => by rw [withCount_zero]; simp [Function.update_of_ne (hm i), h i hi])
    (fun σ w h i hi => by rw [hW7]; simp [appendO, Function.update_of_ne (Rne R hi), h i hi])
    P ?_ [] rest σ (fun i _ => hz i) (by rw [hst]; rfl) hsh (by rw [hos, hoh]; rfl) hz' hcapP hlenP
    (by rw [hW7, hz 7]; omega) (by rw [hW7, hz 7, marks_length]; unfold termsWord at hVb; omega)
  · rw [hW7] at h
    set σ1 := (appendO σ o (R 7) (marks (Interfaces.listWord monoWord P))).seth s
      ([].length + stp false * (Interfaces.listWord monoWord P).length) with hσ1
    have e2 := emitC_spec (cap := cap) o (R 7) false σ1 (by simp [hσ1, appendO, Function.update_apply, hso.symm, hos, hoh])
      (by simp [hσ1, appendO, hz 7, marks_length]; unfold termsWord at hcapw; omega)
    set σ2 := ((σ1.sets o (σ1.st o ++ [false])).seth o (σ1.sh o + 1)).setv (R 7) (σ1.val (R 7) + 1) with hσ2
    have hv2 : σ2.val (R 7) = 2 * (termsWord P).length + 1 := by
      simp [hσ2, hσ1, appendO, hz 7, marks_length, termsWord]
    have e3 := wrewind_spec (cap := cap) o (R 7) (2 * (termsWord P).length + 1) σ2 hv2 (by omega)
    refine WXExec.cast cap (WXExec.seq (WXExec.wm h) (WXExec.seq (WXExec.wm e2) (WXExec.wm e3))) ?_ le_rfl
    apply WState.eq
    · funext y; by_cases hy : y = o
      · subst hy; simp [hσ2, hσ1, appendO, hso.symm, termsWord] <;> rw [hos, Codec.frame_eq_marks] <;> rfl
      · by_cases hy' : y = s
        · subst hy'; simp [hσ2, hσ1, appendO, hso, stp, termsWord]
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hy']
    · funext y; by_cases hy : y = o
      · subst hy; simp [hσ2, hσ1, appendO, hso.symm, hoh, marks_length, termsWord] <;> rw [hos, Codec.frame_eq_marks] <;> rfl
      · by_cases hy' : y = s
        · subst hy'; simp [hσ2, hσ1, appendO, hso, stp, termsWord]
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hy']
    · funext q; by_cases hq : q = R 7
      · subst hq; simp [hσ2, hσ1, appendO, hz 7]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hq]
    · simp [hσ2, hσ1, appendO]
  · intro t _ pre' rest' σ' hok hst' hsh' ho' hV'
    rw [hW7] at hV' ⊢
    have := cpMono_spec cap s o hso R Vb (by omega) t pre' rest' σ' hst' hsh' ho' hok hcapV hlenV (by omega) hV'
    simpa [stp_false] using this

end Gen

end NearCubicGates.Close.Expand.PolyTab

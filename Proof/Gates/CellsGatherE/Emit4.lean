import Proof.Gates.CellsGatherE.Emit3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

def padE : St VV MM :=
  .seq (.op (.copy eA p2K)) (.seq (.op (.shl eA)) (.seq (.op (.mul eA eG2 eB)) (forS eI vNL (.op (.wrM sG eB)))))

def padT : List (Fin VV) := [eA, eB, eI]

theorem padRec_eq (c : Call) (p : Params) :
    GatherPhase.padRec c p = 2 * 2 ^ keyW c p * (2 ^ valueWidth c p * 2 ^ keyW c p) := by
  unfold GatherPhase.padRec tRec GatherPhase.gZ; rw [pow_add]; ring

theorem pad_spec (C : Ctx) (c : Call) (p : Params) (a : DS VV MM) (S W : List ℕ) (L : ℕ) (hc : Cst a)
    (hG : GW a S W) (hL : a.env vNL = L) (hG2 : a.env eG2 = 2 ^ valueWidth c p * 2 ^ keyW c p)
    (hKW : a.env p2K = 2 ^ keyW c p) (hLW : L < 2 ^ C.Wd)
    (hW : 2 * (2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p) < 2 ^ C.Wd) :
    Hs C padE a (L * 5 + 12) (fun e => GW e S (W ++ List.replicate L (GatherPhase.padRec c p)) ∧ Ke a e ∧
      (∀ m, m ≠ sG → e.rc m = a.rc m) ∧ Fr a e padT ∧ Cst e) := by
  have hK1 : 1 ≤ 2 ^ valueWidth c p := Nat.one_le_two_pow
  have hP : 2 * 2 ^ keyW c p * (2 ^ valueWidth c p * 2 ^ keyW c p) < 2 ^ C.Wd := by
    have : 2 * 2 ^ keyW c p * (2 ^ valueWidth c p * 2 ^ keyW c p) =
        2 * (2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p) := by ring
    omega
  have hK2 : 2 * 2 ^ keyW c p < 2 ^ C.Wd := by
    have : 2 * 2 ^ keyW c p ≤ 2 * 2 ^ keyW c p * (2 ^ valueWidth c p * 2 ^ keyW c p) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    omega
  unfold padE
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + (1 + (L * (1 + 4) + 4) + 1) + 1) (hs_copy C eA p2K a (by decide))
    (fun b1 hb1 => ?_)) (by omega) (fun _ h => h)
  subst hb1
  refine Hs.seq (hs_shl C eA _ (by vsimp [hKW]; omega)) (fun b2 hb2 => ?_)
  subst hb2
  refine Hs.seq (hs_mul C eA eG2 eB _ (by decide) (by decide) (by decide) (by vsimp [hKW, hG2]; omega))
    (fun b3 hb3 => ?_)
  subst hb3
  set b := ((a.set eA (a.env p2K)).set eA (2 * (a.set eA (a.env p2K)).env eA)).set eB
    (((a.set eA (a.env p2K)).set eA (2 * (a.set eA (a.env p2K)).env eA)).env eA *
      ((a.set eA (a.env p2K)).set eA (2 * (a.set eA (a.env p2K)).env eA)).env eG2) with hb
  have bB : b.env eB = GatherPhase.padRec c p := by rw [hb, padRec_eq]; vsimp [hKW, hG2]
  have bL : b.env vNL = L := by rw [hb]; vsimp [hL]
  have bG : GW b S W := GW.congr hG rfl rfl
  have bR : b.rc = a.rc := by rw [hb]; rfl
  have bF : Fr a b padT := Fr.set_r (Fr.set_r (Fr.set_r (Fr.refl a padT) _ (by decide)) _ (by decide)) _ (by decide)
  have bK : Ke a b := Ke.set_r (Ke.set_r (Ke.set_r (Ke.refl a) _ _) _ _) _ _
  clear_value b
  let I : ℕ → DS VV MM → Prop := fun k d => GW d S (W ++ List.replicate k (GatherPhase.padRec c p)) ∧ Ke a d ∧
    (∀ m, m ≠ sG → d.rc m = a.rc m) ∧ Fr a d padT ∧ d.env eB = GatherPhase.padRec c p ∧ Cst d
  refine Hs.mono (CounterMachine.PrefixProg.forS_specV (C := C) eI vNL (by decide) (.op (.wrM sG eB)) b L hLW I 1
    (fun k d v _ ⟨i1, i2, i3, i4, i5, i6⟩ => ⟨i1, i2.set_r _ _, i3, Fr.set_r i4 v (by decide),
      by rw [DS.set_env_ne _ _ (by decide)]; exact i5, cst_of i6 (Fr.set d v (show eI ∈ [eI] by simp)) (by decide)⟩)
    ⟨by simpa using bG, bK, fun m _ => by rw [bR], bF, bB, cst_of hc bF (by decide)⟩ bL ?_) le_rfl ?_
  · intro k hk d ⟨i1, i2, i3, i4, i5, i6⟩ hdk hdm
    refine Hs.mono (hs_wrM C sG eB d i1.len_le) le_rfl ?_
    rintro e rfl
    refine ⟨⟨?_, i2.put_r _, fun m hm => ?_, Fr.put_r i4 _ _, by simpa using i5, ⟨i6.z, i6.one, i6.two⟩⟩, by simpa using hdk,
      by simpa using hdm⟩
    · rw [List.replicate_succ', ← List.append_assoc]; exact GW.put' i1 eB rfl rfl i5
    · simp [DS.put, Function.update_of_ne hm, i3 m hm]
  · rintro e ⟨⟨i1, i2, i3, i4, _, i6⟩, _, _⟩
    exact ⟨i1, i2, i3, i4, i6⟩

end NearCubicGates.Close.Cells.RecordEmission

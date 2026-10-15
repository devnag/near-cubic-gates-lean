import Proof.Gates.CellsGatherE.Emit2
import Proof.Gates.CellsGatherE.GW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

/-! ## The table records -/

def eX : Fin VV := ⟨64, by decide⟩
def eY : Fin VV := ⟨65, by decide⟩
def eV : Fin VV := ⟨66, by decide⟩
def eK : Fin VV := ⟨67, by decide⟩
def eRec : Fin VV := ⟨68, by decide⟩
def eTmp : Fin VV := ⟨56, by decide⟩

def tabB : St VV MM :=
  .seq (.op (.rdM sCT eX)) (.seq (.op (.dm eX p2VW eY eV)) (.seq (.op (.dm eY p2K eJk eK)) (.seq (.op (.copy eRec eK))
  (.seq (.op (.shl eRec)) (.seq (.op (.mul eRec eG2 eTmp)) (.seq (.op (.add eTmp eV)) (.op (.wrM sG eTmp))))))))

def tabE : St VV MM := .seq (.op (.rwM sCT)) (forS eI eR tabB)

def tabT : List (Fin VV) := [eX, eY, eV, eJk, eK, eRec, eTmp, eI]

theorem tabRec_eq (c : Call) (p : Params) (x : ℕ) :
    GatherPhase.tabRec c p x = 2 * (x / 2 ^ valueWidth c p % 2 ^ keyW c p) * (2 ^ valueWidth c p * 2 ^ keyW c p) +
      x % 2 ^ valueWidth c p := by
  unfold GatherPhase.tabRec tRec GatherPhase.gZ; rw [pow_add]

theorem tab_spec (C : Ctx) (c : Call) (p : Params) (a : DS VV MM) (S W0 B : List ℕ) (hc : Cst a)
    (hG : GW a S W0) (hB : a.ram sCT = B) (hR : a.env eR = B.length)
    (hG2 : a.env eG2 = 2 ^ valueWidth c p * 2 ^ keyW c p) (hVW : a.env p2VW = 2 ^ valueWidth c p)
    (hKW : a.env p2K = 2 ^ keyW c p) (hrc : ∀ m, a.rc m ≤ (a.ram m).length) (hBW : B.length < 2 ^ C.Wd)
    (hW : 2 * (2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p) < 2 ^ C.Wd) :
    Hs C tabE a (B.length * 25 + 10) (fun e => GW e S (W0 ++ B.map (GatherPhase.tabRec c p)) ∧ Ke a e ∧
      (∀ m, m ≠ sG → m ≠ sCT → e.rc m = a.rc m) ∧ e.rc sCT ≤ B.length ∧ Fr a e tabT ∧ Cst e) := by
  have hV1 : 1 ≤ 2 ^ valueWidth c p := Nat.one_le_two_pow
  have hK1 : 1 ≤ 2 ^ keyW c p := Nat.one_le_two_pow
  have hVK : 2 ^ valueWidth c p * 2 ^ keyW c p ≤ 2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p :=
    Nat.le_mul_of_pos_right _ hK1
  have hK2 : 2 * 2 ^ keyW c p ≤ 2 ^ C.Wd := by
    have : 2 ^ keyW c p ≤ 2 ^ valueWidth c p * 2 ^ keyW c p := Nat.le_mul_of_pos_left _ hV1
    omega
  have hV2 : 2 * 2 ^ valueWidth c p ≤ 2 ^ C.Wd := by
    have : 2 ^ valueWidth c p ≤ 2 ^ valueWidth c p * 2 ^ keyW c p := Nat.le_mul_of_pos_right _ hK1
    omega
  unfold tabE
  refine Hs.mono (Hs.seq (t1 := a.rc sCT + 1) (t2 := B.length * (19 + 4) + 4) (hs_rwM C sCT a)
    (fun b hb => ?_)) (by have := hrc sCT; rw [hB] at this; omega) (fun _ h => h)
  subst hb
  let I : ℕ → DS VV MM → Prop := fun k d => GW d S (W0 ++ (B.take k).map (GatherPhase.tabRec c p)) ∧ d.rc sCT = k ∧
    Ke a d ∧ (∀ m, m ≠ sG → m ≠ sCT → d.rc m = a.rc m) ∧ Fr a d tabT ∧ Cst d
  refine Hs.mono (CounterMachine.PrefixProg.forS_specV (C := C) eI eR (by decide) tabB (a.rew sCT) B.length hBW I 19
    (fun k d v _ ⟨i1, i2, i3, i4, i5, i6⟩ => ⟨i1, i2, i3.set_r _ _, i4, Fr.set_r i5 v (by decide),
      cst_of i6 (Fr.set d v (show eI ∈ [eI] by simp)) (by decide)⟩)
    ⟨⟨by simp [DS.rew, hG.1], by simp [DS.rew, Function.update_of_ne (show sG ≠ sCT by decide), hG.2]⟩, by simp [DS.rew],
      (Ke.refl a).rew_r sCT, fun m _ h2 => by simp [DS.rew, Function.update_of_ne h2], Fr.refl _ _,
      ⟨hc.z, hc.one, hc.two⟩⟩ (by simp [DS.rew, hR]) ?_) le_rfl ?_
  · intro k hk d ⟨i1, i2, i3, i4, i5, i6⟩ hdk hdm
    have dB : d.ram sCT = B := by rw [i3.ram sCT (by decide), hB]
    have gd : ∀ y, y ∉ tabT → d.env y = a.env y := fun y hy => i5 y hy
    have dVW : d.env p2VW = 2 ^ valueWidth c p := by rw [gd p2VW (by decide)]; exact hVW
    have dKW : d.env p2K = 2 ^ keyW c p := by rw [gd p2K (by decide)]; exact hKW
    have dG2 : d.env eG2 = 2 ^ valueWidth c p * 2 ^ keyW c p := by rw [gd eG2 (by decide)]; exact hG2
    set x := B[k] with hx
    have hkW : x / 2 ^ valueWidth c p % 2 ^ keyW c p < 2 ^ keyW c p := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hvW : x % 2 ^ valueWidth c p < 2 ^ valueWidth c p := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hrec : 2 * (x / 2 ^ valueWidth c p % 2 ^ keyW c p) * (2 ^ valueWidth c p * 2 ^ keyW c p) +
        x % 2 ^ valueWidth c p < 2 ^ C.Wd := by
      have h1 : 2 * (x / 2 ^ valueWidth c p % 2 ^ keyW c p) + 1 ≤ 2 * 2 ^ keyW c p := by omega
      have h2 : (2 * (x / 2 ^ valueWidth c p % 2 ^ keyW c p) + 1) * (2 ^ valueWidth c p * 2 ^ keyW c p) ≤
          2 * 2 ^ keyW c p * (2 ^ valueWidth c p * 2 ^ keyW c p) := Nat.mul_le_mul_right _ h1
      have h3 : 2 * 2 ^ keyW c p * (2 ^ valueWidth c p * 2 ^ keyW c p) =
          2 * (2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p) := by ring
      have h4 : (2 * (x / 2 ^ valueWidth c p % 2 ^ keyW c p) + 1) * (2 ^ valueWidth c p * 2 ^ keyW c p) =
          2 * (x / 2 ^ valueWidth c p % 2 ^ keyW c p) * (2 ^ valueWidth c p * 2 ^ keyW c p) +
          2 ^ valueWidth c p * 2 ^ keyW c p := by ring
      have h5 : 2 ^ valueWidth c p ≤ 2 ^ valueWidth c p * 2 ^ keyW c p := Nat.le_mul_of_pos_right _ hK1
      omega
    have hx2 : (d.ram sCT)[d.rc sCT]?.getD 0 = x := by rw [dB, i2]; simp [hk, hx]
    apply Hx.hs
    refine Hs.then (hs_rdM C sCT eX d (by rw [i2, dB]; exact hk)) (fun e1 he1 m1 hm1 => ?_); subst he1
    refine Hs.then (hs_dm C eX p2VW eY eV _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by vsimp [DS.adv, dVW]) (by vsimp [DS.adv, dVW]; omega)) (fun e2 he2 m2 hm2 => ?_); subst he2
    refine Hs.then (hs_dm C eY p2K eJk eK _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by vsimp [DS.adv, dKW]) (by vsimp [DS.adv, dKW]; omega)) (fun e3 he3 m3 hm3 => ?_); subst he3
    refine Hs.then (hs_copy C eRec eK _ (by decide)) (fun e4 he4 m4 hm4 => ?_); subst he4
    refine Hs.then (hs_shl C eRec _ (by vsimp [DS.adv, dKW, dVW, hx2]; omega)) (fun e5 he5 m5 hm5 => ?_); subst he5
    refine Hs.then (hs_mul C eRec eG2 eTmp _ (by decide) (by decide) (by decide)
      (by vsimp [DS.adv, dKW, dVW, dG2, hx2]; omega)) (fun e6 he6 m6 hm6 => ?_); subst he6
    refine Hs.then (hs_add C eTmp eV _ (by decide) (by vsimp [DS.adv, dKW, dVW, dG2, hx2]; omega))
      (fun e7 he7 m7 hm7 => ?_); subst he7
    refine Hs.last (hs_wrM C sG eTmp _ (by vsimp [DS.adv]; exact i1.len_le)) (fun e8 he8 m8 hm8 => ?_)
    subst he8
    have hF : ∀ u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : ℕ, Fr d (((((((((((d.set eX u1).adv sCT).set eY u2).set eV u3).set
        eJk u4).set eK u5).set eRec u6).set eRec u7).set eTmp u8).set eTmp u9).put sG u10) tabT := by
      intro u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 y hy
      simp only [tabT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hy
      simp [DS.set, Function.update_apply, h1, h2, h3, h4, h5, h6, h7]
    have hKe : ∀ u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : ℕ, Ke d (((((((((((d.set eX u1).adv sCT).set eY u2).set eV u3).set
        eJk u4).set eK u5).set eRec u6).set eRec u7).set eTmp u8).set eTmp u9).put sG u10) := by
      intro u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
      exact Ke.put_r (Ke.set_r (Ke.set_r (Ke.set_r (Ke.set_r (Ke.set_r (Ke.set_r (Ke.set_r (Ke.set_r (Ke.adv_r
        (Ke.set_r (Ke.refl d) _ _) _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _
    refine ⟨⟨⟨?_, ?_, i3.trans (hKe _ _ _ _ _ _ _ _ _ _), ?_, Fr.trans i5 (hF _ _ _ _ _ _ _ _ _ _),
      cst_of i6 (hF _ _ _ _ _ _ _ _ _ _) (by decide)⟩, ?_, ?_⟩, by omega⟩
    · rw [List.take_succ_eq_append_getElem hk, List.map_append, List.map_singleton, ← List.append_assoc]
      exact GW.put' i1 eTmp (by vsimp [DS.adv]) (by vsimp [DS.adv]) (by rw [tabRec_eq, ← hx]; vsimp [DS.adv, dKW, dVW, dG2, hx2])
    · vsimp [DS.put, DS.adv, i2]
    · intro m hm1 hm2
      simp [DS.put, DS.adv, DS.set, Function.update_of_ne hm1, Function.update_of_ne hm2, i4 m hm1 hm2]
    · vsimp [DS.put, DS.adv, hdk]
    · vsimp [DS.put, DS.adv, hdm]
  · rintro e ⟨⟨i1, i2, i3, i4, i5, i6⟩, _, _⟩
    rw [List.take_of_length_le le_rfl] at i1
    exact ⟨i1, i3, i4, by rw [i2], i5, i6⟩

end NearCubicGates.Close.Cells.RecordEmission

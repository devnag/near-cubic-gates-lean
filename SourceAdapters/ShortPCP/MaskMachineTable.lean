import SourceAdapters.ShortPCP.MaskMachineKit
import SourceAdapters.ShortPCP.MasksSpec

/-!
# The mask machine: `r0 = max(rand_{RS,=}(f), f)` by a table

 (Step 2 of `thm:short-pcp-ours`): the four sub-verifiers share one random string; on a domain of
dimension `f > η` they use `rand_{RS,=}(f)` or `max(rand_{RS,=}(f), f)` coins, so `r0 = max(rand_{RS,=}(f), f)`
(`Field6.r0f`, `r0_eq`). `rand_{RS,=}` is the recursion (27) of BCGT13 Lemma C.9 (W `PublishedStatements/
BCGT13.lean:193`), which `MasksSpec.randEq_step` puts in table form: entry `κ` is `randStep` of two earlier entries
`⌊κ/2⌋ + 2` and `⌈κ/2⌉`. The machine fills the table `κ = 0, 1, …, f` in record store `sT` (seeking by rewinding),
then takes the maximum with `f`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells
open NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP (randStep randEq_step r0f)

/-- `rand_{RS,=}(κ)` for the tuple `(2, 4, 0, 1)` of Theorem 11.1. -/
abbrev rq (κ : ℕ) : ℕ := NearCubicGates.Published.BCGT13.randEq NearCubicGates.Adapters.Joins.SingleRun.tuple0 κ

theorem rq_step (κ : ℕ) :
    rq κ = if κ ≤ 4 then 0 else 1 + max ((κ + 1) / 2 + rq (κ / 2 + 2)) (κ / 2 + 1 + rq ((κ + 1) / 2)) := by
  rw [rq, randEq_step]; rfl

theorem rq_le (κ : ℕ) : rq κ ≤ 4 * κ := by
  induction κ using Nat.strong_induction_on with
  | _ κ ih =>
    rw [rq_step]
    split_ifs with h
    · omega
    · have h1 := ih (κ / 2 + 2) (by omega)
      have h2 := ih ((κ + 1) / 2) (by omega)
      have h3 : (κ + 1) / 2 + rq (κ / 2 + 2) ≤ 4 * κ - 1 := by omega
      have h4 : κ / 2 + 1 + rq ((κ + 1) / 2) ≤ 4 * κ - 1 := by omega
      have := max_le h3 h4
      omega

theorem r0f_le (f : ℕ) : r0f f ≤ 4 * f := by
  unfold r0f; exact max_le (rq_le f) (by omega)

/-! ## Variables and the store -/

def sT : Fin MM := ⟨0, by decide⟩

def vF : Var := ⟨60, by decide⟩
def vR : Var := ⟨62, by decide⟩
def tK : Var := ⟨69, by decide⟩
def tF1 : Var := ⟨70, by decide⟩
def tV : Var := ⟨71, by decide⟩
def tH : Var := ⟨72, by decide⟩
def tRm : Var := ⟨73, by decide⟩
def tI : Var := ⟨74, by decide⟩
def tX1 : Var := ⟨75, by decide⟩
def tX2 : Var := ⟨76, by decide⟩
def tA : Var := ⟨77, by decide⟩
def tB : Var := ⟨78, by decide⟩
def tc5 : Var := ⟨79, by decide⟩
def sc : Var := ⟨80, by decide⟩
def sJk : Var := ⟨81, by decide⟩
def tQ : Var := ⟨82, by decide⟩

/-- The table of the first `κ` entries. -/
def tab (κ : ℕ) : List ℕ := (List.range κ).map rq

theorem tab_length (κ : ℕ) : (tab κ).length = κ := by simp [tab]

theorem tab_getD {κ j : ℕ} (h : j < κ) : (tab κ).getD j 0 = rq j := by
  simp [tab, List.getD_eq_getElem?_getD, h]

theorem putAt_tab (κ : ℕ) : putAt (tab κ) κ (rq κ) = tab (κ + 1) := by
  unfold putAt; simp [tab, List.range_succ]

/-! ## Seeking: `rc sT := i` -/

def seekS (i : Var) : Sc :=
  .seq (.op (.rwM sT)) (.seq (.op (.zero sc)) (.loop (.lt sc i) (.seq (.op (.rdM sT sJk)) (.op (.inc sc)))))

def seekSet : List Var := [sc, sJk]

theorem seekS_spec (C : Ctx) (a : Ds) (i : Var) (hi : i ∉ seekSet) (len : ℕ) (hlen : (a.ram sT).length = len)
    (hrc : a.rc sT ≤ len) (hk : a.env i ≤ len) (hW : len + 1 < 2 ^ C.Wd) :
    Runs C (seekS i) a (6 * len + 10) seekSet [] (fun b => b.ram = a.ram ∧ b.rc sT = a.env i) := by
  set k := a.env i with hkdef
  let Inv : ℕ → Ds → Prop := fun j b => b.ram = a.ram ∧ b.rc sT = j ∧ b.env sc = j ∧ b.env i = k
  have hloop : ∀ b, Inv 0 b → Runs C (.loop (.lt sc i) (.seq (.op (.rdM sT sJk)) (.op (.inc sc)))) b
      (k * (3 + 2) + 2) seekSet [] (Inv k) := by
    intro b0 hb0
    refine Runs.loopN0F (wf_lt (by simp [seekSet] at hi; exact fun h => hi.1 h.symm)) k 3 Inv b0
      (fun j hj b _ ⟨b1, b2, b3, b4⟩ => ?_) (fun b _ ⟨_, _, b3, b4⟩ => by simp [b3, b4]) hb0
    refine ⟨by simp [b3, b4, hj], ?_⟩
    refine Runs.op1 (r_rdM C seekSet b sT sJk (by decide) (by rw [b2, b1, hlen]; omega)) ?_ (by norm_num)
    refine Runs.last (r_inc C seekSet _ sc (by decide) (by norm_env; rw [b3]; omega)) (fun _ => ?_) le_rfl
    refine ⟨by simp [DS.adv, b1], by simp [DS.adv, b2], by norm_env; rw [b3], ?_⟩
    have hsi : i ≠ sc := fun h => hi (by simp [seekSet, h])
    have hsj : i ≠ sJk := fun h => hi (by simp [seekSet, h])
    simp only [DS.env_set, adv_env, Function.update_apply, if_neg hsi, if_neg hsj]; exact b4
  unfold seekS
  refine Runs.call0 (r_rwM C seekSet a sT) (fun b _ hb => ?_) (by omega)
  subst hb
  refine Runs.op1 (r_zero C seekSet _ sc (by decide)) ?_ (by omega)
  have hsi : i ≠ sc := fun h => hi (by simp [seekSet, h])
  refine (hloop _ ⟨by simp [DS.rew], by simp [DS.rew], by norm_env, ?_⟩).mono ?_ (List.Subset.refl _)
    (fun b _ ⟨b1, b2, _, _⟩ => ⟨by rw [b1], b2⟩)
  · simp only [DS.env_set, rew_env, Function.update_apply, if_neg hsi]; rfl
  · omega

/-! ## One entry: `tV := randStep rq κ` from the table of the first `κ` entries -/

/-- The recursive case `κ > 4` (BCGT13 (27)): read entries `⌊κ/2⌋ + 2` and `⌈κ/2⌉`; `1 + max(…)`. -/
def bigS : Sc :=
  .seq (.op (.dm tK v2 tH tRm)) (.seq (.op (.copy tI tH)) (.seq (.op (.inc tI)) (.seq (.op (.inc tI))
  (.seq (seekS tI) (.seq (.op (.rdM sT tX1))
  (.seq (.op (.copy tI tH)) (.seq (.op (.add tI tRm))
  (.seq (seekS tI) (.seq (.op (.rdM sT tX2))
  (.seq (.op (.copy tA tI)) (.seq (.op (.add tA tX1))
  (.seq (.op (.copy tB tH)) (.seq (.op (.inc tB)) (.seq (.op (.add tB tX2))
  (.seq (.ite (.lt tA tB) (.op (.copy tA tB)) (.op (.zero tQ)))
  (.seq (.op (.copy tV tA)) (.op (.inc tV))))))))))))))))))

def bigSet : List Var := [tV, tH, tRm, tI, tX1, tX2, tA, tB, tQ, sc, sJk]

def bigCost (κ : ℕ) : ℕ := 12 * κ + 80

/-- The maximum by one comparison. -/
theorem maxTail (C : Ctx) (c : Ds) (A B : ℕ) (hA : c.env tA = A) (hB : c.env tB = B) :
    Runs C (.ite (.lt tA tB) (.op (.copy tA tB)) (.op (.zero tQ))) c 2 bigSet []
      (fun d => d.env tA = max A B ∧ d.ram = c.ram ∧ d.rc = c.rc) := by
  by_cases h : A < B
  · refine Runs.iteT (wf_lt (by decide)) (by simp [hA, hB, h]) ?_ (by norm_num)
    refine Runs.last (r_copy C bigSet c tA tB (by decide) (by decide)) (fun _ => ?_) le_rfl
    refine ⟨?_, rfl, rfl⟩; norm_env; rw [hB]; omega
  · refine Runs.iteF (wf_lt (by decide)) (by simp [hA, hB, h]) ?_ (by norm_num)
    refine Runs.last (r_zero C bigSet c tQ (by decide)) (fun _ => ?_) le_rfl
    refine ⟨?_, rfl, rfl⟩; norm_env; rw [hA]; omega

theorem bigS_spec (C : Ctx) (a : Ds) (κ : ℕ) (h5 : 5 ≤ κ) (hram : a.ram sT = tab κ) (hrc : a.rc sT ≤ κ)
    (hK : a.env tK = κ) (h2 : a.env v2 = 2) (hW : 16 * (κ + 2) < 2 ^ C.Wd) :
    Runs C bigS a (bigCost κ) bigSet [] (fun b => b.env tV = rq κ ∧ b.ram = a.ram ∧ b.rc sT ≤ κ) := by
  have hlen : (a.ram sT).length = κ := by rw [hram, tab_length]
  have hr1 := rq_le (κ / 2 + 2)
  have hr2 := rq_le ((κ + 1) / 2)
  unfold bigS
  have f0 := Fx.refl bigSet a
  refine Runs.op1B f0 (r_dm C bigSet a tK v2 tH tRm (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h2]; norm_num) (by rw [h2]; omega)) (fun f0 => ?_)
    (by unfold bigCost; omega)
  refine Runs.op1B f0 (r_copy C bigSet _ tI tH (by decide) (by decide)) (fun f0 => ?_) (by unfold bigCost; omega)
  refine Runs.op1B f0 (r_inc C bigSet _ tI (by decide) (by norm_env; rw [hK, h2]; omega)) (fun f0 => ?_)
    (by unfold bigCost; omega)
  refine Runs.op1B f0 (r_inc C bigSet _ tI (by decide) (by norm_env; rw [hK, h2]; omega)) (fun f0 => ?_)
    (by unfold bigCost; omega)
  refine Runs.callS0B f0 (seekS_spec C _ tI (by decide) κ (by simpa using hlen) (by simpa using hrc)
    (by norm_env; rw [hK, h2]; omega) (by omega)) (by decide) (fun c1 fl f1 ⟨c1ram, c1rc⟩ => ?_)
    (by unfold bigCost; omega)
  have c1H : c1.env tH = κ / 2 := by rw [fl.env tH (by decide)]; norm_env; rw [hK, h2]
  have c1R : c1.env tRm = κ % 2 := by rw [fl.env tRm (by decide)]; norm_env; rw [hK, h2]
  have c1two : c1.env v2 = 2 := by rw [f1.env v2 (by decide)]; exact h2
  have c1rc' : c1.rc sT = κ / 2 + 2 := by rw [c1rc]; norm_env; rw [hK, h2]
  have c1tab : c1.ram sT = tab κ := by rw [c1ram]; simpa using hram
  refine Runs.op1B f1 (r_rdM C bigSet c1 sT tX1 (by decide) (by rw [c1rc', c1tab, tab_length]; omega))
    (fun f1 => ?_) (by unfold bigCost; omega)
  refine Runs.op1B f1 (r_copy C bigSet _ tI tH (by decide) (by decide)) (fun f1 => ?_) (by unfold bigCost; omega)
  refine Runs.op1B f1 (r_add C bigSet _ tI tRm (by decide) (by decide) (by norm_env; rw [c1H, c1R]; omega))
    (fun f1 => ?_) (by unfold bigCost; omega)
  refine Runs.callS0B f1 (seekS_spec C _ tI (by decide) κ (by simp [DS.adv, c1tab, tab_length])
    (by simp [DS.adv, c1rc']; omega) (by norm_env; rw [c1H, c1R]; omega) (by omega)) (by decide)
    (fun c2 fl f2 ⟨c2ram, c2rc⟩ => ?_) (by unfold bigCost; omega)
  have c2H : c2.env tH = κ / 2 := by rw [fl.env tH (by decide)]; norm_env; exact c1H
  have c2X1 : c2.env tX1 = rq (κ / 2 + 2) := by
    rw [fl.env tX1 (by decide)]; norm_env; rw [c1tab, c1rc', tab_getD (by omega)]
  have c2I : c2.env tI = (κ + 1) / 2 := by
    rw [fl.env tI (by decide)]; norm_env; rw [c1H, c1R]; omega
  have c2rc' : c2.rc sT = (κ + 1) / 2 := by rw [c2rc]; norm_env; rw [c1H, c1R]; omega
  have c2tab : c2.ram sT = tab κ := by rw [c2ram]; simp [DS.adv, c1tab]
  have c2ram' : c2.ram = a.ram := by rw [c2ram]; simp [DS.adv, c1ram]
  refine Runs.op1B f2 (r_rdM C bigSet c2 sT tX2 (by decide) (by rw [c2rc', c2tab, tab_length]; omega))
    (fun f2 => ?_) (by unfold bigCost; omega)
  refine Runs.op1B f2 (r_copy C bigSet _ tA tI (by decide) (by decide)) (fun f2 => ?_) (by unfold bigCost; omega)
  refine Runs.op1B f2 (r_add C bigSet _ tA tX1 (by decide) (by decide) (by norm_env; rw [c2I, c2X1]; omega))
    (fun f2 => ?_) (by unfold bigCost; omega)
  refine Runs.op1B f2 (r_copy C bigSet _ tB tH (by decide) (by decide)) (fun f2 => ?_) (by unfold bigCost; omega)
  refine Runs.op1B f2 (r_inc C bigSet _ tB (by decide) (by norm_env; rw [c2H]; omega)) (fun f2 => ?_)
    (by unfold bigCost; omega)
  have hX2 : (c2.ram sT).getD (c2.rc sT) 0 = rq ((κ + 1) / 2) := by rw [c2tab, c2rc', tab_getD (by omega)]
  refine Runs.op1B f2 (r_add C bigSet _ tB tX2 (by decide) (by decide) (by norm_env; rw [c2H, hX2]; omega))
    (fun f2 => ?_) (by unfold bigCost; omega)
  refine Runs.callS0B f2 (maxTail C _ ((κ + 1) / 2 + rq (κ / 2 + 2)) (κ / 2 + 1 + rq ((κ + 1) / 2))
    (by norm_env; rw [c2I, c2X1]) (by norm_env; rw [c2H, hX2])) (List.Subset.refl _)
    (fun c3 _ f3 ⟨c3A, c3ram, c3rc⟩ => ?_) (by unfold bigCost; omega)
  have hmax := max_le (show (κ + 1) / 2 + rq (κ / 2 + 2) ≤ 6 * κ by omega)
    (show κ / 2 + 1 + rq ((κ + 1) / 2) ≤ 6 * κ by omega)
  refine Runs.op1B f3 (r_copy C bigSet _ tV tA (by decide) (by decide)) (fun f3 => ?_) (by unfold bigCost; omega)
  refine Runs.lastB f3 (r_inc C bigSet _ tV (by decide) (by norm_env; rw [c3A]; omega)) (fun _ => ?_)
    (by unfold bigCost; omega)
  refine ⟨?_, ?_, ?_⟩
  · norm_env; rw [c3A, rq_step κ, if_neg (by omega)]; omega
  · simp only [DS.set_ram]; rw [c3ram]; simp [DS.adv, c2ram']
  · simp only [DS.set_rc]; rw [c3rc]; simp [DS.adv, c2rc']; omega

/-! ## The table and `r0` -/

/-- One pass: entry `κ` (zero for `κ ≤ 4`, else `bigS`), appended at the end of the store. -/
def tabBody : Sc :=
  .seq (.ite (.lt tK tc5) (.op (.zero tV)) bigS) (.seq (seekS tK) (.seq (.op (.wrM sT tV)) (.op (.inc tK))))

def loopSet : List Var := tK :: bigSet

def tabPass (f : ℕ) : ℕ := bigCost f + 6 * f + 20

/-- **Table.** `vR := max(rand_{RS,=}(f), f) = r0f f` for `vF = f`, from an empty store `sT`. -/
def tableS : Sc :=
  .seq (.op (.zero tK)) (.seq (.op (.copy tc5 v2)) (.seq (.op (.add tc5 v2)) (.seq (.op (.inc tc5))
  (.seq (.op (.copy tF1 vF)) (.seq (.op (.inc tF1))
  (.seq (.loop (.lt tK tF1) tabBody)
  (.seq (.op (.copy vR tV)) (.ite (.lt vR vF) (.op (.copy vR vF)) (.op (.zero tQ))))))))))

def tableSet : List Var := [vR, tF1, tc5, tK, tV, tH, tRm, tI, tX1, tX2, tA, tB, tQ, sc, sJk]

def tableCost (f : ℕ) : ℕ := (f + 1) * (tabPass f + 2) + 40

theorem tabBody_spec (C : Ctx) (a : Ds) (f κ : ℕ) (hκ : κ ≤ f) (hram : a.ram sT = tab κ) (hrc : a.rc sT ≤ κ)
    (hK : a.env tK = κ) (h2 : a.env v2 = 2) (h5 : a.env tc5 = 5) (hW : 16 * (f + 3) < 2 ^ C.Wd) :
    Runs C tabBody a (tabPass f) loopSet []
      (fun b => b.ram sT = tab (κ + 1) ∧ b.rc sT ≤ κ + 1 ∧ b.env tK = κ + 1 ∧ b.env tV = rq κ) := by
  unfold tabBody
  refine Runs.callS0B (Fx.refl loopSet a) (n := bigCost κ + 1) (Q1 := fun b => b.env tV = rq κ ∧
    b.ram sT = tab κ ∧ b.rc sT ≤ κ ∧ b.env tK = κ) ?_ (List.Subset.refl _) (fun c _ _ ⟨c1, c2, c3, c4⟩ => ?_)
    (by unfold tabPass bigCost; omega)
  · by_cases hs : κ < 5
    · refine Runs.iteT (wf_lt (by decide)) (by simp [hK, h5, hs]) ?_ (by omega)
      refine Runs.last (r_zero C loopSet a tV (by decide)) (fun _ => ?_) (by unfold bigCost; omega)
      refine ⟨?_, hram, hrc, by norm_env; exact hK⟩
      norm_env; rw [rq_step, if_pos (by omega)]
    · refine Runs.iteF (wf_lt (by decide)) (by simp [hK, h5, hs]) ?_ (by omega)
      refine Runs.lastS (bigS_spec C a κ (by omega) hram hrc hK h2 (by omega)) (by decide)
        (fun b hf ⟨b1, b2, b3⟩ => ⟨b1, by rw [b2]; exact hram, b3, by rw [hf.env tK (by decide)]; exact hK⟩)
        (by omega)
  · have hlen : (c.ram sT).length = κ := by rw [c2, tab_length]
    refine Runs.callS0B (Fx.refl loopSet c) (seekS_spec C c tK (by decide) κ hlen c3 (by rw [c4]) (by omega))
      (by decide) (fun d dl _ ⟨d1, d2⟩ => ?_) (by unfold tabPass bigCost; omega)
    have dK : d.env tK = κ := by rw [dl.env tK (by decide), c4]
    have dV : d.env tV = rq κ := by rw [dl.env tV (by decide), c1]
    have d2' : d.rc sT = κ := by rw [d2, c4]
    have d1' : d.ram sT = tab κ := by rw [d1, c2]
    refine Runs.op1 (r_wrM C loopSet d sT tV (by rw [d2', d1', tab_length])) ?_ (by unfold tabPass bigCost; omega)
    refine Runs.last (r_inc C loopSet _ tK (by decide) (by simp only [put_env]; rw [dK]; omega)) (fun _ => ?_)
      (by unfold tabPass bigCost; omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [DS.set_ram, DS.put, Function.update_self]
      rw [d1', d2', dV, putAt_tab]
    · simp only [DS.set_rc, DS.put, Function.update_self]; rw [d2']
    · norm_env; rw [dK]
    · norm_env; exact dV

theorem tableTail_spec (C : Ctx) (s : Ds) (f : ℕ) (hF : s.env vF = f) (s2 : s.env v2 = 2) (s5 : s.env tc5 = 5)
    (sF1 : s.env tF1 = f + 1) (sK : s.env tK = 0) (sram : s.ram sT = []) (src : s.rc sT = 0)
    (hW : 16 * (f + 3) < 2 ^ C.Wd) :
    Runs C (.seq (.loop (.lt tK tF1) tabBody)
      (.seq (.op (.copy vR tV)) (.ite (.lt vR vF) (.op (.copy vR vF)) (.op (.zero tQ))))) s
      ((f + 1) * (tabPass f + 2) + 10) tableSet [] (fun b => b.env vR = r0f f) := by
  let Inv : ℕ → Ds → Prop := fun j b => b.ram sT = tab j ∧ b.rc sT ≤ j ∧ b.env tK = j ∧
    (1 ≤ j → b.env tV = rq (j - 1))
  have hloop : Runs C (.loop (.lt tK tF1) tabBody) s ((f + 1) * (tabPass f + 2) + 2) loopSet [] (Inv (f + 1)) := by
    refine Runs.loopN0F (wf_lt (by decide)) (f + 1) (tabPass f) Inv s (fun j hj b hfb ⟨b1, b2, b3, _⟩ => ?_)
      (fun b hfb ⟨_, _, b3, _⟩ => ?_) ⟨by rw [sram]; rfl, by rw [src], sK, fun h => by omega⟩
    · have bF1 : b.env tF1 = f + 1 := by rw [hfb.env tF1 (by decide), sF1]
      refine ⟨by simp [b3, bF1, hj], ?_⟩
      refine (tabBody_spec C b f j (by omega) b1 b2 b3 (by rw [hfb.env v2 (by decide), s2])
        (by rw [hfb.env tc5 (by decide), s5]) hW).mono le_rfl (List.Subset.refl _)
        (fun d _ ⟨d1, d2, d3, d4⟩ => ⟨d1, d2, d3, fun _ => by simpa using d4⟩)
    · have bF1 : b.env tF1 = f + 1 := by rw [hfb.env tF1 (by decide), sF1]
      simp [b3, bF1]
  refine Runs.callS0B (Fx.refl tableSet s) hloop (by decide) (fun b _ f1 ⟨_, _, _, b4⟩ => ?_) (by omega)
  have bV : b.env tV = rq f := by simpa using b4 (by omega)
  have bF : b.env vF = f := by rw [f1.env vF (by decide), hF]
  refine Runs.op1B f1 (r_copy C tableSet b vR tV (by decide) (by decide)) (fun _ => ?_) (by omega)
  by_cases hlt : rq f < f
  · refine Runs.iteT (wf_lt (by decide)) (by norm_env; rw [bV, bF]; simpa using hlt) ?_ (by omega)
    refine Runs.last (r_copy C tableSet _ vR vF (by decide) (by decide)) (fun _ => ?_) (by omega)
    norm_env; rw [bF]; unfold r0f; rw [max_eq_right hlt.le]
  · refine Runs.iteF (wf_lt (by decide)) (by norm_env; rw [bV, bF]; simpa using hlt) ?_ (by omega)
    refine Runs.last (r_zero C tableSet _ tQ (by decide)) (fun _ => ?_) (by omega)
    norm_env; rw [bV]; unfold r0f; exact (max_eq_left (not_lt.1 hlt)).symm

theorem tableS_spec (C : Ctx) (a : Ds) (f : ℕ) (hF : a.env vF = f) (h2 : a.env v2 = 2) (hram : a.ram sT = [])
    (hrc : a.rc sT = 0) (hW : 16 * (f + 3) < 2 ^ C.Wd) :
    Runs C tableS a (tableCost f) tableSet [] (fun b => b.env vR = r0f f) := by
  unfold tableS
  refine Runs.op1 (r_zero C tableSet a tK (by decide)) ?_ (by unfold tableCost; omega)
  refine Runs.op1 (r_copy C tableSet _ tc5 v2 (by decide) (by decide)) ?_ (by unfold tableCost; omega)
  refine Runs.op1 (r_add C tableSet _ tc5 v2 (by decide) (by decide) (by norm_env; rw [h2]; omega)) ?_
    (by unfold tableCost; omega)
  refine Runs.op1 (r_inc C tableSet _ tc5 (by decide) (by norm_env; rw [h2]; omega)) ?_ (by unfold tableCost; omega)
  refine Runs.op1 (r_copy C tableSet _ tF1 vF (by decide) (by decide)) ?_ (by unfold tableCost; omega)
  refine Runs.op1 (r_inc C tableSet _ tF1 (by decide) (by norm_env; rw [hF]; omega)) ?_ (by unfold tableCost; omega)
  refine (tableTail_spec C _ f (by norm_env; exact hF) (by norm_env; exact h2) (by norm_env; rw [h2])
    (by norm_env; rw [hF]) (by norm_env) (by simpa using hram) (by simpa using hrc) hW).costLe
    (by unfold tableCost; omega)

end NearCubicGates.Adapters.ShortPCP.MaskMachine

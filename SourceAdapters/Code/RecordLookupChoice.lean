import SourceAdapters.Code.RecordLookupData

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": retain an equality's index only while no earlier match was saved. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.RecordLookup
open NearCubicGates.Close.Cells

def choose (target len result : Fin VV) : St VV MM :=
  .ite (.eq vJ target) (.ite (.eq result len) (.op (.copy result c0)) skipS) skipS

theorem choose_spec (C : Ctx) (target len result : Fin VV)
    (htj : target ≠ vJ) (hrl : result ≠ len) (hr0 : result ≠ c0) (hrj : result ≠ vJ)
    (a : DS VV MM) :
    Hs C (choose target len result) a 3 (fun b =>
      b.env result = (if a.env vJ = a.env target ∧ a.env result = a.env len
        then a.env c0 else a.env result) ∧ Same a b ∧ Fr a b [vJ, result]) := by
  have skipRun : Hs C skipS a 1 (fun b =>
      b.env result = a.env result ∧ Same a b ∧ Fr a b [vJ, result]) := by
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨DS.set_env_ne _ _ hrj, Same.set _ _ _, Fr.set _ _ (by simp)⟩
  by_cases ht : a.env vJ = a.env target
  · by_cases hr : a.env result = a.env len
    · have hc : Hs C (.op (.copy result c0)) a 1 (fun b =>
          b.env result = a.env c0 ∧ Same a b ∧ Fr a b [vJ, result]) := by
        refine Hs.mono (hs_copy C result c0 a hr0) le_rfl ?_
        rintro b rfl
        exact ⟨DS.set_env_self .., Same.set _ _ _, Fr.set _ _ (by simp)⟩
      have hi := Hs.iteT (c := .eq result len) (u := skipS) hrl (by simp [Cnd.eval, hr]) hc
      have ho := Hs.iteT (c := .eq vJ target) (u := skipS) (Ne.symm htj) (by simp [Cnd.eval, ht]) hi
      simpa [choose, ht, hr] using ho
    · have hi := Hs.iteF (c := .eq result len) (s := .op (.copy result c0)) hrl
        (by simp [Cnd.eval, hr]) skipRun
      have ho := Hs.iteT (c := .eq vJ target) (u := skipS) (Ne.symm htj) (by simp [Cnd.eval, ht]) hi
      simpa [choose, ht, hr] using ho
  · have ho := Hs.iteF (c := .eq vJ target)
      (s := .ite (.eq result len) (.op (.copy result c0)) skipS)
      (Ne.symm htj) (by simp [Cnd.eval, ht]) skipRun
    simpa [choose, ht] using ho.mono (by omega : 1 + 1 ≤ 3) (fun _ h => h)

end NearCubicGates.Adapters.Code.RecordLookup

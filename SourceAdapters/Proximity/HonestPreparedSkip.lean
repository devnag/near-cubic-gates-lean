import SourceAdapters.Proximity.HonestSource

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": advance through a counted raw source word by
actual input reads, preserving the source-length register and all stores. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicGates.Close.Cells
open SourceRequests (State Script lengthReg)

def skipSource : Script := forS c0 lengthReg (.op (.rdI t0))

theorem skip_source (C : Ctx) (a : State) (bits pre tail : List Bool)
    (hin : C.inp = pre ++ bits ++ tail) (hip : a.ip = pre.length)
    (hlen : a.env lengthReg = bits.length) (hwidth : bits.length < 2 ^ C.Wd) :
    Hs C skipSource a (5 * bits.length + 4) (fun b =>
      b.ip = a.ip + bits.length ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, t0]) := by
  let I : ℕ → State → Prop := fun k b => b.ip = a.ip + k ∧ b.out = a.out ∧ b.ram = a.ram ∧
    b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, t0]
  have loopRun := forS_spec' (C := C) c0 lengthReg (by decide) (.op (.rdI t0)) a bits.length hwidth I 1
    (fun k b v ⟨hi, ho, hm, hr, hki, hko, hkc, hf⟩ =>
      ⟨hi, ho, hm, hr, hki, hko, hkc, hf.trans (Fr.set b v (by simp))⟩)
    ⟨by omega, rfl, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩ hlen ?_
  · exact loopRun.mono (by omega) (fun _ h => h.1)
  · intro k hk b ⟨hi, ho, hm, hr, hki, hko, hkc, hf⟩ hindex hlength
    have e := hs_rdI C t0 b (by rw [hi, hip, hin]; simp only [List.length_append]; omega)
    refine e.mono le_rfl ?_
    rintro d rfl
    refine ⟨⟨?_, ho, hm, hr, hki, hko, hkc, hf.trans (Fr.set b _ (by simp))⟩, ?_, ?_⟩
    · change b.ip + 1 = a.ip + (k + 1)
      omega
    · change (b.set t0 (bitOf C.inp b.ip)).env c0 = k
      rw [DS.set_env_ne _ _ (by decide : c0 ≠ t0), hindex]
    · change (b.set t0 (bitOf C.inp b.ip)).env lengthReg = bits.length
      rw [DS.set_env_ne _ _ (by decide : lengthReg ≠ t0), hlength]

end NearCubicGates.Adapters.Proximity.HonestPrepared

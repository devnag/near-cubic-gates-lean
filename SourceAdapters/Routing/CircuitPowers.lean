import SourceAdapters.Routing.CircuitLoops

/-! The coordinate compiler's shared Frobenius-power prefix. See `lem:generator`. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit
open NearCubicGates.Adapters.ACSP
variable {F : Type} [Field F]

def powerStep (x : ℕ) (_ : ℕ) (powers : List ℕ) : Builder F (List ℕ) := do
  let prev := powers.getLastD x
  let next ← pushGate (.mul prev prev)
  return powers ++ [next]

def powers {n : ℕ} (p : Poly n F) (len : ℕ) : List (Poly n F) :=
  (List.range len).map fun i => p ^ (2 ^ i)

@[simp] theorem powers_length {n : ℕ} (p : Poly n F) (len : ℕ) : (powers p len).length = len := by
  simp [powers]

theorem powers_getD {n : ℕ} (p : Poly n F) {i len : ℕ} (h : i < len) :
    (powers p len).getD i 0 = p ^ (2 ^ i) := by
  simp [powers, h]

theorem powers_succ {n : ℕ} (p : Poly n F) (len : ℕ) :
    powers p (len + 1) = powers p len ++ [p ^ (2 ^ len)] := by
  simp [powers, List.range_succ]

theorem powerStep_spec {n : ℕ} (p : Poly n F) (x r : ℕ) (ids : List ℕ)
    (gs : Gates F) (hw : WF n gs) (hpos : 0 < ids.length)
    (hr : Refs n gs ids (powers p ids.length)) :
    let result := (powerStep x r ids).run gs
    Ext n gs result.2 ∧ result.1.length = ids.length + 1 ∧
      Refs n result.2 result.1 (powers p (ids.length + 1)) ∧
      result.2.length = gs.length + 1 := by
  have hl : ids.getLastD x = ids.getD (ids.length - 1) x := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  have hp : Has n gs (ids.getLastD x) (p ^ (2 ^ (ids.length - 1))) := by
    have h := hr.getD (ids.length - 1) (by simp; omega) x 0
    rwa [← hl, powers_getD p (by omega)] at h
  let gs' := gs ++ [ArithGate.mul (ids.getLastD x) (ids.getLastD x)]
  have he : Ext n gs gs' := ⟨List.prefix_append _ _, wf_push hw _ ⟨hp.1, hp.1⟩⟩
  have hpow : p ^ (2 ^ (ids.length - 1)) * p ^ (2 ^ (ids.length - 1)) = p ^ (2 ^ ids.length) := by
    rw [← pow_two, ← pow_mul, ← pow_succ]
    congr 2
    omega
  have hnew : Has n gs' gs.length (p ^ (2 ^ ids.length)) := by
    simpa only [hpow] using has_mul hp hp
  change Ext n gs gs' ∧ (ids ++ [gs.length]).length = ids.length + 1 ∧
    Refs n gs' (ids ++ [gs.length]) (powers p (ids.length + 1)) ∧ gs'.length = gs.length + 1
  refine ⟨he, by simp, ?_, by simp [gs']⟩
  rw [powers_succ]
  exact List.rel_append (hr.mono he.initial) (.cons hnew .nil)

theorem powerLoop_spec {n : ℕ} (p : Poly n F) (x : ℕ) (rs : List ℕ) (ids : List ℕ)
    (gs : Gates F) (hw : WF n gs) (hpos : 0 < ids.length)
    (hr : Refs n gs ids (powers p ids.length)) :
    let result := (loop (powerStep x) rs ids).run gs
    Ext n gs result.2 ∧ result.1.length = ids.length + rs.length ∧
      Refs n result.2 result.1 (powers p (ids.length + rs.length)) ∧
      result.2.length = gs.length + rs.length := by
  induction rs generalizing ids gs with
  | nil =>
      change Ext n gs gs ∧ ids.length = ids.length + 0 ∧
        Refs n gs ids (powers p (ids.length + 0)) ∧ gs.length = gs.length + 0
      exact ⟨Ext.refl hw, by omega, by simpa using hr, by omega⟩
  | cons r rs ih =>
      let step := (powerStep x r ids).run gs
      obtain ⟨he, hl, hr', hg⟩ := powerStep_spec p x r ids gs hw hpos hr
      have hpos' : 0 < step.1.length := by change step.1.length = _ at hl; omega
      have hrs : Refs n step.2 step.1 (powers p step.1.length) := by
        change step.1.length = _ at hl
        simpa only [hl] using hr'
      obtain ⟨he', hl', hr'', hg'⟩ := ih step.1 step.2 he.wf hpos' hrs
      change Ext n gs ((loop (powerStep x) rs step.1).run step.2).2 ∧
        ((loop (powerStep x) rs step.1).run step.2).1.length = ids.length + (r :: rs).length ∧
        Refs n ((loop (powerStep x) rs step.1).run step.2).2
          ((loop (powerStep x) rs step.1).run step.2).1 (powers p (ids.length + (r :: rs).length)) ∧
        ((loop (powerStep x) rs step.1).run step.2).2.length = gs.length + (r :: rs).length
      refine ⟨he.trans he', ?_, ?_, ?_⟩
      · change step.1.length = _ at hl
        simp only [List.length_cons]
        omega
      · change step.1.length = _ at hl
        simpa only [hl, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hr''
      · change step.2.length = _ at hg
        simp only [List.length_cons]
        omega

end NearCubicGates.Adapters.Routing.Circuit
end

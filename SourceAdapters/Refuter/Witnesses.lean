import SourceAdapters.Refuter.Assembly
import SourceAdapters.Refuter.FaithfulPrefix

/-!
# `M(x_1)` is the disjunction over the enumerated witnesses (input 7, F06 condition)

proof of `lem:multitape-refuter`, Step 2: "Every run of `M` halts within `t_M(N) ≤ T(N)` steps and reads at most `⌊N/10⌋`
witness bits." With proof of `cor:framed-refuter` ("enumerate all `g(N)`-bit strings as `w_1,…,w_s`, where
`s=2^{g(N)}`") and CLW20 p.18 ("`M(x) = 1 ⇔ ∨_{w∈{0,1}^{g(n)}} V_M(x,T(n),w) = 1`"), this discharges
`WitnessesComplete` for every clock, using only `OrdinaryLittleO` (multiplier 1).

`machineValue` agrees with existential acceptance on exactly `⌊n/16⌋` witnesses: this
is `machineValue`'s definition through `OrdinaryWeakMachine.accepts`; the enumeration `unrank` is a
bijection from `[0, 2^g)` onto `BitInput g` (`unrank_surjective`).
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Theorem113

set_option autoImplicit false

theorem unrank_injective (g : ℕ) {i i' : ℕ} (hi : i < 2 ^ g) (hi' : i' < 2 ^ g)
    (h : unrank g i = unrank g i') : i = i' := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < g
  · have := congrFun h ⟨g - 1 - k, by omega⟩
    simp only [unrank] at this
    rwa [show g - 1 - (g - 1 - k) = k by omega] at this
  · have h1 : i < 2 ^ k := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : i' < 2 ^ k := lt_of_lt_of_le hi' (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

/-- Every `g`-bit witness is enumerated: it is `w_i` for some `i < 2^g`. -/
theorem unrank_surjective (g : ℕ) (w : BitInput g) : ∃ i < 2 ^ g, unrank g i = w := by
  let f : Fin (2 ^ g) → BitInput g := fun i => unrank g i.val
  have hinj : Function.Injective f := fun a b h =>
    Fin.ext (unrank_injective g a.isLt b.isLt h)
  have hcard : Fintype.card (Fin (2 ^ g)) = Fintype.card (BitInput g) := by simp
  obtain ⟨i, hi⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩).2 w
  exact ⟨i.val, i.isLt, hi⟩

/-- More fuel keeps an accepting framed run accepting. -/
theorem acceptsAt_mono (v : RepairOrdinary.Verifier) {f f' : ℕ} (h : f ≤ f') (x w : List Bool)
    (ha : v.acceptsAt f x w) : v.acceptsAt f' x w := by
  obtain ⟨r, hr, hacc⟩ := ha
  refine ⟨r, ?_, hacc⟩
  have := runFrom_mono v.machine f _ r hr (f' - f)
  rwa [Nat.add_sub_of_le h] at this

/-- A weak machine accepts iff some witness is accepted within its declared runtime (copied from
`Audit.Step2.Input7A.accepts_iff_bounded`). -/
theorem accepts_iff_bounded (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) :
    M.accepts n x ↔ ∃ w : BitInput (n / 16),
      M.verifier.acceptsAt (M.runtime n) (List.ofFn x) (List.ofFn w) := by
  constructor
  · rintro ⟨w, fuel, r, hr, hacc⟩
    obtain ⟨r0, hr0⟩ := M.halts n x w
    refine ⟨w, r0, hr0, ?_⟩
    have := runFrom_unique M.verifier.machine _ fuel (M.runtime n) r r0 hr hr0
    subst this
    exact hacc
  · rintro ⟨w, h⟩
    exact ⟨w, M.runtime n, h⟩

/-- **`WitnessesComplete` holds for every clock** (proof of `lem:multitape-refuter`). -/
theorem witnessesComplete (T : ℕ → ℕ) : WitnessesComplete T := by
  intro M hM
  obtain ⟨onset, hon⟩ := hM 1 (by norm_num)
  refine ⟨onset, fun N hN => ?_⟩
  have hrt : M.runtime N ≤ T N := by simpa using hon N hN
  unfold CompleteWitnesses memberData hitData machineValue
  simp only [decide_eq_true_eq]
  constructor
  · intro hacc
    obtain ⟨w, hw⟩ := (accepts_iff_bounded M N _).mp hacc
    obtain ⟨i, hi, rfl⟩ := unrank_surjective (N / 16) w
    exact ⟨i, hi, acceptsAt_mono _ hrt _ _ hw⟩
  · rintro ⟨i, _, hi⟩
    obtain ⟨r, hr, hacc⟩ := hi
    exact ⟨unrank (N / 16) i, T N, r, hr, hacc⟩

/-- **F06, full field, with `WitnessesComplete` discharged**: the consumer from the two internal
joins at every admissible clock. -/
theorem clw20_theorem1_13_of_parts
    (parts : ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T →
      ∃ H : OrdinaryHierarchy T, HierarchyRecurrence T H ∧ RefuterRealization T) :
    CLW20_Theorem1_13 :=
  clw20_theorem1_13_of_joins parts (fun T _ => witnessesComplete T)

end NearCubicGates.Adapters.Refuter

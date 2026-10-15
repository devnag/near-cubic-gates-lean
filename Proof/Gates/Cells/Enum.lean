import Mathlib.Tactic
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicGates.Close.Interfaces.Formats

def vecsM : List ℕ → List (List ℕ)
  | [] => [[]]
  | b :: bs => (List.range b).flatMap fun a => (vecsM bs).map (a :: ·)

/-- The mixed-radix digits of `t` (most significant first). -/
def digitsM : List ℕ → ℕ → List ℕ
  | [], _ => []
  | b :: bs, t => (t / bs.prod) % b :: digitsM bs t

theorem digitsM_length : ∀ (bs : List ℕ) (t : ℕ), (digitsM bs t).length = bs.length
  | [], _ => rfl
  | _ :: bs, t => by simp [digitsM, digitsM_length bs t]

theorem digitsM_mod : ∀ (bs : List ℕ) (t : ℕ), digitsM bs (t % bs.prod) = digitsM bs t
  | [], _ => rfl
  | c :: cs, t => by
    simp only [digitsM, List.prod_cons]
    congr 1
    · rw [mul_comm, Nat.mod_mul_right_div_self, Nat.mod_mod]
    · rw [← digitsM_mod cs (t % (c * cs.prod)), ← digitsM_mod cs t, Nat.mod_mod_of_dvd _ (Dvd.intro_left c rfl)]

theorem range_mul_flatMap (b Q : ℕ) :
    List.range (b * Q) = (List.range b).flatMap fun a => (List.range Q).map (a * Q + ·) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem vecsM_eq : ∀ bs : List ℕ, vecsM bs = (List.range bs.prod).map (digitsM bs)
  | [] => rfl
  | b :: bs => by
    simp only [vecsM, List.prod_cons, vecsM_eq bs]
    rw [range_mul_flatMap, List.map_flatMap]
    apply List.flatMap_congr
    intro a ha
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro u hu
    rw [List.mem_range] at ha hu
    simp only [Function.comp, digitsM]
    have hQ : 0 < bs.prod := by omega
    congr 1
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hu, zero_add, Nat.mod_eq_of_lt ha]
    · rw [← digitsM_mod bs (a * bs.prod + u), Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]

theorem vecsM_length (bs : List ℕ) : (vecsM bs).length = bs.prod := by rw [vecsM_eq]; simp

theorem mem_vecsM : ∀ (bs v : List ℕ), v ∈ vecsM bs ↔ v.length = bs.length ∧ ∀ i < v.length, v[i]! < bs[i]!
  | [], v => by
    simp only [vecsM, List.mem_singleton, List.length_nil]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, _⟩; exact List.eq_nil_of_length_eq_zero h
  | b :: bs, v => by
    simp only [vecsM, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨a, ha, w, hw, rfl⟩
      obtain ⟨h1, h2⟩ := (mem_vecsM bs w).1 hw
      refine ⟨by simp [h1], fun i hi => ?_⟩
      cases i with
      | zero => simpa using ha
      | succ i => simpa using h2 i (by simpa using hi)
    · rintro ⟨h1, h2⟩
      cases v with
      | nil => simp at h1
      | cons a w =>
        refine ⟨a, by simpa using h2 0 (by simp), w, (mem_vecsM bs w).2 ⟨by simpa using h1, fun i hi => ?_⟩, rfl⟩
        simpa using h2 (i + 1) (by simpa using hi)

theorem vecsM_nodup : ∀ bs : List ℕ, (vecsM bs).Nodup
  | [] => by simp [vecsM]
  | b :: bs => by
    simp only [vecsM]
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => (vecsM_nodup bs).map (fun _ _ h => by simpa using h), ?_⟩
    refine List.Pairwise.imp_of_mem ?_ List.nodup_range
    intro a a' _ _ hne
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨w, _, rfl⟩ ⟨w', _, h⟩
    simp at h; exact hne h.1.symm

theorem vecs_eq_vecsM (q : ℕ) : ∀ d : ℕ, vecs q d = vecsM (List.replicate d q)
  | 0 => rfl
  | d + 1 => by simp [vecs, vecsM, vecs_eq_vecsM q d, List.replicate_succ]

end NearCubicGates.Close.Cells

import Proof.Gates.CounterMachine.CellTablesCls3

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem lt_of_mem_vecs (q : ℕ) : ∀ (n : ℕ) (v : List ℕ), v ∈ vecs q n → ∀ x ∈ v, x < q
  | 0, v, h => by simp [vecs] at h; subst h; simp
  | n + 1, v, h => by
    simp only [vecs, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨a, ha, w, hw, rfl⟩ := h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact lt_of_mem_vecs q n w hw x hx

theorem descN_bound (r : CellReq B1 B2 cT) (id : ReqId) (hid : id ∈ reqIds r.c r.p) :
    (descN id).length ≤ 2 * (cellInput r).length + 6 ∧
      ∀ v ∈ descN id, v ≤ r.c.n + 2 * (cellInput r).length + 2 := by
  have sz := sizes r
  have hDd : dOf r.c r.p = roleCount r.c.kind * r.p.J + roleCount r.c.kind := by unfold dOf; ring
  unfold reqIds at hid
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at hid
  rcases hid with ⟨part, hpart, q, hq, κ, hκ, σ, hσ, rfl⟩ | ⟨ro, hro, (⟨j, hj, rfl⟩ | rfl)⟩
  · have hq' : q ∈ r.p.primes := (Finset.mem_sort _).mp hq
    have hqP := (sz.q q hq').1
    have hκl := length_of_mem_vecs q _ κ hκ
    have hσl := length_of_mem_vecs q _ σ hσ
    have hpc : partCode part ≤ 2 := by cases part with | none => decide | some b => cases b <;> decide
    have hDX := sz.D
    refine ⟨by simp [descN, hκl, hσl]; omega, fun v hv => ?_⟩
    simp only [descN, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with ((rfl | rfl | rfl | rfl) | hv) | hv
    · omega
    · omega
    · have := sz.P; omega
    · simp [hκl, hσl]; omega
    · have := lt_of_mem_vecs q _ κ hκ v hv; have := sz.P; omega
    · have := lt_of_mem_vecs q _ σ hσ v hv; have := sz.P; omega
  · refine ⟨by simp [descN], fun v hv => ?_⟩
    simp only [descN, List.mem_cons, List.mem_nil_iff, or_false] at hv
    have := sz.JX; have := sz.rc
    rcases hv with rfl | rfl | rfl <;> omega
  · refine ⟨by simp [descN], fun v hv => ?_⟩
    simp only [descN, List.mem_cons, List.mem_nil_iff, or_false] at hv
    have := sz.rc
    rcases hv with rfl | rfl | rfl <;> omega

theorem natWord_len_le (v : ℕ) : (natWord v).length ≤ 2 * v + 3 := by
  rw [Cells.natWord_length]; have := nbl_le_self v; omega

theorem tabCallInput_le (x : TabCallReq B1 B2 cT) :
    (tabCallInput x).length ≤ 20 * (x.r.c.n + (cellInput x.r).length + 3) ^ 2 := by
  obtain ⟨hl, hv⟩ := descN_bound x.r x.id x.mem
  set Z := x.r.c.n + (cellInput x.r).length + 3 with hZ
  have h1 : ((descN x.id).flatMap natWord).length ≤ (descN x.id).length * (2 * (2 * Z) + 3) := by
    rw [List.length_flatMap]
    have := List.sum_le_card_nsmul ((descN x.id).map fun v => (natWord v).length) (2 * (2 * Z) + 3)
      (fun y hy => by
        simp only [List.mem_map] at hy
        obtain ⟨v, hv', rfl⟩ := hy
        have := hv v hv'; have := natWord_len_le v; omega)
    simpa using this
  have h2 : (descN x.id).length * (2 * (2 * Z) + 3) ≤ (2 * Z) * (4 * Z + 3) := Nat.mul_le_mul (by omega) (by omega)
  show ((descN x.id).flatMap natWord ++ cellInput x.r).length ≤ _
  rw [List.length_append]
  nlinarith

/-! ## The chosen sizes -/

def b0Of (B1 B2 : ℕ) : ℕ := B1 + B2 + 13
def zeta : ℕ := 2 ^ 19 + 4

/-- The width, call-input and call-budget constants: `W = a₁2^{c₁L}`, `c₁ = e₀ + 2b₀`; `Lk = a₂2^{c₂L}`,
`c₂ = 2b₀`; `Bk = a₃2^{c₃L}` (times `2^{n−kLow}` by `zK`), `c₃ = e₀`. The exponents do not depend on `c_T`. -/
def zOf (B1 B2 C0 e0 : ℕ) : Sz :=
  ⟨C0 + 100 * zeta ^ 2 + 16, e0 + 2 * b0Of B1 B2, 20 * zeta ^ 2, 2 * b0Of B1 B2, C0 + 1, e0⟩

theorem Z_le (r : CellReq B1 B2 cT) :
    r.c.n + 1 + (cellInput r).length + 3 ≤ zeta * (r.c.n + 1) ^ b0Of B1 B2 := by
  have hX := cellInput_le r
  have h1 : 1 ≤ (r.c.n + 1) ^ b0Of B1 B2 := Nat.one_le_pow _ _ (by omega)
  have h2 : r.c.n + 1 ≤ (r.c.n + 1) ^ b0Of B1 B2 := by
    calc r.c.n + 1 = (r.c.n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by unfold b0Of; omega)
  unfold zeta b0Of at *
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg

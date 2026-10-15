import Proof.Gates.CellsGather.EmitSpec
import Proof.Gates.Cells.Format

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem rk_inj (b : ℕ) : ∀ (l l' : List ℕ), l.length = l'.length → (∀ x ∈ l, x < 2 ^ b) →
    (∀ x ∈ l', x < 2 ^ b) → rk b l = rk b l' → l = l'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen
  | x :: l, x' :: l', hlen, h1, h2, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rw [rk_cons, rk_cons, hlen] at he
    have r1 := rk_lt b l (fun z hz => h1 z (List.mem_cons_of_mem _ hz))
    have r2 := rk_lt b l' (fun z hz => h2 z (List.mem_cons_of_mem _ hz))
    rw [hlen] at r1
    have hx : x = x' := by
      have e1 : (x * 2 ^ (b * l'.length) + rk b l) / 2 ^ (b * l'.length) = x := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt r1, zero_add]
      have e2 : (x' * 2 ^ (b * l'.length) + rk b l') / 2 ^ (b * l'.length) = x' := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt r2, zero_add]
      rw [← e1, ← e2, he]
    subst hx
    have : rk b l = rk b l' := by omega
    rw [rk_inj b l l' hlen (fun z hz => h1 z (List.mem_cons_of_mem _ hz))
      (fun z hz => h2 z (List.mem_cons_of_mem _ hz)) this]

section K
variable (c : Call) (p : Params)

theorem mem_reqIds_residue {part : Option Bool} {q : ℕ} {κ σ : List ℕ} :
    ReqId.residue part q κ σ ∈ reqIds c p ↔ part ∈ parts c ∧ q ∈ p.primes.sort (· ≤ ·) ∧
      κ ∈ vecs q (roleCount c.kind * p.J) ∧ σ ∈ vecs q (roleCount c.kind) := by
  unfold reqIds
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨part', hp, q', hq, κ', hκ, σ', hσ, he⟩ | ⟨r, _, hm⟩)
    · cases he; exact ⟨hp, hq, hκ, hσ⟩
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hm
      rcases hm with ⟨j, _, he⟩ | he <;> cases he
  · rintro ⟨hp, hq, hκ, hσ⟩
    exact Or.inl ⟨part, hp, q, hq, κ, hκ, σ, hσ, rfl⟩

theorem keyFields_len (id : ReqId) (hid : id ∈ reqIds c p) :
    (keyFields id).length = if kindOf id = 0 then keyLen c p else 3 := by
  cases id with
  | residue part q κ σ =>
    obtain ⟨-, -, hκ, hσ⟩ := (mem_reqIds_residue c p).1 hid
    simp only [keyFields, kindOf, if_true, List.length_append, List.length_cons, List.length_nil,
      vecs_length q _ κ hκ, vecs_length q _ σ hσ]
    unfold keyLen; ring
  | digitMoment r j => simp [keyFields, kindOf]
  | phiMoment r => simp [keyFields, kindOf]

theorem partCode_inj {a b : Option Bool} (h : partCode a = partCode b) : a = b := by
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [partCode]

theorem keyFields_inj (id id' : ReqId) (hid : id ∈ reqIds c p) (hid' : id' ∈ reqIds c p)
    (h : keyFields id = keyFields id') : id = id' := by
  cases id with
  | residue part q κ σ =>
    cases id' with
    | residue part' q' κ' σ' =>
      obtain ⟨-, -, hκ, -⟩ := (mem_reqIds_residue c p).1 hid
      obtain ⟨-, -, hκ', -⟩ := (mem_reqIds_residue c p).1 hid'
      simp only [keyFields, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hl : κ.length = κ'.length := by rw [vecs_length q _ κ hκ, vecs_length q' _ κ' hκ']
      obtain ⟨h4, h5⟩ := List.append_inj h3 hl
      rw [partCode_inj h1, h2, h4, h5]
    | digitMoment r j => simp [keyFields] at h
    | phiMoment r => simp [keyFields] at h
  | digitMoment r j =>
    cases id' with
    | residue part' q' κ' σ' => simp [keyFields] at h
    | digitMoment r' j' => simp only [keyFields, List.cons.injEq, and_true, true_and] at h; rw [h.1, h.2]
    | phiMoment r' => simp [keyFields] at h
  | phiMoment r =>
    cases id' with
    | residue part' q' κ' σ' => simp [keyFields] at h
    | digitMoment r' j' => simp [keyFields] at h
    | phiMoment r' => simp only [keyFields, List.cons.injEq, and_true, true_and] at h; rw [h]

/-- **Request keys are injective on the requests.** -/
theorem reqKey_inj {cT : ℕ} (hs : Spec cT (header c) p) (id id' : ReqId) (hid : id ∈ reqIds c p)
    (hid' : id' ∈ reqIds c p) (h : reqKey c p id = reqKey c p id') : id = id' := by
  unfold reqKey at h
  rw [radixKey_eq, radixKey_eq] at h
  have hl := keyFields_length_le c p id hid
  have hl' := keyFields_length_le c p id' hid'
  have hlt := keyFields_lt c p hs id hid
  have hlt' := keyFields_lt c p hs id' hid'
  have hP := rk_inj (keyBits p) _ _ (by simp; omega)
    (fun x hx => by
      simp only [List.mem_append, List.mem_replicate] at hx
      rcases hx with hx | ⟨_, rfl⟩
      · exact hlt x hx
      · positivity)
    (fun x hx => by
      simp only [List.mem_append, List.mem_replicate] at hx
      rcases hx with hx | ⟨_, rfl⟩
      · exact hlt' x hx
      · positivity) h
  obtain ⟨r, hr⟩ := keyFields_head id
  obtain ⟨r', hr'⟩ := keyFields_head id'
  have hk : kindOf id = kindOf id' := by
    rw [hr, hr'] at hP; simp only [List.cons_append, List.cons.injEq] at hP; exact hP.1
  have hlen : (keyFields id).length = (keyFields id').length := by
    rw [keyFields_len c p id hid, keyFields_len c p id' hid', hk]
  apply keyFields_inj c p id id' hid hid'
  have := congrArg (List.take (keyFields id).length) hP
  rwa [List.take_left, hlen, List.take_left] at this

end K

section F
variable (c : Call) (p : Params) (wt : Wit c.n)

open Classical in
/-- **The functional table** of cell `y`: the value of the request with key `k` (`0` if none). -/
noncomputable def F (y : Cells wt.I) (k : ℕ) : ℕ :=
  if h : ∃ id ∈ reqIds c p, reqKey c p id = k then reqValue c p wt y (Classical.choose h) else 0

theorem F_key {cT : ℕ} (hs : Spec cT (header c) p) (y : Cells wt.I) (id : ReqId) (hid : id ∈ reqIds c p) :
    F c p wt y (reqKey c p id) = reqValue c p wt y id := by
  have hex : ∃ id' ∈ reqIds c p, reqKey c p id' = reqKey c p id := ⟨id, hid, rfl⟩
  unfold F
  rw [dif_pos hex]
  have := Classical.choose_spec hex
  rw [reqKey_inj c p hs _ id this.1 hid this.2]

theorem F_lt {cT : ℕ} (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)
    (y : Cells wt.I) (k : ℕ) : F c p wt y k < 2 ^ valueWidth c p := by
  unfold F
  split_ifs with h
  · exact reqValue_lt c p wt hs w hw y _ (Classical.choose_spec h).1
  · positivity

theorem F_pad {cT : ℕ} (hs : Spec cT (header c) p) (y : Cells wt.I) : F c p wt y (2 ^ keyW c p) = 0 := by
  unfold F
  rw [dif_neg]
  rintro ⟨id, hid, he⟩
  have := reqKey_lt c p hs id hid
  unfold keyW at he
  omega

end F

end NearCubicGates.Close.Cells.GatherPhase

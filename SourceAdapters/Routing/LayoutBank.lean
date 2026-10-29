import SourceAdapters.Routing.LayoutPacking

/-!
The construction in `app:affine-embedding`: every literal affine offset lies in the full domain, the bank
has the exact small size, and all three access families occur in it.-/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.LayoutFacts

theorem k_lt_m (l : Layout) : l.k < l.m := by unfold Layout.m;omega

theorem dimension_lt (l : Layout) (j : ℕ) : dimension l.k j < l.k := by
  have hk := l.k_pos
  unfold dimension
  omega

theorem stage_lt (l : Layout) (j : ℕ) (hj : j < switchCount l.k) :
    j < 2^l.ell ∧ j+1 < 2^l.ell := by
  have hs := l.stages_fit
  unfold switchCount at hj
  omega

theorem single_lt (l : Layout) (d : ℕ) (hd : d < l.k) : 2^d < l.h :=
  Nat.pow_lt_pow_right (by decide) (hd.trans (k_lt_m l))

theorem zero_range (l : Layout) : InRange l 0 0 0 0 0 :=
  ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,by decide,by decide⟩

theorem eta_lt (l : Layout) (r : ℕ) (hr : r<8) : eta l r < l.h :=
  cellMask_lt l 0 0 0 r 0 ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,hr,by decide⟩

theorem areaMask_lt (l : Layout) : areaMask l < l.h :=
  cellMask_lt l 0 0 0 0 1 ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,by decide,by decide⟩

theorem stageDelta_lt (l : Layout) (j : ℕ) (hj : j < switchCount l.k) : stageDelta l j < l.h :=
  Nat.xor_lt_two_pow
    (cellMask_lt l 0 j 0 0 0 ⟨Nat.two_pow_pos _,(stage_lt l j hj).1,Nat.two_pow_pos _,by decide,by decide⟩)
    (cellMask_lt l 0 (j+1) 0 0 0 ⟨Nat.two_pow_pos _,(stage_lt l j hj).2,Nat.two_pow_pos _,by decide,by decide⟩)

theorem laneCarry_lt (l : Layout) (t : ℕ) (ht : t<l.k) : laneCarry t < l.h := by
  have hp : 2^(t+1) ≤ 2^l.m := Nat.pow_le_pow_right (by decide) (by have := k_lt_m l;omega)
  have hpos := Nat.two_pow_pos (t+1)
  unfold laneCarry Layout.h
  omega

theorem columnCarry_lt (l : Layout) (t : ℕ) (ht : t<l.q) : columnCarry l t < l.h := by
  have hp : 2^(t+1) ≤ 2^l.q := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos := Nat.two_pow_pos (t+1)
  exact cellMask_lt l 0 0 (2^(t+1)-1) 0 0
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,by change _ < 2^l.q;omega,by decide,by decide⟩

theorem localMask_lt (l : Layout) (b : ℕ) (hb : b<16*l.C) : 2^(l.k+l.ell)*b < l.h := by
  rw [h_eq, pow_add]
  have hp := Nat.two_pow_pos (l.k+l.ell)
  have h := Nat.mul_lt_mul_of_pos_left hb hp
  simpa only [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem routingBank_lt (l : Layout) : ∀ b ∈ routingBank l, b<l.h := by
  simp only [routingBank,List.forall_mem_append,List.forall_mem_map,List.forall_mem_cons,
    List.not_mem_nil,IsEmpty.forall_iff,forall_const,and_true,List.mem_range]
  repeat' apply And.intro
  · exact Nat.two_pow_pos _
  · exact stageDelta_lt l
  · intro j hj
    exact Nat.xor_lt_two_pow (stageDelta_lt l j hj) (single_lt l _ (dimension_lt l j))
  · exact single_lt l
  · exact eta_lt l 1 (by decide)
  · exact eta_lt l 2 (by decide)
  · exact Nat.xor_lt_two_pow (eta_lt l 3 (by decide)) (eta_lt l 1 (by decide))
  · exact Nat.xor_lt_two_pow (eta_lt l 4 (by decide)) (eta_lt l 1 (by decide))
  · intro d hd
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (eta_lt l 4 (by decide))
      (eta_lt l 1 (by decide))) (single_lt l d hd)
  · exact columnCarry_lt l

theorem globalBank_lt (l : Layout) : ∀ b ∈ globalBank l, b<l.h := by
  simp only [globalBank,List.forall_mem_append,List.forall_mem_map,List.mem_range]
  refine ⟨⟨⟨routingBank_lt l,localMask_lt l⟩,?_⟩,?_⟩
  · intro t ht
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (laneCarry_lt l t ht) (eta_lt l 5 (by decide)))
      (eta_lt l 1 (by decide))
  · intro t ht
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (laneCarry_lt l t ht) (areaMask_lt l))
      (eta_lt l 6 (by decide))

theorem globalBank_length (l : Layout) : (globalBank l).length = 8*l.k+l.q+16*l.C+3 := by
  have hk := l.k_pos
  simp only [globalBank,routingBank,List.length_append,List.length_map,List.length_range,
    List.length_cons,List.length_nil,switchCount]
  omega

theorem zero_mem_globalBank (l : Layout) : 0 ∈ globalBank l := by
  simp [globalBank,routingBank]

theorem stage_mem_globalBank (l : Layout) (j : ℕ) (hj : j<switchCount l.k) :
    stageDelta l j ∈ globalBank l ∧ (stageDelta l j ^^^ 2^dimension l.k j) ∈ globalBank l := by
  have ha := List.mem_map_of_mem (f := stageDelta l) (List.mem_range.mpr hj)
  have hb := List.mem_map_of_mem (f := fun j => stageDelta l j ^^^ 2^dimension l.k j) (List.mem_range.mpr hj)
  simp only [globalBank,routingBank,List.mem_append]
  aesop

theorem local_mem_globalBank (l : Layout) (c r a : ℕ) (hc : c<l.C) (hr : r<8) (ha : a<2) :
    cellMask l 0 0 c r a ∈ globalBank l := by
  have hb : c+2^l.q*(r+8*a)<16*l.C := by
    have h := block_lt l.q c (r+8*a) 16 hc (by omega)
    simpa [Layout.C,Nat.mul_comm] using h
  have hm := List.mem_map_of_mem (f := fun b => 2^(l.k+l.ell)*b) (List.mem_range.mpr hb)
  have he : 2^(l.k+l.ell)*(c+2^l.q*(r+8*a)) = cellMask l 0 0 c r a := by
    simp [cellMask,pow_add,Nat.mul_assoc]
  rw [he] at hm
  simp only [globalBank,List.mem_append]
  aesop

theorem predecessor_mem_globalBank (l : Layout) (t : ℕ) (ht : t<l.k) :
    (laneCarry t ^^^ eta l 5 ^^^ eta l 1) ∈ globalBank l ∧
    (laneCarry t ^^^ areaMask l ^^^ eta l 6) ∈ globalBank l := by
  have ha := List.mem_map_of_mem (f := fun t => laneCarry t ^^^ eta l 5 ^^^ eta l 1) (List.mem_range.mpr ht)
  have hb := List.mem_map_of_mem (f := fun t => laneCarry t ^^^ areaMask l ^^^ eta l 6) (List.mem_range.mpr ht)
  simp only [globalBank,List.mem_append]
  aesop

theorem accessCoverage (l : Layout) : AccessCoverage l :=
  ⟨stage_mem_globalBank l,fun c hc r hr a ha => local_mem_globalBank l c r a hc hr ha,
    predecessor_mem_globalBank l⟩

variable {F : Type} [Field F] [CharP F 2]

theorem layoutCorrect (l : Layout) (e : Fin l.m → F) (hi : Independent l.m e) : LayoutCorrect l e :=
  ⟨cellMask_lt l,label_eq_iff l e hi,fun u v _ _ => maskEval_xor l.m e u v,
    globalBank_length l,zero_mem_globalBank l,
    fun b hb => ⟨globalBank_lt l b hb,fun z hz => inH_translate l.m e b z hz⟩,h_eq l⟩

end NearCubicGates.Adapters.Routing.LayoutFacts

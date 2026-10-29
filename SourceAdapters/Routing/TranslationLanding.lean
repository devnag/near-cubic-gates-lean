import SourceAdapters.Routing.LayoutBank
import SourceAdapters.Routing.TranslationBits

/-!
The construction in `app:affine-embedding`: the literal bank masks land at the declared cells.
The proofs use the disjoint blocks of cellMask and actual binary carries.
No affine-realization or landing assumption is used.
-/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.LayoutFacts

variable {F : Type} [Field F] [CharP F 2]

theorem label_translate (l : Layout) (e : Fin l.m → F)
    (x s c r a x' s' c' r' a' : ℕ) :
    label l e x s c r a +
      maskEval l.m e (cellMask l x s c r a ^^^ cellMask l x' s' c' r' a') =
      label l e x' s' c' r' a' := by
  rw [maskEval_xor]
  change label l e x s c r a + (label l e x s c r a + label l e x' s' c' r' a') = _
  rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add]

theorem label_local (l : Layout) (e : Fin l.m → F) (x s c r a c' r' a' : ℕ)
    (h : InRange l x s c r a) (h' : InRange l x s c' r' a') :
    label l e x s c r a + maskEval l.m e (cellMask l 0 0 (c^^^c') (r^^^r') (a^^^a')) =
      label l e x s c' r' a' := by
  have he := label_translate l e x s c r a x s c' r' a'
  rw [cellMask_xor l _ _ _ _ _ _ _ _ _ _ h h'] at he
  simpa only [Nat.xor_self] using he

theorem label_lane_role_flip (l : Layout) (e : Fin l.m → F)
    (x s c r a d r' : ℕ) (h : InRange l x s c r a) (hd : d<l.k) (hr' : r'<8) :
    label l e x s c r a + maskEval l.m e (eta l r ^^^ eta l r' ^^^ 2^d) =
      label l e (x^^^2^d) s c r' a := by
  have hp : 2^d<2^l.k := Nat.pow_lt_pow_right (by decide) hd
  have hrange : InRange l 0 0 0 (r^^^r') 0 :=
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,
      Nat.xor_lt_two_pow (n:=3) h.2.2.2.1 hr',by decide⟩
  have hlane : InRange l (2^d) 0 0 0 0 :=
    ⟨hp,Nat.two_pow_pos _,Nat.two_pow_pos _,by decide,by decide⟩
  have heta : eta l r ^^^ eta l r' = cellMask l 0 0 0 (r^^^r') 0 := by
    have he := cellMask_xor l 0 0 0 r 0 0 0 0 r' 0
      ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,h.2.2.2.1,by decide⟩
      ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,hr',by decide⟩
    simpa only [eta,Nat.xor_self] using he
  have hmask : eta l r ^^^ eta l r' ^^^ 2^d = cellMask l (2^d) 0 0 (r^^^r') 0 := by
    rw [heta]
    have he := cellMask_xor l 0 0 0 (r^^^r') 0 (2^d) 0 0 0 0 hrange hlane
    simpa [cellMask] using he
  rw [hmask]
  have he := label_add l e x s c r a (2^d) 0 0 (r^^^r') 0 h
    ⟨hp,Nat.two_pow_pos _,Nat.two_pow_pos _,hrange.2.2.2.1,by decide⟩
  simpa only [label,Nat.xor_zero,←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor] using he

theorem partner_toNat (l : Layout) (d : ℕ) (hd : d<l.k) (x : Lane l.k) :
    (partner l.k d x).toNat = x.toNat ^^^ 2^d := by
  have hp : 2^d<2^l.k := Nat.pow_lt_pow_right (by decide) hd
  simp only [partner,BitVec.toNat_xor,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp]

theorem label_stage (l : Layout) (e : Fin l.m → F) (j : ℕ) (hj : j<switchCount l.k)
    (x : Lane l.k) (c r a : ℕ) (hc : c<l.C) (hr : r<8) (ha : a<2) :
    label l e x.toNat j c r a + maskEval l.m e (stageDelta l j) =
      label l e x.toNat (j+1) c r a := by
  have h := label_translate l e x.toNat j c r a x.toNat (j+1) c r a
  have h₀ : InRange l 0 j 0 0 0 :=
    ⟨Nat.two_pow_pos _,(stage_lt l j hj).1,Nat.two_pow_pos _,by decide,by decide⟩
  have h₁ : InRange l 0 (j+1) 0 0 0 :=
    ⟨Nat.two_pow_pos _,(stage_lt l j hj).2,Nat.two_pow_pos _,by decide,by decide⟩
  rw [cellMask_xor l _ _ _ _ _ _ _ _ _ _
    ⟨x.isLt,(stage_lt l j hj).1,hc,hr,ha⟩ ⟨x.isLt,(stage_lt l j hj).2,hc,hr,ha⟩] at h
  simpa only [stageDelta,cellMask_xor l _ _ _ _ _ _ _ _ _ _ h₀ h₁,Nat.xor_self] using h

theorem label_stage_cross (l : Layout) (e : Fin l.m → F) (j : ℕ) (hj : j<switchCount l.k)
    (x : Lane l.k) (c r a : ℕ) (hc : c<l.C) (hr : r<8) (ha : a<2) :
    label l e x.toNat j c r a + maskEval l.m e (stageDelta l j ^^^ 2^dimension l.k j) =
      label l e (partner l.k (dimension l.k j) x).toNat (j+1) c r a := by
  rw [maskEval_xor,←add_assoc,label_stage l e j hj x c r a hc hr ha,
    partner_toNat l _ (dimension_lt l j)]
  simpa only [Nat.xor_self,Nat.zero_xor] using
    label_lane_role_flip l e x.toNat (j+1) c r a (dimension l.k j) r
      ⟨x.isLt,(stage_lt l j hj).2,hc,hr,ha⟩ (dimension_lt l j) hr

theorem label_column (l : Layout) (e : Fin l.m → F) (x s c r a t : ℕ)
    (h : InRange l x s c r a) (ht : ColumnCase l.q t c) :
    label l e x s c r a + maskEval l.m e (columnCarry l t) =
      label l e x s ((c+1)%l.C) r a := by
  have hp : 2^(t+1)≤2^l.q := Nat.pow_le_pow_right (by decide) (by have := ht.1;omega)
  have hpos := Nat.two_pow_pos (t+1)
  have he := label_add l e x s c r a 0 0 (2^(t+1)-1) 0 0 h
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,by change _<2^l.q;omega,by decide,by decide⟩
  simpa only [label,columnCarry,Nat.xor_zero,column_xor_successor l.q t c h.2.2.1 ht,Layout.C] using he

theorem label_predecessor (l : Layout) (e : Fin l.m → F) (x s c r a t r' a' : ℕ)
    (h : InRange l x s c r a) (hr' : r'<8) (ha' : a'<2) (ht : t<l.k)
    (hx : x%2^(t+1)=2^t) :
    label l e x s c r a +
      maskEval l.m e (laneCarry t ^^^ eta l (r^^^r') ^^^ cellMask l 0 0 0 0 (a^^^a')) =
      label l e (x-1) s c r' a' := by
  have hp : 2^(t+1)≤2^l.k := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos := Nat.two_pow_pos (t+1)
  have hcarry : laneCarry t<2^l.k := by unfold laneCarry;omega
  have hrole : r^^^r'<8 := Nat.xor_lt_two_pow (n:=3) h.2.2.2.1 hr'
  have harea : a^^^a'<2 := Nat.xor_lt_two_pow (n:=1) h.2.2.2.2 ha'
  have hlane : InRange l (laneCarry t) 0 0 0 0 :=
    ⟨hcarry,Nat.two_pow_pos _,Nat.two_pow_pos _,by decide,by decide⟩
  have hroleRange : InRange l 0 0 0 (r^^^r') 0 :=
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,hrole,by decide⟩
  have hareaRange : InRange l 0 0 0 0 (a^^^a') :=
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,by decide,harea⟩
  have hfirst : laneCarry t ^^^ eta l (r^^^r') = cellMask l (laneCarry t) 0 0 (r^^^r') 0 := by
    have he := cellMask_xor l (laneCarry t) 0 0 0 0 0 0 0 (r^^^r') 0 hlane hroleRange
    simpa [cellMask,eta] using he
  have hmask : laneCarry t ^^^ eta l (r^^^r') ^^^ cellMask l 0 0 0 0 (a^^^a') =
      cellMask l (laneCarry t) 0 0 (r^^^r') (a^^^a') := by
    rw [hfirst]
    have he := cellMask_xor l (laneCarry t) 0 0 (r^^^r') 0 0 0 0 0 (a^^^a')
      ⟨hcarry,Nat.two_pow_pos _,Nat.two_pow_pos _,hrole,by decide⟩ hareaRange
    simpa only [Nat.xor_zero,Nat.zero_xor] using he
  rw [hmask]
  have he := label_add l e x s c r a (laneCarry t) 0 0 (r^^^r') (a^^^a') h
    ⟨hcarry,Nat.two_pow_pos _,Nat.two_pow_pos _,hrole,harea⟩
  simpa only [label,laneCarry,predecessor_xor t x hx,Nat.xor_zero,
    ←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor] using he

theorem translationLanding (l : Layout) (e : Fin l.m → F) : TranslationLanding l e :=
  ⟨label_local l e,fun j hj x c hc r hr a ha =>
    ⟨label_stage l e j hj x c r a hc hr ha,label_stage_cross l e j hj x c r a hc hr ha⟩,
    label_column l e,label_predecessor l e⟩

end NearCubicGates.Adapters.Routing.LayoutFacts

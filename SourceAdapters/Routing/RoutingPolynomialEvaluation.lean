import SourceAdapters.Routing.TranslationLanding
import SourceAdapters.Routing.FieldSoundness

/-! Evaluation of every literal routing equation at its designated host.-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.RoutingPolynomial

variable {F : Type} [Field F] [CharP F 2]

theorem bit_equation_iff (u : F) : u^2 + u = 0 ↔ IsBit u := by
  rw [CharTwo.add_eq_zero]
  constructor
  · exact eq_zero_or_one_of_sq_eq_self
  · rintro (rfl | rfl) <;> simp

theorem role_translation (l : Layout) (e : Fin l.m → F) (x s c r r' : ℕ)
    (h : InRange l x s c r 0) (hr' : r'<8) :
    label l e x s c r 0 + maskEval l.m e (eta l r ^^^ eta l r') =
      label l e x s c r' 0 := by
  have he := LayoutFacts.cellMask_xor l 0 0 0 r 0 0 0 0 r' 0
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,h.2.2.2.1,by decide⟩
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,hr',by decide⟩
  have hm : eta l r ^^^ eta l r' = cellMask l 0 0 0 (r^^^r') 0 := by
    simpa only [eta,Nat.xor_self] using he
  rw [hm]
  simpa only [Nat.xor_self] using LayoutFacts.label_local l e x s c r 0 c r' 0 h
    ⟨h.1,h.2.1,h.2.2.1,hr',by decide⟩

theorem host_range (l : Layout) (j : ℕ) (hj : j < 2*l.k)
    (x : Lane l.k) (c : Fin l.C) (r : ℕ) (hr : r<8) :
    InRange l x.toNat j c.val r 0 :=
  ⟨x.isLt,lt_of_lt_of_le hj l.stages_fit,c.isLt,hr,by decide⟩

theorem switch_stage_lt (l : Layout) (j : ℕ) (hj : j < switchCount l.k) : j < 2*l.k := by
  unfold switchCount at hj
  omega

theorem evaluate_route (l : Layout) (e : Fin l.m → F) (a : F → F)
    (j : ℕ) (hj : j < switchCount l.k) (x : Lane l.k) (c : Fin l.C) :
    evaluate l e a (label l e x.toNat j c.val 0 0) ((RoutingItem.route j).expr l).poly =
      dataValue l e a j x c + dataValue l e a (j+1) x c +
      switchValue l e a j x c *
        (dataValue l e a (j+1) x c +
          dataValue l e a (j+1) (partner l.k (dimension l.k j) x) c) := by
  have hr := role_translation l e x.toNat j c.val 0 1
    (host_range l j (switch_stage_lt l j hj) x c 0 (by decide)) (by decide)
  have hr' : label l e x.toNat j c.val 0 0 + maskEval l.m e (eta l 1) =
      label l e x.toNat j c.val 1 0 := by simpa [eta,cellMask] using hr
  simp only [evaluate,RoutingItem.expr,Expr.poly,map_add,map_mul,MvPolynomial.eval_X]
  rw [LayoutFacts.maskEval_zero,add_zero,hr',
    LayoutFacts.label_stage l e j hj x c.val 0 0 c.isLt (by decide) (by decide),
    LayoutFacts.label_stage_cross l e j hj x c.val 0 0 c.isLt (by decide) (by decide)]
  rfl

theorem evaluate_switchBit (l : Layout) (e : Fin l.m → F) (a : F → F)
    (j : ℕ) (hj : j < switchCount l.k) (x : Lane l.k) (c : Fin l.C) :
    evaluate l e a (label l e x.toNat j c.val 3 0) ((RoutingItem.switchBit j).expr l).poly =
      (switchValue l e a j x c)^2 + switchValue l e a j x c := by
  simp only [evaluate,RoutingItem.expr,Expr.poly,map_add,map_pow,MvPolynomial.eval_X]
  rw [role_translation l e x.toNat j c.val 3 1
    (host_range l j (switch_stage_lt l j hj) x c 3 (by decide)) (by decide)]
  rfl

theorem evaluate_pair (l : Layout) (e : Fin l.m → F) (a : F → F)
    (j : ℕ) (hj : j < switchCount l.k) (x : Lane l.k) (c : Fin l.C) :
    evaluate l e a (label l e x.toNat j c.val 4 0) ((RoutingItem.pair j).expr l).poly =
      switchValue l e a j x c + switchValue l e a j (partner l.k (dimension l.k j) x) c := by
  simp only [evaluate,RoutingItem.expr,Expr.poly,map_add,MvPolynomial.eval_X]
  rw [role_translation l e x.toNat j c.val 4 1
    (host_range l j (switch_stage_lt l j hj) x c 4 (by decide)) (by decide),
    LayoutFacts.label_lane_role_flip l e x.toNat j c.val 4 0 (dimension l.k j) 1
      (host_range l j (switch_stage_lt l j hj) x c 4 (by decide))
      (LayoutFacts.dimension_lt l j) (by decide),
    ← LayoutFacts.partner_toNat l _ (LayoutFacts.dimension_lt l j) x]
  rfl

theorem evaluate_column (l : Layout) (e : Fin l.m → F) (a : F → F)
    (j : ℕ) (hj : j < switchCount l.k) (t : ℕ) (x : Lane l.k) (c : Fin l.C)
    (ht : ColumnCase l.q t c.val) :
    evaluate l e a (label l e x.toNat j c.val 1 0) ((RoutingItem.column j t).expr l).poly =
      switchValue l e a j x c +
      switchValue l e a j x ⟨(c.val+1)%l.C,Nat.mod_lt _ (Nat.two_pow_pos l.q)⟩ := by
  simp only [evaluate,RoutingItem.expr,Expr.poly,map_add,MvPolynomial.eval_X]
  rw [LayoutFacts.maskEval_zero,add_zero,
    LayoutFacts.label_column l e x.toNat j c.val 1 0 t
      (host_range l j (switch_stage_lt l j hj) x c 1 (by decide)) ht]
  rfl

theorem evaluate_dataBit (l : Layout) (e : Fin l.m → F) (a : F → F)
    (j : ℕ) (hj : j < 2*l.k) (x : Lane l.k) (c : Fin l.C) :
    evaluate l e a (label l e x.toNat j c.val 2 0) ((RoutingItem.dataBit j).expr l).poly =
      (dataValue l e a j x c)^2 + dataValue l e a j x c := by
  have hr := role_translation l e x.toNat j c.val 2 0
    (host_range l j hj x c 2 (by decide)) (by decide)
  have hr' : label l e x.toNat j c.val 2 0 + maskEval l.m e (eta l 2) =
      label l e x.toNat j c.val 0 0 := by simpa [eta,cellMask] using hr
  simp only [evaluate,RoutingItem.expr,Expr.poly,map_add,map_pow,MvPolynomial.eval_X]
  rw [hr']
  rfl

end NearCubicGates.Adapters.Routing.RoutingPolynomial

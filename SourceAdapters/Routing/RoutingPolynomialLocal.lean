import SourceAdapters.Routing.RoutingPolynomialEvaluation
import SourceAdapters.Routing.RoutingPolynomialColumns

/-! The five families of checked host equations are exactly LocalRouting. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.RoutingPolynomial

variable {F : Type} [Field F] [CharP F 2]

def HostEquations (l : Layout) (e : Fin l.m → F) (a : F → F) : Prop :=
  (∀ j < 2*l.k, ∀ (x : Lane l.k) (c : Fin l.C),
    evaluate l e a (label l e x.toNat j c.val 2 0) ((RoutingItem.dataBit j).expr l).poly = 0) ∧
  (∀ j < switchCount l.k, ∀ (x : Lane l.k) (c : Fin l.C),
    evaluate l e a (label l e x.toNat j c.val 3 0) ((RoutingItem.switchBit j).expr l).poly = 0) ∧
  (∀ j < switchCount l.k, ∀ t (x : Lane l.k) (c : Fin l.C), ColumnCase l.q t c.val →
    evaluate l e a (label l e x.toNat j c.val 1 0) ((RoutingItem.column j t).expr l).poly = 0) ∧
  (∀ j < switchCount l.k, ∀ (x : Lane l.k) (c : Fin l.C),
    evaluate l e a (label l e x.toNat j c.val 4 0) ((RoutingItem.pair j).expr l).poly = 0) ∧
  (∀ j < switchCount l.k, ∀ (x : Lane l.k) (c : Fin l.C),
    evaluate l e a (label l e x.toNat j c.val 0 0) ((RoutingItem.route j).expr l).poly = 0)

theorem host_equations_iff (l : Layout) (e : Fin l.m → F) (a : F → F) :
    HostEquations l e a ↔ LocalRouting l e a := by
  constructor
  · rintro ⟨hdata,hswitch,hcolumn,hpair,hroute⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj x c
      apply (bit_equation_iff _).mp
      simpa only [evaluate_dataBit l e a j hj x c] using hdata j hj x c
    · intro j hj x c
      apply (bit_equation_iff _).mp
      simpa only [evaluate_switchBit l e a j hj x c] using hswitch j hj x c
    · intro j hj x
      apply column_cases_constant l.q (switchValue l e a j x)
      intro t c ht
      apply CharTwo.add_eq_zero.mp
      simpa only [evaluate_column l e a j hj t x c ht, Layout.C] using hcolumn j hj t x c ht
    · intro j hj x c
      apply Eq.symm
      apply CharTwo.add_eq_zero.mp
      simpa only [evaluate_pair l e a j hj x c] using hpair j hj x c
    · intro j hj x c
      simpa only [evaluate_route l e a j hj x c] using hroute j hj x c
  · rintro ⟨hdata,hswitch,hcolumn,hpair,hroute⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj x c
      rw [evaluate_dataBit l e a j hj x c]
      exact (bit_equation_iff _).mpr (hdata j hj x c)
    · intro j hj x c
      rw [evaluate_switchBit l e a j hj x c]
      exact (bit_equation_iff _).mpr (hswitch j hj x c)
    · intro j hj t x c ht
      rw [evaluate_column l e a j hj t x c ht]
      exact CharTwo.add_eq_zero.mpr (hcolumn j hj x c _)
    · intro j hj x c
      rw [evaluate_pair l e a j hj x c]
      exact CharTwo.add_eq_zero.mpr (hpair j hj x c).symm
    · intro j hj x c
      rw [evaluate_route l e a j hj x c]
      exact hroute j hj x c

end NearCubicGates.Adapters.Routing.RoutingPolynomial

import SourceAdapters.Routing.RoutingPolynomialLocal
import SourceAdapters.Routing.RoutingPolynomialEmission
import SourceAdapters.Routing.RoutingPatternsItems
import SourceAdapters.Routing.RoutingPatternsCover
import SourceAdapters.Routing.RoutingCatalog

/-! Active guards on all cube points select precisely the five host families. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.RoutingPolynomial

variable {F : Type} [Field F]

theorem guarded_iff_item_hosts (l : Layout) (e : Fin l.m → F) (a : F → F) :
    GuardedEquations l e a ↔
      ∀ i, Catalog.Active l i → ∀ (x : Lane l.k) (c : Fin l.C),
        Catalog.itemCondition l i c.val →
        evaluate l e a (label l e x.toNat (Catalog.itemStage i) c.val (Catalog.hostRole i) 0)
          (i.expr l).poly = 0 := by
  constructor
  · intro h i hi x c hc
    have hrange : InRange l x.toNat (Catalog.itemStage i) c.val (Catalog.hostRole i) 0 :=
      ⟨x.isLt,Catalog.itemStage_lt l i hi,c.isLt,Catalog.hostRole_lt i,by decide⟩
    have hg := (Patterns.guard_iff l i hi _ _ _ _ _ hrange).mpr ⟨rfl,rfl,rfl,hc⟩
    exact h (Patterns.bits l.m (cellMask l x.toNat (Catalog.itemStage i) c.val
      (Catalog.hostRole i) 0)) i ((Catalog.mem_routingItems_iff l i).mpr hi) hg
  · intro h v i hi hg
    have hactive := (Catalog.mem_routingItems_iff l i).mp hi
    obtain ⟨x,s,c,r,ar,hrange,hbits⟩ := Patterns.cube_bits_cell l v
    rw [← hbits] at hg ⊢
    obtain ⟨hs,hr,ha,hc⟩ := (Patterns.guard_iff l i hactive _ _ _ _ _ hrange).mp hg
    subst s; subst r; subst ar
    change evaluate l e a (label l e x (Catalog.itemStage i) c (Catalog.hostRole i) 0)
      (i.expr l).poly = 0
    have hh := h i hactive (BitVec.ofNat l.k x) ⟨c,hrange.2.2.1⟩ hc
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hrange.1] using hh

theorem item_hosts_iff (l : Layout) (e : Fin l.m → F) (a : F → F) :
    (∀ i, Catalog.Active l i → ∀ (x : Lane l.k) (c : Fin l.C),
      Catalog.itemCondition l i c.val →
      evaluate l e a (label l e x.toNat (Catalog.itemStage i) c.val (Catalog.hostRole i) 0)
        (i.expr l).poly = 0) ↔ HostEquations l e a := by
  constructor
  · intro h
    exact ⟨fun j hj x c => h (.dataBit j) hj x c trivial,
      fun j hj x c => h (.switchBit j) hj x c trivial,
      fun j hj t x c ht => h (.column j t) ⟨hj,ht.1⟩ x c ht,
      fun j hj x c => h (.pair j) hj x c trivial,
      fun j hj x c => h (.route j) hj x c trivial⟩
  · rintro ⟨hd,hs,hc,hp,hr⟩ i hi x c hcond
    cases i with
    | route j => exact hr j hi x c
    | switchBit j => exact hs j hi x c
    | pair j => exact hp j hi x c
    | column j t => exact hc j hi.1 t x c hcond
    | dataBit j => exact hd j hi x c

theorem guarded_iff_host (l : Layout) (e : Fin l.m → F) (a : F → F) :
    GuardedEquations l e a ↔ HostEquations l e a :=
  (guarded_iff_item_hosts l e a).trans (item_hosts_iff l e a)

end NearCubicGates.Adapters.Routing.RoutingPolynomial

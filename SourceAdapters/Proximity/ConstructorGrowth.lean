import SourceAdapters.Proximity.AllocationGrowth

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the checked constructor's complete abstract clock
is polynomial in the actual source word. This bounds an existing run. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Growth

open NearCubicWires
variable {α : Type} {size f : α → ℕ}

theorem Bounded.bitLength (h : Bounded size f) : Bounded size (fun x => natBitLength (f x)) :=
  (h.add (bounded_const 1)).mono (fun x => (natBitLength_le_bits_succ (f x)).trans
    (Nat.add_le_add_right (SourceCallee.bits_length_le (f x)) 1))

end NearCubicGates.Adapters.Proximity.Growth
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicGates.Published.CW19Proximity Growth

theorem rowCost_bounded (q : ℕ) (Lk Bk Λ : SourceCircuit → ℕ)
    (hLk : Bounded sourceMeasure Lk) (hBk : Bounded sourceMeasure Bk) (hΛ : Bounded sourceMeasure Λ) :
    Bounded sourceMeasure (fun S => rowCost q (sourceMeasure S) (Lk S) (Bk S) (Λ S)) := by
  have h15 := (bounded_const 15).mul (bounded_size (size := sourceMeasure))
  have hpass := (((h15.add hLk).add hBk).add ((bounded_const 30).mul hΛ)).add (bounded_const 64)
  have hfirst := ((((((bounded_const q).mul hpass).add h15).add hLk).add hBk).add
    ((bounded_const 20).mul hΛ)).add (bounded_const (2 * q))
  have hdecision := ((((h15.add ((bounded_const 10).mul hΛ)).add (bounded_const (6 * q))).add
    hLk).add hBk).add (bounded_const 45)
  have hsecond := ((bounded_const (2 ^ q)).mul hdecision).add (bounded_const 3)
  have hstep := ((bounded_const (12 * q)).add ((bounded_const 50).mul hΛ)).add (bounded_const 247)
  have hthird := ((((bounded_const (9 * 2 ^ q)).add hLk).add hBk).add
    ((bounded_const (3 * predicateBlockSize q)).mul (hstep.add (bounded_const 1)))).add (bounded_const 22)
  exact ((((hfirst.add (bounded_const 50)).add hsecond).add hthird).add (bounded_const 2))

theorem constructorCost_bounded {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 (sourceMeasure S + 2))
    (Lk Bk Λ : SourceCircuit → ℕ)
    (hLk : Bounded sourceMeasure Lk) (hBk : Bounded sourceMeasure Bk) (hΛ : Bounded sourceMeasure Λ) :
    Bounded sourceMeasure (fun S => constructorCost V S (Lk S) (Bk S) (Λ S)) := by
  have hrow := rowCost_bounded q Lk Bk Λ hLk hBk hΛ
  have hrand := random_bounded V a hr
  have hrbits : Bounded sourceMeasure (fun S => (V S).randomBits.bits.length) :=
    hrand.mono (fun S => bits_length_le (V S).randomBits)
  have hcoins := coins_bounded V a hr
  have hlength : Bounded sourceMeasure (fun S => natBitLength (sourceMeasure S)) := bounded_size.bitLength
  have harity : Bounded sourceMeasure (fun S => S.arity.bits.length) := bounded_size.mono arity_bits_source
  have harityfield : Bounded sourceMeasure (fun S => natBitLength S.arity) :=
    (harity.add (bounded_const 1)).mono (fun S => natBitLength_le_bits_succ S.arity)
  have hcombined := (hrand.add (bounded_const (predicateBlockBits q))).bitLength
  have hload := (((bounded_const (2 * q + 2 * 2 ^ q)).add ((bounded_const 30).mul hlength)).add
    ((bounded_const 25).mul harity)).add (bounded_const 80)
  have hcall := ((((bounded_const 15).mul (bounded_size (size := sourceMeasure))).add hLk).add hBk).add
    ((bounded_const 10).mul hrbits)
  have hparams := (((bounded_const 5).mul hrand).add (bounded_const (2 * predicateBlockBits q))).add
    (bounded_const 12)
  have hheader := (((bounded_const 40).mul harityfield).add ((bounded_const 40).mul hcombined)).add
    (bounded_const 87)
  have hloop := (hcoins.mul (hrow.add (bounded_const 4))).add (bounded_const 4)
  exact ((((hload.add (hcall.add (bounded_const 34))).add hparams).add hheader).add hloop).add
    (bounded_const 4)

end NearCubicGates.Adapters.Proximity.SourceCallee

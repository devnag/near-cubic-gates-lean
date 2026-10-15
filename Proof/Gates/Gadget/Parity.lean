import Proof.Gates.Gadget.CircuitKit

/-!
# XOR, parity chains and conjunctions on the DAG builder

`addXor` appends four nodes `(a ∨ b) ∧ ¬(a ∧ b)`. `addParity` folds `addXor` over an index list in the order of
`parityOn`'s `foldl`, starting from a constant `false` node.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires

variable {n : ℕ}

/-- `f xor g` from nodes computing `f` and `g`. -/
def addXor (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    Node b0 (fun y => xor (f y) (g y)) :=
  let o := addOr b0 hr hs hlt
  let a := addAnd o.ext.b (o.ext.keep _ _ hr) (o.ext.keep _ _ hs)
    ⟨lt_of_lt_of_le hlt.1 o.ext.grow, lt_of_lt_of_le hlt.2 o.ext.grow⟩
  let na := addNot a.ext.b a.computes (a.computes.lt (fun _ => false))
  let x := addAnd na.ext.b (na.ext.keep _ _ (a.ext.keep _ _ o.computes)) na.computes
    ⟨(na.ext.keep _ _ (a.ext.keep _ _ o.computes)).lt (fun _ => false), na.computes.lt (fun _ => false)⟩
  ⟨((o.ext.trans a.ext).trans na.ext).trans x.ext, x.out, by
    intro y
    simp only [Ext.trans_b]
    rw [x.computes y]
    cases hf : f y <;> cases hg : g y <;> simp [hf, hg]⟩

/-- The parity of `y` on the indices of `l`, folded from an accumulator node computing `acc`. -/
def addParityFrom (b0 : BooleanDAGBuilder n) (l : List (Fin n)) {r : ℕ} {acc : BitInput n → Bool}
    (hr : Computes b0 r acc) : Node b0 (fun y => l.foldl (fun p i => xor p (y i)) (acc y)) :=
  match l with
  | [] => ⟨Ext.refl b0, r, hr⟩
  | i :: rest =>
      let inp := addInput b0 i
      let hr' := inp.ext.keep _ _ hr
      let x := addXor inp.ext.b hr' inp.computes ⟨hr'.lt (fun _ => false), inp.computes.lt (fun _ => false)⟩
      let tail := addParityFrom x.ext.b rest x.computes
      ⟨(inp.ext.trans x.ext).trans tail.ext, tail.out, by
        intro y
        simp only [Ext.trans_b]
        rw [tail.computes y]
        simp [List.foldl_cons]⟩

/-- The parity of `y` on the indices of `l`, i.e. `l.foldl (· xor y ·) false`. -/
def addParity (b0 : BooleanDAGBuilder n) (l : List (Fin n)) :
    Node b0 (fun y => l.foldl (fun p i => xor p (y i)) false) :=
  let z := addConst b0 false
  let p := addParityFrom z.ext.b l z.computes
  ⟨z.ext.trans p.ext, p.out, by intro y; simp only [Ext.trans_b]; exact p.computes y⟩

end NearCubicGates.Close.Gadget

import Proof.Wire_3_5.Skeleton
import Proof.Wire_3_5.Contracts
import Proof.Wire_3_5.LedgerBudget
import Proof.Wire_3_5.TransferUnion
import Proof.Wire_3_5.UnionEventual

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Theorem113 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Transfer NearCubicWires.ExecutableInterfaces

structure Gate where

  E : Envelope

  Apad : ℕ
  hσ : Apad + 1 ≤ E.sigma

  row : RowBParams

  D : ℕ
  D_pos : 0 < D
  kDeg : ℕ
  descDeg : ℕ
  nameCount : ℕ
  carrierDeg : ℕ
  filterErrDeg : ℕ

  hG7 : D + 2 ≤ filterErrDeg

  alg : RepairRepresentation.DecompositionAlgorithm

namespace Gate
variable (G : Gate)

/-- The time ledger (B9's `rowBNativeBudget`) at the gate constants, the machines' coefficient `coef` (the frozen
cost contracts `costsOf`), and the union's clock and source work. -/
noncomputable def budget (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : TimeBudget kclk G.E :=
  rowBNativeBudget kclk G.Apad G.E G.hσ (Machine.costsOf G.E coef) G.row A a ha

/-- The caller's inputs of `lem:primitive` at the gate constants. -/
def inputs (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : PrimitiveInputs (G.budget kclk coef A a ha) :=
  ⟨G.D, G.D_pos, G.kDeg, G.descDeg, G.nameCount, G.carrierDeg, G.filterErrDeg⟩

abbrev Setup :=
  ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language), InNTIME (fun n => n ^ (kclk + 2)) L →
    UnionSetup (G.inputs kclk coef A a ha)

end Gate

structure UnionLeafAt {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (S : ∀ L : Language, InNTIME (fun n => n ^ (kclk + 2)) L → UnionSetup I) extends UnionConstruction I where
  complete : ∀ (P : FusedPrimitive I) (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L),
    CompleteForEventually (S L hL) P (build P L)

variable (G : Gate) (S : G.Setup)

def PrimitiveLeaf :=
  Σ coef : ℕ, ∀ (kclk A a : ℕ) (ha : a ≤ kclk + 1), FusedPrimitive (G.inputs kclk coef A a ha)

def UnionLeaf :=
  Σ kclk : ℕ, Σ A : ℕ, Σ a : ℕ, Σ' ha : a ≤ kclk + 1,
    ∀ coef : ℕ, UnionLeafAt (G.inputs kclk coef A a ha) (S kclk coef A a ha)

def RecoveryLeaf :=
  ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (U : UnionLeafAt (G.inputs kclk coef A a ha) (S kclk coef A a ha))
    (P : FusedPrimitive (G.inputs kclk coef A a ha)), Recovery U.toUnionConstruction P

noncomputable def parts_of_leaves (p : PrimitiveLeaf G) (u : UnionLeaf G S) (r : RecoveryLeaf G S) : Parts :=
  { kclk := u.1
    envelope := G.E
    budget := G.budget u.1 p.1 u.2.1 u.2.2.1 u.2.2.2.1
    inputs := G.inputs u.1 p.1 u.2.1 u.2.2.1 u.2.2.2.1
    union := (u.2.2.2.2 p.1).toUnionConstruction
    primitive := p.2 u.1 u.2.1 u.2.2.1 u.2.2.2.1
    recovery := r u.1 p.1 u.2.1 u.2.2.1 u.2.2.2.1 (u.2.2.2.2 p.1) (p.2 u.1 u.2.1 u.2.2.1 u.2.2.2.1) }

noncomputable def literals_parts_of_leaves (G : Literals → Gate) (S : ∀ l, (G l).Setup)
    (p : ∀ l, PrimitiveLeaf (G l)) (u : ∀ l, UnionLeaf (G l) (S l)) (r : ∀ l, RecoveryLeaf (G l) (S l)) :
    Literals → Parts :=
  fun l => parts_of_leaves (G l) (S l) (p l) (u l) (r l)

theorem rowB_of_leaves (G : Literals → Gate) (S : ∀ l, (G l).Setup)
    (p : ∀ l, PrimitiveLeaf (G l)) (u : ∀ l, UnionLeaf (G l) (S l)) (r : ∀ l, RecoveryLeaf (G l) (S l)) :
    Literals → rowB :=
  literals_rowB_of_parts (literals_parts_of_leaves G S p u r)

end NearCubicWires.WireExponent3_5.Split

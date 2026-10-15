import Proof.Gates.Gadget.Parity
import Proof.Foundations.BooleanCircuitSizePadding
import Proof.Gates.PublishedSources.PCPP

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP

section Lift
variable {q L : ℕ}

def liftNode : BooleanNode q → BooleanNode (q + L)
  | .const v => .const v
  | .input i => .input (Fin.castAdd L i)
  | .not c => .not c
  | .and a b => .and a b
  | .or a b => .or a b

/-- The first `q` coordinates. -/
def prefixOf (y : BitInput (q + L)) : BitInput q := fun i => y (Fin.castAdd L i)

theorem liftNode_eval (y : BitInput (q + L)) (prior : Array Bool) (node : BooleanNode q) :
    (liftNode (L := L) node).eval y prior = node.eval (prefixOf y) prior := by
  cases node <;> rfl

theorem liftNode_wellFormed (k : ℕ) (node : BooleanNode q) (h : node.WellFormedAt k) :
    (liftNode (L := L) node).WellFormedAt k := by
  cases node <;> simp_all [liftNode, BooleanNode.WellFormedAt]

def liftBuilder (D : BooleanCircuit q) : BooleanDAGBuilder (q + L) where
  nodes := D.nodes.map liftNode
  wellFormed := by
    intro index
    have hlt : index.val < D.nodes.length := by simpa using index.isLt
    have h := D.wellFormed ⟨index.val, hlt⟩
    simp only [List.get_eq_getElem, List.getElem_map] at h ⊢
    exact liftNode_wellFormed _ _ h

theorem liftBuilder_values (D : BooleanCircuit q) (y : BitInput (q + L)) :
    (liftBuilder (L := L) D).values y = D.values (prefixOf y) := by
  simp only [BooleanDAGBuilder.values, liftBuilder, BooleanCircuit.values, List.foldl_map]
  congr 1
  funext prior node
  rw [liftNode_eval]

theorem circuit_values_size (D : BooleanCircuit q) (x : BitInput q) :
    (D.values x).size = D.nodes.length :=
  BooleanDAGBuilder.values_size ⟨D.nodes, D.wellFormed⟩ x

theorem liftBuilder_output (D : BooleanCircuit q) :
    Computes (liftBuilder (L := L) D) D.output.val (fun y => D.eval (prefixOf y)) := by
  intro y
  rw [liftBuilder_values]
  have hs : D.output.val < (D.values (prefixOf y)).size := by
    rw [circuit_values_size]; exact D.output.isLt
  simp [BooleanCircuit.eval, Array.getElem?_eq_getElem hs]

end Lift

/-- A support in increasing order. `Finset.toList` is a choice, so every circuit and call word built from a support
uses this determined list (the machines must reproduce the words). -/
def canonList {q : ℕ} (S : Finset (Fin q)) : List (Fin q) := (List.finRange q).filter (· ∈ S)

theorem mem_canonList {q : ℕ} (S : Finset (Fin q)) (i : Fin q) : i ∈ canonList S ↔ i ∈ S := by
  simp [canonList]

theorem canonList_nodup {q : ℕ} (S : Finset (Fin q)) : (canonList S).Nodup :=
  (List.nodup_finRange q).filter _

theorem canonList_perm {q : ℕ} (S : Finset (Fin q)) : (canonList S).Perm S.toList :=
  List.perm_of_nodup_nodup_toFinset_eq (canonList_nodup S) S.nodup_toList (by ext i; simp [mem_canonList])

theorem parityOn_canon {q : ℕ} (S : Finset (Fin q)) (z : BitInput q) :
    parityOn S z = (canonList S).foldl (fun p i => xor p (z i)) false := by
  unfold parityOn
  exact ((canonList_perm S).foldl_eq' (fun x _ y _ w => by
    cases w <;> cases z x <;> cases z y <;> rfl) false).symm

section Checks
variable (E : LinearCodeFamily) (q : ℕ)

/-- Bit `q + j` equals the `j`-th parity of the first `q` bits. -/
noncomputable def checkBit (j : Fin (E.length q)) (y : BitInput (q + E.length q)) : Bool :=
  y (Fin.natAdd q j) == parityOn (E.support q j) (prefixOf y)

theorem parityOn_eq_foldl (S : Finset (Fin q)) (y : BitInput (q + E.length q)) :
    parityOn S (prefixOf y) =
      (((canonList S).map (Fin.castAdd (E.length q))).foldl (fun p i => xor p (y i)) false) := by
  rw [parityOn_canon]
  simp only [List.foldl_map, prefixOf]

/-- One check: parity chain, the code bit, XOR, negation. -/
noncomputable def addCheck (b0 : BooleanDAGBuilder (q + E.length q)) (j : Fin (E.length q)) :
    Node b0 (checkBit E q j) :=
  let p := addParity b0 ((canonList (E.support q j)).map (Fin.castAdd (E.length q)))
  let i := addInput p.ext.b (Fin.natAdd q j)
  let hp := i.ext.keep _ _ p.computes
  let x := addXor i.ext.b i.computes hp ⟨i.computes.lt (fun _ => false), hp.lt (fun _ => false)⟩
  let e := addNot x.ext.b x.computes (x.computes.lt (fun _ => false))
  ⟨((p.ext.trans i.ext).trans x.ext).trans e.ext, e.out, by
    intro y
    simp only [Ext.trans_b]
    rw [e.computes y]
    simp only [checkBit, parityOn_eq_foldl]
    cases y (Fin.natAdd q j) <;> simp⟩

/-- All checks in `js`, conjoined with a node computing `base`. -/
noncomputable def addChecks (b0 : BooleanDAGBuilder (q + E.length q)) (js : List (Fin (E.length q)))
    {r : ℕ} {base : BitInput (q + E.length q) → Bool} (hr : Computes b0 r base) :
    Node b0 (fun y => base y && js.all (fun j => checkBit E q j y)) :=
  match js with
  | [] => ⟨Ext.refl b0, r, by intro y; simp only [Ext.refl_b, List.all_nil, Bool.and_true]; exact hr y⟩
  | j :: rest =>
      let c := addCheck E q b0 j
      let hb := c.ext.keep _ _ hr
      let a := addAnd c.ext.b hb c.computes ⟨hb.lt (fun _ => false), c.computes.lt (fun _ => false)⟩
      let t := addChecks a.ext.b rest a.computes
      ⟨(c.ext.trans a.ext).trans t.ext, t.out, by
        intro y
        simp only [Ext.trans_b]
        rw [t.computes y]
        simp [List.all_cons, Bool.and_assoc]⟩

end Checks

/-- The checked circuit on `D.n + E.length D.n` inputs. -/
noncomputable def checkedCircuit (E : LinearCodeFamily) (D : Circuit) : Circuit :=
  let c := addChecks E D.n (liftBuilder D.D) (List.finRange (E.length D.n)) (liftBuilder_output D.D)
  let C := c.ext.b.finish ⟨c.out, c.computes.lt (fun _ => false)⟩
  ⟨D.n + E.length D.n, C.padToArity, C.arity_le_padToArity_size⟩

theorem checkedCircuit_n (E : LinearCodeFamily) (D : Circuit) :
    (checkedCircuit E D).n = D.n + E.length D.n := rfl

theorem checkedCircuit_eval (E : LinearCodeFamily) (D : Circuit) (y : BitInput (D.n + E.length D.n)) :
    (checkedCircuit E D).D.eval y =
      (D.D.eval (prefixOf y) && (List.finRange (E.length D.n)).all (fun j => checkBit E D.n j y)) := by
  let c := addChecks E D.n (liftBuilder D.D) (List.finRange (E.length D.n)) (liftBuilder_output D.D)
  change ((c.ext.b.finish ⟨c.out, c.computes.lt (fun _ => false)⟩).padToArity).eval y = _
  rw [BooleanCircuit.padToArity_eval, BooleanDAGBuilder.finish_eval, c.computes y]
  rfl

/-- The systematic encoding `(x, Enc x)`. -/
noncomputable def sysEnc (E : LinearCodeFamily) (q : ℕ) (x : BitInput q) : BitInput (q + E.length q) :=
  Fin.addCases x (E.enc q x)

theorem prefixOf_sysEnc (E : LinearCodeFamily) (q : ℕ) (x : BitInput q) : prefixOf (sysEnc E q x) = x := by
  funext i; simp [prefixOf, sysEnc]

theorem sysEnc_natAdd (E : LinearCodeFamily) (q : ℕ) (x : BitInput q) (j : Fin (E.length q)) :
    sysEnc E q x (Fin.natAdd q j) = E.enc q x j := by
  simp [sysEnc]

/-- A word passes every check exactly when it is the systematic encoding of its prefix. -/
theorem checks_iff (E : LinearCodeFamily) (q : ℕ) (y : BitInput (q + E.length q)) :
    (List.finRange (E.length q)).all (fun j => checkBit E q j y) = true ↔ y = sysEnc E q (prefixOf y) := by
  constructor
  · intro h
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [sysEnc, prefixOf]
    · have hj := List.all_eq_true.mp h j (List.mem_finRange j)
      simp only [checkBit, beq_iff_eq] at hj
      rw [sysEnc_natAdd, hj]
      rfl
  · intro h
    refine List.all_eq_true.mpr (fun j _ => ?_)
    simp only [checkBit, beq_iff_eq]
    conv_lhs => rw [h]
    rw [sysEnc_natAdd]
    rfl

/-- The checked circuit accepts `y` iff `y = sysEnc x` for some `x` that `D` accepts. -/
theorem checkedCircuit_accepts_iff (E : LinearCodeFamily) (D : Circuit) (y : BitInput (D.n + E.length D.n)) :
    (checkedCircuit E D).D.eval y = true ↔ D.D.eval (prefixOf y) = true ∧ y = sysEnc E D.n (prefixOf y) := by
  rw [checkedCircuit_eval, Bool.and_eq_true, checks_iff]

end NearCubicGates.Close.Gadget

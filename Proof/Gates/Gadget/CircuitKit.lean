import Proof.Foundations.BooleanDAGBuilder

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires

variable {n : ℕ}

/-- Node `r` of `b` computes `f`. -/
def Computes (b : BooleanDAGBuilder n) (r : ℕ) (f : BitInput n → Bool) : Prop :=
  ∀ y, (b.values y)[r]? = some (f y)

theorem Computes.lt {b : BooleanDAGBuilder n} {r : ℕ} {f : BitInput n → Bool} (h : Computes b r f)
    (y : BitInput n) : r < b.nodes.length := by
  have hy := h y
  have : r < (b.values y).size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at hy
    exact absurd hy (by simp)
  simpa using this

theorem Computes.append {b : BooleanDAGBuilder n} {r : ℕ} {f : BitInput n → Bool} (h : Computes b r f)
    (node : BooleanNode n) (hnode : node.WellFormedAt b.nodes.length) :
    Computes (b.appendNode node hnode) r f := by
  intro y
  have hr : r < b.nodes.length := h.lt y
  have := b.appendNode_preserves node hnode y ⟨r, hr⟩
  simp only [BooleanDAGBuilder.liftRef_val] at this
  rw [this, h y]

theorem computes_newest (b : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt b.nodes.length) :
    Computes (b.appendNode node hnode) b.nodes.length (fun y => node.eval y (b.values y)) := by
  intro y
  exact b.appendNode_newest node hnode y

/-- An extension of `b0`: every node of `b0` keeps its function. -/
structure Ext (b0 : BooleanDAGBuilder n) where
  b : BooleanDAGBuilder n
  keep : ∀ r f, Computes b0 r f → Computes b r f
  grow : b0.nodes.length ≤ b.nodes.length

def Ext.refl (b0 : BooleanDAGBuilder n) : Ext b0 := ⟨b0, fun _ _ h => h, le_refl _⟩

def Ext.trans {b0 : BooleanDAGBuilder n} (e : Ext b0) (e' : Ext e.b) : Ext b0 :=
  ⟨e'.b, fun r f h => e'.keep r f (e.keep r f h), e.grow.trans e'.grow⟩

@[simp] theorem Ext.refl_b (b0 : BooleanDAGBuilder n) : (Ext.refl b0).b = b0 := rfl

@[simp] theorem Ext.trans_b {b0 : BooleanDAGBuilder n} (e : Ext b0) (e' : Ext e.b) : (e.trans e').b = e'.b := rfl

/-- A one-node extension. -/
def Ext.one (b0 : BooleanDAGBuilder n) (node : BooleanNode n) (hnode : node.WellFormedAt b0.nodes.length) :
    Ext b0 :=
  ⟨b0.appendNode node hnode, fun _ _ h => h.append node hnode, by simp [BooleanDAGBuilder.appendNode]⟩

/-- A node result: an extension with a designated node computing `f`. -/
structure Node (b0 : BooleanDAGBuilder n) (f : BitInput n → Bool) where
  ext : Ext b0
  out : ℕ
  computes : Computes ext.b out f

theorem one_newest (b0 : BooleanDAGBuilder n) (node : BooleanNode n) (hnode : node.WellFormedAt b0.nodes.length)
    (F : BitInput n → Bool) (hF : ∀ y, node.eval y (b0.values y) = F y) :
    Computes (Ext.one b0 node hnode).b b0.nodes.length F := by
  intro y
  exact (computes_newest b0 node hnode y).trans (congrArg some (hF y))

def addConst (b0 : BooleanDAGBuilder n) (v : Bool) : Node b0 (fun _ => v) :=
  ⟨Ext.one b0 (.const v) trivial, b0.nodes.length,
    one_newest b0 _ _ _ (fun _ => rfl)⟩

def addInput (b0 : BooleanDAGBuilder n) (i : Fin n) : Node b0 (fun y => y i) :=
  ⟨Ext.one b0 (.input i) trivial, b0.nodes.length,
    one_newest b0 _ _ _ (fun _ => rfl)⟩

def addNot (b0 : BooleanDAGBuilder n) {r : ℕ} {f : BitInput n → Bool} (hr : Computes b0 r f)
    (hlt : r < b0.nodes.length) : Node b0 (fun y => !f y) :=
  ⟨Ext.one b0 (.not r) (by simp only [BooleanNode.WellFormedAt]; exact hlt), b0.nodes.length,
    one_newest b0 _ _ _ (fun y => by simp [BooleanNode.eval, hr y])⟩

def addAnd (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    Node b0 (fun y => f y && g y) :=
  ⟨Ext.one b0 (.and r s) (by simp only [BooleanNode.WellFormedAt]; exact hlt), b0.nodes.length,
    one_newest b0 _ _ _ (fun y => by simp [BooleanNode.eval, hr y, hs y])⟩

def addOr (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    Node b0 (fun y => f y || g y) :=
  ⟨Ext.one b0 (.or r s) (by simp only [BooleanNode.WellFormedAt]; exact hlt), b0.nodes.length,
    one_newest b0 _ _ _ (fun y => by simp [BooleanNode.eval, hr y, hs y])⟩

end NearCubicGates.Close.Gadget

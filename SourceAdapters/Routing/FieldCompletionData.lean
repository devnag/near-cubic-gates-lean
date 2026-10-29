import SourceAdapters.Routing.FieldSoundness
import SourceAdapters.Routing.LayoutPacking

/-! Values on each routing cell, and their extension to the entire field.-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.FieldCompletion

variable {F : Type}

/-- Pull each next row back across its involutive switch stage. -/
def rows (l : Layout) (s : Settings l.k) (U : Lane l.k → Fin l.C → F) :
    ℕ → Lane l.k → Fin l.C → F
  | 0 => U
  | j + 1 => fun x c => rows l s U j (stageMap l.k s j x) c

theorem rows_bit [Field F] (l : Layout) (s : Settings l.k) (U : Lane l.k → Fin l.C → F)
    (hU : ∀ x c, IsBit (U x c)) (j : ℕ) : ∀ x c, IsBit (rows l s U j x c) := by
  induction j with
  | zero => exact hU
  | succ j ih => exact fun x c => ih (stageMap l.k s j x) c

theorem rows_transport (l : Layout) (s : Settings l.k) (hs : Coherent l.k s)
    (U : Lane l.k → Fin l.C → F) (j : ℕ) (hj : j < switchCount l.k)
    (x : Lane l.k) (c : Fin l.C) :
    rows l s U (j+1) (stageMap l.k s j x) c = rows l s U j x c := by
  simp only [rows, Soundness.stageMap_involutive l.k s j (hs j hj) x]

abbrev Cell (l : Layout) :=
  (Fin (2*l.k) × Lane l.k × Fin l.C) ⊕
  (Fin (switchCount l.k) × Lane l.k × Fin l.C)

def address [Field F] (l : Layout) (e : Fin l.m → F) : Cell l → F
  | .inl (j,x,c) => label l e x.toNat j.val c.val 0 0
  | .inr (j,x,c) => label l e x.toNat j.val c.val 1 0

theorem cell_inRange (l : Layout) (j : ℕ) (hj : j < 2*l.k)
    (x : Lane l.k) (c : Fin l.C) (r : ℕ) (hr : r < 8) :
    InRange l x.toNat j c.val r 0 :=
  ⟨x.isLt, lt_of_lt_of_le hj l.stages_fit, c.isLt, hr, by decide⟩

theorem address_injective [Field F] (l : Layout) (e : Fin l.m → F) (he : Independent l.m e) :
    Function.Injective (address l e) := by
  have sc : switchCount l.k < 2*l.k := by
    have := l.k_pos
    unfold switchCount
    omega
  intro p q h
  cases p with
  | inl p =>
    rcases p with ⟨j,x,c⟩
    cases q with
    | inl q =>
      rcases q with ⟨j',x',c'⟩
      obtain ⟨hx,hj,hc,_,_⟩ :=
        (LayoutFacts.label_eq_iff l e he _ _ _ _ _ _ _ _ _ _
          (cell_inRange l _ j.isLt x c 0 (by decide))
          (cell_inRange l _ j'.isLt x' c' 0 (by decide))).mp h
      have hx' := BitVec.eq_of_toNat_eq hx
      have hj' := Fin.ext hj
      have hc' := Fin.ext hc
      subst x'; subst j'; subst c'
      rfl
    | inr q =>
      rcases q with ⟨j',x',c'⟩
      have hh := (LayoutFacts.label_eq_iff l e he _ _ _ _ _ _ _ _ _ _
        (cell_inRange l _ j.isLt x c 0 (by decide))
        (cell_inRange l _ (lt_trans j'.isLt sc) x' c' 1 (by decide))).mp h
      omega
  | inr p =>
    rcases p with ⟨j,x,c⟩
    cases q with
    | inl q =>
      rcases q with ⟨j',x',c'⟩
      have hh := (LayoutFacts.label_eq_iff l e he _ _ _ _ _ _ _ _ _ _
        (cell_inRange l _ (lt_trans j.isLt sc) x c 1 (by decide))
        (cell_inRange l _ j'.isLt x' c' 0 (by decide))).mp h
      omega
    | inr q =>
      rcases q with ⟨j',x',c'⟩
      obtain ⟨hx,hj,hc,_,_⟩ :=
        (LayoutFacts.label_eq_iff l e he _ _ _ _ _ _ _ _ _ _
          (cell_inRange l _ (lt_trans j.isLt sc) x c 1 (by decide))
          (cell_inRange l _ (lt_trans j'.isLt sc) x' c' 1 (by decide))).mp h
      have hx' := BitVec.eq_of_toNat_eq hx
      have hj' := Fin.ext hj
      have hc' := Fin.ext hc
      subst x'; subst j'; subst c'
      rfl

def cellValue [Field F] (l : Layout) (s : Settings l.k) (U : Lane l.k → Fin l.C → F) : Cell l → F
  | .inl (j,x,c) => rows l s U j x c
  | .inr (j,x,_) => if s j x then 1 else 0

noncomputable def table [Field F] (l : Layout) (e : Fin l.m → F) (s : Settings l.k)
    (U : Lane l.k → Fin l.C → F) (background : F → F) : F → F :=
  Function.extend (address l e) (cellValue l s U) background

theorem table_data [Field F] (l : Layout) (e : Fin l.m → F) (he : Independent l.m e)
    (s : Settings l.k) (U : Lane l.k → Fin l.C → F) (background : F → F)
    (j : ℕ) (hj : j < 2*l.k) (x : Lane l.k) (c : Fin l.C) :
    dataValue l e (table l e s U background) j x c = rows l s U j x c :=
  (address_injective l e he).extend_apply (cellValue l s U) background (.inl (⟨j,hj⟩,x,c))

theorem table_switch [Field F] (l : Layout) (e : Fin l.m → F) (he : Independent l.m e)
    (s : Settings l.k) (U : Lane l.k → Fin l.C → F) (background : F → F)
    (j : ℕ) (hj : j < switchCount l.k) (x : Lane l.k) (c : Fin l.C) :
    switchValue l e (table l e s U background) j x c = if s j x then 1 else 0 :=
  (address_injective l e he).extend_apply (cellValue l s U) background (.inr (⟨j,hj⟩,x,c))

theorem table_preserves [Field F] (l : Layout) (e : Fin l.m → F) (s : Settings l.k)
    (U : Lane l.k → Fin l.C → F) (background : F → F) (z : F)
    (hz : ¬ RoutingWritable l e z) : table l e s U background z = background z := by
  apply Function.extend_apply'
  rintro ⟨p,hp⟩
  apply hz
  cases p with
  | inl p => exact Or.inl ⟨p.1, p.1.isLt, p.2.1, p.2.2, hp.symm⟩
  | inr p => exact Or.inr ⟨p.1, p.1.isLt, p.2.1, p.2.2, hp.symm⟩

end NearCubicGates.Adapters.Routing.FieldCompletion

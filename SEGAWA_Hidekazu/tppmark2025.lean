import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.DeriveFintype

/-!
# Reachability framework for the lamp toggling puzzle

This file develops the basic combinatorial machinery used to reason about line selections
on an `n × n × n` grid of lamps.  We build small list lemmas, enumerate coordinates and axes,
and prove that a list-based reachability test agrees with the logical reachability relation.
-/

namespace TPPmark2025

-- Auxiliary lemmas about lists that we reuse throughout the reachability proofs.
namespace List

open Function

lemma nodup_map_of_injective {α β : Type _} {xs : List α} (f : α → β)
    (hf : Function.Injective f) (hxs : xs.Nodup) :
    (xs.map f).Nodup := by
  classical
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      obtain ⟨hx_notin, hxs_nodup⟩ := List.nodup_cons.mp hxs
      have hx_notin_map : f x ∉ xs.map f := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨x', hx', hx_eq⟩
        have : x' = x := hf hx_eq
        subst this
        exact hx_notin hx'
      have htail : (xs.map f).Nodup := ih hxs_nodup
      exact List.nodup_cons.mpr ⟨hx_notin_map, htail⟩

lemma nodup_map {α β : Type _} {xs : List α} (f : α → β)
    (hf : Function.Injective f) (hxs : xs.Nodup) :
    (xs.map f).Nodup :=
  nodup_map_of_injective f hf hxs

lemma mem_product_left {α β : Type _} {a : α} {b : β}
    {xs : List α} {ys : List β} :
    (a, b) ∈ xs.product ys → a ∈ xs := by
  classical
  intro h
  exact (List.mem_product.mp h).1

lemma nodup_product {α β : Type _} {xs : List α} {ys : List β}
    (hx : xs.Nodup) (hy : ys.Nodup) :
    (xs.product ys).Nodup := by
  classical
  induction xs with
  | nil =>
      have {ys : List β}: (([] : List α).product ys) = [] := by
        simp [List.product]
      simp [this]
  | cons x xs ih =>
      obtain ⟨hx_notin, hxs_nodup⟩ := List.nodup_cons.mp hx
      have hinj : Function.Injective (fun y : β => (x, y)) := by
        intro y₁ y₂ h
        exact congrArg Prod.snd h
      have hmap :
          (ys.map fun y => (x, y)).Nodup :=
        nodup_map_of_injective _ hinj hy
      have htail : (xs.product ys).Nodup := ih hxs_nodup
      have hdisjoint :
          List.Disjoint (ys.map fun y => (x, y)) (xs.product ys) := by
        intro p hp₁ hp₂
        rcases List.mem_map.mp hp₁ with ⟨y, hy, hy_eq⟩
        subst hy_eq
        have hx_mem : x ∈ xs := mem_product_left hp₂
        exact hx_notin hx_mem
      change List.Nodup ((ys.map fun y => (x, y)) ++ xs.product ys)
      apply List.nodup_append.mpr
      constructor
      . exact hmap
      . constructor
        . exact htail
        . intro a ha b hb hab
          apply List.disjoint_left.mp hdisjoint ha
          rw [hab]
          exact hb

end List

/-- Coordinates for a lamp in an `n × n × n` cube. -/
structure Coord (n : ℕ) where
  x : Fin n
  y : Fin n
  z : Fin n
deriving DecidableEq

/-- Explicit enumeration of all coordinates in an `n × n × n` cube. -/
def Coord.all (n : ℕ) : List (Coord n) :=
  (List.finRange n).flatMap fun x =>
    (List.finRange n).flatMap fun y =>
      (List.finRange n).map fun z =>
        { x, y, z }

/-- Every coordinate occurs in the list enumeration `Coord.all`. -/
lemma Coord.all_mem {n : ℕ} (c : Coord n) :
    c ∈ Coord.all n := by
  classical
  cases c with
  | mk x y z =>
      simp [Coord.all, List.mem_flatMap, List.mem_map, List.mem_finRange]

/-- A lamp configuration assigns an on/off value to every coordinate. -/
abbrev Config (n : ℕ) := Coord n → Bool

/-- The configuration with every lamp switched off. -/
def offConfig (n : ℕ) : Config n := fun _ => false

@[simp] lemma offConfig_apply {n : ℕ} (c : Coord n) :
    offConfig n c = false := rfl

/-- Boolean equality test for lamp configurations using the explicit enumeration of coordinates. -/
def configsEqual {n : ℕ} (cfg₁ cfg₂ : Config n) : Bool :=
  (Coord.all n).all (fun c => decide (cfg₁ c = cfg₂ c))

lemma configsEqual_eq_true {n : ℕ} {cfg₁ cfg₂ : Config n} :
    configsEqual cfg₁ cfg₂ = true ↔ cfg₁ = cfg₂ := by
  classical
  constructor
  · intro h
    have hcoord :
        ∀ c : Coord n, cfg₁ c = cfg₂ c := by
      intro c
      have hmem : c ∈ Coord.all n := Coord.all_mem c
      have hAll :=
        (List.all_eq_true).1 h c hmem
      simpa using (of_decide_eq_true hAll)
    ext c
    exact hcoord c
  · intro h
    subst h
    simp [configsEqual]

/-- The three axes perpendicular to the faces of the large cube. -/
inductive Axis
| x | y | z
deriving DecidableEq, Inhabited, Fintype, Ord, Repr

/-- Fixed enumeration of the three coordinate axes. -/
def Axis.allList : List Axis :=
  [Axis.x, Axis.y, Axis.z]

@[simp] lemma Axis.mem_allList (axis : Axis) :
    axis ∈ Axis.allList := by
  cases axis <;> simp [Axis.allList]

/-- A choice of side (front/back) for a face perpendicular to an axis. -/
inductive Side
| neg | pos
deriving DecidableEq

/-- A face of the large cube, determined by an axis and a side. -/
structure Face where
  axis : Axis
  side : Side
deriving DecidableEq

/-- Selecting one of the `n` lamps along a fixed line through the cube. -/
structure LineSelection (n : ℕ) where
  axis : Axis
  frozen₁ : Fin n
  frozen₂ : Fin n
deriving DecidableEq

/-- equality condition for LineSelection -/
def LineSelection.eq {n : ℕ} (sel₁ sel₂ : LineSelection n) : Prop :=
  sel₁.axis = sel₂.axis ∧ sel₁.frozen₁ = sel₂.frozen₁ ∧ sel₁.frozen₂ = sel₂.frozen₂

/-- Lamps that lie on the line selected by `sel`. -/
def LineSelection.contains {n : ℕ} (sel : LineSelection n) (c : Coord n) : Prop :=
  match sel.axis with
  | Axis.x => c.y = sel.frozen₁ ∧ c.z = sel.frozen₂
  | Axis.y => c.x = sel.frozen₁ ∧ c.z = sel.frozen₂
  | Axis.z => c.x = sel.frozen₁ ∧ c.y = sel.frozen₂

instance (sel : LineSelection n) (c : Coord n) :
    Decidable (sel.contains c) := by
  cases h : sel.axis with
  | x =>
      simpa [LineSelection.contains, h] using
        (inferInstance : Decidable ((c.y = sel.frozen₁) ∧ (c.z = sel.frozen₂)))
  | y =>
      simpa [LineSelection.contains, h] using
        (inferInstance : Decidable ((c.x = sel.frozen₁) ∧ (c.z = sel.frozen₂)))
  | z =>
      simpa [LineSelection.contains, h] using
        (inferInstance : Decidable ((c.x = sel.frozen₁) ∧ (c.y = sel.frozen₂)))

/-- Toggle exactly the lamps that lie on the line picked by `sel`. -/
def LineSelection.toggle {n : ℕ} (sel : LineSelection n)
    (cfg : Config n) :
    Config n := fun c =>
  if _ : sel.contains c then
    not (cfg c)
  else
    cfg c

@[simp] lemma LineSelection.toggle_apply {n : ℕ} (sel : LineSelection n)
    (cfg : Config n) (c : Coord n) :
    sel.toggle cfg c = if _ : sel.contains c then not (cfg c) else cfg c := rfl

@[simp] lemma LineSelection.toggle_toggle {n : ℕ} (sel : LineSelection n)
    (cfg : Config n) :
    sel.toggle (sel.toggle cfg) = cfg := by
  classical
  funext c
  by_cases h : sel.contains c
  · simp [LineSelection.toggle, h]
  · simp [LineSelection.toggle, h]

lemma LineSelection.toggle_comm {n : ℕ} (sel₁ sel₂ : LineSelection n)
    (cfg : Config n) :
    sel₁.toggle (sel₂.toggle cfg) = sel₂.toggle (sel₁.toggle cfg) := by
  classical
  funext c
  by_cases h₁ : sel₁.contains c
  · by_cases h₂ : sel₂.contains c
    · simp [LineSelection.toggle, h₁, h₂]
    · simp [LineSelection.toggle, h₁, h₂]
  · by_cases h₂ : sel₂.contains c
    · simp [LineSelection.toggle, h₁, h₂]
    · simp [LineSelection.toggle, h₁, h₂]

/-- Applying a list of line selections sequentially. -/
def LineSelection.applyList {n : ℕ}
    (sels : List (LineSelection n)) (cfg : Config n) : Config n :=
  sels.foldl (fun state sel => sel.toggle state) cfg

@[simp] lemma LineSelection.applyList_nil {n : ℕ} (cfg : Config n) :
    LineSelection.applyList ([] : List (LineSelection n)) cfg = cfg := rfl

@[simp] lemma LineSelection.applyList_cons {n : ℕ} (sel : LineSelection n)
    (sels : List (LineSelection n)) (cfg : Config n) :
    LineSelection.applyList (sel :: sels) cfg =
      LineSelection.applyList sels (sel.toggle cfg) := rfl

lemma LineSelection.applyList_comm {n : ℕ} (sel₁ sel₂ : LineSelection n)
    (sels : List (LineSelection n)) (cfg : Config n) :
    LineSelection.applyList (sel₁ :: sel₂ :: sels) cfg =
      LineSelection.applyList (sel₂ :: sel₁ :: sels) cfg := by
  classical
  simp [LineSelection.applyList, LineSelection.toggle_comm]

lemma LineSelection.applyList_toggle_swap {n : ℕ} (sel : LineSelection n)
    (sels : List (LineSelection n)) (cfg : Config n) :
    LineSelection.applyList sels (sel.toggle cfg) =
      sel.toggle (LineSelection.applyList sels cfg) := by
  classical
  induction sels generalizing cfg with
  | nil =>
      simp
  | cons sel' sels ih =>
      -- Use the induction hypothesis after commuting the outer pair of toggles.
      have := ih (sel'.toggle cfg)
      simpa [LineSelection.applyList, LineSelection.toggle_comm sel sel'] using this

/-- Toggle membership of a line selection inside a finite set. -/
def LineSelection.standardUpdate {n : ℕ}
    (S : Finset (LineSelection n)) (sel : LineSelection n) :
    Finset (LineSelection n) :=
  if sel ∈ S then S.erase sel else insert sel S

/-- Auxiliary fold building the canonical set for a sequence of line selections. -/
def LineSelection.standardSetAux {n : ℕ} :
    List (LineSelection n) → Finset (LineSelection n) →
      Finset (LineSelection n)
  | [], S => S
  | sel :: presses, S =>
      LineSelection.standardSetAux presses (LineSelection.standardUpdate S sel)

@[simp] lemma LineSelection.standardSetAux_nil {n : ℕ}
    (S : Finset (LineSelection n)) :
    LineSelection.standardSetAux ([] : List (LineSelection n)) S = S := rfl

@[simp] lemma LineSelection.standardSetAux_cons {n : ℕ}
    (sel : LineSelection n) (presses : List (LineSelection n))
    (S : Finset (LineSelection n)) :
    LineSelection.standardSetAux (sel :: presses) S =
      LineSelection.standardSetAux presses
        (LineSelection.standardUpdate S sel) := rfl

/-- Canonical set representation toggling every pressed line exactly once. -/
def LineSelection.standardSet {n : ℕ}
    (presses : List (LineSelection n)) :
    Finset (LineSelection n) :=
  LineSelection.standardSetAux presses ∅

@[simp] lemma LineSelection.mem_standardSetAux {n : ℕ}
    (presses : List (LineSelection n)) (S : Finset (LineSelection n))
    (sel : LineSelection n) :
    (sel ∈ LineSelection.standardSetAux presses S) =
      (presses.foldl (fun b t => if t = sel then not b else b) (sel ∈ S)) := by
  classical
  induction presses generalizing S with
  | nil =>
      simp
  | cons t presses ih =>
      have hrec := ih (LineSelection.standardUpdate S t)
      simp at hrec
      by_cases ht : t ∈ S
      · have hupdate :
            (sel ∈ LineSelection.standardUpdate S t) =
              (if t = sel then ¬ sel ∈ S else sel ∈ S) := by
            have := ht
            by_cases hsel : t = sel
            · subst hsel
              simp [LineSelection.standardUpdate, ht]
            · simp [LineSelection.standardUpdate, ht, hsel]
              tauto
        rw [standardSetAux_cons, hrec]
        by_cases hsel : t = sel
        · simp [hsel] at hupdate
          simp [hupdate, hsel]
        · simp [hsel] at hupdate
          simp [hupdate, hsel]
      · have hupdate :
            (sel ∈ LineSelection.standardUpdate S t) =
              (if t = sel then ¬ sel ∈ S else sel ∈ S) := by
            by_cases hsel : t = sel
            · subst hsel
              simp [LineSelection.standardUpdate, ht]
            · simp [LineSelection.standardUpdate, ht, hsel]
              tauto
        rw [standardSetAux_cons, hrec]
        by_cases hsel : t = sel
        · simp [hsel] at hupdate
          simp [hupdate, hsel]
        · simp [hsel] at hupdate
          simp [hupdate, hsel]

@[simp] lemma LineSelection.mem_standardSet {n : ℕ}
    (presses : List (LineSelection n)) (sel : LineSelection n) :
    (sel ∈ LineSelection.standardSet presses) =
      presses.foldl (fun b t => if t = sel then not b else b) false := by
  rw [LineSelection.standardSet]
  exact
    LineSelection.mem_standardSetAux presses (∅ : Finset (LineSelection n)) sel

/- Parity (mod 2) of occurrences of `sel` inside `presses`. -/
def LineSelection.paritySel {n : ℕ}
    (presses : List (LineSelection n)) (sel : LineSelection n) : Bool :=
  presses.foldl (fun b t => if t = sel then not b else b) false

@[simp] lemma LineSelection.paritySel_nil {n : ℕ}
    (sel : LineSelection n) :
    LineSelection.paritySel ([] : List (LineSelection n)) sel = false := rfl

private lemma bool_foldl_neg_eq {α : Type} [DecidableEq α] (t : α) (presses : List α) (init : Bool) :
 List.foldl (fun b t_1 ↦ if t_1 = t then !b else b) (!init) presses =
  !List.foldl (fun b t_1 ↦ if t_1 = t then !b else b) (init) presses := by
  induction presses with
  | nil =>
      simp
  | cons hd tl ih =>
      rw [List.foldl_cons, List.foldl_cons]
      simp at ih
      simp
      by_cases h : hd = t
      · simp [h, ih]
      · simp [h, ih]


@[simp] lemma LineSelection.paritySel_cons {n : ℕ}
    (sel t : LineSelection n) (presses : List (LineSelection n)) :
    LineSelection.paritySel (t :: presses) sel =
      (if t = sel then not (LineSelection.paritySel presses sel)
        else LineSelection.paritySel presses sel) := by
  by_cases h : t = sel
  · subst h
    rw [LineSelection.paritySel]
    simp only [if_true]
    rw [LineSelection.paritySel]
    rw [List.foldl_cons]
    rw [← bool_foldl_neg_eq _ _ _]
    simp
  . rw [LineSelection.paritySel]
    have : (t = sel) = False := by
      simp [h]
    simp [this, paritySel]

lemma LineSelection.mem_standardSet_cons {n : ℕ}
    (m sel: LineSelection n) (presses : List (LineSelection n)) :
    m ∈ LineSelection.standardSet (sel :: presses) ↔
      (if sel = m then
        ¬ (m ∈ LineSelection.standardSet presses)
      else
        m ∈ LineSelection.standardSet presses) := by
  rw [LineSelection.standardSet]
  rw [LineSelection.standardSet]
  rw [LineSelection.mem_standardSetAux]
  rw [LineSelection.mem_standardSetAux]
  rw [List.foldl_cons]
  by_cases hsel : sel = m
  · subst hsel
    simp
    have {init : Bool}: List.foldl (fun b t ↦ if t = sel then !b else b) init presses =
      ! List.foldl (fun b t ↦ if t = sel then !b else b) (!init) presses := by
      induction presses with
      | nil =>
          simp
      | cons t presses ih =>
          rw [List.foldl_cons, List.foldl_cons]
          simp at ih
          simp
          by_cases ht : t = sel
          · simp [ht, ih]
          · simp [ht, ih]
    rw [this]
    congr
  · simp [hsel]

lemma LineSelection.mem_standardSet_iff {n : ℕ}
    (presses : List (LineSelection n)) (sel : LineSelection n) :
    sel ∈ LineSelection.standardSet presses ↔
      LineSelection.paritySel presses sel = true := by
  classical
  induction presses generalizing sel with
  | nil =>
      simp [LineSelection.standardSet]
  | cons t presses ih =>
      rw [LineSelection.mem_standardSet_cons]
      by_cases hsel : t = sel
      · subst hsel
        rw [paritySel_cons]
        simp only [if_true]
        rw [ih]
        simp
      · rw [paritySel_cons]
        simp only [hsel, if_false]
        exact ih _

def Axis.all : List Axis := [Axis.x, Axis.y, Axis.z]

lemma Axis.all_mem (axis : Axis) : axis ∈ Axis.all := by
  cases axis <;> simp [Axis.all]

@[simp] lemma Axis.all_nodup : Axis.all.Nodup := by
  decide  -- the list [x, y, z] has no duplicates

/-! ### Rewriting `all` via a product list and `map` -/
private def tripleList (n : ℕ) :
    List (((Axis × Fin n) × Fin n)) :=
  (Axis.all.product (List.finRange n)).product (List.finRange n)

private def fromTriple {n} :
    ((Axis × Fin n) × Fin n) → LineSelection n
  | ((a,i),j) => { axis := a, frozen₁ := i, frozen₂ := j }

def LineSelection.all (n : ℕ) : List (LineSelection n) :=
  (tripleList n).map (fromTriple)

/-! ### Surjectivity (coverage) -/
lemma LineSelection.mem_all {n : ℕ} (sel : LineSelection n) :
    sel ∈ LineSelection.all n := by
  classical
  cases sel with
  | mk axis frozen₁ frozen₂ =>
    refine List.mem_map.mpr ?_
    refine ⟨((axis, frozen₁), frozen₂), ?_, ?_⟩
    ·
      have hAxis : axis ∈ Axis.all := Axis.all_mem axis
      have hFrozen₁ : frozen₁ ∈ List.finRange n := List.mem_finRange frozen₁
      have hFrozen₂ : frozen₂ ∈ List.finRange n := List.mem_finRange frozen₂
      simp [tripleList, hAxis, hFrozen₁, hFrozen₂]
    · simp [fromTriple]

/-! ### Injectivity (no duplicates) -/
lemma LineSelection.all_nodup (n : ℕ) :
    (LineSelection.all n).Nodup := by
  classical
  -- first, the triple product list has no duplicates
  have hA  : Axis.all.Nodup := Axis.all_nodup
  have hF  : (List.finRange n).Nodup := List.nodup_finRange n
  have hProd₁ :
      (Axis.all.product (List.finRange n)).Nodup :=
    List.nodup_product hA hF
  have hProd₂ :
      ((Axis.all.product (List.finRange n)).product (List.finRange n)).Nodup :=
    List.nodup_product hProd₁ hF
  -- `fromTriple` is injective
  have hinj : Function.Injective (@fromTriple n) := by
    intro x y h
    rcases x with ⟨⟨a, i⟩, j⟩
    rcases y with ⟨⟨a', i'⟩, j'⟩
    dsimp [fromTriple] at h
    cases h
    rfl
  -- mapping preserves the nodup property
  have hMap :
      ((tripleList n).map (fromTriple)).Nodup :=
    List.nodup_map _ hinj (by simpa [tripleList] using hProd₂)
  -- finish: substitute the definition of `all`
  dsimp [all]
  exact hMap

/-- Deterministic list for a canonical set of line selections. -/
def LineSelection.sequenceOfStandardSet {n : ℕ}
    (standard : Finset (LineSelection n)) :
    List (LineSelection n) :=
  (LineSelection.all n).filter fun sel => sel ∈ standard

/-- Computable canonical list representation obtained from the canonical set. -/
def LineSelection.standardSequence {n : ℕ}
    (presses : List (LineSelection n)) :
    List (LineSelection n) :=
  LineSelection.sequenceOfStandardSet (LineSelection.standardSet presses)

lemma LineSelection.sequenceOfStandardSet_nodup {n : ℕ}
    (standard : Finset (LineSelection n)) :
    (LineSelection.sequenceOfStandardSet standard).Nodup := by
  classical
  unfold LineSelection.sequenceOfStandardSet
  exact (LineSelection.all_nodup n).filter _

def LineSelection.lineX {n : ℕ} (c : Coord n) : LineSelection n :=
  { axis := Axis.x, frozen₁ := c.y, frozen₂ := c.z }

def LineSelection.lineY {n : ℕ} (c : Coord n) : LineSelection n :=
  { axis := Axis.y, frozen₁ := c.x, frozen₂ := c.z }

def LineSelection.lineZ {n : ℕ} (c : Coord n) : LineSelection n :=
  { axis := Axis.z, frozen₁ := c.x, frozen₂ := c.y }

lemma LineSelection.contains_lineX {n : ℕ} (c : Coord n) :
    (LineSelection.lineX c).contains c := by
  simp [LineSelection.lineX, LineSelection.contains]

lemma LineSelection.contains_lineY {n : ℕ} (c : Coord n) :
    (LineSelection.lineY c).contains c := by
  simp [LineSelection.lineY, LineSelection.contains]

lemma LineSelection.contains_lineZ {n : ℕ} (c : Coord n) :
    (LineSelection.lineZ c).contains c := by
  simp [LineSelection.lineZ, LineSelection.contains]

lemma LineSelection.contains_cases {n : ℕ} {sel : LineSelection n}
    {c : Coord n} (h : sel.contains c) :
    sel = LineSelection.lineX c ∨ sel = LineSelection.lineY c ∨
      sel = LineSelection.lineZ c := by
  cases haxis : sel.axis with
  | x =>
      have : sel.frozen₁ = c.y ∧ sel.frozen₂ = c.z := by
        rw [LineSelection.contains] at h
        rw [haxis] at h
        simp only at h
        tauto
      rcases this with ⟨hy, hz⟩
      left
      rw [LineSelection.lineX]
      rw [LineSelection.contains] at h
      rw [haxis] at h
      simp only at h
      cases sel
      congr
  | y =>
      have : sel.frozen₁ = c.x ∧ sel.frozen₂ = c.z := by
        rw [LineSelection.contains] at h
        rw [haxis] at h
        simp only at h
        tauto
      rcases this with ⟨hx, hz⟩
      right; left
      rw [LineSelection.lineY]
      rw [LineSelection.contains] at h
      rw [haxis] at h
      simp only at h
      cases sel
      congr
  | z =>
      have : sel.frozen₁ = c.x ∧ sel.frozen₂ = c.y := by
        rw [LineSelection.contains] at h
        rw [haxis] at h
        simp only at h
        tauto
      rcases this with ⟨hx, hy⟩
      right; right
      rw [LineSelection.lineZ]
      rw [LineSelection.contains] at h
      rw [haxis] at h
      simp only at h
      cases sel
      congr


/-- Parity of toggles affecting a particular lamp. -/
def LineSelection.parityContains {n : ℕ}
    (presses : List (LineSelection n)) (c : Coord n) : Bool :=
  presses.foldl (fun b sel => if sel.contains c then not b else b) false

@[simp] lemma LineSelection.parityContains_nil {n : ℕ}
    (c : Coord n) :
    LineSelection.parityContains ([] : List (LineSelection n)) c = false := rfl

private lemma bool_foldl_neg_eq_2 {α : Type} [DecidableEq α] (t : α) (presses : List α) (init : Bool) :
 List.foldl (fun b t_1 ↦ if t_1 = t then !b else b) (!init) presses =
  !List.foldl (fun b t_1 ↦ if t_1 = t then !b else b) (init) presses := by
  induction presses with
  | nil =>
      simp
  | cons hd tl ih =>
      rw [List.foldl_cons, List.foldl_cons]
      simp at ih
      simp
      by_cases h : hd = t
      · simp [h, ih]
      · simp [h, ih]

@[simp] lemma LineSelection.parityContains_cons {n : ℕ}
    (sel : LineSelection n) (presses : List (LineSelection n))
    (c : Coord n) :
    LineSelection.parityContains (sel :: presses) c =
      (if sel.contains c then not (LineSelection.parityContains presses c)
        else LineSelection.parityContains presses c) := by
  rw [parityContains, List.foldl_cons]
  rw [parityContains]
  by_cases h : sel.contains c
  · simp [h]
    have {init : Bool}: List.foldl (fun b sel ↦ if sel.contains c then !b else b) (init) presses =
      !List.foldl (fun b sel ↦ if sel.contains c then !b else b) (!init) presses := by
      induction presses with
      | nil =>
          simp
      | cons t presses ih =>
          rw [List.foldl_cons, List.foldl_cons]
          simp at ih
          simp
          by_cases ht : t.contains c
          · simp [ht, ih]
          · simp [ht, ih]
    rw [this]
    simp
  · simp [h]



/-- Apply a list of line selections from left to right. -/
def LineSelection.applySequence {n : ℕ}
    (presses : List (LineSelection n)) (cfg : Config n) :
    Config n :=
  LineSelection.applyList presses cfg

@[simp] lemma LineSelection.applySequence_nil {n : ℕ} (cfg : Config n) :
    LineSelection.applySequence ([] : List (LineSelection n)) cfg = cfg := rfl

@[simp] lemma LineSelection.applySequence_cons {n : ℕ}
    (sel : LineSelection n) (presses : List (LineSelection n))
    (cfg : Config n) :
    LineSelection.applySequence (sel :: presses) cfg =
      LineSelection.applySequence presses (sel.toggle cfg) := rfl

/-- Swapping adjacent selections in a sequence leaves the result unchanged. -/
lemma LineSelection.applySequence_swap {n : ℕ}
    (sel₁ sel₂ : LineSelection n) (presses : List (LineSelection n))
    (cfg : Config n) :
    LineSelection.applySequence (sel₁ :: sel₂ :: presses) cfg =
      LineSelection.applySequence (sel₂ :: sel₁ :: presses) cfg := by
  classical
  simpa [LineSelection.applySequence] using
    LineSelection.applyList_comm sel₁ sel₂ presses cfg

/-- Pressing the same line twice in a row has no effect. -/
lemma LineSelection.applySequence_cancel {n : ℕ}
    (sel : LineSelection n) (presses : List (LineSelection n))
    (cfg : Config n) :
    LineSelection.applySequence (sel :: sel :: presses) cfg =
      LineSelection.applySequence presses cfg := by
  classical
  simp [LineSelection.applySequence, LineSelection.applyList,
    LineSelection.toggle_toggle, List.foldl]

lemma LineSelection.paritySel_of_nodup {n : ℕ}
    {presses : List (LineSelection n)} (h : presses.Nodup)
    (sel : LineSelection n) :
    LineSelection.paritySel presses sel =
      (if sel ∈ presses then true else false) := by
  classical
  induction presses with
  | nil =>
      simp [LineSelection.paritySel]
  | cons t presses ih =>
      have hnot : t ∉ presses := List.Nodup.notMem h
      have hnodup : presses.Nodup := List.Nodup.of_cons h
      by_cases hsel : sel = t
      · subst hsel
        rw [LineSelection.paritySel_cons]
        simp only [List.mem_cons_self, if_true]
        rw [ih hnodup]
        split_ifs
        simp
      · rw [LineSelection.paritySel_cons]
        have : (t = sel) = False := by
          simp
          tauto
        simp only[this]
        simp only [if_false]
        have : sel ∈ t :: presses ↔ sel ∈ presses := by
          simp [hsel]
        simp only [this]
        rw [ih hnodup]

lemma LineSelection.parityContains_eq_axes {n : ℕ}
    (presses : List (LineSelection n)) (c : Coord n) :
    LineSelection.parityContains presses c =
      Bool.xor (LineSelection.paritySel presses (LineSelection.lineX c))
        (Bool.xor (LineSelection.paritySel presses (LineSelection.lineY c))
          (LineSelection.paritySel presses (LineSelection.lineZ c))) := by
  classical
  induction presses with
  | nil =>
      simp [LineSelection.parityContains, LineSelection.paritySel]
  | cons sel presses ih =>
      by_cases h : sel.contains c
      · obtain hcases | hcases | hcases := LineSelection.contains_cases (n:=n)
          (sel := sel) (c := c) h
        · subst hcases
          rw [parityContains_cons]
          rw [paritySel_cons, paritySel_cons, paritySel_cons]
          simp only [h, if_true]
          rw [ih]
          simp
          congr 1
        · subst hcases
          rw [parityContains_cons]
          rw [paritySel_cons, paritySel_cons, paritySel_cons]
          simp only [h, if_true]
          rw [ih]
          simp
          congr 1
        . subst hcases
          rw [parityContains_cons]
          rw [paritySel_cons, paritySel_cons, paritySel_cons]
          simp only [h, if_true]
          rw [ih]
          simp
          congr 1
      · rw [parityContains_cons]
        rw [paritySel_cons, paritySel_cons, paritySel_cons]
        rw [ih]
        simp only [h, if_false]
        have hx : ¬ (sel = LineSelection.lineX c) := by
          intro heq
          subst heq
          apply h
          apply LineSelection.contains_lineX
        have hy : ¬ (sel = LineSelection.lineY c) := by
          intro heq
          subst heq
          apply h
          apply LineSelection.contains_lineY
        have hz : ¬ (sel = LineSelection.lineZ c) := by
          intro heq
          subst heq
          apply h
          apply LineSelection.contains_lineZ
        simp [hx, hy, hz]

lemma LineSelection.paritySel_sequenceOfStandardSet {n : ℕ}
    (standard : Finset (LineSelection n)) (sel : LineSelection n) :
    LineSelection.paritySel (LineSelection.sequenceOfStandardSet standard) sel =
      (if sel ∈ standard then true else false) := by
  classical
  have hnodup := LineSelection.sequenceOfStandardSet_nodup (n := n) standard
  have := LineSelection.paritySel_of_nodup (n := n) (presses := _)
    hnodup sel
  -- evaluate membership in filtered list
  simpa [LineSelection.sequenceOfStandardSet, LineSelection.mem_all,
    List.mem_filter, and_left_comm, and_self_right] using this

lemma LineSelection.paritySel_standardSequence {n : ℕ}
    (presses : List (LineSelection n)) (sel : LineSelection n) :
    LineSelection.paritySel (LineSelection.standardSequence presses) sel =
      LineSelection.paritySel presses sel := by
  classical
  have := LineSelection.paritySel_sequenceOfStandardSet
    (n := n) (standard := LineSelection.standardSet presses) sel
  simpa [LineSelection.mem_standardSet_iff, LineSelection.standardSequence]
    using this

lemma LineSelection.parityContains_standardSequence {n : ℕ}
    (presses : List (LineSelection n)) (c : Coord n) :
    LineSelection.parityContains (LineSelection.standardSequence presses) c =
      LineSelection.parityContains presses c := by
  classical
  have hx := LineSelection.paritySel_standardSequence (n := n) presses
    (LineSelection.lineX c)
  have hy := LineSelection.paritySel_standardSequence (n := n) presses
    (LineSelection.lineY c)
  have hz := LineSelection.paritySel_standardSequence (n := n) presses
    (LineSelection.lineZ c)
  rw [LineSelection.parityContains_eq_axes] at *
  rw [hx, hy, hz]
  have := LineSelection.parityContains_eq_axes (n := n)
    (presses := presses) (c := c)
  exact id (Eq.symm this)

lemma LineSelection.applyList_parity {n : ℕ}
    (presses : List (LineSelection n)) (cfg : Config n) (c : Coord n) :
    LineSelection.applyList presses cfg c =
      if LineSelection.parityContains presses c then
        not (cfg c)
      else
        cfg c := by
  classical
  induction presses generalizing cfg with
  | nil =>
      simp [LineSelection.parityContains]
  | cons sel presses ih =>
      rw [LineSelection.applyList_cons, LineSelection.parityContains_cons, ih]
      by_cases h : sel.contains c
      · simp only [h, if_true]
        by_cases h1 : LineSelection.parityContains presses c
        · simp [h1, h]
        · simp [h1, h]
      · simp only [h, if_false]
        by_cases h1 : LineSelection.parityContains presses c
        · simp [h1, h]
        · simp [h1, h]

lemma LineSelection.applyList_standardSequence {n : ℕ}
    (presses : List (LineSelection n)) (cfg : Config n) :
    LineSelection.applyList presses cfg =
      LineSelection.applyList (LineSelection.standardSequence presses) cfg := by
  classical
  funext c
  simp [LineSelection.applyList_parity, LineSelection.parityContains_standardSequence]

/-- `reachable cfg cfg'` means there exists a sequence of line selections that transforms
`cfg` into `cfg'`. -/
def reachable {n : ℕ} (cfg cfg' : Config n) : Prop :=
  ∃ presses : List (LineSelection n),
    LineSelection.applyList presses cfg = cfg'

/-- Reachability can be phrased in terms of the canonical finite set of pressed lines. -/
theorem reachable_of_finset_iff {n : ℕ}
    (cfg cfg' : Config n) :
    reachable cfg cfg' ↔
      ∃ standard : Finset (LineSelection n),
        LineSelection.applyList (LineSelection.sequenceOfStandardSet standard) cfg = cfg' := by
  classical
  constructor
  · rintro ⟨presses, hpress⟩
    let standard := LineSelection.standardSet presses
    use standard
    have hseq := LineSelection.applyList_standardSequence presses cfg
    rw [hpress] at hseq
    exact hseq.symm
  · rintro ⟨standard, hstandard⟩
    let presses := LineSelection.sequenceOfStandardSet standard
    use presses

/-- Reachability is equivalent to appearing among the sublists of the complete enumeration
of line selections. -/
theorem reachable_of_lineSelection_all {n : ℕ}
    (cfg cfg' : Config n) :
    reachable cfg cfg' ↔
      ∃ presses ∈  (LineSelection.all n).sublists,
        LineSelection.applyList presses cfg = cfg' := by
  classical
  constructor
  · intro hreach
    obtain ⟨standard, hstandard⟩ :=
      (reachable_of_finset_iff (cfg := cfg) (cfg' := cfg')).1 hreach
    refine ⟨LineSelection.sequenceOfStandardSet standard, ?_, hstandard⟩
    unfold LineSelection.sequenceOfStandardSet
    have hSub :
        List.Sublist
          ((LineSelection.all n).filter
            (fun sel : LineSelection n => sel ∈ standard))
          (LineSelection.all n) :=
      List.filter_sublist
        (p := fun sel : LineSelection n => sel ∈ standard)
        (l := LineSelection.all n)
    exact (List.mem_sublists).2 hSub
  · rintro ⟨presses, _, hpress⟩
    exact ⟨presses, hpress⟩

/-- Boolean test that enumerates every sublist of `LineSelection.all n` and checks whether it
reaches `cfg'` from `cfg`. -/
def reachable_from_lineSelection_all {n : ℕ}
    (cfg cfg': Config n) :
    Bool :=
  ((LineSelection.all n).sublists).any
    (fun presses => configsEqual (LineSelection.applyList presses cfg) cfg')

/-- The Boolean test `reachable_from_lineSelection_all` agrees with the propositional notion
`reachable`. -/
theorem reachable_iff_reachable_from_lineSelection_all {n : ℕ}
    (cfg cfg' : Config n) :
    reachable cfg cfg' ↔
      reachable_from_lineSelection_all cfg cfg' = true := by
  classical
  have any_iff :
      (((LineSelection.all n).sublists).any
          (fun presses => configsEqual (LineSelection.applyList presses cfg) cfg')) =
        true ↔
        ∃ presses ∈ (LineSelection.all n).sublists,
          configsEqual (LineSelection.applyList presses cfg) cfg' = true :=
    List.any_eq_true
      (l := (LineSelection.all n).sublists)
      (p := fun presses => configsEqual (LineSelection.applyList presses cfg) cfg')
  have any_iff_eq :
      (((LineSelection.all n).sublists).any
          (fun presses => configsEqual (LineSelection.applyList presses cfg) cfg')) =
        true ↔
        ∃ presses ∈ (LineSelection.all n).sublists,
          LineSelection.applyList presses cfg = cfg' := by
    refine any_iff.trans ?_
    constructor
    · intro h
      rcases h with ⟨presses, hmem, hcfg⟩
      exact ⟨presses, hmem,
        (configsEqual_eq_true (cfg₁ := LineSelection.applyList presses cfg) (cfg₂ := cfg')).1 hcfg⟩
    · intro h
      rcases h with ⟨presses, hmem, happly⟩
      refine ⟨presses, hmem,
        (configsEqual_eq_true (cfg₁ := LineSelection.applyList presses cfg) (cfg₂ := cfg')).2 happly⟩
  constructor
  · intro hreach
    obtain ⟨presses, hpress_mem, hpress_apply⟩ :=
      (reachable_of_lineSelection_all (cfg := cfg) (cfg' := cfg')).1 hreach
    unfold reachable_from_lineSelection_all
    exact any_iff_eq.mpr ⟨presses, hpress_mem, hpress_apply⟩
  · intro hbool
    unfold reachable_from_lineSelection_all at hbool
    obtain ⟨presses, hpress_mem, hpress_apply⟩ := any_iff_eq.mp hbool
    exact
      (reachable_of_lineSelection_all (cfg := cfg) (cfg' := cfg')).2
        ⟨presses, hpress_mem, hpress_apply⟩


end  TPPmark2025

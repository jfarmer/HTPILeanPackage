import HTPILib.Chap5
namespace HTPI.Exercises

/- Section 5.1 -/
-- 1.
theorem func_from_graph_ltr {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) → is_func_graph F := by

  assume h1 : ∃ (f : A → B), graph f = F
  obtain (f : A → B) (hf : graph f = F) from h1

  define

  fix a : A

  exists_unique
  · apply Exists.intro (f a)
    rw [←hf]
    rfl
  · fix b1 : B
    fix b2 : B

    assume hb1 : (a, b1) ∈ F
    assume hb2 : (a, b2) ∈ F

    rewrite [←hf] at hb1
    rewrite [←hf] at hb2

    define at hb1; define at hb2

    rw [←hb1, ←hb2]
  done

-- 2.
theorem Exercise_5_1_13a
    {A B C : Type} (R : Set (A × B)) (S : Set (B × C)) (f : A → C)
    (h1 : ∀ (b : B), b ∈ Ran R ∧ b ∈ Dom S) (h2 : graph f = comp S R) :
    is_func_graph S := sorry

-- 3.
theorem Exercise_5_1_14a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : A), R x y ↔ S (f x) (f y)) :
    reflexive S → reflexive R := sorry

-- 4.
--You might not be able to complete this proof
theorem Exercise_5_1_15a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    reflexive R → reflexive S := sorry

-- 5.
--You might not be able to complete this proof
theorem Exercise_5_1_15c
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    transitive R → transitive S := sorry

-- 6.
theorem Exercise_5_1_16b
    {A B : Type} (R : BinRel B) (S : BinRel (A → B))
    (h : ∀ (f g : A → B), S f g ↔ ∀ (x : A), R (f x) (g x)) :
    symmetric R → symmetric S := sorry

-- 7.
theorem Exercise_5_1_17a {A : Type} (f : A → A) (a : A)
    (h : ∀ (x : A), f x = a) : ∀ (g : A → A), f ∘ g = f := sorry

-- 8.
theorem Exercise_5_1_17b {A : Type} (f : A → A) (a : A)
    (h : ∀ (g : A → A), f ∘ g = f) :
    ∃ (y : A), ∀ (x : A), f x = y := sorry

/- Section 5.2 -/
-- 1.
theorem Exercise_5_2_10a {A B C : Type} (f: A → B) (g : B → C) :
    onto (g ∘ f) → onto g := by

  assume h_gof_onto : onto (g ∘ f)
  define at h_gof_onto; define

  fix c : C

  obtain (a : A) (ha : (g ∘ f) a = c) from h_gof_onto c

  apply Exists.intro (f a)
  exact ha
  done

-- 2.
theorem Exercise_5_2_10b
    {A B C : Type}
    (f: A → B) (g : B → C) :
    one_to_one (g ∘ f) → one_to_one f := by

  assume igof : one_to_one (g ∘ f)
  define at igof;define

  fix a1 : A
  fix a2 : A

  assume hfa : f a1 = f a2

  have hgf : (g ∘ f) a1 = (g ∘ f) a2 := by rw [comp_def, comp_def, hfa]

  exact igof a1 a2 hgf
  done

-- 3.
theorem Exercise_5_2_11a {A B C : Type} (f: A → B) (g : B → C) :
    onto f → ¬(one_to_one g) → ¬(one_to_one (g ∘ f)) := by

  assume hf : onto f
  contrapos
  assume hgf : one_to_one (g ∘ f)

  define at hf; define at hgf; define

  fix b1: B
  fix b2: B

  obtain (a1: A) (ha1: f a1 = b1) from hf b1
  obtain (a2: A) (ha2: f a2 = b2) from hf b2

  rewrite [←ha1, ←ha2]
  assume hg

  have ha1_a2: a1 = a2 := hgf a1 a2 hg

  rw [ha1_a2]
  done

-- 4.
theorem Exercise_5_2_11b {A B C : Type} (f: A → B) (g : B → C) :
    ¬(onto f) → one_to_one g → ¬(onto (g ∘ f)) := by
  assume f_not_surj : ¬(onto f)
  assume g_inj : one_to_one g

  define at f_not_surj
  quant_neg at f_not_surj

  obtain (b: B) (hb: ¬∃ (x : A), f x = b) from f_not_surj
  quant_neg at hb

  define; quant_neg

  apply Exists.intro (g b)

  quant_neg; fix a: A

  -- g (f a) = g b → f a = b
  have h := g_inj (f a) b
  contrapos at h

  show (¬g (f a) = g b) from h (hb a)
  done

-- 5.
theorem Exercise_5_2_12 {A B : Type} (f : A → B) (g : B → Set A)
    (h : ∀ (b : B), g b = {a : A | f a = b}) :
    onto f → one_to_one g := sorry

-- 6.
theorem Exercise_5_2_16 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) (f : A → C) (g : B → C)
    (h1 : graph f = comp S R) (h2 : graph g = S) (h3 : one_to_one g) :
    is_func_graph R := sorry

-- 7.
theorem Exercise_5_2_17a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : onto f) : reflexive R → reflexive S := sorry

-- 8.
theorem Exercise_5_2_17b
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : one_to_one f) : transitive R → transitive S := sorry

-- 9.
theorem Exercise_5_2_21a {A B C : Type} (f : B → C) (g h : A → B)
    (h1 : one_to_one f) (h2 : f ∘ g = f ∘ h) : g = h := sorry

-- 10.
theorem Exercise_5_2_21b {A B C : Type} (f : B → C) (a : A)
    (h1 : ∀ (g h : A → B), f ∘ g = f ∘ h → g = h) :
    one_to_one f := sorry

/- Section 5.3 -/
-- 1.
theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := by

  apply funext
  fix b : B

  have h : (b, g b) ∈ inv (graph f) := by
    rw [← h1]
    rfl
    done

  show (f ∘ g) b = id b from h
  done

-- 2.
theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : f ∘ g = id) : onto f := by
  define
  fix b : B

  apply Exists.intro (g b)

  rw [← comp_def f g, h1]
  rfl
  done

lemma inj_right_inv_is_left_inv {A B : Type} (f : A → B) (g : B → A)
    (h1 : one_to_one f) (h2 : f ∘ g = id) :
    g ∘ f = id := by

  define at h1

  apply funext
  fix a : A

  have h : f (g (f a)) = f a := by
    calc f (g (f a))
      _ = (f ∘ g) (f a) := by rfl
      _ = id (f a) := by rw [h2]
      _ = f a := by rfl
    done

  apply h1 (g (f a)) a
  exact h
  done

-- 3.
theorem Exercise_5_3_11a {A B : Type} (f : A → B) (g : B → A) :
    one_to_one f → f ∘ g = id → graph g = inv (graph f) := by

  assume h_f_inj : one_to_one f
  assume h_fog_id : f ∘ g = id

  have h_f_onto : onto f :=
    Theorem_5_3_3_2 f g h_fog_id

  have h_gof_id : g ∘ f = id :=
    inj_right_inv_is_left_inv f g h_f_inj h_fog_id

  exact Theorem_5_3_5 f g h_gof_id h_fog_id
  done

-- 4.
theorem Exercise_5_3_11b {A B : Type} (f : A → B) (g : B → A) :
    onto f → g ∘ f = id → graph g = inv (graph f) := sorry

-- 5.
theorem Exercise_5_3_14a {A B : Type} (f : A → B) (g : B → A)
    (h : f ∘ g = id) : ∀ x ∈ Ran (graph g), g (f x) = x := sorry

-- 6.
theorem Exercise_5_3_18 {A B C : Type} (f : A → C) (g : B → C)
    (h1 : one_to_one g) (h2 : onto g) :
    ∃ (h : A → B), g ∘ h = f := by
  obtain g_inv h_ginv from Theorem_5_3_1 g h1 h2
  have h_g_id : (g ∘ g_inv = id) := Theorem_5_3_2_2 g g_inv h_ginv

  apply Exists.intro (g_inv ∘ f)

  show g ∘ g_inv ∘ f = f from
    calc g ∘ g_inv ∘ f
      _ = (g ∘ g_inv) ∘ f := by rfl
      _ = id ∘ f := by rw [h_g_id]
      _ = f := by rfl
  done

-- Definition for next two exercises:
def conjugate (A : Type) (f1 f2 : A → A) : Prop :=
    ∃ (g g' : A → A), (f1 = g' ∘ f2 ∘ g) ∧ (g ∘ g' = id) ∧ (g' ∘ g = id)

-- 7.
theorem Exercise_5_3_17a {A : Type} : symmetric (conjugate A) := sorry

-- 8.
theorem Exercise_5_3_17b {A : Type} (f1 f2 : A → A)
    (h1 : conjugate A f1 f2) (h2 : ∃ (a : A), f1 a = a) :
    ∃ (a : A), f2 a = a := sorry

/- Section 5.4 -/
-- 1.
example {A : Type} (F : Set (Set A)) (B : Set A) :
    smallestElt (sub A) B F → B = ⋂₀ F := sorry

-- 2.
def complement {A : Type} (B : Set A) : Set A := {a : A | a ∉ B}

theorem Exercise_5_4_7 {A : Type} (f g : A → A) (C : Set A)
    (h1 : f ∘ g = id) (h2 : closed f C) : closed g (complement C) := sorry

theorem inter_subset_union {A: Type} (X Y : Set A):
    X ∩ Y ⊆ X ∪ Y := by
  fix a : A
  assume ainXY : a ∈ X ∩ Y

  apply Or.inl
  exact ainXY.left
  done

theorem inter_of_closed_is_closed {A : Type} (f : A → A) (X Y : Set A)
    (h1 : closed f X) (h2 : closed f Y) : closed f (X ∩ Y) := by

  define at h1; define at h2; define

  fix a : A
  assume ainXY

  exact ⟨h1 a ainXY.left, h2 a ainXY.right⟩
  done

-- 3.
theorem Exercise_5_4_9a {A : Type} (f : A → A) (C1 C2 : Set A)
    (h1 : closed f C1) (h2 : closed f C2) : closed f (C1 ∪ C2) := by
  fix a : A
  define at h1; define at h2

  assume a_in_union : a ∈ C1 ∪ C2

  by_cases on a_in_union
  · apply Or.inl
    exact h1 a a_in_union
  · apply Or.inr
    exact h2 a a_in_union
  done

-- 4.
theorem Exercise_5_4_10a {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    B1 ⊆ B2 → C1 ⊆ C2 := sorry

-- 5.
theorem Exercise_5_4_10b {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    closure f (B1 ∪ B2) (C1 ∪ C2) := sorry

-- 6.
theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

-- 7.
theorem Exercise_5_4_13a {A : Type} (F : Set (A → A)) (B : Set A) :
    ∃ (C : Set A), closure_family F B C := sorry

/- Section 5.5 -/

--Warning!  Not all of these examples are correct!
example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∪ X) = image f W ∪ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W \ X) = image f W \ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    W ⊆ X ↔ image f W ⊆ image f X := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∩ Z) =
        inverse_image f Y ∩ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∪ Z) =
        inverse_image f Y ∪ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y \ Z) =
        inverse_image f Y \ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    Y ⊆ Z ↔ inverse_image f Y ⊆ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (X : Set A) :
    inverse_image f (image f X) = X := sorry

example {A B : Type} (f : A → B) (Y : Set B) :
    image f (inverse_image f Y) = Y := sorry

example {A : Type} (f : A → A) (C : Set A) :
    closed f C → image f C ⊆ C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    image f C ⊆ C → C ⊆ inverse_image f C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    C ⊆ inverse_image f C → closed f C := sorry

example {A B : Type} (f : A → B) (g : B → A) (Y : Set B)
    (h1 : f ∘ g = id) (h2 : g ∘ f = id) :
    inverse_image f Y = image g Y := sorry

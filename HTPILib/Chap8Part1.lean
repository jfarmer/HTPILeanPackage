import Chap5
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

/- Definition of equinumerous -/

def invRel {A B : Type} (R : Rel A B) : Rel B A :=
  RelFromExt (inv (extension R))

lemma invRel_def {A B : Type} (R : Rel A B) (a : A) (b : B) :
    invRel R b a ↔ R a b := by rfl

def rel_within {A B : Type} (R : Rel A B) (X : Set A) (Y : Set B) : Prop :=
  ∀ ⦃x : A⦄ ⦃y : B⦄, R x y → x ∈ X ∧ y ∈ Y

def fcnl_on {A B : Type} (R : Rel A B) (X : Set A) : Prop :=
  ∀ ⦃x : A⦄, x ∈ X → ∃! (y : B), R x y

def matching {A B : Type} (R : Rel A B) (X : Set A) (Y : Set B) : Prop :=
  rel_within R X Y ∧ fcnl_on R X ∧ fcnl_on (invRel R) Y

def equinum {A B : Type} (X : Set A) (Y : Set B) : Prop :=
  ∃ (R : Rel A B), matching R X Y

notation:50  X:50 " ∼ " Y:50 => equinum X Y

def RelWithinFromFunc {A B : Type} (f : A → B) (X : Set A)
  (x : A) (y : B) : Prop := x ∈ X ∧ f x = y

def one_one_on {A B : Type} (f : A → B) (X : Set A) : Prop :=
  ∀ ⦃x1 x2 : A⦄, x1 ∈ X → x2 ∈ X → f x1 = f x2 → x1 = x2

theorem equinum_image {A B : Type} {X : Set A} {f : A → B}
    (h1 : one_one_on f X) : X ∼ image f X := by
  define   --Goal : ∃ (R : Rel A B), matching R X (image f X)
  set R : Rel A B := RelWithinFromFunc f X
  apply Exists.intro R
  define   --Goal : rel_within R X (image f X) ∧
           --fcnl_on R X ∧ fcnl_on (invRel R) (image f X)
  apply And.intro
  · -- Proof of rel_within
    define --Goal : ∀ ⦃x : A⦄ ⦃y : B⦄, R x y → x ∈ X ∧ y ∈ image f X
    fix x : A; fix y : B
    assume h2 : R x y  --Goal : x ∈ X ∧ y ∈ image f X
    define at h2       --h2 : x ∈ X ∧ f x = y
    apply And.intro h2.left
    define
    show ∃ (x : A), x ∈ X ∧ f x = y from Exists.intro x h2
    done
  · -- Proofs of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on R X
      define  --Goal : ∀ ⦃x : A⦄, x ∈ X → ∃! (y : B), R x y
      fix x : A
      assume h2 : x ∈ X
      exists_unique
      · -- Existence
        apply Exists.intro (f x)
        define  --Goal : x ∈ X ∧ f x = f x
        apply And.intro h2
        rfl
        done
      · -- Uniqueness
        fix y1 : B; fix y2 : B
        assume h3 : R x y1
        assume h4 : R x y2   --Goal : y1 = y2
        define at h3; define at h4
          --h3 : x ∈ X ∧ f x = y1;  h4 : x ∈ X ∧ f x = y2
        rewrite [h3.right] at h4
        show y1 = y2 from h4.right
        done
      done
    · -- Proof of fcnl_on (invRel R) (image f X)
      define  --Goal : ∀ ⦃x : B⦄, x ∈ image f X → ∃! (y : A), invRel R x y
      fix y : B
      assume h2 : y ∈ image f X
      obtain (x : A) (h3 : x ∈ X ∧ f x = y) from h2
      exists_unique
      · -- Existence
        apply Exists.intro x
        define
        show x ∈ X ∧ f x = y from h3
        done
      · -- Uniqueness
        fix x1 : A; fix x2 : A
        assume h4 : invRel R y x1
        assume h5 : invRel R y x2
        define at h4; define at h5
          --h4 : x1 ∈ X ∧ f x1 = y;  h5 : x2 ∈ X ∧ f x2 = y
        rewrite [←h5.right] at h4
        show x1 = x2 from h1 h4.left h5.left h4.right
        done
      done
    done
  done

lemma one_one_on_of_one_one {A B : Type} {f : A → B}
    (h : one_to_one f) (X : Set A) : one_one_on f X := by
  define
  fix x1 : A; fix x2 : A
  assume h1 : x1 ∈ X
  assume h2 : x2 ∈ X
  show f x1 = f x2 → x1 = x2 from h x1 x2
  done

def Univ (A : Type) : Set A := { x : A | True }

lemma elt_Univ {A : Type} (a : A) :
    a ∈ Univ A := by trivial

def Range {A B : Type} (f : A → B) : Set B := image f (Univ A)

theorem equinum_Range {A B : Type} {f : A → B} (h : one_to_one f) :
    Univ A ∼ Range f := equinum_image (one_one_on_of_one_one h (Univ A))

theorem equinum_Univ {A B : Type} {f : A → B}
    (h1 : one_to_one f) (h2 : onto f) : Univ A ∼ Univ B := by
  have h3 : Univ A ∼ Range f := equinum_Range h1
  have h4 : Range f = Univ B := by
    apply Set.ext
    fix b : B
    apply Iff.intro
    · -- (→)
      assume h4 : b ∈ Range f
      show b ∈ Univ B from elt_Univ b
      done
    · -- (←)
      assume h4 : b ∈ Univ B
      obtain (a : A) (h5 : f a = b) from h2 b
      apply Exists.intro a
      apply And.intro _ h5
      show a ∈ Univ A from elt_Univ a
      done
    done
  rewrite [h4] at h3
  show Univ A ∼ Univ B from h3
  done

/- Equinumerous is an equivalence relation -/
lemma id_one_one_on {A : Type} (X : Set A) : one_one_on id X := by
  define
  fix x1 : A; fix x2 : A
  assume h1 : x1 ∈ X; assume h2 : x2 ∈ X
  assume h3 : id x1 = id x2
  show x1 = x2 from h3
  done

lemma image_id {A : Type} (X : Set A) : image id X = X := by
  apply Set.ext
  fix x : A
  apply Iff.intro
  · -- (→)
    assume h1 : x ∈ image id X
    obtain (y : A) (h2 : y ∈ X ∧ id y = x) from h1
    rewrite [←h2.right]
    show id y ∈ X from h2.left
    done
  · -- (←)
    assume h1 : x ∈ X
    apply Exists.intro x  --Goal : x ∈ X ∧ id x = x
    apply And.intro h1
    rfl
    done
  done

theorem Theorem_8_1_3_1 {A : Type} (X : Set A) : X ∼ X := by
  have h : X ∼ image id X := equinum_image (id_one_one_on X)
  rewrite [image_id] at h
  show X ∼ X from h
  done

/- Old version
def idRel_on {A : Type} (X : Set A) (a b : A) : Prop := a ∈ X ∧ a = b

lemma id_rel_within {A : Type} (X : Set A) :
    rel_within (idRel_on X) X X := by
  define
  fix a : A; fix b : A
  assume h : idRel_on X a b  --Goal : a ∈ X ∧ b ∈ X
  define at h                --h : a ∈ X ∧ a = b
  apply And.intro h.left
  rewrite [←h.right]
  show a ∈ X from h.left
  done

lemma id_fcnl {A : Type} (X : Set A) : fcnl_on (idRel_on X) X := by
  define
  fix a : A
  assume h1 : a ∈ X
  exists_unique
  · -- Existence
    apply Exists.intro a
    define   --Goal : a ∈ X ∧ a = a
    apply And.intro h1
    rfl
    done
  · -- Uniqueness
    fix b1 : A; fix b2 : A
    assume h2 : idRel_on X a b1
    assume h3 : idRel_on X a b2
    define at h2; define at h3
    rewrite [←h2.right, ←h3.right]
    rfl
    done
  done

lemma idRel_symm {A : Type} (X : Set A) (a b : A) :
    idRel_on X a b → idRel_on X b a := by
  assume h : idRel_on X a b
  define at h; define
  apply And.intro _ h.right.symm
  rewrite [←h.right]
  show a ∈ X from h.left
  done

lemma inv_id {A : Type} (X : Set A) :
    invRel (idRel_on X) = idRel_on X := by
  apply relext
  fix a : A; fix b : A
  rewrite [invRel_def] --Goal : idRel_on X b a ↔ idRel_on X a b
  show idRel_on X b a ↔ idRel_on X a b from
    Iff.intro (idRel_symm X b a) (idRel_symm X a b)
  done

lemma id_match {A : Type} (X : Set A) :
    matching (idRel_on X) X X := by
  define --Goal : rel_within (idRel_on X) X X ∧
    --fcnl_on (idRel_on X) X ∧ fcnl_on (invRel (idRel_on X)) X
  apply And.intro (id_rel_within X)
  apply And.intro (id_fcnl X)
  rewrite [inv_id]
  show fcnl_on (idRel_on X) X from id_fcnl X
  done

theorem Theorem_8_1_3_1 {A : Type} (X : Set A) : X ∼ X := by
  define   --Goal : ∃ (R : Rel A A), matching R X X
  apply Exists.intro (idRel_on X)
  show matching (idRel_on X) X X from id_match X
  done
-/

lemma inv_inv {A B : Type} (R : Rel A B) : invRel (invRel R) = R := by rfl

lemma inv_match {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B}
    (h : matching R X Y) : matching (invRel R) Y X := by
  define       --Goal : rel_within (invRel R) Y X ∧
               --fcnl_on (invRel R) Y ∧ fcnl_on (invRel (invRel R)) X
  define at h  --h : rel_within R X Y ∧ fcnl_on R X ∧ fcnl_on (invRel R) Y
  apply And.intro
  · -- Proof that rel_within R Y X
    define     --Goal : ∀ ⦃x : B⦄ ⦃y : A⦄, invRel R x y → x ∈ Y ∧ y ∈ X
    fix y : B; fix x : A
    assume h1 : invRel R y x
    define at h1  --h1 : R x y
    have h2 : x ∈ X ∧ y ∈ Y := h.left h1
    show y ∈ Y ∧ x ∈ X from And.intro h2.right h2.left
    done
  · -- proof that fcnl_on (inv R) Y ∧ fcnl_on (inv (inv R)) X
    rewrite [inv_inv]
    show fcnl_on (invRel R) Y ∧ fcnl_on R X from
      And.intro h.right.right h.right.left
    done
  done

theorem Theorem_8_1_3_2 {A B : Type} {X : Set A} {Y : Set B}
    (h : X ∼ Y) : Y ∼ X := by
  obtain (R : Rel A B) (h1 : matching R X Y) from h
  apply Exists.intro (invRel R)
  show matching (invRel R) Y X from inv_match h1
  done

def compRel {A B C : Type} (S : Rel B C) (R : Rel A B) : Rel A C :=
  RelFromExt (comp (extension S) (extension R))

lemma compRel_def {A B C : Type}
    (S : Rel B C) (R : Rel A B) (a : A) (c : C) :
    compRel S R a c ↔ ∃ (x : B), R a x ∧ S x c := by rfl

lemma inv_comp {A B C : Type} (R : Rel A B) (S : Rel B C) :
    invRel (compRel S R) = compRel (invRel R) (invRel S) := 
  calc invRel (compRel S R)
    _ = RelFromExt (inv (comp (extension S) (extension R))) := by rfl
    _ = RelFromExt (comp (inv (extension R)) (inv (extension S))) :=
        by rw [Theorem_4_2_5_5]
    _ = compRel (invRel R) (invRel S) := by rfl

/- Don't use anymore
lemma match_rel_within {A B : Type}
    {R : Rel A B} {X : Set A} {Y : Set B} {a : A} {b : B}
    (h1 : matching R X Y) (h2 : R a b) : a ∈ X ∧ b ∈ Y := h1.left h2
-/

lemma fcnl_exists {A B : Type} {R : Rel A B} {X : Set A} {x : A}
    (h1 : fcnl_on R X) (h2 : x ∈ X) : ∃ (y : B), R x y := by
  define at h1
  obtain (y : B) (h3 : R x y)
    (h4 : ∀ (y_1 y_2 : B), R x y_1 → R x y_2 → y_1 = y_2) from h1 h2
  show ∃ (y : B), R x y from Exists.intro y h3
  done

lemma fcnl_unique {A B : Type} {R : Rel A B} {X : Set A} {j : A} {u v : B}
    (h1 : fcnl_on R X) (h2 : j ∈ X) (h3 : R j u) (h4 : R j v) : u = v := by
  define at h1
  have h5 := h1 h2
  obtain z _h6 h7 from h5
  exact h7 u v h3 h4
  done

lemma comp_fcnl {A B C : Type}
    {R : Rel A B} {S : Rel B C} {X : Set A} {Y : Set B} {Z : Set C}
    (h1 : matching R X Y) (h2 : matching S Y Z) : fcnl_on (compRel S R) X := by
  define; define at h1; define at h2
  fix a
  assume h3
  obtain b h4 from fcnl_exists h1.right.left h3
  have h5 := h1.left h4
  obtain c h6 from fcnl_exists h2.right.left h5.right
  exists_unique
  · -- Existence
    apply Exists.intro c
    rewrite [compRel_def]
    exact Exists.intro b (And.intro h4 h6)
    done
  · -- Uniqueness
    fix c1; fix c2
    assume h7; assume h8
    rewrite [compRel_def] at h7
    rewrite [compRel_def] at h8
    obtain b1 h9 from h7
    obtain b2 h10 from h8
    have h11 := fcnl_unique h1.right.left h3 h9.left h4
    have h12 := fcnl_unique h1.right.left h3 h10.left h4
    rewrite [h11] at h9
    rewrite [h12] at h10
    exact fcnl_unique h2.right.left h5.right h9.right h10.right
    done
  done

lemma comp_match {A B C : Type} {R : Rel A B} {S : Rel B C}
    {X : Set A} {Y : Set B} {Z : Set C} (h1 : matching R X Y)
    (h2 : matching S Y Z) : matching (compRel S R) X Z := by
  define
  apply And.intro
  · -- Proof of rel_within (compRel S R) X Z
    define
    fix a; fix c
    assume h3 : compRel S R a c
    rewrite [compRel_def] at h3
    obtain b h4 from h3
    have h5 := h1.left h4.left
    have h6 := h2.left h4.right
    exact And.intro h5.left h6.right
    done
  · -- Proof of fcnl_on statements
    apply And.intro
    · -- Proof of fcnl_on (compRel S R) X
      exact comp_fcnl h1 h2
      done
    · -- Proof of fcnl_on (invRel (compRel S R)) Z
      rewrite [inv_comp]
      have h3 := inv_match h1
      have h4 := inv_match h2
      exact comp_fcnl h4 h3
      done
    done
  done

theorem Theorem_8_1_3_3 {A B C : Type} {X : Set A} {Y : Set B} {Z : Set C}
    (h1 : X ∼ Y) (h2 : Y ∼ Z) : X ∼ Z := by
  obtain (R : Rel A B) (h3 : matching R X Y) from h1
  obtain (S : Rel B C) (h4 : matching S Y Z) from h2
  apply Exists.intro (compRel S R)
  show matching (compRel S R) X Z from comp_match h3 h4
  done

/- Definitions of finite and denumerable -/

def I (n : Nat) : Set Nat := { k : Nat | k < n }

lemma I_def (k n : Nat) : k ∈ I n ↔ k < n := by rfl

def finite {A : Type} (X : Set A) : Prop :=
  ∃ (n : Nat), I n ∼ X

def denum {A : Type} (X : Set A) : Prop :=
  Univ Nat ∼ X

lemma denum_def {A : Type} (X : Set A) : denum X ↔ Univ Nat ∼ X := by rfl

def ctble {A : Type} (X : Set A) : Prop :=
  finite X ∨ denum X

/- Basic theorems about finite sets and number of elements -/
theorem relext {A B : Type} {R S : Rel A B}
    (h : ∀ (a : A) (b : B), R a b ↔ S a b) : R = S := by
  have h2 : extension R = extension S := by
    apply Set.ext
    fix (a, b) : A × B --Goal : (a, b) ∈ extension R ↔ (a, b) ∈ extension S
    rewrite [ext_def, ext_def]  --Goal : R a b ↔ S a b
    show R a b ↔ S a b from h a b
    done
  show R = S from
    calc R
      _ = RelFromExt (extension R) := by rfl
      _ = RelFromExt (extension S) := by rw [h2]
      _ = S := by rfl
  done

def numElts {A : Type} (X : Set A) (n : Nat) : Prop :=
    I n ∼ X

lemma numElts_def {A : Type} (X : Set A) (n : Nat) : numElts X n ↔ I n ∼ X := by rfl

lemma I_0_empty : empty (I 0) := by
  define
  by_contra h1
  obtain x h2 from h1
  define at h2
  linarith
  done

lemma I_1_singleton : I 1 = {0} := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- (→)
    assume h1
    rewrite [I_def] at h1
    define
    linarith
    done
  · -- (←)
    assume h1
    define at h1
    rewrite [h1, I_def]
    linarith
    done
  done

lemma I_diff (n : Nat) : I (n + 1) \ {n} = I n := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- (→)
    assume h1
    define
    define at h1
    have h2 := h1.left
    have h3 := h1.right
    define at h2
    define at h3
    have h4 : x ≤ n := Nat.le_of_lt_succ h2
    show x < n from Nat.lt_of_le_of_ne h4 h3
    done
  · -- (←)
    assume h1
    define at h1
    define
    apply And.intro
    · -- Proof that x ∈ I (n + 1)
      define
      linarith
      done
    · -- Proof that x ∉ {n}
      by_contra h2
      define at h2
      linarith
      done
    done
  done

lemma I_max (n : Nat) : n ∈ I (n + 1) := by
  define
  linarith
  done

def remove_one {A B : Type} (R : Rel A B) (u : A) (v : B) (x : A) (y : B) : Prop :=
    x ≠ u ∧ y ≠ v ∧ (R x y ∨ (R x v ∧ R u y))

theorem remove_one_rel_within {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {x u : A} {y v : B}
    (h1 : matching R X Y) (h2 : remove_one R u v x y) : x ∈ X \ {u} ∧ y ∈ Y \ {v} := by
  define at h2
  have h3 : x ∈ X ∧ y ∈ Y := by
    by_cases on h2.right.right with h3
    · -- Case 1. h3: R x y
      exact h1.left h3
      done
    · -- Case 2. h3: R x v ∧ R y u
      have h4 := h1.left h3.left
      have h5 := h1.left h3.right
      exact And.intro h4.left h5.right
      done
    done
  exact And.intro (And.intro h3.left h2.left) (And.intro h3.right h2.right.left)
  done

theorem remove_inv_comm {A B : Type} (R : Rel A B) (u : A) (v : B) :
    invRel (remove_one R u v) = remove_one (invRel R) v u := by
  apply relext
  fix b; fix a
  define : invRel (remove_one R u v) b a
  define : remove_one (invRel R) v u b a
  rewrite [invRel_def, invRel_def, invRel_def]
  rewrite [←and_assoc, @and_comm (¬a = u), and_assoc, @and_comm (R a v)]
  rfl
  done

theorem remove_one_Rxv {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {x u : A} {v : B}
    (h1 : matching R X Y) (h2 : x ≠ u) (h3 : R x v) :
    ∀ (y : B), remove_one R u v x y ↔ R u y := by
  fix y
  define at h1
  have h4 := h1.left h3
  apply Iff.intro
  · -- (→)
    assume h5
    define at h5
    by_cases on h5.right.right with h6
    · -- Case 1. h6: (x, y) ∈ R
      have h7 := fcnl_unique h1.right.left h4.left h6 h3
      exact absurd h7 h5.right.left
      done
    · -- Case 2. h6: (x, v) ∈ R ∧ (u, y) ∈ R
      exact h6.right
      done
    done
  · -- (←)
    assume h5
    define
    apply And.intro h2
    apply And.intro _ (Or.inr (And.intro h3 h5))
    contradict h2 with h6
    rewrite [h6] at h5
    exact fcnl_unique h1.right.right h4.right h3 h5
    done
  done

theorem remove_one_not_Rxv {A B : Type} {R : Rel A B} {x u : A} {v : B}
    (h2 : x ≠ u) (h3 : ¬R x v) :
    ∀ (y : B), remove_one R u v x y ↔ R x y := by
  fix y
  apply Iff.intro
  · -- (→)
    assume h4
    define at h4
    by_cases on h4.right.right with h5
    · -- Case 1. h5: (x, y) ∈ R
      exact h5
      done
    · -- Case 2. h5: (x, v) ∈ R ∧ (u, y) ∈ R
      exact absurd h5.left h3
      done
    done
  · -- (←)
    assume h4
    define
    apply And.intro h2
    apply And.intro _ (Or.inl h4)
    contradict h3 with h5
    rewrite [h5] at h4
    exact h4
    done
  done

theorem remove_one_fcnl {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {u : A}
    (h1 : matching R X Y) (h2 : u ∈ X) (v : B): fcnl_on (remove_one R u v) (X \ {u}) := by
  define
  fix x
  assume h3
  define at h3
  have h4 : ∃ (w : A), w ∈ X ∧ ∀ (y : B), remove_one R u v x y ↔ R w y := by
    by_cases h4 : R x v
    · -- Case 1. h4 : R x v
      apply Exists.intro u
      apply And.intro h2
      exact remove_one_Rxv h1 h3.right h4
      done
    · -- Case 2. h4 : ¬R x v
      apply Exists.intro x
      apply And.intro h3.left
      exact remove_one_not_Rxv h3.right h4
      done
    done
  obtain w h5 from h4
  define at h1
  exists_unique
  · -- Existence
    obtain y h6 from fcnl_exists h1.right.left h5.left
    apply Exists.intro y
    rewrite [h5.right]
    exact h6
    done
  · -- Uniqueness
    fix y1; fix y2
    rewrite [h5.right, h5.right]
    assume h6; assume h7
    exact fcnl_unique h1.right.left h5.left h6 h7
    done
  done

theorem remove_one_match {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {u : A} {v : B}
    (h1 : matching R X Y) (h2 : u ∈ X) (h3 : v ∈ Y) :
    matching (remove_one R u v) (X \ {u}) (Y \ {v}) := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix x; fix y
    assume h4
    exact remove_one_rel_within h1 h4
    done
  · -- Proof of fcnl_ons
    apply And.intro (remove_one_fcnl h1 h2 v)
    rewrite [remove_inv_comm]
    exact remove_one_fcnl (inv_match h1) h3 u
  done

theorem remove_one_equinum {A B : Type} {X : Set A} {Y : Set B} {x : A} {y : B}
    (h1 : X ∼ Y) (h2 : x ∈ X) (h3 : y ∈ Y) : X \ { x } ∼ Y \ { y } := by
  define
  obtain R h4 from h1
  apply Exists.intro (remove_one R x y)
  exact remove_one_match h4 h2 h3
  done

theorem remove_one_numElts {A : Type} {X : Set A} {n : Nat} {x : A}
    (h1 : numElts X (n + 1)) (h2 : x ∈ X) : numElts (X \ {x}) n := by
  have h3 : n ∈ I (n + 1) := I_max n
  rewrite [numElts_def] at h1
  have h4 := remove_one_equinum h1 h3 h2
  rewrite [I_diff] at h4
  exact h4
  done

lemma fcnl_on_empty {A B : Type} (R : Rel A B) {X : Set A} (h : empty X) : fcnl_on R X := by
  define
  fix a
  assume h2
  contradict h
  exact Exists.intro a h2
  done

def emptyRel (A B : Type) (a : A) (b : B) : Prop := False

lemma empty_match {A B : Type} {X : Set A} {Y : Set B} (h1 : empty X) (h2 : empty Y) :
    matching (emptyRel A B) X Y := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix a; fix b
    assume h
    define at h
    exact False.elim h
    done
  · -- Proof of fcnl_on
    apply And.intro
    · -- Proof of fcnl_on emptyRel
      exact fcnl_on_empty (emptyRel A B) h1
      done
    · -- Proof of fcnl_on (invRel emptyRel)
      exact fcnl_on_empty (invRel (emptyRel A B)) h2
      done
  done

theorem zero_elts_iff_empty {A : Type} (X : Set A) : numElts X 0 ↔ empty X := by
  apply Iff.intro
  · -- (→)
    assume h1
    define
    by_contra h2
    obtain x h3 from h2
    define at h1
    obtain R h4 from h1
    define at h4
    obtain j h5 from fcnl_exists h4.right.right h3
    define at h5
    have h6 := h4.left h5
    contradict I_0_empty
    exact Exists.intro j h6.left
    done
  · -- (←)
    assume h1
    define
    exact Exists.intro (emptyRel Nat A) (empty_match I_0_empty h1)
    done
  done

def one_match {A B : Type} (a : A) (b : B) (x : A) (y : B) : Prop :=
    x = a ∧ y = b

theorem one_match_fcnl {A B : Type} (a : A) (b : B) :
    fcnl_on (one_match a b) {a} := by
  define
  fix x
  assume h1
  define at h1
  rewrite [h1]
  exists_unique
  · -- Existence
    apply Exists.intro b
    define
    apply And.intro
    rfl
    rfl
    done
  · -- Uniqueness
    fix b1; fix b2
    assume h2; assume h3
    define at h2; define at h3
    rewrite [h3.right]
    exact h2.right
    done
  done

theorem one_elt_iff_singleton {A : Type} (X : Set A) : numElts X 1 ↔ ∃ (x : A), X = {x} := by
  define : numElts X 1
  rewrite [I_1_singleton]
  apply Iff.intro
  · -- (→)
    assume h1
    obtain R h2 from h1
    define at h2
    have h3 : 0 ∈ {0} := by define; rfl
    obtain x h4 from fcnl_exists h2.right.left h3
    have h5 := h2.left h4
    apply Exists.intro x
    apply Set.ext
    fix a
    apply Iff.intro
    · -- (→)
      assume h6
      define
      obtain j h7 from fcnl_exists h2.right.right h6
      define at h7
      have h8 := h2.left h7
      have h9 := h8.left
      define at h9
      rewrite [h9] at h7
      exact fcnl_unique h2.right.left h3 h7 h4
      done
    · -- (←)
      assume h6
      define at h6
      rewrite [h6]
      exact h5.right
      done
    done
  · -- (←)
    assume h1
    obtain x h2 from h1
    set R : Rel Nat A := one_match 0 x
    apply Exists.intro R
    define
    apply And.intro
    · -- Proof of rel_within R {0} X
      define
      fix n; fix a
      assume h3
      define at h3
      rewrite [h3.left, h3.right, h2]
      apply And.intro
      · -- Proof that 0 ∈ {0}
        define
        rfl
        done
      · -- Proof that x ∈ {x}
        define
        rfl
        done
      done
    · -- Proof of fcnls
      apply And.intro
      · -- Proof that fcnl_on R {0}
        exact one_match_fcnl 0 x
        done
      · -- Proof that fcnl_on (inv R) X
        have h3 : invRel R = one_match x 0 := by
          apply relext
          fix y; fix n
          define : invRel R y n
          define : one_match x 0 y n
          rewrite [and_comm]
          rfl
          done
        rewrite [h2, h3]     
        exact one_match_fcnl x 0
        done
      done
    done
  done

theorem nonempty_of_pos_numElts {A : Type} {X : Set A} {n : Nat}
    (h1 : numElts X n) (h2 : n > 0) : ∃ (x : A), x ∈ X := by
  define at h1
  obtain R h3 from h1
  define at h3
  have h4 : 0 ∈ I n := h2
  obtain x h5 from fcnl_exists h3.right.left h4
  have h6 := h3.left h5
  exact Exists.intro x h6.right
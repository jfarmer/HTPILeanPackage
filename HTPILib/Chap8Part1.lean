import Chap5
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

-- Version of finite sets using relations rather than sets of ordered pairs

theorem RelExt {A B : Type} (R S : Rel A B)
    (h : ∀ (a : A) (b : B), R a b ↔ S a b) : R = S := by
  apply funext
  fix a
  apply funext
  fix b
  rewrite [h]
  rfl

def invRel {A B : Type} (R : Rel A B) (b : B) (a : A) : Prop := R a b

theorem invRel_invRel {A B : Type} (R : Rel A B) : invRel (invRel R) = R := by
  apply RelExt
  fix a; fix b
  rfl
  done

theorem invRel_def {A B : Type} (R : Rel A B) (a : A) (b : B) :
    invRel R b a ↔ R a b := by rfl

/- Basic properties of finite sets -/

def I (n : Nat) : Set Nat := { k : Nat | 1 ≤ k ∧ k ≤ n }

theorem I_1 {n : Nat} (h : n > 0) : 1 ∈ I n := by
  define
  apply And.intro _ h
  norm_num
  done

theorem I_top {n : Nat} (h : n > 0) : n ∈ I n := by
  define
  apply And.intro h
  linarith
  done

theorem I_0_empty : empty (I 0) := by
  define
  by_contra h1
  obtain x h2 from h1
  define at h2
  linarith
  done

theorem I_1_singleton : I 1 = {1} := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- (→)
    assume h1
    define at h1
    define
    exact Nat.le_antisymm h1.right h1.left
    done
  · -- (←)
    assume h1
    define at h1
    rewrite [h1]
    exact I_1 zero_lt_one
    done
  done

theorem I_diff (n : Nat) : I (n + 1) \ { n + 1 } = I n := by
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
    apply And.intro h2.left
    have h4 : x < n + 1 := Nat.lt_of_le_of_ne h2.right h3
    exact Nat.le_of_lt_succ h4
    done
  · -- (←)
    assume h1
    define; define at h1
    apply And.intro
    · -- Proof that x ∈ I (n + 1)
      define
      apply And.intro h1.left
      linarith
      done
    · -- Proof that x ∉ {n + 1}
      by_contra h2
      define at h2
      rewrite [h2] at h1
      linarith
      done
    done
  done

def pairing {A B : Type} (R : Rel A B) (X : Set A) (Y : Set B) : Prop :=
    ∀ (x : A) (y : B), R x y → x ∈ X ∧ y ∈ Y

def match_from {A B : Type} (R : Rel A B) (X : Set A) : Prop :=
    ∀ x ∈ X, ∃! (y : B), R x y

def matching {A B : Type} (R : Rel A B) (X : Set A) (Y : Set B) : Prop :=
    pairing R X Y ∧ match_from R X ∧ match_from (invRel R) Y

def equinum {A B : Type} (X : Set A) (Y : Set B) : Prop :=
    ∃ (R : Rel A B), matching R X Y

def numElts {A : Type} (X : Set A) (n : Nat) : Prop :=
    equinum (I n) X

def finite {A : Type} (X : Set A) : Prop :=
    ∃ (n : Nat), numElts X n

theorem match_pair {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {a : A} {b : B}
    (h1 : matching R X Y) (h2 : R a b) : a ∈ X ∧ b ∈ Y := by
  define at h1
  have h3 := h1.left
  define at h3
  exact h3 a b h2
  done

theorem match_inv {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B}
    (h : matching R X Y) : matching (invRel R) Y X := by
  define
  apply And.intro
  · -- Proof that pairing R Y X
    define
    fix y; fix x
    assume h1
    define at h1
    have h2 := match_pair h h1
    exact And.intro h2.right h2.left
    done
  · -- proof that match_from (inv R) Y ∧ match_from (inv (inv R)) X
    rewrite [invRel_invRel]
    define at h
    exact And.intro h.right.right h.right.left
    done
  done

theorem match_unique {A B : Type} {R : Rel A B} {X : Set A} {j : A} {u v : B}
    (h1 : match_from R X) (h2 : j ∈ X) (h3 : R j u) (h4 : R j v) : u = v := by
  define at h1
  have h5 := h1 j h2
  obtain z _h6 h7 from h5
  exact h7 u v h3 h4
  done

def remove_one {A B : Type} (R : Rel A B) (u : A) (v : B) (x : A) (y : B) : Prop :=
    x ≠ u ∧ y ≠ v ∧ (R x y ∨ (R x v ∧ R u y))

theorem remove_one_pair {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {x u : A} {y v : B}
    (h1 : matching R X Y) (h2 : remove_one R u v x y) : x ∈ X \ {u} ∧ y ∈ Y \ {v} := by
  define at h2
  have h3 : x ∈ X ∧ y ∈ Y := by
    by_cases on h2.right.right with h3
    · -- Case 1. h3: R x y
      exact match_pair h1 h3
      done
    · -- Case 2. h3: R x v ∧ R y u
      have h4 := match_pair h1 h3.left
      have h5 := match_pair h1 h3.right
      exact And.intro h4.left h5.right
      done
    done
  exact And.intro (And.intro h3.left h2.left) (And.intro h3.right h2.right.left)
  done

theorem remove_inv_comm {A B : Type} (R : Rel A B) (u : A) (v : B) :
    invRel (remove_one R u v) = remove_one (invRel R) v u := by
  apply RelExt
  fix b; fix a
  define : invRel (remove_one R u v) b a
  define : remove_one (invRel R) v u b a
  rewrite [invRel_def, invRel_def, invRel_def]
  rewrite [←and_assoc, @and_comm (¬a = u), and_assoc, @and_comm (R a v)]
  rfl
  done

theorem remove_iff_1 {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {x u : A} {v : B}
    (h1 : matching R X Y) (h2 : x ≠ u) (h3 : R x v) :
    ∀ (y : B), remove_one R u v x y ↔ R u y := by
  fix y
  have h4 := match_pair h1 h3
  apply Iff.intro
  · -- (→)
    assume h5
    define at h5
    by_cases on h5.right.right with h6
    · -- Case 1. h6: (x, y) ∈ R
      have h7 := match_unique h1.right.left h4.left h6 h3
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
    exact match_unique h1.right.right h4.right h3 h5
    done
  done

theorem remove_iff_2 {A B : Type} {R : Rel A B} {x u : A} {v : B}
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

theorem unique_in_remove_one {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {w x u : A} {v : B}
    (h1 : matching R X Y) (h2 : w ∈ X) (h3 : ∀ (y : B), remove_one R u v x y ↔ R w y) :
    ∃! (y : B), remove_one R u v x y := by
  have h4 := h1.right.left w h2
  define at h4; define
  obtain z h5 from h4
  apply Exists.intro z
  rewrite [h3 z]
  apply And.intro h5.left
  fix y1
  rewrite [h3 y1]
  exact h5.right y1
  done

theorem remove_one_match_from {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {u : A}
    (h1 : matching R X Y) (h2 : u ∈ X) (v : B): match_from (remove_one R u v) (X \ {u}) := by
  define
  fix x
  assume h4
  define at h4
  by_cases h5 : R x v
  · -- Case 1. h5: R x v
    exact unique_in_remove_one h1 h2 (remove_iff_1 h1 h4.right h5)
    done
  · -- Case 2. h5: ¬R x v
    exact unique_in_remove_one h1 h4.left (remove_iff_2 h4.right h5)
    done
  done

theorem remove_one_matching {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {u : A} {v : B}
    (h1 : matching R X Y) (h2 : u ∈ X) (h3 : v ∈ Y) :
    matching (remove_one R u v) (X \ {u}) (Y \ {v}) := by
  define
  apply And.intro
  · -- Proof of pairing
    define
    fix x; fix y
    assume h4
    exact remove_one_pair h1 h4
    done
  · -- Proof of match_froms
    apply And.intro (remove_one_match_from h1 h2 v)
    rewrite [remove_inv_comm]
    exact remove_one_match_from (match_inv h1) h3 u
  done

theorem empty_match_from {A B : Type} {R : Rel A B} {X : Set A} (h : empty X) : match_from R X := by
  define
  fix x
  assume h1
  define at h
  contradict h
  exact Exists.intro x h1
  done

def one_match {A B : Type} (a : A) (b : B) (x : A) (y : B) : Prop :=
    x = a ∧ y = b

theorem one_elt_match_from {A B : Type} (a : A) (b : B) :
    match_from (one_match a b) {a} := by
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

/- Basic theorems about finite sets and number of elements -/

theorem remove_one_equinum {A B : Type} {X : Set A} {Y : Set B} {x : A} {y : B}
    (h1 : equinum X Y) (h2 : x ∈ X) (h3 : y ∈ Y) : equinum (X \ { x }) (Y \ { y }) := by
  define
  obtain R h4 from h1
  apply Exists.intro (remove_one R x y)
  exact remove_one_matching h4 h2 h3
  done

theorem remove_one_numElts {A : Type} {X : Set A} {n : Nat} {x : A}
    (h1 : numElts X (n + 1)) (h2 : x ∈ X) : numElts (X \ {x}) n := by
  have h3 : n + 1 ∈ I (n + 1) := I_top (Nat.zero_lt_succ n)
  unfold numElts at h1
  have h4 := remove_one_equinum h1 h3 h2
  rewrite [I_diff] at h4
  exact h4
  done

def empty_match {A B : Type} (a : A) (b : B) : Prop := False

theorem zero_elts_iff_empty {A : Type} (X : Set A) : numElts X 0 ↔ empty X := by
  apply Iff.intro
  · -- (→)
    assume h1
    define
    by_contra h2
    obtain x h3 from h2
    define at h1
    obtain R h4 from h1
    obtain j h5 _h6 from h4.right.right x h3
    define at h5
    have h7 := match_pair h4 h5
    contradict I_0_empty
    exact Exists.intro j h7.left
    done
  · -- (←)
    assume h1
    define
    apply Exists.intro empty_match
    define
    apply And.intro
    · -- Proof of pairing
      define
      fix n; fix a
      assume h2
      exact False.elim h2
      done
    · -- Proofs of match_from
      apply And.intro
      · -- Proof of match_from empty_match (I 0)
        exact empty_match_from I_0_empty
        done
      · -- Proof of match_from (invRel empty_match) X
        exact empty_match_from h1
        done
      done
    done
  done

theorem one_elt_iff_singleton {A : Type} (X : Set A) : numElts X 1 ↔ ∃ (x : A), X = {x} := by
  define : numElts X 1
  rewrite [I_1_singleton]
  apply Iff.intro
  · -- (→)
    assume h1
    obtain R h2 from h1
    have h3 : 1 ∈ {1} := by define; rfl
    obtain x h4 _h5 from h2.right.left 1 h3
    have h6 := match_pair h2 h4
    apply Exists.intro x
    apply Set.ext
    fix a
    apply Iff.intro
    · -- (→)
      assume h7
      define
      have h8 := h2.right.right a h7
      obtain j h9 _h10 from h8
      define at h9
      have h11 := match_pair h2 h9
      have h12 := h11.left
      define at h12
      rewrite [h12] at h9
      exact match_unique h2.right.left h3 h9 h4
      done
    · -- (←)
      assume h7
      define at h7
      rewrite [h7]
      exact h6.right
      done
    done
  · -- (←)
    assume h1
    obtain x h2 from h1
    set R : Rel Nat A := one_match 1 x
    apply Exists.intro R
    define
    apply And.intro
    · -- Proof of pairing R {1} X
      define
      fix n; fix a
      assume h3
      define at h3
      rewrite [h3.left, h3.right, h2]
      apply And.intro
      · -- Proof that 1 ∈ {1}
        define
        rfl
        done
      · -- Proof that x ∈ {x}
        define
        rfl
        done
      done
    · -- Proof of matchings
      apply And.intro
      · -- Proof that match_from R {1}
        exact one_elt_match_from 1 x
        done
      · -- Proof that match_from (inv R) X
        have h3 : invRel R = one_match x 1 := by
          apply RelExt
          fix y; fix n
          define : invRel R y n
          define : one_match x 1 y n
          rewrite [and_comm]
          rfl
          done
        rewrite [h2, h3]     
        exact one_elt_match_from x 1
        done
      done
    done
  done

theorem nonempty_of_pos_numElts {A : Type} {X : Set A} {n : Nat}
    (h1 : numElts X n) (h2 : n > 0) : ∃ (x : A), x ∈ X := by
  obtain R h3 from h1
  have h4 : 1 ∈ I n := I_1 h2
  have h5 := h3.right.left 1 h4
  obtain x h6 _h7 from h5
  have h8 := match_pair h3 h6
  exact Exists.intro x h8.right